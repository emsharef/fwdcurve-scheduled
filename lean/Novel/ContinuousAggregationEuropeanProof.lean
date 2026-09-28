import Standalone.ContinuousAggregationEuropean
import Novel.ContinuousAggregationLevelProof
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Claim 054 (b), (c): the post-cutoff state and European post-cutoff cash claims (proof)

`cell_sum` and `riem_tendsto`: dyadic Riemann sums of a continuous function converge to its
integral (uniform continuity on a compact interval). With it, `J_t(Ξ) = ∫_A^t (Y_s − Y_A) ds` on
every path, and integrating (54.2) at `U = s` over `[A, t]` gives `∫_A^t r = Λ_{V_A}(t, y_A, Ξ)`.

Reused, not reproved: `Novel.ContinuousAggregationCurveProof.curveS_aux`, `g_ii`, `gc_ii`;
`Novel.DiffusionMeetingGaussProof.int_step`, `step_ii`; `Novel.SpliceCrossTermDriftProof.ii_bdd`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.ContinuousAggregationEuropeanProof

/-! ### Dyadic Riemann sums -/

/-- The uniform-mesh left-open Riemann sum of `φ` on `[c 0, c m]`: with `c j = c₀ + j h`,
`Σ_{j < m} h φ(c_{j+1})` is within `m h ε` of `∫_{c 0}^{c m} φ` when `φ` varies by at most `ε` on
each cell. -/
lemma cell_sum (φ : ℝ → ℝ) (hφ : Continuous φ) (c₀ h ε : ℝ) (hh : 0 ≤ h) (m : ℕ)
    (hε : ∀ j < m, ∀ s ∈ Icc (c₀ + j * h) (c₀ + (j + 1) * h), |φ (c₀ + (j + 1) * h) - φ s| ≤ ε) :
    |∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) - ∫ s in c₀..(c₀ + m * h), φ s| ≤ m * h * ε := by
  have hint : ∀ j < m, IntervalIntegrable φ volume (c₀ + j * h) (c₀ + ((j + 1 : ℕ) : ℝ) * h) :=
    fun j _ => hφ.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => c₀ + j * h) hint
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range m, |h * φ (c₀ + (j + 1) * h) - ∫ s in (c₀ + j * h)..(c₀ + ((j + 1 : ℕ) : ℝ) * h), φ s|
      ≤ ∑ j ∈ Finset.range m, h * ε := Finset.sum_le_sum fun j hj => by
        have hle : c₀ + j * h ≤ c₀ + ((j + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
        have e : h * φ (c₀ + (j + 1) * h) = ∫ s in (c₀ + j * h)..(c₀ + ((j + 1 : ℕ) : ℝ) * h),
            φ (c₀ + (j + 1) * h) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
        rw [e, ← intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _)]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c₀ + j * h)
          (b := c₀ + ((j + 1 : ℕ) : ℝ) * h) (C := ε)
          (f := fun s => φ (c₀ + (j + 1) * h) - φ s) fun s hs => by
            rw [uIoc_of_le hle] at hs
            rw [Real.norm_eq_abs]
            exact hε j (Finset.mem_range.1 hj) s ⟨hs.1.le, by push_cast at hs; exact hs.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle)] at this
        push_cast at this ⊢
        calc _ ≤ ε * (c₀ + (j + 1) * h - (c₀ + j * h)) := this
          _ = h * ε := by ring
    _ = m * h * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Dyadic Riemann sums of a continuous function converge to its integral: the points
`(⌊A 2ⁿ⌋ + j + 1)/2ⁿ`, `j < ⌊t 2ⁿ⌋ − ⌊A 2ⁿ⌋`, are the dyadic points of `(A, t]`. -/
lemma riem_tendsto (φ : ℝ → ℝ) (hφ : Continuous φ) {A t : ℝ} (hAt : A ≤ t) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋).toNat,
      φ ((⌊A * 2 ^ n⌋ + j + 1) / 2 ^ n) / 2 ^ n) atTop (𝓝 (∫ s in A..t, φ s)) := by
  set K := Icc (A - 1) (t + 1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := K) hφ.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC A ⟨by linarith, by linarith⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hL : 0 < t - A + 1 := by linarith
  set ε' := ε / (4 * (t - A + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ.continuousOn) ε' hε'
  set η := min (min δ 1) (ε / (8 * (C + 1)))
  have hη : 0 < η := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set h : ℝ := (1 / 2) ^ n
  have hh0 : 0 < h := by positivity
  have hhη : h < η := lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hN
  have hhδ : h < δ := lt_of_lt_of_le hhη ((min_le_left _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := (lt_of_lt_of_le hhη ((min_le_left _ _).trans (min_le_right _ _))).le
  have hhC : h < ε / (8 * (C + 1)) := lt_of_lt_of_le hhη (min_le_right _ _)
  have h2n : (2:ℝ) ^ n = h⁻¹ := by simp [h, one_div, inv_pow]
  have h2h : (2:ℝ) ^ n * h = 1 := by rw [h2n, inv_mul_cancel₀ hh0.ne']
  set K0 := ⌊A * 2 ^ n⌋
  set K1 := ⌊t * 2 ^ n⌋
  have hK : K0 ≤ K1 := Int.floor_mono (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n])
  set m := (K1 - K0).toNat
  have hm : (m : ℝ) = K1 - K0 := by
    rw [show (m : ℝ) = ((m : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  set c₀ : ℝ := K0 * h
  have hc0 : c₀ ≤ A ∧ A < c₀ + h := by
    have h1 := Int.floor_le (A * 2 ^ n)
    have h2 := Int.lt_floor_add_one (A * 2 ^ n)
    constructor
    · have := mul_le_mul_of_nonneg_right h1 hh0.le
      rwa [mul_assoc, h2h, mul_one] at this
    · have := mul_lt_mul_of_pos_right h2 hh0
      rwa [mul_assoc, h2h, mul_one, add_mul, one_mul] at this
  have hcm : c₀ + m * h ≤ t ∧ t < c₀ + m * h + h := by
    have h1 := Int.floor_le (t * 2 ^ n)
    have h2 := Int.lt_floor_add_one (t * 2 ^ n)
    have e : c₀ + m * h = K1 * h := by rw [hm]; ring
    rw [e]
    constructor
    · have := mul_le_mul_of_nonneg_right h1 hh0.le
      rwa [mul_assoc, h2h, mul_one] at this
    · have := mul_lt_mul_of_pos_right h2 hh0
      rwa [mul_assoc, h2h, mul_one, add_mul, one_mul] at this
  -- the sum in cell form
  have hsum : ∑ j ∈ Finset.range m, φ ((K0 + j + 1) / 2 ^ n) / 2 ^ n =
      ∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2n, div_inv_eq_mul, div_inv_eq_mul]
    simp only [c₀]
    rw [mul_comm]
    congr 2
    ring
  have hcell := cell_sum φ hφ c₀ h ε' hh0.le m fun j hj s hs => by
    have hcj : c₀ + (j + 1) * h ≤ c₀ + m * h := by
      have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
      nlinarith
    have hmem1 : c₀ + (j + 1) * h ∈ K := ⟨by nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)], by linarith⟩
    have hmem2 : s ∈ K := ⟨by nlinarith [hs.1, (Nat.cast_nonneg j : (0:ℝ) ≤ j)], by linarith [hs.2]⟩
    have hd : dist (c₀ + (j + 1) * h) s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]
    exact (hUC _ hmem1 _ hmem2 hd).le
  -- the two boundary pieces
  have hb : ∀ a b, a ≤ b → b - a ≤ h → a ∈ K → b ∈ K → |∫ s in a..b, φ s| ≤ C * h := fun a b hab hba ha hb => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C) (f := φ)
      fun s hs => by
        rw [uIoc_of_le hab] at hs
        exact hC s ⟨ha.1.trans hs.1.le, hs.2.trans hb.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
    exact this.trans (mul_le_mul_of_nonneg_left hba hC0)
  have hKc0 : c₀ ∈ K := ⟨by linarith [hc0.2], by linarith [hc0.1]⟩
  have hKcm : c₀ + m * h ∈ K := ⟨by nlinarith [hc0.2, hcm.2], by linarith [hcm.1]⟩
  have b1 := hb c₀ A hc0.1 (by linarith [hc0.2]) hKc0 ⟨by linarith, by linarith⟩
  have b2 := hb (c₀ + m * h) t hcm.1 (by linarith [hcm.2]) hKcm ⟨by linarith, by linarith⟩
  have hsplit : ∫ s in A..t, φ s = (∫ s in c₀..(c₀ + m * h), φ s) +
      (∫ s in (c₀ + m * h)..t, φ s) - ∫ s in c₀..A, φ s := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable (μ := volume) c₀ A)
      (hφ.intervalIntegrable A t)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable (μ := volume) c₀ (c₀ + m * h)) (hφ.intervalIntegrable (c₀ + m * h) t)
    linarith
  have hmh : (m : ℝ) * h ≤ t - A + 1 := by linarith [hc0.2, hcm.1]
  rw [Real.dist_eq, hsum, hsplit]
  have hε'bd : (m : ℝ) * h * ε' ≤ ε / 4 := by
    calc (m : ℝ) * h * ε' ≤ (t - A + 1) * ε' := mul_le_mul_of_nonneg_right hmh hε'.le
      _ = ε / 4 := by simp only [ε']; field_simp
  have hCh : C * h ≤ ε / 8 := by
    have : C * h ≤ (C + 1) * h := by nlinarith
    calc C * h ≤ (C + 1) * h := this
      _ ≤ (C + 1) * (ε / (8 * (C + 1))) := mul_le_mul_of_nonneg_left hhC.le (by linarith)
      _ = ε / 8 := by field_simp
  calc |∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) -
        ((∫ s in c₀..(c₀ + m * h), φ s) + (∫ s in (c₀ + m * h)..t, φ s) - ∫ s in c₀..A, φ s)|
      ≤ |∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) - ∫ s in c₀..(c₀ + m * h), φ s| +
        |∫ s in (c₀ + m * h)..t, φ s| + |∫ s in c₀..A, φ s| := by
        have := abs_sub (∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) -
          ∫ s in c₀..(c₀ + m * h), φ s) ((∫ s in (c₀ + m * h)..t, φ s) - ∫ s in c₀..A, φ s)
        have h2 := abs_sub (∫ s in (c₀ + m * h)..t, φ s) (∫ s in c₀..A, φ s)
        calc _ = |(∑ j ∈ Finset.range m, h * φ (c₀ + (j + 1) * h) -
              ∫ s in c₀..(c₀ + m * h), φ s) - ((∫ s in (c₀ + m * h)..t, φ s) -
                ∫ s in c₀..A, φ s)| := by ring_nf
          _ ≤ _ := by linarith
    _ ≤ ε / 4 + ε / 8 + ε / 8 := by linarith
    _ < ε := by linarith

/-! ### (b): the post-cutoff state and `Λ` -/

open Standalone.CompoundedFuturesIdentification (w d)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw rate)
open Standalone.DiffusionMeetingPricing (QS Qacc disc P0)
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationEuropean

lemma dy_cast (A : ℝ) (n j : ℕ) : ((dy A n j : ℚ) : ℝ) = (⌊A * 2 ^ n⌋ + j + 1) / 2 ^ n := by
  simp [dy]

/-- The dyadic points used by `riem` lie in `(A, t]`. -/
lemma dy_mem {A t : ℝ} (n j : ℕ) (hj : j < (⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋).toNat) :
    A < (dy A n j : ℝ) ∧ (dy A n j : ℝ) ≤ t := by
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [dy_cast]
  have hj' : (⌊A * 2 ^ n⌋ + j + 1 : ℤ) ≤ ⌊t * 2 ^ n⌋ := by omega
  constructor
  · rw [lt_div_iff₀ h2]
    have := Int.lt_floor_add_one (A * 2 ^ n)
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · rw [div_le_iff₀ h2]
    have h1 := Int.floor_le (t * 2 ^ n)
    have : ((⌊A * 2 ^ n⌋ + j + 1 : ℤ) : ℝ) ≤ ⌊t * 2 ^ n⌋ := by exact_mod_cast hj'
    push_cast at this
    linarith

/-- `J_t` depends on `ξ` only through its coordinates `q ≤ t`. -/
lemma J_local (A H t : ℝ) (ξ ξ' : Rat' A H → ℝ) (h : ∀ q : Rat' A H, (q.1 : ℝ) ≤ t → ξ q = ξ' q) :
    J A H t ξ = J A H t ξ' := by
  unfold J
  congr 1
  funext n
  unfold riem
  refine Finset.sum_congr rfl fun j hj => ?_
  split_ifs with hq
  · rw [h ⟨_, hq⟩ (dy_mem n j (Finset.mem_range.1 hj)).2]
  · rfl

/-- The convention for `J_t` where the limsup is not finite (Red's note 2 on Claim 054): Lean's
`limsup` on `ℝ` is `0` when the Riemann sums are not eventually bounded above. -/
lemma J_unbounded (A H t : ℝ) (ξ : Rat' A H → ℝ)
    (h : ¬ ∃ a, ∀ᶠ n in atTop, riem A H t n ξ ≤ a) : J A H t ξ = 0 := by
  unfold J
  rw [limsup_eq]
  have e : {a | ∀ᶠ n in atTop, riem A H t n ξ ≤ a} = ∅ := by
    ext a
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun ha => h ⟨a, ha⟩
  rw [e, Real.sInf_empty]

/-- The same convention when the Riemann sums tend to `−∞`: `J_t = 0`. -/
lemma J_atBot (A H t : ℝ) (ξ : Rat' A H → ℝ)
    (h : Tendsto (fun n => riem A H t n ξ) atTop atBot) : J A H t ξ = 0 := by
  unfold J
  rw [limsup_eq]
  have e : {a | ∀ᶠ n in atTop, riem A H t n ξ ≤ a} = univ := by
    ext a
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact h.eventually_le_atBot a
  rw [e, Real.sInf_of_not_bddBelow fun ⟨b, hb⟩ => by
    have := hb (mem_univ (b - 1)); linarith]

/-- On a continuous path, `J_t(Ξ) = ∫_A^t (Y_s − Y_A) ds`. -/
lemma J_path {A H t : ℝ} (hAt : A ≤ t) (htH : t ≤ H) (y : ℝ → ℝ) (hy : Continuous y) :
    J A H t (fun q => y q.1 - y A) = ∫ s in A..t, (y s - y A) := by
  have hφ : Continuous fun s => y s - y A := hy.sub continuous_const
  have ht := riem_tendsto (fun s => y s - y A) hφ hAt
  have e : ∀ n, riem A H t n (fun q => y q.1 - y A) =
      ∑ j ∈ Finset.range (⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋).toNat,
        (y ((⌊A * 2 ^ n⌋ + j + 1) / 2 ^ n) - y A) / 2 ^ n := fun n => by
    unfold riem
    refine Finset.sum_congr rfl fun j hj => ?_
    have hm := dy_mem (A := A) (t := t) n j (Finset.mem_range.1 hj)
    rw [dite_eq_left ⟨hm.1, hm.2.trans htH⟩]
    show (y (dy A n j : ℝ) - y A) / 2 ^ n = _
    rw [dy_cast]
  unfold J
  simp only [e]
  exact ht.limsup_eq

section Path
variable {Ω : Type*} {N : ℕ} (M : DiffModel Ω N) (hg : Measurable M.g) (hB : ∃ C, ∀ s, |M.g s| ≤ C)
include hg hB

/-- `s ↦ ∫_A^s g(u)(s − u) du` is continuous. -/
lemma inner_cont (A : ℝ) : Continuous fun s => ∫ u in A..s, M.g u * (s - u) := by
  have i0 := Novel.ContinuousAggregationCurveProof.g_ii M hg hB
  have i1 : ∀ x y, IntervalIntegrable (fun u => u * M.g u) volume x y := fun x y => by
    simpa only [mul_comm, id] using
      Novel.ContinuousAggregationCurveProof.gc_ii M hg hB (φ := id) continuous_id x y
  have e : (fun s => ∫ u in A..s, M.g u * (s - u)) =
      fun s => s * (∫ u in A..s, M.g u) - ∫ u in A..s, u * M.g u := by
    funext s
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((i0 A s).const_mul s) (i1 A s)]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [e]
  exact (continuous_id.mul (intervalIntegral.continuous_primitive i0 A)).sub
    (intervalIntegral.continuous_primitive i1 A)

/-- (b): on every path, `∫_A^t r = Λ_{V_A}(t, y_A, Ξ)`. -/
theorem rate_Lam (hf0 : Measurable M.f0) (hf0B : ∃ C, ∀ s, |M.f0 s| ≤ C)
    (hY : ∀ ω, Continuous fun u => M.Y u ω) {A H t : ℝ} (hAt : A ≤ t) (htH : t ≤ H) (ω : Ω) :
    ∫ u in A..t, rate M u ω = Lam M A H (Qacc M A) t (yA M A ω) (Xi M A H ω) := by
  obtain ⟨C, hC⟩ := hf0B
  have hr : ∀ s ∈ uIcc A t, rate M s ω = M.f0 s + yA M A ω + Qacc M A * (s - A) +
      ∑ i, (if A < M.T i ∧ M.T i ≤ s then M.Z i ω + M.v i * (s - M.T i) else 0) +
      (M.Y s ω - M.Y A ω) + ∫ u in A..s, M.g u * (s - u) := fun s hs => by
    rw [uIcc_of_le hAt] at hs
    exact Novel.ContinuousAggregationCurveProof.curveS_aux M hg hB A s s hs.1 ω
  have i1 : IntervalIntegrable M.f0 volume A t := Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC A t
  have i3 : IntervalIntegrable (fun s => Qacc M A * (s - A)) volume A t :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have istep : ∀ i, IntervalIntegrable
      (fun s => if A < M.T i ∧ M.T i ≤ s then M.Z i ω + M.v i * (s - M.T i) else 0) volume A t :=
    fun i => by
      by_cases hAT : A < M.T i
      · simpa only [hAT, true_and] using
          Novel.DiffusionMeetingGaussProof.step_ii (M.T i) (M.Z i ω) (M.v i) A t
      · simp only [hAT, false_and, ite_false]; exact intervalIntegrable_const
  have i4 : IntervalIntegrable (fun s => ∑ i,
      (if A < M.T i ∧ M.T i ≤ s then M.Z i ω + M.v i * (s - M.T i) else 0)) volume A t := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => istep i
    convert this using 1
    funext s; simp [Finset.sum_apply]
  have i5 : IntervalIntegrable (fun s => M.Y s ω - M.Y A ω) volume A t :=
    ((hY ω).sub continuous_const).intervalIntegrable _ _
  have i6 : IntervalIntegrable (fun s => ∫ u in A..s, M.g u * (s - u)) volume A t :=
    (inner_cont M hg hB A).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr hr,
    intervalIntegral.integral_add (((i1.add intervalIntegrable_const).add i3).add i4 |>.add i5) i6,
    intervalIntegral.integral_add (((i1.add intervalIntegrable_const).add i3).add i4) i5,
    intervalIntegral.integral_add ((i1.add intervalIntegrable_const).add i3) i4,
    intervalIntegral.integral_add (i1.add intervalIntegrable_const) i3,
    intervalIntegral.integral_add i1 intervalIntegrable_const,
    intervalIntegral.integral_finsetSum fun i _ => istep i,
    J_path hAt htH (fun u => M.Y u ω) (hY ω) |>.symm]
  have hsum : ∀ i, ∫ s in A..t,
      (if A < M.T i ∧ M.T i ≤ s then M.Z i ω + M.v i * (s - M.T i) else 0) =
      if A < M.T i ∧ M.T i ≤ t then (Xi M A H ω).1 i * (t - M.T i) + M.v i * (t - M.T i) ^ 2 / 2
      else 0 := fun i => by
    by_cases hAT : A < M.T i
    · simp only [hAT, true_and, Xi, ite_true]
      rw [Novel.DiffusionMeetingGaussProof.int_step hAt, w, d,
        max_eq_right (by linarith : A - M.T i ≤ 0)]
      by_cases hTt : M.T i ≤ t
      · rw [ite_eq_left hTt, max_eq_left (by linarith)]; ring
      · rw [ite_eq_right hTt, max_eq_right (by linarith [not_le.1 hTt])]; ring
    · simp only [hAT, false_and, ite_false, intervalIntegral.integral_zero]
  simp only [hsum, intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  have hJ : (Xi M A H ω).2 = fun q => M.Y q.1 ω - M.Y A ω := rfl
  unfold Lam
  rw [hJ]
  ring

end Path

/-! ### Measurability of `Λ` -/

lemma riem_meas (A H t : ℝ) (n : ℕ) : Measurable (riem A H t n) := by
  unfold riem
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases hc : A < (dy A n j : ℝ) ∧ (dy A n j : ℝ) ≤ H
  · simp only [dite_eq_left hc]
    exact (measurable_pi_apply _).div_const _
  · simp only [dite_eq_right hc, zero_div]
    exact measurable_const

lemma J_meas (A H t : ℝ) : Measurable (J A H t) := by
  unfold J
  exact Measurable.limsup fun n => riem_meas A H t n

lemma Lam_meas {Ω : Type*} {N : ℕ} (M : DiffModel Ω N) (A H V t : ℝ) :
    Measurable fun p : ℝ × State N A H => Lam M A H V t p.1 p.2 := by
  unfold Lam
  refine ((((measurable_const.add (measurable_fst.mul_const _)).add measurable_const).add
    (Finset.measurable_sum _ fun i _ => ?_)).add
      ((J_meas A H t).comp (measurable_snd.comp measurable_snd))).add measurable_const
  by_cases h : A < M.T i ∧ M.T i ≤ t
  · simp only [h, and_self, ite_true]
    exact (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).mul_const _).add
      measurable_const
  · simp only [h, ite_false]
    exact measurable_const

theorem lambdaS : lambdaStatement := fun _ _ M hg hB hf0 hf0B hY A H t _ hAt htH =>
  ⟨fun ω => rate_Lam M hg hB hf0 hf0B hY hAt htH ω, fun V => Lam_meas M A H V t,
    fun ξ ξ' h => J_local A H t ξ ξ' h⟩

/-! ### (c): the law of `(y_A, Ξ)` under `Q^A` -/

open Standalone.DiffusionMeetingGauss (Integrand)
open Standalone.ContinuousAggregationLevel
open Novel.DiffusionMeetingGaussProof (comb comb_meas)
open Novel.ContinuousAggregationLevelProof

section Model
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

/-- `1_{(A, q]}`, the integrand of `Y_q − Y_A`. -/
noncomputable def ind (A q : ℝ) : ℝ → ℝ := (Ioc A q).indicator 1

omit m₀ in
lemma ind_future {A : ℝ} (hA : 0 ≤ A) {q : ℝ} (hqH : q ≤ H) :
    Future M H A 0 (ind A q) := by
  refine ⟨fun i h => absurd rfl h, ⟨measurable_one.indicator measurableSet_Ioc, ⟨1, fun s => ?_⟩,
    fun s hs => ?_⟩, fun s hs => ?_⟩
  · by_cases h : s ∈ Ioc A q <;> simp [ind, indicator, h]
  · by_cases h : s ∈ Ioc A q
    · exact ⟨hA.trans h.1.le, h.2.trans hqH⟩
    · simp [ind, indicator, h] at hs
  · by_cases h : s ∈ Ioc A q
    · exact h.1
    · simp [ind, indicator, h] at hs

omit m₀ in
lemma single_future {A : ℝ} {i : Fin N} (hi : A < M.T i) (H : ℝ) :
    Future M H A (Pi.single i 1) (fun _ => 0) := by
  refine ⟨fun j hj => ?_, integrand_zero H, fun _ h => absurd rfl h⟩
  by_cases h : j = i
  · rw [h]; exact hi
  · simp [h] at hj

/-- `Y_q − Y_A = I(1_{(A, q]})` almost surely. -/
lemma Y_incr (hG : GaussLaw M Q H) {A q : ℝ} (hA : 0 ≤ A) (hAq : A ≤ q) (hqH : q ≤ H) :
    (fun ω => M.Y q ω - M.Y A ω) =ᵐ[Q] inc M 0 (ind A q) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlin, -, -, -, hY, -⟩ := id hG
  have hq := f1_integrand (A := q) hqH
  have hAi := f1_integrand (A := A) (hAq.trans hqH)
  have e : (fun s => (Icc 0 q).indicator (1 : ℝ → ℝ) s + -1 * (Icc 0 A).indicator 1 s) =
      ind A q := by
    funext s
    by_cases h1 : 0 ≤ s <;> by_cases h2 : s ≤ A <;> by_cases h3 : s ≤ q <;>
      simp [ind, indicator, h1, h2, h3] <;> linarith
  have hl := hlin _ _ (-1) hq hAi
  rw [e] at hl
  filter_upwards [hY q (hA.trans hAq) hqH, hY A hA (hAq.trans hqH), hl] with ω h1 h2 h3
  simp only [inc, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, h1, h2, h3]
  ring

/-- The future-increment version of `Ξ`. -/
noncomputable def Xi' (M : DiffModel Ω N) (A H : ℝ) (ω : Ω) : State N A H :=
  (fun i => if A < M.T i then inc M (Pi.single i 1) (fun _ => 0) ω else 0,
    fun q => inc M 0 (ind A q.1) ω)

lemma Xi'_meas (_hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) :
    Measurable[futureAlg M H A] (Xi' M A H) := by
  have hF : ∀ β f, Future M H A β f → Measurable[futureAlg M H A] (inc M β f) := fun β f h =>
    Measurable.of_comap_le (by unfold futureAlg; exact le_iSup₂_of_le (β, f) h le_rfl)
  refine Measurable.prodMk (@Measurable.of_eval _ _ _ (futureAlg M H A) _ _ fun i => ?_)
    (@Measurable.of_eval _ _ _ (futureAlg M H A) _ _ fun q => ?_)
  · by_cases hi : A < M.T i
    · simp only [hi, ite_true]; exact hF _ _ (single_future hi H)
    · simp only [hi, ite_false]; exact measurable_const
  · exact hF _ _ (ind_future (M := M) hA q.2.2)

lemma Xi_ae (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) : Xi M A H =ᵐ[Q] Xi' M A H := by
  have h1 : ∀ i, ∀ᵐ ω ∂Q, (if A < M.T i then M.Z i ω else 0) =
      (if A < M.T i then inc M (Pi.single i 1) (fun _ => 0) ω else 0) := fun i => by
    filter_upwards [I_zero hG] with ω hω
    split_ifs
    · simp [inc, hω, Pi.single_apply]
    · rfl
  have h2 : ∀ q : Rat' A H, ∀ᵐ ω ∂Q, M.Y q.1 ω - M.Y A ω = inc M 0 (ind A q.1) ω := fun q =>
    Y_incr hG hA q.2.1.le q.2.2
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2] with ω e1 e2
  exact Prod.ext (funext e1) (funext e2)

lemma Xi_aem (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) : AEMeasurable (Xi M A H) Q :=
  ((Xi'_meas hG hA).mono (futureAlg_le hG A) le_rfl).aemeasurable.congr (Xi_ae hG hA).symm

lemma QS_prob [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    IsProbabilityMeasure (QS M Q A) := by
  obtain ⟨ρ, -, h1, hQS⟩ := QS_density hG hA hAH
  exact ⟨by rw [hQS, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1]⟩

/-- Under `Q^A`, `(y_A, Ξ)` has law `N(0, V_A) ⊗ law_Q(Ξ)`. -/
theorem law_pair [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A)
    (hAH : A ≤ H) :
    (QS M Q A).map (fun ω => (yA M A ω, Xi M A H ω)) =
      (gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H)) := by
  have := QS_prob hG hA hAH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -⟩ := id hG
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  set y' : Ω → ℝ := fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω
  have hy'F : Measurable[M.F A] y' := yA'_meas hG
  have hy' : Measurable y' := hy'F.mono (hFle A) le_rfl
  have hX'F := Xi'_meas hG hA (A := A) (H := H)
  have hX' : Measurable (Xi' M A H) := hX'F.mono (futureAlg_le hG A) le_rfl
  have hyae : yA M A =ᵐ[QS M Q A] y' := hac.ae_le (yA_ae hG hA hAH)
  have hXae : Xi M A H =ᵐ[QS M Q A] Xi' M A H := hac.ae_le (Xi_ae hG hA)
  have hind : IndepFun y' (Xi' M A H) (QS M Q A) := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (futureAlg_QS hG hA hAH).1
      hX'F.comap_le) hy'F.comap_le).symm
  have hlawy : (QS M Q A).map y' = gaussianReal 0 (Qacc M A).toNNReal := by
    rw [← Measure.map_congr hyae]; exact (law_yA hG hA hAH).map_eq
  have hlawX : (QS M Q A).map (Xi' M A H) = Q.map (Xi M A H) := by
    rw [Measure.map_congr (Xi_ae hG hA)]
    ext B hB
    rw [Measure.map_apply hX' hB, Measure.map_apply hX' hB]
    exact (futureAlg_QS hG hA hAH).2 _ (hX'F hB)
  rw [Measure.map_congr (hyae.prodMk hXae),
    (indepFun_iff_map_prod_eq_prod_map_map hy'.aemeasurable hX'.aemeasurable).1 hind, hlawy,
    hlawX]

end Model

/-! ### (c): European post-cutoff cash claims -/

section Path2
variable {Ω : Type*} {N : ℕ} (M : DiffModel Ω N)

/-- The short-rate path is interval integrable. -/
lemma rate_ii (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) (hf0 : Measurable M.f0)
    {C : ℝ} (hC : ∀ s, |M.f0 s| ≤ C) (hY : ∀ ω, Continuous fun u => M.Y u ω) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun u => rate M u ω) volume a b := by
  have i1 : IntervalIntegrable M.f0 volume a b := Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC a b
  have i2 : IntervalIntegrable (fun u => ∑ n, (if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n)
      else 0)) volume a b := by
    have := IntervalIntegrable.sum Finset.univ fun n _ =>
      Novel.DiffusionMeetingGaussProof.step_ii (M.T n) (M.Z n ω) (M.v n) a b
    convert this using 1
    funext u; simp [Finset.sum_apply]
  have i3 : IntervalIntegrable (fun u => M.Y u ω) volume a b := (hY ω).intervalIntegrable a b
  have i4 := (Novel.DiffusionMeetingGaussProof.drift_cont (M := M) hg hB).intervalIntegrable
    (μ := volume) a b
  exact ((i1.add i2).add i3).add i4

/-- `B_S⁻¹ = B_A⁻¹ e^{−Λ_{V_A}(S, y_A, Ξ)}` on every path. -/
lemma disc_split (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) (hf0 : Measurable M.f0)
    {C : ℝ} (hC : ∀ s, |M.f0 s| ≤ C) (hY : ∀ ω, Continuous fun u => M.Y u ω) {A S H : ℝ}
    (hAS : A ≤ S) (hSH : S ≤ H) (ω : Ω) :
    disc M S ω = disc M A ω * Real.exp (-Lam M A H (Qacc M A) S (yA M A ω) (Xi M A H ω)) := by
  have ii := rate_ii M hg hB hf0 hC hY ω
  rw [disc, disc, ← intervalIntegral.integral_add_adjacent_intervals (ii 0 A) (ii A S),
    rate_Lam M hg ⟨B, hB⟩ hf0 ⟨C, hC⟩ hY hAS hSH ω, ← Real.exp_add]
  ring_nf

end Path2

section Model2
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

/-- (54.3). -/
theorem european [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A S : ℝ} (hA : 0 ≤ A)
    (hAS : A ≤ S) (hSH : S ≤ H) (Ψ : ℝ × State N A H → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ω, ENNReal.ofReal (disc M S ω) * Ψ (yA M A ω, Xi M A H ω) ∂Q =
      ENNReal.ofReal (P0 M A) * ∫⁻ p, ENNReal.ofReal (Real.exp (-Lam M A H (Qacc M A) S p.1 p.2)) *
        Ψ p ∂((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))) := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -, hf0, ⟨C, hC⟩, -, -, -, -, hY, -⟩ := id hG
  have hAH : A ≤ H := hAS.trans hSH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  set F : ℝ × State N A H → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (-Lam M A H (Qacc M A) S p.1 p.2)) * Ψ p
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Lam_meas M A H _ S).neg)).mul hΨ
  set ρ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (disc M A ω / P0 M A)
  have hP : 0 < P0 M A := Real.exp_pos _
  have step : ∀ ω, ENNReal.ofReal (disc M S ω) * Ψ (yA M A ω, Xi M A H ω) =
      ENNReal.ofReal (P0 M A) * (ρ ω * F (yA M A ω, Xi M A H ω)) := fun ω => by
    have hd : 0 ≤ disc M A ω := (Real.exp_pos _).le
    rw [disc_split M hg hB hf0 hC hY hAS hSH ω, ENNReal.ofReal_mul hd,
      show disc M A ω = P0 M A * (disc M A ω / P0 M A) by field_simp,
      ENNReal.ofReal_mul hP.le]
    simp only [ρ, F]
    ring
  have hρ : AEMeasurable ρ Q := by
    have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (-Novel.DiffusionMeetingGaussProof.Cst M 0 A) *
        Real.exp (-1 * comb M (fun n => w 0 A (M.T n)) (Novel.DiffusionMeetingGaussProof.Wf 0 A) ω) /
          P0 M A) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (comb_meas hG (Novel.DiffusionMeetingGaussProof.Wf_integrand
          (a := 0) hAH))))).div_const _)
    refine hm.aemeasurable.congr ?_
    filter_upwards [Novel.DiffusionMeetingPricingProof.disc_ae hG hA hAH] with ω hω
    simp only [ρ, hω]
  have hpair : AEMeasurable (fun ω => (yA M A ω, Xi M A H ω)) (QS M Q A) :=
    (law_yA hG hA hAH).aemeasurable.prodMk ((Xi_aem hG hA).mono_ac hac)
  rw [lintegral_congr step, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hQS : QS M Q A = Q.withDensity ρ := rfl
  rw [← law_pair hG hA hAH, lintegral_map' hF.aemeasurable hpair]
  have hpairQ : AEMeasurable (fun ω => (yA M A ω, Xi M A H ω)) Q := by
    refine AEMeasurable.prodMk ?_ (Xi_aem hG hA)
    exact (measurable_const.add (comb_meas hG (f1_integrand hAH))).aemeasurable.congr
      (yA_ae hG hA hAH).symm
  rw [hQS]
  exact (lintegral_withDensity_eq_lintegral_mul₀ hρ (hF.comp_aemeasurable hpairQ)).symm

theorem lawS : lawStatement := fun _ _ _ _ _ _ _ hG _ hA hAH =>
  ⟨Xi_aem hG hA, law_pair hG hA hAH⟩

theorem europeanS : europeanStatement := fun _ _ _ _ _ _ _ hG _ _ hA hAS hSH Ψ hΨ =>
  european hG hA hAS hSH Ψ hΨ

end Model2

/-! ### (c): `λ_post` depends only on the post-`A` data -/

open Novel.DiffusionMeetingPricingProof (integrand_add comb_add)

lemma ind_integrand {A q H : ℝ} (hA : 0 ≤ A) (hqH : q ≤ H) : Integrand (ind A q) 0 H := by
  refine ⟨measurable_one.indicator measurableSet_Ioc, ⟨1, fun s => ?_⟩, fun s hs => ?_⟩
  · by_cases h : s ∈ Ioc A q <;> simp [ind, indicator, h]
  · by_cases h : s ∈ Ioc A q
    · exact ⟨hA.trans h.1.le, h.2.trans hqH⟩
    · simp [ind, indicator, h] at hs

lemma integrand_sum (H : ℝ) {ι : Type*} (s : Finset ι) (p : ι → (Fin N → ℝ) × (ℝ → ℝ))
    (hp : ∀ k, Integrand (p k).2 0 H) (c : ι → ℝ) :
    Integrand (fun u => ∑ k ∈ s, c k * (p k).2 u) 0 H := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integrand_zero H
  | insert a s ha ih =>
    have := integrand_add ih (hp a) (c a)
    convert this using 1
    funext u; rw [Finset.sum_insert ha]; ring

section Pair
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

/-- A finite linear combination of combinations is, almost surely, the combination with the
combined coefficients. -/
lemma comb_sum (hG : GaussLaw M Q H) {ι : Type*} (s : Finset ι) (p : ι → (Fin N → ℝ) × (ℝ → ℝ))
    (hp : ∀ k, Integrand (p k).2 0 H) (c : ι → ℝ) :
    (fun ω => ∑ k ∈ s, c k * comb M (p k).1 (p k).2 ω) =ᵐ[Q]
      comb M (fun i => ∑ k ∈ s, c k * (p k).1 i) (fun u => ∑ k ∈ s, c k * (p k).2 u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [I_zero hG] with ω hω
    simp [comb, hω]
  | insert a s ha ih =>
    filter_upwards [ih, comb_add hG _ (p a).1 (integrand_sum H s p hp c) (hp a) (c a)] with ω h1 h2
    have e1 : (fun i => ∑ k ∈ insert a s, c k * (p k).1 i) =
        fun i => (∑ k ∈ s, c k * (p k).1 i) + c a * (p a).1 i := by
      funext i; rw [Finset.sum_insert ha]; ring
    have e2 : (fun u => ∑ k ∈ insert a s, c k * (p k).2 u) =
        fun u => (∑ k ∈ s, c k * (p k).2 u) + c a * (p a).2 u := by
      funext u; rw [Finset.sum_insert ha]; ring
    rw [Finset.sum_insert ha, e1, e2, ← h2, ← h1]
    ring

end Pair

/-- For each coordinate of `Ξ` (meetings, then rational times), the future driving increment it
equals almost surely: `Z_i` for `T_i > A`, `0` for `T_i ≤ A`, and `I(1_{(A, q]})`. -/
noncomputable def coordP {N : ℕ} (T : Fin N → ℝ) (A H : ℝ) :
    Fin N ⊕ Rat' A H → (Fin N → ℝ) × (ℝ → ℝ)
  | Sum.inl i => if A < T i then (Pi.single i 1, fun _ => 0) else (0, fun _ => 0)
  | Sum.inr q => (0, ind A q.1)

lemma coordP_integrand {N : ℕ} {A H : ℝ} (hA : 0 ≤ A) (T : Fin N → ℝ) :
    ∀ k, Integrand (coordP T A H k).2 0 H
  | Sum.inl i => by simp only [coordP]; split_ifs <;> exact integrand_zero H
  | Sum.inr q => ind_integrand hA q.2.2

/-- The first coordinate of `coordP` vanishes at a pre-`A` meeting. -/
lemma coordP_pre {N : ℕ} {T : Fin N → ℝ} {A H : ℝ} {i : Fin N} (hi : ¬ A < T i) :
    ∀ k, (coordP T A H k).1 i = 0
  | Sum.inl j => by
    simp only [coordP]
    split_ifs with hj
    · have : j ≠ i := fun h => hi (h ▸ hj)
      simp [this.symm]
    · rfl
  | Sum.inr q => rfl

/-- The second coordinate of `coordP` vanishes outside `(A, H]`. -/
lemma coordP_out {N : ℕ} {T : Fin N → ℝ} {A H u : ℝ} (hu : ¬ (A < u ∧ u ≤ H)) :
    ∀ k, (coordP T A H k).2 u = 0
  | Sum.inl j => by simp only [coordP]; split_ifs <;> rfl
  | Sum.inr q => by
    simp only [coordP, ind, indicator]
    split_ifs with h
    · exact absurd ⟨h.1, h.2.trans q.2.2⟩ hu
    · rfl

section Pair2
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

/-- The coordinates of `Ξ` as combinations. -/
noncomputable def Wc (M : DiffModel Ω N) (A H : ℝ) (ω : Ω) : Fin N ⊕ Rat' A H → ℝ :=
  fun k => comb M (coordP M.T A H k).1 (coordP M.T A H k).2 ω

lemma Wc_meas (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) : Measurable (Wc M A H) :=
  Measurable.of_eval fun k => comb_meas hG (coordP_integrand hA M.T k)

lemma Xi_eq_Wc (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) :
    Xi M A H =ᵐ[Q] (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Rat' A H => ℝ)) ∘ Wc M A H := by
  have h : ∀ k, ∀ᵐ ω ∂Q, Sum.elim (Xi M A H ω).1 (Xi M A H ω).2 k = Wc M A H ω k := fun k => by
    cases k with
    | inl i =>
      filter_upwards [I_zero hG] with ω hω
      simp only [Sum.elim_inl, Xi, Wc, coordP, comb]
      split_ifs <;> simp [hω, Pi.single_apply]
    | inr q =>
      filter_upwards [Y_incr hG hA q.2.1.le q.2.2] with ω hω
      exact hω
  filter_upwards [ae_all_iff.2 h] with ω hω
  have hw : Sum.elim (Xi M A H ω).1 (Xi M A H ω).2 = Wc M A H ω := funext hω
  rw [Function.comp_apply, ← hw]
  rfl

end Pair2

section Pair3
variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {N : ℕ} {Q : Measure Ω}
  {Q' : Measure Ω'} [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] {M : DiffModel Ω N}
  {M' : DiffModel Ω' N} {H A : ℝ}

/-- The finite-dimensional laws of `Ξ` agree. -/
lemma map_restrict (hG : GaussLaw M Q H) (hG' : GaussLaw M' Q' H) (hA : 0 ≤ A)
    (hT : M.T = M'.T) (hv : ∀ i, A < M.T i → M.v i = M'.v i)
    (hg : ∀ s, A < s → s ≤ H → M.g s = M'.g s) (s : Finset (Fin N ⊕ Rat' A H)) :
    Q.map (fun ω => s.restrict (Wc M A H ω)) = Q'.map (fun ω => s.restrict (Wc M' A H ω)) := by
  classical
  have hV : Measurable fun ω => s.restrict (Wc M A H ω) :=
    (Finset.measurable_restrict s).comp (Wc_meas hG hA)
  have hV' : Measurable fun ω => s.restrict (Wc M' A H ω) :=
    (Finset.measurable_restrict s).comp (Wc_meas hG' hA)
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable hV, Measure.map_map L.continuous.measurable hV']
  congr 1
  set c : s → ℝ := fun k => L (Pi.single k 1)
  set p : s → (Fin N → ℝ) × (ℝ → ℝ) := fun k => coordP M.T A H k.1
  have hp : ∀ k, Integrand (p k).2 0 H := fun k => coordP_integrand hA M.T k.1
  have hL : ∀ x : s → ℝ, L x = ∑ k, c k * x k := fun x => by
    have := L.toLinearMap.pi_apply_eq_sum_univ x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  set β : Fin N → ℝ := fun i => ∑ k, c k * (p k).1 i
  set f : ℝ → ℝ := fun u => ∑ k, c k * (p k).2 u
  have hf : Integrand f 0 H := integrand_sum H Finset.univ p hp c
  have e : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {Q₀ : Measure Ω₀} {M₀ : DiffModel Ω₀ N},
      GaussLaw M₀ Q₀ H → M₀.T = M.T → (fun ω => L (s.restrict (Wc M₀ A H ω))) =ᵐ[Q₀] comb M₀ β f :=
    fun {Ω₀} _ {Q₀} {M₀} hG₀ hT₀ => by
      have h : (fun ω => L (s.restrict (Wc M₀ A H ω))) =
          fun ω => ∑ k ∈ Finset.univ, c k * comb M₀ (p k).1 (p k).2 ω := funext fun ω => by
        rw [hL]
        simp only [Finset.restrict, Wc, p, hT₀]
      rw [h]
      exact comb_sum hG₀ Finset.univ p hp c
  simp only [Function.comp_def]
  rw [Measure.map_congr (e hG rfl), Measure.map_congr (e hG' hT.symm),
    Novel.DiffusionMeetingGaussProof.comb_law hG β hf,
    Novel.DiffusionMeetingGaussProof.comb_law hG' β hf]
  congr 2
  unfold Novel.DiffusionMeetingGaussProof.var
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : A < M.T i
    · rw [hv i hi]
    · have : β i = 0 := Finset.sum_eq_zero fun k _ => by rw [coordP_pre hi k.1, mul_zero]
      rw [this]; ring
  · refine intervalIntegral.integral_congr fun u _ => ?_
    by_cases hu : A < u ∧ u ≤ H
    · simp only [hg u hu.1 hu.2]
    · have : f u = 0 := Finset.sum_eq_zero fun k _ => by rw [coordP_out hu k.1, mul_zero]
      simp only [this]; ring

/-- `λ_post` depends only on the post-`A` data. -/
theorem post_law (hG : GaussLaw M Q H) (hG' : GaussLaw M' Q' H) (hA : 0 ≤ A)
    (hT : M.T = M'.T) (hv : ∀ i, A < M.T i → M.v i = M'.v i)
    (hg : ∀ s, A < s → s ≤ H → M.g s = M'.g s) :
    Q.map (Xi M A H) = Q'.map (Xi M' A H) := by
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Rat' A H => ℝ)
  have hW : Q.map (Wc M A H) = Q'.map (Wc M' A H) := by
    refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders (fun t ht => ?_) (by simp [measure_univ])
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
    rw [Measure.map_apply (Wc_meas hG hA) (MeasurableSet.cylinder s hS),
      Measure.map_apply (Wc_meas hG' hA) (MeasurableSet.cylinder s hS)]
    have := congrArg (fun μ => μ S) (map_restrict hG hG' hA hT hv hg s)
    have h1 : Measurable fun ω => s.restrict (Wc M A H ω) :=
      (Finset.measurable_restrict s).comp (Wc_meas hG hA)
    have h2 : Measurable fun ω => s.restrict (Wc M' A H ω) :=
      (Finset.measurable_restrict s).comp (Wc_meas hG' hA)
    rw [Measure.map_apply h1 hS, Measure.map_apply h2 hS] at this
    exact this
  rw [Measure.map_congr (Xi_eq_Wc hG hA), Measure.map_congr (Xi_eq_Wc hG' hA),
    ← Measure.map_map e.measurable (Wc_meas hG hA),
    ← Measure.map_map e.measurable (Wc_meas hG' hA), hW]

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] in
/-- `Λ` depends only on the post-`A` data. -/
lemma Lam_eq (hf : M.f0 = M'.f0) (hT : M.T = M'.T) (hv : ∀ i, A < M.T i → M.v i = M'.v i)
    (hg : ∀ s, A < s → s ≤ H → M.g s = M'.g s) {S V : ℝ} (hAS : A ≤ S) (hSH : S ≤ H) (y : ℝ)
    (ξ : State N A H) : Lam M A H V S y ξ = Lam M' A H V S y ξ := by
  have hsum : ∑ i, (if A < M.T i ∧ M.T i ≤ S then
      ξ.1 i * (S - M.T i) + M.v i * (S - M.T i) ^ 2 / 2 else 0) =
      ∑ i, (if A < M'.T i ∧ M'.T i ≤ S then
      ξ.1 i * (S - M'.T i) + M'.v i * (S - M'.T i) ^ 2 / 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT]
    split_ifs with h
    · rw [hv i h.1]
    · rfl
  have hint : ∫ t in A..S, ∫ u in A..t, M.g u * (t - u) =
      ∫ t in A..S, ∫ u in A..t, M'.g u * (t - u) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hAS] at ht
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le ht.1] at hu
    simp only [hg u hu.1 (hu.2.trans (ht.2.trans hSH))]
  unfold Lam
  rw [hf, hsum, hint]

end Pair3

theorem postLawPairS : postLawPairStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hG hG' _ hA _ hT hv hg => post_law hG hG' hA hT hv hg

theorem europeanPairS : europeanPairStatement := by
  intro Ω Ω' _ _ N Q Q' _ _ M M' H hG hG' A S hA hAS hSH hf hT hv hg hV Ψ hΨ
  have hP : P0 M A = P0 M' A := by
    simp only [P0, Standalone.DiffusionMeetingGauss.Aint, hf]
  rw [european hG hA hAS hSH Ψ hΨ, european hG' hA hAS hSH Ψ hΨ,
    post_law hG hG' hA hT hv hg, hV, hP]
  congr 1
  exact lintegral_congr fun p => by rw [Lam_eq hf hT hv hg hAS hSH p.1 p.2]

theorem continuousAggregationEuropean : Standalone.ContinuousAggregationEuropean.statement :=
  ⟨lambdaS, lawS, europeanS, postLawPairS, europeanPairS⟩

end Novel.ContinuousAggregationEuropeanProof

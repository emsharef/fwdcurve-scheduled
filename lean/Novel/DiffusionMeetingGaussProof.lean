import Standalone.DiffusionMeetingGauss
import Novel.DiffusionMeetingIdentitiesProof
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.CompoundedFuturesIdentification Standalone.DiffusionMeetingIdentities
open Standalone.DiffusionMeetingGauss
namespace Novel.DiffusionMeetingGaussProof

/-- `∫_a^b 1{T ≤ u} (c + e(u − T)) du = c w(T) + e d(T)`. -/
lemma int_step {a b : ℝ} (hab : a ≤ b) (T c e : ℝ) :
    ∫ u in a..b, (if T ≤ u then c + e * (u - T) else 0) = c * w a b T + e * d a b T := by
  have hcont : Continuous fun u : ℝ => c + e * (u - T) := by fun_prop
  have hlin : ∀ x y : ℝ, ∫ u in x..y, (c + e * (u - T)) =
      c * (y - x) + e * ((y - T) ^ 2 - (x - T) ^ 2) / 2 := fun x y => by
    rw [intervalIntegral.integral_add (f := fun _ => c) (g := fun u => e * (u - T))
      intervalIntegrable_const ((by fun_prop : Continuous fun u : ℝ => e * (u - T)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
      intervalIntegral.integral_comp_sub_right (fun x => x) T, integral_id]
    ring
  rcases le_or_gt T a with hTa | haT
  · rw [intervalIntegral.integral_congr (g := fun u => c + e * (u - T)) fun u hu => by
      rw [uIcc_of_le hab] at hu
      simp [hTa.trans hu.1], hlin]
    simp only [w, d, max_eq_left (by linarith : (0:ℝ) ≤ b - T),
      max_eq_left (by linarith : (0:ℝ) ≤ a - T)]
    ring
  rcases le_or_gt T b with hTb | hbT
  · have h1 : (fun u => if T ≤ u then c + e * (u - T) else 0) =ᵐ[volume.restrict (uIoc a T)]
        fun _ => (0:ℝ) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [Measure.ae_ne volume T] with u hu hmem
      rw [uIoc_of_le haT.le] at hmem
      simp [not_le.2 (lt_of_le_of_ne hmem.2 hu)]
    have h2 : EqOn (fun u => if T ≤ u then c + e * (u - T) else 0) (fun u => c + e * (u - T))
        (uIcc T b) := fun u hu => by
      rw [uIcc_of_le hTb] at hu
      simp [hu.1]
    have h1' : ∀ᵐ u ∂volume, u ∈ uIoc a T →
        (if T ≤ u then c + e * (u - T) else 0) = (fun _ => (0:ℝ)) u :=
      (ae_restrict_iff' measurableSet_uIoc).1 h1
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := T)
      (intervalIntegrable_const.congr_ae h1.symm)
      ((hcont.intervalIntegrable T b).congr fun u hu => (h2 (uIoc_subset_uIcc hu)).symm),
      intervalIntegral.integral_congr_ae h1', intervalIntegral.integral_congr h2, hlin]
    simp only [intervalIntegral.integral_zero, w, d, max_eq_left (by linarith : (0:ℝ) ≤ b - T),
      max_eq_right (by linarith : a - T ≤ 0)]
    ring
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun u hu => by
      rw [uIcc_of_le hab] at hu
      simp [not_le.2 (lt_of_le_of_lt hu.2 hbT)]]
    simp only [intervalIntegral.integral_zero, w, d, max_eq_right (by linarith : b - T ≤ 0),
      max_eq_right (by linarith : a - T ≤ 0)]
    ring

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

omit m₀ in
/-- `u ↦ ∫_0^u σ(s)²(u − s) ds` is continuous. -/
lemma drift_cont (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) :
    Continuous fun u => ∫ s in (0:ℝ)..u, M.g s * (u - s) := by
  have ii := fun (φ : ℝ → ℝ) (hφ : Continuous φ) (x y : ℝ) =>
    Novel.DiffusionMeetingIdentitiesProof.ii hg hB φ hφ x y
  have hK : ∀ u, ∫ s in (0:ℝ)..u, M.g s * (u - s) =
      u * (∫ s in (0:ℝ)..u, M.g s) - ∫ s in (0:ℝ)..u, M.g s * s := fun u => by
    have h1 : IntervalIntegrable (fun s => M.g s * u) volume 0 u := ii (fun _ => u) continuous_const 0 u
    have h2 : IntervalIntegrable (fun s => M.g s * s) volume 0 u := ii id continuous_id 0 u
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_mul_const]
    ring
  simp only [hK]
  have c1 := intervalIntegral.continuous_primitive (fun x y => ii (fun _ => 1) continuous_const x y) 0
  have c2 := intervalIntegral.continuous_primitive (fun x y => ii id continuous_id x y) 0
  simp only [mul_one, id] at c1 c2
  exact (continuous_id.mul c1).sub c2

lemma step_ii (T c e a b : ℝ) :
    IntervalIntegrable (fun u => if T ≤ u then c + e * (u - T) else 0) volume a b := by
  have hc := (by fun_prop : Continuous fun u : ℝ => c + e * (u - T)).intervalIntegrable (μ := volume) a b
  have : (fun u => if T ≤ u then c + e * (u - T) else 0) =
      (Ici T).indicator fun u => c + e * (u - T) := by
    funext u; simp [indicator, mem_Ici]
  rw [this]
  exact ⟨hc.1.indicator measurableSet_Ici, hc.2.indicator measurableSet_Ici⟩

/-- The pathwise decomposition of `∫_a^b r`. -/
lemma rate_int (hG : GaussLaw M Q H) (ω : Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, rate M u ω = Aint M a b +
      ∑ n, (M.Z n ω * w a b (M.T n) + M.v n * d a b (M.T n)) + (∫ u in a..b, M.Y u ω) +
        ∫ s in (0:ℝ)..b, M.g s * dfun a b s := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -, hf0, ⟨C, hC⟩, -, -, -, -, hY, -⟩ := hG
  have i1 : IntervalIntegrable M.f0 volume a b :=
    Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC a b
  have i2 : IntervalIntegrable (fun u => ∑ n, (if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n)
      else 0)) volume a b := by
    have := IntervalIntegrable.sum Finset.univ fun n _ => step_ii (M.T n) (M.Z n ω) (M.v n) a b
    convert this using 1
    funext u; simp [Finset.sum_apply]
  have i3 : IntervalIntegrable (fun u => M.Y u ω) volume a b := (hY ω).intervalIntegrable a b
  have i4 := (drift_cont (M := M) hg hB).intervalIntegrable (μ := volume) a b
  unfold rate
  rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_finsetSum fun n _ => step_ii (M.T n) (M.Z n ω) (M.v n) a b,
    Novel.DiffusionMeetingIdentitiesProof.driftS M.g hg ⟨B, hB⟩ a b ha hab]
  simp only [int_step hab, Aint]

/-- The Fubini integrand `w_{a,b}` on `[0, b]`. -/
noncomputable def Wf (a b : ℝ) : ℝ → ℝ := (Icc 0 b).indicator fun s => max (b - s) 0 - max (a - s) 0

lemma Wf_integrand {a b H : ℝ} (hbH : b ≤ H) : Integrand (Wf a b) 0 H := by
  refine ⟨Measurable.indicator (by fun_prop) measurableSet_Icc, ⟨|b| + |a|, fun s => ?_⟩,
    fun s hs => ?_⟩
  · simp only [Wf, indicator]
    split_ifs with h
    · refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [h.1, le_abs_self b]) (abs_nonneg _)
      · rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [h.1, le_abs_self a]) (abs_nonneg _)
    · simp; positivity
  · simp only [Wf, indicator] at hs
    split_ifs at hs with h
    · exact ⟨h.1, h.2.trans hbH⟩
    · exact absurd rfl hs

/-- A combination `Σ β_i Z_i + I f`. -/
noncomputable def comb (M : DiffModel Ω N) (β : Fin N → ℝ) (f : ℝ → ℝ) (ω : Ω) : ℝ :=
  ∑ i, β i * M.Z i ω + M.I f ω

/-- Its variance `Σ β_i² v_i + ∫_0^H f² σ²`. -/
noncomputable def var (M : DiffModel Ω N) (H : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, β i ^ 2 * M.v i + ∫ s in (0:ℝ)..H, f s ^ 2 * M.g s

lemma comb_meas (hG : GaussLaw M Q H) {β : Fin N → ℝ} {f : ℝ → ℝ} (hf : Integrand f 0 H) :
    Measurable (comb M β f) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hZm, hIm, -⟩ := hG
  exact (Finset.measurable_sum _ fun n _ => measurable_const.mul (hZm n)).add (hIm _ hf)

lemma comb_law (hG : GaussLaw M Q H) (β : Fin N → ℝ) {f : ℝ → ℝ} (hf : Integrand f 0 H) :
    Q.map (comb M β f) = gaussianReal 0 (var M H β f).toNNReal := by
  obtain ⟨-, -, -, -, -, -, -, hlaw, -⟩ := hG
  exact hlaw β f hf

lemma var_nonneg (hG : GaussLaw M Q H) (hH : 0 ≤ H) (β : Fin N → ℝ) (f : ℝ → ℝ) :
    0 ≤ var M H β f := by
  obtain ⟨-, hv, -, -, hg0, -⟩ := hG
  exact add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hv n))
    (intervalIntegral.integral_nonneg hH fun s _ => mul_nonneg (sq_nonneg _) (hg0 s))

/-- The Gaussian exponential moment of a combination. -/
lemma exp_comb [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (hH : 0 ≤ H) (β : Fin N → ℝ)
    {f : ℝ → ℝ} (hf : Integrand f 0 H) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * comb M β f ω)) Q ∧
      ∫ ω, Real.exp (c * comb M β f ω) ∂Q = Real.exp (c ^ 2 * var M H β f / 2) := by
  have hm := comb_meas hG (β := β) hf
  have hmap := comb_law hG β hf
  refine ⟨?_, ?_⟩
  · have := integrable_exp_mul_gaussianReal (μ := 0) (v := (var M H β f).toNNReal) c
    rw [← hmap] at this
    exact (integrable_map_measure (by fun_prop) hm.aemeasurable).1 this
  · rw [← integral_map (f := fun x => Real.exp (c * x)) hm.aemeasurable (by fun_prop), hmap]
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := (var M H β f).toNNReal)) c
    simp only [mgf, id] at this
    rw [this, Real.coe_toNNReal _ (var_nonneg hG hH β f)]
    ring_nf

/-- The deterministic part of `∫_a^b r`. -/
noncomputable def Cst (M : DiffModel Ω N) (a b : ℝ) : ℝ :=
  Aint M a b + ∑ n, M.v n * d a b (M.T n) + ∫ s in (0:ℝ)..b, M.g s * dfun a b s

/-- `∫_a^b r = Cst + Σ w_n Z_n + I w`, almost surely. -/
lemma rate_ae (hG : GaussLaw M Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H) :
    (fun ω => ∫ u in a..b, rate M u ω) =ᵐ[Q]
      fun ω => Cst M a b + comb M (fun n => w a b (M.T n)) (Wf a b) ω := by
  have hfub := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hfub a b ha hab hbH] with ω hω
  rw [rate_int hG ω ha hab, hω]
  simp only [Cst, comb, Wf, Finset.sum_add_distrib]
  have : ∀ n, M.Z n ω * w a b (M.T n) = w a b (M.T n) * M.Z n ω := fun n => mul_comm _ _
  simp only [this]
  ring

omit m₀ in
lemma int_Wf (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbH : b ≤ H) :
    ∫ s in (0:ℝ)..H, Wf a b s ^ 2 * M.g s = ∫ s in (0:ℝ)..b, w a b s ^ 2 * M.g s := by
  have hb : 0 ≤ b := ha.trans hab
  have ii := fun (φ : ℝ → ℝ) (hφ : Continuous φ) (x y : ℝ) =>
    Novel.DiffusionMeetingIdentitiesProof.ii hg hB φ hφ x y
  have hwc : Continuous fun s => w a b s ^ 2 := by unfold w; fun_prop
  have e1 : EqOn (fun s => Wf a b s ^ 2 * M.g s) (fun s => w a b s ^ 2 * M.g s) (uIcc 0 b) :=
    fun s hs => by
      rw [uIcc_of_le hb] at hs
      simp [Wf, indicator, hs.1, hs.2, w]
  have e2 : EqOn (fun s => Wf a b s ^ 2 * M.g s) (fun _ => (0:ℝ)) (uIcc b H) := fun s hs => by
    rw [uIcc_of_le hbH] at hs
    rcases hs.1.eq_or_lt with h | h
    · subst h; simp [Wf, hab]
    · simp [Wf, indicator, not_le.2 h]
  have iw : IntervalIntegrable (fun s => w a b s ^ 2 * M.g s) volume 0 b := by
    simpa only [mul_comm] using ii _ hwc 0 b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
    (iw.congr fun s hs => (e1 (uIoc_subset_uIcc hs)).symm)
    (intervalIntegrable_const.congr fun s hs => (e2 (uIoc_subset_uIcc hs)).symm),
    intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2]
  simp

omit m₀ in
/-- `Cst + V/2 = A + p`. -/
lemma key (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbH : b ≤ H) :
    Cst M a b + var M H (fun n => w a b (M.T n)) (Wf a b) / 2 = Aint M a b + pdiff M a b := by
  have ii := fun (φ : ℝ → ℝ) (hφ : Continuous φ) (x y : ℝ) =>
    Novel.DiffusionMeetingIdentitiesProof.ii hg hB φ hφ x y
  have hdc : Continuous fun s => dfun a b s := by unfold dfun; fun_prop
  have hwc : Continuous fun s => w a b s ^ 2 := by unfold w; fun_prop
  have iw : IntervalIntegrable (fun s => w a b s ^ 2 * M.g s) volume 0 b := by
    simpa only [mul_comm] using ii _ hwc 0 b
  have eint : ∫ s in (0:ℝ)..b, M.g s * h a b s =
      (∫ s in (0:ℝ)..b, M.g s * dfun a b s) + (∫ s in (0:ℝ)..b, w a b s ^ 2 * M.g s) / 2 := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_add (ii _ hdc 0 b)
      (iw.div_const 2)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [h, dfun, d]
    ring
  have esum : ∑ i, h a b (M.T i) * M.v i =
      ∑ n, M.v n * d a b (M.T n) + (∑ n, w a b (M.T n) ^ 2 * M.v n) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by simp only [h]; ring
  simp only [Cst, var, pdiff, int_Wf hg hB ha hab hbH, eint, esum]
  ring

lemma futuresS : Standalone.DiffusionMeetingGauss.futuresStatement := by
  intro Ω _ N Q _ M H hG a b ha hab hbH
  obtain ⟨-, -, hg, ⟨B, hB⟩, -⟩ := id hG
  have hE := (exp_comb hG (ha.trans (hab.trans hbH)) (fun n => w a b (M.T n))
    (Wf_integrand (a := a) hbH) 1).2
  simp only [one_mul, one_pow] at hE
  rw [integral_congr_ae (g := fun ω => Real.exp (Cst M a b) *
      Real.exp (comb M (fun n => w a b (M.T n)) (Wf a b) ω))
    ((rate_ae hG ha hab hbH).mono fun ω h => by simp only [h, Real.exp_add]),
    integral_const_mul, hE, ← Real.exp_add, key hg hB ha hab hbH]

end

theorem diffusionMeetingGauss : Standalone.DiffusionMeetingGauss.statement := futuresS

end Novel.DiffusionMeetingGaussProof

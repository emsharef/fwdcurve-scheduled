import Standalone.MaturityShapeGauss
import Novel.MaturityShapeIdentitiesProof
import Novel.DiffusionMeetingGaussProof
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.CompoundedFuturesIdentification Standalone.MaturityShapeIdentities
open Standalone.MaturityShapeGauss
open Standalone.DiffusionMeetingGauss (Integrand)
open Novel.MaturityShapeIdentitiesProof (meas_param ii_of_bound congr_Ioc k_meas k_bound Phi_meas
  Phi_bound)
namespace Novel.MaturityShapeGaussProof

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : ShapeModel Ω N}
  {φ : ℝ → ℝ → ℝ} {H : ℝ}

/-! ### The Gaussian combinations -/

/-- A combination `Σ β_i Z_i + I f`. -/
noncomputable def comb (M : ShapeModel Ω N) (β : Fin N → ℝ) (f : ℝ → ℝ) (ω : Ω) : ℝ :=
  ∑ i, β i * M.Z i ω + M.I f ω

/-- Its variance `Σ β_i² v_i + ∫_0^H f² σ²`. -/
noncomputable def var (M : ShapeModel Ω N) (H : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, β i ^ 2 * M.v i + ∫ s in (0:ℝ)..H, f s ^ 2 * M.g s

lemma comb_meas (hG : ShapeGaussLaw M φ Q H) {β : Fin N → ℝ} {f : ℝ → ℝ} (hf : Integrand f 0 H) :
    Measurable (comb M β f) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZm, hIm, -⟩ := hG
  exact (Finset.measurable_sum _ fun n _ => measurable_const.mul (hZm n)).add (hIm _ hf)

lemma comb_law (hG : ShapeGaussLaw M φ Q H) (β : Fin N → ℝ) {f : ℝ → ℝ} (hf : Integrand f 0 H) :
    Q.map (comb M β f) = gaussianReal 0 (var M H β f).toNNReal := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlaw, -⟩ := hG
  exact hlaw β f hf

lemma var_nonneg (hG : ShapeGaussLaw M φ Q H) (hH : 0 ≤ H) (β : Fin N → ℝ) (f : ℝ → ℝ) :
    0 ≤ var M H β f := by
  obtain ⟨-, hv, -, -, hg0, -⟩ := hG
  exact add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hv n))
    (intervalIntegral.integral_nonneg hH fun s _ => mul_nonneg (sq_nonneg _) (hg0 s))

/-- The Gaussian exponential moment of a combination. -/
lemma exp_comb [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) (hH : 0 ≤ H) (β : Fin N → ℝ)
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

/-! ### `W̃` -/

omit m₀ in
lemma Wt_integrand (hφ : Measurable (Function.uncurry φ)) {C : ℝ} (hC : ∀ s x, |φ s x| ≤ C)
    {a b : ℝ} (hbH : b ≤ H) : Integrand (Wt φ a b) 0 H := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  refine ⟨Measurable.indicator (meas_param (measurable_const.max measurable_id) measurable_const
      (K := φ) hφ) measurableSet_Icc, ⟨C * (|a| + 2 * |b|), fun s => ?_⟩, fun s hs => ?_⟩
  · simp only [Wt, indicator]
    split_ifs with h
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := max a s) (b := b)
        (f := φ s) (C := C) fun x _ => by rw [Real.norm_eq_abs]; exact hC s x
      rw [Real.norm_eq_abs] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      rw [abs_le]
      constructor
      · have : max a s ≤ |a| + |b| := max_le ((le_abs_self a).trans (by linarith [abs_nonneg b]))
          (h.2.trans ((le_abs_self b).trans (by linarith [abs_nonneg a])))
        linarith [neg_abs_le b, abs_nonneg a, abs_nonneg b]
      · have : -|a| ≤ max a s := (neg_abs_le a).trans (le_max_left _ _)
        linarith [le_abs_self b, abs_nonneg b]
    · simp; positivity
  · simp only [Wt, indicator] at hs
    split_ifs at hs with h
    · exact ⟨h.1, h.2.trans hbH⟩
    · exact absurd rfl hs


/-! ### The futures quote -/

omit m₀ in
/-- The drift term is integrable in `u`. -/
lemma drift_ii (hφ : Measurable (Function.uncurry φ)) {C : ℝ} (hC : ∀ s x, |φ s x| ≤ C)
    (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => ∫ s in (0:ℝ)..u, M.g s * φ s u * Phi φ s u) volume a b := by
  have hb := ha.trans hab
  have hbd := k_bound (S := b) hC hB
  refine ii_of_bound (meas_param measurable_const measurable_id
    (K := fun u s => M.g s * φ s u * Phi φ s u) (k_meas hφ hg)) hab (M := B * C * (C * b) * b)
    fun u hu => ?_
  have hu' : u ∈ Icc 0 b := ⟨ha.trans hu.1, hu.2⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u)
    (f := fun s => M.g s * φ s u * Phi φ s u) (C := B * C * (C * b)) fun s hs => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hu'.1] at hs
      exact hbd u hu' s ⟨hs.1.le, hs.2.trans hu'.2⟩
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hu'.1] at this
  exact this.trans (mul_le_mul_of_nonneg_left hu'.2 ((abs_nonneg _).trans (hbd 0 ⟨le_rfl, hb⟩ 0 ⟨le_rfl, hb⟩)))

lemma rate_int (hG : ShapeGaussLaw M φ Q H) (ω : Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, rate M φ u ω = Aint M a b +
      ∑ n, (M.Z n ω * w a b (M.T n) + M.v n * d a b (M.T n)) + (∫ u in a..b, M.X u u ω) +
        ∫ s in (0:ℝ)..b, M.g s * dtil φ a b s := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -, hf0, ⟨C0, hC0⟩, hφ, ⟨C, hC⟩, -, -, -, -, hXd, -⟩ := hG
  have i1 : IntervalIntegrable M.f0 volume a b :=
    Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C0 hC0 a b
  have i2 : IntervalIntegrable (fun u => ∑ n, (if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n)
      else 0)) volume a b := by
    have := IntervalIntegrable.sum Finset.univ fun n _ =>
      Novel.DiffusionMeetingGaussProof.step_ii (M.T n) (M.Z n ω) (M.v n) a b
    convert this using 1
    funext u; simp [Finset.sum_apply]
  have i3 := hXd ω a b
  have i4 := drift_ii (M := M) hφ hC hg hB ha hab
  unfold rate
  rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_finsetSum fun n _ =>
      Novel.DiffusionMeetingGaussProof.step_ii (M.T n) (M.Z n ω) (M.v n) a b,
    Novel.MaturityShapeIdentitiesProof.driftS φ hφ ⟨C, hC⟩ M.g hg ⟨B, hB⟩ a b ha hab]
  simp only [Novel.DiffusionMeetingGaussProof.int_step hab, Aint]

/-- The deterministic part of `∫_a^b r`. -/
noncomputable def Cst (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  Aint M a b + ∑ n, M.v n * d a b (M.T n) + ∫ s in (0:ℝ)..b, M.g s * dtil φ a b s

/-- `∫_a^b r = Cst + Σ w_n Z_n + I W̃`, almost surely. -/
lemma rate_ae (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H) :
    (fun ω => ∫ u in a..b, rate M φ u ω) =ᵐ[Q]
      fun ω => Cst M φ a b + comb M (fun n => w a b (M.T n)) (Wt φ a b) ω := by
  have hfub := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hfub a b ha hab hbH] with ω hω
  rw [rate_int hG ω ha hab, hω]
  simp only [Cst, comb, Finset.sum_add_distrib]
  have : ∀ n, M.Z n ω * w a b (M.T n) = w a b (M.T n) * M.Z n ω := fun n => mul_comm _ _
  simp only [this]
  ring

omit m₀ in
lemma Wt_eq {a b s : ℝ} (hs : s ∈ Icc 0 b) : Wt φ a b s = ∫ x in max a s..b, φ s x := by
  simp [Wt, indicator, hs.1, hs.2]

omit m₀ in
lemma int_Wt (hφ : Measurable (Function.uncurry φ)) {C : ℝ} (hC : ∀ s x, |φ s x| ≤ C)
    (hg : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {a b : ℝ} (_hb : 0 ≤ b) (hbH : b ≤ H) :
    ∫ s in (0:ℝ)..H, Wt φ a b s ^ 2 * M.g s = ∫ s in (0:ℝ)..b, Wt φ a b s ^ 2 * M.g s := by
  have hi : ∀ x y, IntervalIntegrable (fun s => Wt φ a b s ^ 2 * M.g s) volume x y := fun x y => by
    obtain ⟨hm, ⟨K, hK⟩, -⟩ := Wt_integrand (H := H) (a := a) hφ hC hbH
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
    refine Novel.SpliceCrossTermDriftProof.ii_bdd ((hm.pow_const 2).mul hg) (K ^ 2 * B)
      (fun s => ?_) x y
    simp only [Pi.mul_apply]
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hK s) 2) (hB s) (abs_nonneg _)
      (sq_nonneg _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 b) (hi b H),
    congr_Ioc hbH (g := fun _ => 0) fun s hs => by simp [Wt, indicator, not_le.2 hs.1]]
  simp

/-- `Cst + V/2 = A + p̃`. -/
lemma key (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H) :
    Cst M φ a b + var M H (fun n => w a b (M.T n)) (Wt φ a b) / 2 = Aint M a b + ptil M φ a b := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -, -, -, hφ, ⟨C, hC⟩, -⟩ := hG
  have hb := ha.trans hab
  obtain ⟨hWm, ⟨K, hK⟩, -⟩ := Wt_integrand (H := H) (a := a) hφ hC hbH
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have iW : IntervalIntegrable (fun s => Wt φ a b s ^ 2 * M.g s) volume 0 b :=
    Novel.SpliceCrossTermDriftProof.ii_bdd ((hWm.pow_const 2).mul hg) (K ^ 2 * B) (fun s => by
      simp only [Pi.mul_apply]
      rw [abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hK s) 2) (hB s) (abs_nonneg _)
        (sq_nonneg _)) 0 b
  have hdm : Measurable fun s => dtil φ a b s := by
    unfold dtil
    exact ((((Phi_meas hφ).comp (measurable_id.prodMk measurable_const)).pow_const 2).sub
      (((Phi_meas hφ).comp (measurable_id.prodMk (measurable_const.max measurable_id))).pow_const 2)).div_const 2
  have iD : IntervalIntegrable (fun s => M.g s * dtil φ a b s) volume 0 b := by
    refine ii_of_bound (hg.mul hdm) hb (M := B * ((C * (|a| + 2 * b)) ^ 2)) fun s hs => ?_
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have hP : ∀ y, 0 ≤ y → y ≤ |a| + 2 * b → |Phi φ s y| ≤ C * (|a| + 2 * b) := fun y hy0 hy => by
      refine (Phi_bound hC s y).trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hC 0 0)))
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, abs_nonneg a]
    have h1 := hP b hb (by linarith [abs_nonneg a])
    have h2 := hP (max a s) (le_max_of_le_right hs.1) (max_le (by linarith [le_abs_self a])
      (by linarith [hs.2, abs_nonneg a]))
    have hsq : ∀ y, |Phi φ s y| ≤ C * (|a| + 2 * b) → Phi φ s y ^ 2 ≤ (C * (|a| + 2 * b)) ^ 2 :=
      fun y hy => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    simp only [Pi.mul_apply]
    rw [abs_mul]
    refine mul_le_mul (hB s) ?_ (abs_nonneg _) hB0
    unfold dtil
    rw [abs_div, abs_two]
    have := abs_sub (Phi φ s b ^ 2) (Phi φ s (max a s) ^ 2)
    rw [abs_of_nonneg (sq_nonneg (Phi φ s b)), abs_of_nonneg (sq_nonneg (Phi φ s (max a s)))] at this
    linarith [hsq b h1, hsq _ h2]
  have esum : ∑ i, h a b (M.T i) * M.v i =
      ∑ n, M.v n * d a b (M.T n) + (∑ n, w a b (M.T n) ^ 2 * M.v n) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by simp only [h]; ring
  have eint : ∫ s in (0:ℝ)..b, M.g s * (dtil φ a b s + Wt φ a b s ^ 2 / 2) =
      (∫ s in (0:ℝ)..b, M.g s * dtil φ a b s) + (∫ s in (0:ℝ)..b, Wt φ a b s ^ 2 * M.g s) / 2 := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_add iD (iW.div_const 2)]
    exact intervalIntegral.integral_congr fun s _ => by ring
  simp only [Cst, var, ptil, int_Wt hφ hC hg hB hb hbH, eint, esum]
  ring

end

lemma futuresS : futuresStatement := by
  intro Ω _ N Q _ M φ H hG a b ha hab hbH
  obtain ⟨-, -, -, -, -, -, -, hφ, ⟨C, hC⟩, -⟩ := id hG
  have hE := (exp_comb hG (ha.trans (hab.trans hbH)) (fun n => w a b (M.T n))
    (Wt_integrand (a := a) hφ hC hbH) 1).2
  simp only [one_mul, one_pow] at hE
  rw [integral_congr_ae (g := fun ω => Real.exp (Cst M φ a b) *
      Real.exp (comb M (fun n => w a b (M.T n)) (Wt φ a b) ω))
    ((rate_ae hG ha hab hbH).mono fun ω h => by simp only [h, Real.exp_add]),
    integral_const_mul, hE, ← Real.exp_add, key hG ha hab hbH]

theorem maturityShapeGauss : Standalone.MaturityShapeGauss.statement := futuresS

end Novel.MaturityShapeGaussProof

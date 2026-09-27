import Standalone.JumpShapeCond
import Novel.JumpShapeProfileProof
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
namespace Novel.JumpShapeCondProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof

/-- `M(τ) = ∫ e^{−τx} ν(dx) ∈ [0, ∞]`. -/
noncomputable def Ml (ν : Measure ℝ) (τ : ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂ν

lemma integrable_of_Ml {ν : Measure ℝ} {τ : ℝ} (h : Ml ν τ < ∞) :
    Integrable (fun x => Real.exp (-τ * x)) ν :=
  ⟨(by fun_prop : Continuous fun x : ℝ => Real.exp (-τ * x)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)).2 h⟩

lemma Ml_eq {ν : Measure ℝ} {τ : ℝ} (h : Integrable (fun x => Real.exp (-τ * x)) ν) :
    Ml ν τ = ENNReal.ofReal (Mlap ν τ) :=
  (ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

section
variable {Ω : Type*} (G : MeasurableSpace Ω)

/-- `H(·, τ)` is `G`-measurable. -/
lemma H_meas (h : ℝ → Ω → ℝ)
    (hh : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _ (Function.uncurry h))
    (τ : ℝ) : Measurable[G] (fun ω => ∫ u in (0:ℝ)..τ, h u ω) := by
  let _ : MeasurableSpace Ω := G
  simp only [intervalIntegral]
  exact ((hh.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc 0 τ))).measurable).sub
    ((hh.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc τ 0))).measurable)

/-- `M(·, τ)` is `G`-measurable. -/
lemma Ml_meas (κ : @Kernel Ω ℝ G _) (τ : ℝ) : Measurable[G] (fun ω => Ml (κ ω) τ) := by
  let _ : MeasurableSpace Ω := G
  exact Measurable.lintegral_kernel (by fun_prop)

end

section Main
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω} {G : MeasurableSpace Ω}
  {X : Ω → ℝ} {h : ℝ → Ω → ℝ} {L : ℝ≥0∞} {κ : @Kernel Ω ℝ G _}

/-- Step 0: `exp(−∫_0^τ ξ) = e^{−H(τ)} e^{−τX}`, and `κ` computes the conditional expectation. -/
lemma step0
    (hh : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _ (Function.uncurry h))
    (hloc : ∀ ω τ, InI L τ → IntervalIntegrable (fun u => h u ω) volume 0 τ)
    (hR : RegCond P G X κ) {τ : ℝ} (hτ : InI L τ) {φ : Ω → ℝ≥0∞} (hφ : Measurable[G] φ) :
    ∫⁻ ω, φ ω * ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, (X ω + h u ω))) ∂P =
      ∫⁻ ω, φ ω * ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, h u ω)) * Ml (κ ω) τ ∂P := by
  have e : ∀ ω, ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, (X ω + h u ω))) =
      ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, h u ω)) *
        ENNReal.ofReal (Real.exp (-τ * X ω)) := fun ω => by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hloc ω τ hτ),
      intervalIntegral.integral_const, smul_eq_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    congr 2
    ring
  simp_rw [e, ← mul_assoc]
  exact hR _ (fun x => ENNReal.ofReal (Real.exp (-τ * x)))
    (hφ.mul (Real.measurable_exp.comp (H_meas G h hh τ).neg).ennreal_ofReal) (by fun_prop)

/-- (H) at one `τ` is `M(·, τ) = e^{H(·, τ)}` almost surely (45.14). -/
lemma key [IsProbabilityMeasure P] (hG : G ≤ m₀)
    (hh : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _ (Function.uncurry h))
    (hloc : ∀ ω τ, InI L τ → IntervalIntegrable (fun u => h u ω) volume 0 τ)
    (hR : RegCond P G X κ) {τ : ℝ} (hτ : InI L τ) :
    (∀ D : Set Ω, MeasurableSet[G] D →
      ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, (X ω + h u ω))) ∂P = P D) ↔
    ∀ᵐ ω ∂P, Ml (κ ω) τ = ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..τ, h u ω)) := by
  set E : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, h u ω))
  set Mf : Ω → ℝ≥0∞ := fun ω => Ml (κ ω) τ
  have hEm : Measurable[G] E := (Real.measurable_exp.comp (H_meas G h hh τ).neg).ennreal_ofReal
  have hMm : Measurable[G] Mf := Ml_meas G κ τ
  have hset : ∀ D, MeasurableSet[G] D →
      ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, (X ω + h u ω))) ∂P =
        ∫⁻ ω in D, E ω * Mf ω ∂P := fun D hD => by
    rw [← lintegral_indicator (hG _ hD), ← lintegral_indicator (hG _ hD)]
    have := step0 hh hloc hR hτ (φ := D.indicator 1) (measurable_one.indicator hD)
    convert this using 2 <;> (funext ω; by_cases hω : ω ∈ D <;> simp [hω, E, Mf])
  have hinv : ∀ ω, E ω * ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..τ, h u ω)) = 1 := fun ω => by
    simp only [E]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  constructor
  · intro hHyp
    have hae : (fun ω => E ω * Mf ω) =ᵐ[P] fun _ => 1 := by
      refine ae_eq_of_ae_eq_trim (hm := hG) (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
        (hEm.mul hMm) measurable_const fun D hD _ => ?_)
      rw [setLIntegral_trim hG (f := fun ω => E ω * Mf ω) (hEm.mul hMm) hD,
        setLIntegral_trim hG measurable_const hD,
        ← hset D hD, hHyp D hD]
      simp
    filter_upwards [hae] with ω hω
    calc Mf ω = ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..τ, h u ω)) * (E ω * Mf ω) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal _) (E ω), hinv, one_mul]
      _ = _ := by rw [hω, mul_one]
  · intro hae D hD
    rw [hset D hD]
    calc ∫⁻ ω in D, E ω * Mf ω ∂P = ∫⁻ _ in D, 1 ∂P := by
          refine setLIntegral_congr_fun_ae (hG _ hD) ?_
          filter_upwards [hae] with ω hω _
          simp only [Mf] at hω ⊢
          rw [hω, hinv]
      _ = P D := by simp

/-- Off the null set of rational `τ`, `M(ω, ·) < ∞` and `H = K` on `[0, L)`. -/
lemma pointwise [@IsMarkovKernel Ω ℝ G _ κ] {ω : Ω}
    (hloc : ∀ ω τ, InI L τ → IntervalIntegrable (fun u => h u ω) volume 0 τ)
    (hq : ∀ q : ℚ, InI L q → Ml (κ ω) q = ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..q, h u ω))) :
    LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L := by
  -- a rational `q ∈ (τ, L)`
  have hrat : ∀ τ, InI L τ → ∃ q : ℚ, τ < q ∧ InI L q := fun τ hτ => by
    obtain ⟨r, hτr, hrL⟩ := exists_between hτ.1 hτ.2
    obtain ⟨q, hτq, hqr⟩ := exists_rat_btwn hτr
    exact ⟨q, hτq, inI_of_lt (hτ.1.trans hτq.le) le_rfl
      (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hqr.le) hrL)⟩
  have hfinq : ∀ q : ℚ, InI L q → Integrable (fun x => Real.exp (-(q : ℝ) * x)) (κ ω) :=
    fun q hq' => integrable_of_Ml (by rw [hq q hq']; exact ENNReal.ofReal_lt_top)
  have hfin : LapFinite (κ ω) L := fun τ hτ => by
    obtain ⟨q, hτq, hq'⟩ := hrat τ hτ
    refine ((integrable_const (1:ℝ)).add (hfinq q hq')).mono'
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-τ * x)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    show Real.exp (-τ * x) ≤ 1 + Real.exp (-(q : ℝ) * x)
    rcases le_total 0 x with hx | hx
    · have : Real.exp (-τ * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hτ.1])
      linarith [Real.exp_pos (-(q : ℝ) * x)]
    · have : Real.exp (-τ * x) ≤ Real.exp (-(q : ℝ) * x) := Real.exp_le_exp.2 (by nlinarith)
      linarith
  refine ⟨hfin, fun τ hτ => ?_⟩
  obtain ⟨q₂, hτq, hq₂⟩ := hrat τ hτ
  have hq₂0 : (0:ℝ) < q₂ := lt_of_le_of_lt hτ.1 hτq
  -- `K = H` at the rationals of `[0, q₂]`
  set s : Set ℝ := Icc 0 (q₂ : ℝ) ∩ range ((↑) : ℚ → ℝ)
  have hs : EqOn (Klap (κ ω)) (fun τ => ∫ u in (0:ℝ)..τ, h u ω) s := by
    rintro _ ⟨hmem, q, rfl⟩
    have hqI : InI L q := inI_of_lt hmem.1 hmem.2 hq₂.2
    have e := hq q hqI
    rw [Ml_eq (hfin q hqI), ENNReal.ofReal_eq_ofReal_iff (Mlap_pos hfin hqI).le
      (Real.exp_pos _).le] at e
    simp only [Klap, e, Real.log_exp]
  have hcK : ContinuousOn (Klap (κ ω)) (Icc 0 (q₂ : ℝ)) := Klap_continuousOn hfin hq₂0.le hq₂.2
  have hcH : ContinuousOn (fun τ => ∫ u in (0:ℝ)..τ, h u ω) (Icc 0 (q₂ : ℝ)) := by
    have hI : IntegrableOn (fun u => h u ω) (uIcc 0 (q₂ : ℝ)) := by
      rw [uIcc_of_le hq₂0.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hq₂0.le).1 (hloc ω q₂ hq₂)
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le hq₂0.le] at this
  have hcl : Icc 0 (q₂ : ℝ) ⊆ closure s := by
    intro x hx
    rcases hx.1.eq_or_lt with h0 | h0
    · exact subset_closure (show x ∈ s from ⟨hx, 0, by simp [h0]⟩)
    rcases hx.2.eq_or_lt with h1 | h1
    · exact subset_closure (show x ∈ s from ⟨hx, q₂, h1.symm⟩)
    exact closure_mono (fun y (hy : y ∈ Ioo 0 (q₂ : ℝ) ∩ range ((↑) : ℚ → ℝ)) =>
      (show y ∈ s from ⟨Ioo_subset_Icc_self hy.1, hy.2⟩))
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo ⟨h0, h1⟩)
  exact (hs.of_subset_closure hcK hcH inter_subset_left hcl ⟨hτ.1, hτq.le⟩).symm

end Main

lemma charS : Standalone.JumpShapeCond.charStatement := by
  intro Ω m₀ P _ G hG X hX h hh L hloc κ hκ hR
  constructor
  · intro hH
    have hae : ∀ q : ℚ, InI L q → ∀ᵐ ω ∂P,
        Ml (κ ω) q = ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..q, h u ω)) := fun q hq =>
      (key hG hh hloc hR hq).1 (hH q hq)
    have hEm : ∀ q : ℝ, Measurable[G] fun ω => ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..q, h u ω)) :=
      fun q => (Real.measurable_exp.comp (H_meas G h hh q)).ennreal_ofReal
    set N : Set Ω := ⋃ q : ℚ, {ω | InI L q} ∩
      {ω | Ml (κ ω) q = ENNReal.ofReal (Real.exp (∫ u in (0:ℝ)..q, h u ω))}ᶜ
    refine ⟨N, ?_, ?_, fun ω hω => pointwise hloc fun q hq => ?_⟩
    · exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
        (measurableSet_eq_fun (Ml_meas G κ q) (hEm q)).compl
    · refine measure_iUnion_null fun q => ?_
      by_cases hq : InI L q
      · exact measure_mono_null inter_subset_right (ae_iff.1 (hae q hq))
      · simp [hq]
    · by_contra hne
      exact hω (mem_iUnion.2 ⟨q, hq, hne⟩)
  · rintro ⟨N, -, hN0, hN⟩ τ hτ
    refine (key hG hh hloc hR hτ).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    obtain ⟨hf, hs⟩ := hN ω hω
    rw [Ml_eq (hf τ hτ), hs τ hτ, Klap, Real.exp_log (Mlap_pos hf hτ)]

theorem jumpShapeCond : Standalone.JumpShapeCond.statement := charS

end Novel.JumpShapeCondProof

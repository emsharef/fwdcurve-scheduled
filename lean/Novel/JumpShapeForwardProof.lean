import Standalone.JumpShapeForward
import Novel.JumpShapeCondBProof

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB Standalone.JumpShapeForward
namespace Novel.JumpShapeForwardProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof Novel.JumpShapeCondProof
open Novel.JumpShapeCondBProof

/-- The shape `h(u) = r_t − f(t, T_n + u)`. -/
def hD (r : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (u : ℝ) (ω : Ω) : ℝ := r ω - fT (Tn + u) ω

section
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω} {Ft G : MeasurableSpace Ω}
  {r J : Ω → ℝ} {fT : ℝ → Ω → ℝ} {Tn : ℝ} {L : ℝ≥0∞}

lemma int_shift (ω : Ω) (τ : ℝ) :
    ∫ T in Tn..Tn + τ, (r ω + J ω - fT T ω) = ∫ u in (0:ℝ)..τ, (J ω + hD r fT Tn u ω) := by
  rw [← add_zero Tn]
  rw [show Tn + 0 + τ = Tn + τ by ring, ← intervalIntegral.integral_comp_add_left
    (fun T => r ω + J ω - fT T ω) Tn]
  simp only [add_zero]
  exact intervalIntegral.integral_congr fun u _ => by simp only [hD]; ring

lemma hyp_iff : HypD P G r J fT Tn L ↔ HypH P G J (hD r fT Tn) L := by
  simp only [HypD, HypH, int_shift]

/-- `h` is `B ⊗ Ft`-measurable. -/
lemma hD_meas (hr : Measurable[Ft] r)
    (hf : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ Ft) _ (Function.uncurry fT)) :
    @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ Ft) _
      (Function.uncurry (hD r fT Tn)) := by
  let _ : MeasurableSpace Ω := Ft
  have h1 : Measurable fun p : ℝ × Ω => (Tn + p.1, p.2) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  exact (hr.comp measurable_snd).sub (hf.comp h1)

lemma prod_mono (hle : Ft ≤ G) :
    @Prod.instMeasurableSpace ℝ Ω _ Ft ≤ @Prod.instMeasurableSpace ℝ Ω _ G :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono hle)

lemma hD_loc (hloc : ∀ ω τ, InI L τ → IntervalIntegrable (fun T => fT T ω) volume Tn (Tn + τ))
    (ω : Ω) (τ : ℝ) (hτ : InI L τ) :
    IntervalIntegrable (fun u => hD r fT Tn u ω) volume 0 τ := by
  have := (hloc ω τ hτ).comp_add_left Tn
  simp only [sub_self, add_sub_cancel_left] at this
  exact intervalIntegrable_const.sub this

/-- The hypotheses of (a) for `h`, given `σ`-algebra `G' ⊇ Ft`. -/
lemma setting_of {G' : MeasurableSpace Ω} (hS : SettingD P Ft G r J fT Tn L) (hFG' : Ft ≤ G')
    (hG' : G' ≤ m₀) {κ : @Kernel Ω ℝ G' _} (hκ : @IsMarkovKernel Ω ℝ G' _ κ)
    (hR : RegCond P G' J κ) : Setting P G' J (hD r fT Tn) L κ := by
  obtain ⟨hP, -, -, hr, hJ, hf, hloc⟩ := hS
  exact ⟨hP, hG', hJ, (hD_meas hr hf).mono (prod_mono hFG') le_rfl, fun ω τ hτ =>
    hD_loc hloc ω τ hτ, hκ, hR⟩
end

lemma forwardS : Standalone.JumpShapeForward.forwardStatement := by
  intro Ω m₀ P Ft G r J fT Tn L κ hS hκ hR
  have hSet := setting_of hS hS.2.1 hS.2.2.1 hκ hR
  rw [hyp_iff]
  constructor
  · intro hH
    obtain ⟨N, -, hN0, hN⟩ := shapeCondS Ω m₀ P G J _ L κ hSet hH
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    obtain ⟨hf, -, -, hae, -⟩ := hN ω hω
    refine ⟨hf, ?_⟩
    filter_upwards [hae] with τ hτ hIo
    have := hτ hIo
    simp only [hD] at this
    linarith
  · intro hae
    refine converseCondS Ω m₀ P G J _ L κ hSet ?_
    filter_upwards [hae] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with τ hτ hIo
    simp only [hD]
    linarith [hτ hIo]

lemma lawS : Standalone.JumpShapeForward.lawStatement := by
  intro Ω m₀ P Ft G r J fT Tn L κ κt hL hS hκ hR hκt hRt hH
  have hSet := setting_of hS hS.2.1 hS.2.2.1 hκ hR
  have hSett := setting_of hS le_rfl (hS.2.1.trans hS.2.2.1) hκt hRt
  have hHG := hyp_iff.1 hH
  have hHt : HypH P Ft J (hD r fT Tn) L := fun τ hτ D hD' => hHG τ hτ D (hS.2.1 _ hD')
  obtain ⟨N, -, hN0, hN⟩ := null_of_hyp hSet hHG
  obtain ⟨Nt, -, hNt0, hNt⟩ := null_of_hyp hSett hHt
  have heq : ∀ᵐ ω ∂P, κt ω = κ ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, measure_eq_zero_iff_ae_notMem.1 hNt0]
      with ω hω hωt
    obtain ⟨hf, hs⟩ := hN ω hω
    obtain ⟨hft, hst⟩ := hNt ω hωt
    refine uniqueS (κt ω) (κ ω) L hL hft hf fun τ hτ => ?_
    rw [← Real.exp_log (Mlap_pos hft hτ), ← Real.exp_log (Mlap_pos hf hτ)]
    change Real.exp (Klap (κt ω) τ) = Real.exp (Klap (κ ω) τ)
    rw [← hst τ hτ, ← hs τ hτ]
  refine ⟨heq, ?_⟩
  filter_upwards [(forwardS Ω m₀ P Ft G r J fT Tn L κ hS hκ hR).1 hH, heq] with ω hω he
  rw [he]
  exact hω

lemma rightS : Standalone.JumpShapeForward.rightStatement := by
  intro Ω m₀ P Ft G r J fT Tn L κ hS hκ hR hH hc
  have hSet := setting_of hS hS.2.1 hS.2.2.1 hκ hR
  obtain ⟨N, -, hN0, hN⟩ := shapeCondS Ω m₀ P G J _ L κ hSet (hyp_iff.1 hH)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω τ hτ
  obtain ⟨-, -, -, -, hrc, -⟩ := hN ω hω
  have hcont : ContinuousWithinAt (fun u => hD r fT Tn u ω) (Ici τ) τ := by
    have h1 : ContinuousWithinAt (fun u : ℝ => Tn + u) (Ici τ) τ :=
      (continuous_const.add continuous_id).continuousWithinAt
    exact continuousWithinAt_const.sub ((hc ω τ hτ).comp h1 fun u hu => by
      simp only [mem_Ici] at hu ⊢
      linarith)
  have := hrc τ hτ hcont
  simp only [hD] at this
  linarith

lemma bondS : Standalone.JumpShapeForward.bondStatement := by
  intro Ω m₀ P Ft G r J fT t Tn L κ κt hL htT hS hflat hκ hR hκt hRt hH
  have hSet := setting_of hS hS.2.1 hS.2.2.1 hκ hR
  obtain ⟨N, -, hN0, hN⟩ := null_of_hyp hSet (hyp_iff.1 hH)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0,
    (lawS Ω m₀ P Ft G r J fT Tn L κ κt hL hS hκ hR hκt hRt hH).1] with ω hω he τ hτ
  obtain ⟨hf, hs⟩ := hN ω hω
  have hae : ∀ᵐ x ∂volume, x ∈ uIoc t Tn → fT x ω = r ω := by
    filter_upwards [Measure.ae_ne volume Tn] with x hx hmem
    rw [uIoc_of_le htT.le] at hmem
    exact hflat ω x ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩
  have hI1 : IntervalIntegrable (fun T => fT T ω) volume t Tn :=
    (intervalIntegrable_const (c := r ω)).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 (by
        filter_upwards [hae] with x hx hmem using (hx hmem).symm))
  have hI2 := hS.2.2.2.2.2.2 ω τ hτ
  have e1 : ∫ T in t..Tn, fT T ω = r ω * (Tn - t) := by
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have e2 : ∫ T in Tn..Tn + τ, fT T ω = r ω * τ - Klap (κ ω) τ := by
    rw [← hs τ hτ]
    have := int_shift (r := r) (J := fun _ => 0) (fT := fT) (Tn := Tn) ω τ
    simp only [zero_add, add_zero] at this
    rw [show (∫ T in Tn..Tn + τ, fT T ω) = r ω * τ - ∫ T in Tn..Tn + τ, (r ω - fT T ω) by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hI2, intervalIntegral.integral_const,
        smul_eq_mul]
      ring, this]
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, e1, e2, Klap,
    show -(r ω * (Tn - t) + (r ω * τ - Real.log (Mlap (κ ω) τ))) =
      -r ω * (Tn + τ - t) + Real.log (Mlap (κ ω) τ) by ring, Real.exp_add,
    Real.exp_log (Mlap_pos hf hτ)]

theorem jumpShapeForward : Standalone.JumpShapeForward.statement :=
  ⟨forwardS, lawS, rightS, bondS⟩

end Novel.JumpShapeForwardProof

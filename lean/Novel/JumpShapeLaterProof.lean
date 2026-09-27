import Standalone.JumpShapeLater
import Novel.JumpShapeCondBProof

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB Standalone.JumpShapeLater
namespace Novel.JumpShapeLaterProof

lemma laterS : Standalone.JumpShapeLater.laterStatement := by
  intro Ω m₀ P hP G hG S hS hES
  have hf : Measurable[m₀] fun ω => ENNReal.ofReal (Real.exp (-S ω)) :=
    (Real.measurable_exp.comp hS.neg).ennreal_ofReal
  have hfin : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (-S ω)) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hset : ∀ (D : Set Ω), MeasurableSet[m₀] D → ∀ g : Ω → ℝ≥0∞,
      ∫⁻ ω in D, g ω ∂tiltS P S = ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-S ω)) * g ω ∂P :=
    fun D hD g => by
      rw [tiltS, restrict_withDensity hD,
        lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf (ae_restrict_of_ae hfin)]
      rfl
  have hGD : ∀ D : Set Ω, MeasurableSet[G] D → tiltS P S D = P D := fun D hD => by
    rw [tiltS, withDensity_apply _ (hG _ hD)]
    exact hES D hD
  refine ⟨⟨by rw [hGD univ MeasurableSet.univ, measure_univ]⟩, hGD, fun X h L => ?_⟩
  refine forall_congr' fun τ => imp_congr_right fun _ => forall_congr' fun D =>
    imp_congr_right fun hD => ?_
  rw [hset D (hG _ hD), hGD D hD]
  simp_rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← sub_eq_add_neg]

lemma laterCharS : Standalone.JumpShapeLater.laterCharStatement := by
  intro Ω m₀ P hP G hG S hS hES X h L κ hSet
  obtain ⟨-, hGD, hiff⟩ := laterS Ω m₀ P hP G hG S hS hES
  obtain ⟨hPS, -, hX, hh, hloc, hκ, hR⟩ := hSet
  have hchar := @Novel.JumpShapeCondProof.charS Ω m₀ (tiltS P S) hPS G hG X hX h hh L hloc κ hκ hR
  refine ⟨(hiff X h L).trans (hchar.trans ?_), fun hH => ?_⟩
  · refine exists_congr fun N => and_congr_right fun hN => and_congr_left fun _ => ?_
    rw [hGD N hN]
  · obtain ⟨N, hN, hN0, hNω⟩ := Novel.JumpShapeCondBProof.shapeCondS Ω m₀ (tiltS P S) G X h L κ
      ⟨hPS, hG, hX, hh, hloc, hκ, hR⟩ ((hiff X h L).1 hH)
    exact ⟨N, hN, by rw [← hGD N hN]; exact hN0, fun ω hω => (hNω ω hω).2.2.2.1⟩

theorem jumpShapeLater : Standalone.JumpShapeLater.statement := ⟨laterS, laterCharS⟩

end Novel.JumpShapeLaterProof

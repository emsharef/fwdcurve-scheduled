import Standalone.RecurrentLoadingAssembly
import Novel.RecurrentLoadingAlgebraProof
import Novel.RecurrentLoadingDriftProof
import Novel.RecurrentLoadingDiffusionProof
import Novel.RecurrentLoadingStatePProof
import Novel.RecurrentLoadingRestartPProof
import Novel.RecurrentLoadingStateQProof
import Novel.RecurrentLoadingRestartQProof
import Novel.RecurrentLoadingXiProof
import Novel.RecurrentLoadingXiEquationProof
import Novel.ExternalScaleConditionsProof
import Novel.RecurrentLoadingCharacterizationProof

open MeasureTheory Matrix
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingDrift Standalone.RecurrentLoadingDiffusion
open Standalone.ExternalScaleConditions Standalone.RecurrentLoadingAssembly
namespace Novel.RecurrentLoadingAssemblyProof

lemma curve : curveStatement := by
  intro Ω mΩ S k p r Tm u v M c b A
  let h : ℝ≥0 → Ω → ℝ := fun _ _ => 1
  have hP : IsStronglyPredictable S.ℱ h := stronglyMeasurable_const
  have hC : ∀ s ω, |h s ω| ≤ 1 := fun _ _ => by simp [h]
  have e : ∀ T, sigmaInt Tm u v M c b A h T =
      fun (s : ℝ≥0) (_ : Ω) => sigma030 Tm u v M c b A (s : ℝ) T :=
    fun T => by funext s ω; simp [sigmaInt, h]
  refine ⟨fun T => ?_, fun t x hx => ?_⟩
  · rw [← e]
    exact (Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP 1 hC p r Tm
      u v M c b A 0).1 T
  have hD := (Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP 1 hC p r Tm
    u v M c b A t).2.2 x hx
  rw [e] at hD
  filter_upwards [hD] with ω hω
  have hdr := Novel.RecurrentLoadingDriftProof.drift p r Tm u v M c b A t x t.coe_nonneg hx
  simp only [hjm030, curve031, state030]
  rw [hdr, hω, dotProduct_add, dotProduct_add, dotProduct_add]
  have e' : ∀ X : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
      of (X : Fin p × Fin r → Fin p × Fin r → ℝ) = X := fun X => rfl
  rw [e']
  ring

lemma symmetry : symmetryStatement := by
  intro p r Tm v M b A t
  ext i j
  simp only [transpose_apply, P030]
  congr 1
  funext s
  ring

theorem recurrentLoadingAssembly : Standalone.RecurrentLoadingAssembly.statement := ⟨Novel.RecurrentLoadingAlgebraProof.recurrentLoadingAlgebra, Novel.RecurrentLoadingDriftProof.recurrentLoadingDrift, Novel.RecurrentLoadingDiffusionProof.recurrentLoadingDiffusion, Novel.RecurrentLoadingStatePProof.recurrentLoadingStateP, Novel.RecurrentLoadingRestartPProof.recurrentLoadingRestartP, Novel.RecurrentLoadingStateQProof.recurrentLoadingStateQ, Novel.RecurrentLoadingRestartQProof.recurrentLoadingRestartQ, Novel.RecurrentLoadingXiProof.recurrentLoadingXi, Novel.RecurrentLoadingXiEquationProof.recurrentLoadingXiEquation, Novel.ExternalScaleConditionsProof.externalScaleConditions, Novel.RecurrentLoadingCharacterizationProof.recurrentLoadingCharacterization, curve, symmetry⟩

end Novel.RecurrentLoadingAssemblyProof

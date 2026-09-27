import Standalone.ExternalScaleAssembly
import Novel.RecurrentLoadingAlgebraProof
import Novel.ExternalScaleDriftProof
import Novel.RecurrentLoadingDiffusionProof
import Novel.ExternalScaleStatePProof
import Novel.ExternalScaleStateQProof
import Novel.RecurrentLoadingXiProof
import Novel.RecurrentLoadingXiEquationProof
import Novel.ExternalScaleConditionsProof

open MeasureTheory Matrix
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingDrift Standalone.RecurrentLoadingDiffusion
open Standalone.ExternalScaleDrift Standalone.ExternalScaleConditions
open Standalone.BoundedVarianceMartingale Standalone.ExternalScaleAssembly
namespace Novel.ExternalScaleAssemblyProof

lemma curve : curveStatement := by
  intro Ω mΩ S k hPred n Z hZa hZc ψ C hψc hψC p r Tm u v M c b A
  let h : ℝ≥0 → Ω → ℝ := fun s ω => ψ (Z s ω)
  have hP : IsStronglyPredictable S.ℱ h :=
    hPred.continuous_predictable h (fun t => hψc.measurable.comp (hZa t))
      (fun ω => hψc.comp (hZc ω))
  have hC : ∀ s ω, |h s ω| ≤ C := fun s ω => hψC _
  refine ⟨fun T => (Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP C hC p r Tm
    u v M c b A 0).1 T, fun t x hx => ?_⟩
  have hD := (Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP C hC p r Tm
    u v M c b A t).2.2 x hx
  filter_upwards [hD] with ω hω
  have hmeas : Measurable fun s : ℝ => ψ (Z (Real.toNNReal s) ω) :=
    ((hψc.comp (hZc ω)).comp continuous_real_toNNReal).measurable
  have hdr := Novel.ExternalScaleDriftProof.drift p r Tm u v M c b A
    (fun s => ψ (Z (Real.toNNReal s) ω)) hmeas ⟨C, fun s => hψC _⟩ t x t.coe_nonneg hx
  simp only [hjm031, curve031, state031]
  rw [hdr, hω, dotProduct_add, dotProduct_add, dotProduct_add]
  have e : ∀ X : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
      of (X : Fin p × Fin r → Fin p × Fin r → ℝ) = X := fun X => rfl
  rw [e]
  ring

lemma symmetry : symmetryStatement := by
  intro p r Tm v M b A h t
  ext i j
  simp only [transpose_apply, P031]
  congr 1
  funext s
  ring

theorem externalScaleAssembly : Standalone.ExternalScaleAssembly.statement := ⟨Novel.RecurrentLoadingAlgebraProof.recurrentLoadingAlgebra, Novel.ExternalScaleDriftProof.externalScaleDrift, Novel.RecurrentLoadingDiffusionProof.recurrentLoadingDiffusion, Novel.ExternalScaleStatePProof.externalScaleStateP, Novel.ExternalScaleStateQProof.externalScaleStateQ, Novel.RecurrentLoadingXiProof.recurrentLoadingXi, Novel.RecurrentLoadingXiEquationProof.recurrentLoadingXiEquation, Novel.ExternalScaleConditionsProof.externalScaleConditions, curve, symmetry⟩

end Novel.ExternalScaleAssemblyProof

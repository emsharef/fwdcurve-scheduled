import Standalone.BoundedVarianceExistence
import Standalone.BoundedVarianceMartingale

/-! # Claim 028 (a0): a scale state with every path continuous

From any `Solution6` solution `Z'` of (28.1) started at `z0` (the form AX-06a
supplies), replacing it by `z0` on one null set in `ℱ 0` gives a process `Z`
that is adapted, has every path continuous, is indistinguishable from `Z'`, and
is again a `Solution6` solution. AX-09 (`Predictability`) then makes every
`psi (t, Z t)` with `psi` jointly continuous predictable; with `psi` bounded it
is in (U4), which is the scale hypothesis of Claim 026. The calculus and AX-09
are the supplied standalone mirrors of the audited inputs.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale
namespace Standalone.SeparableMeetingScaleVersion

def statement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → ∀ (p : ℕ) (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ)
  (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ) (z0 : Fin p → ℝ)
  (Z' : ℝ≥0 → Ω → Fin p → ℝ),
  Coefficients6 beta Sigma → Solution6 S beta Sigma (fun _ => z0) Z' →
  ∃ Z : ℝ≥0 → Ω → Fin p → ℝ,
    (∀ ω, Continuous fun t => Z t ω) ∧ (∀ t, Measurable[S.ℱ t] (Z t)) ∧
    (∀ᵐ ω ∂S.μ, ∀ t, Z t ω = Z' t ω) ∧
    Solution6 S beta Sigma (fun _ => z0) Z ∧
    ∀ (psi : ℝ≥0 × (Fin p → ℝ) → ℝ), Continuous psi → ∀ K : ℝ, (∀ q, |psi q| ≤ K) →
      U4 S.ℱ S.μ (fun t ω => psi (t, Z t ω))

end Standalone.SeparableMeetingScaleVersion

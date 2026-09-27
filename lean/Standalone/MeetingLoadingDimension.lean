import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Claim 029 (a): the dimension step

If a random vector `V` in `ℝ^r` has a law absolutely continuous with respect to
Lebesgue measure and almost surely equals `Φ (Y)` for a random `Y` that almost surely lies in a
set `Z ⊆ ℝ^q` on which every coordinate of `Φ` is locally Lipschitz (the
regularity the claim adds to (R3); `Z` may be the open domain of `G` in
[bjork2001existence] Definition 3.1, or all of `ℝ^q`), then `r ≤ q`. No
measurability of `Y` or of `Z` is assumed. This is the
step of (a) that bounds `rank H_{R,n}` by the state dimension once `V` is the
projection of the curve values onto independent rows; the curve formula (29.3)
and the absolute continuity of that `V` are not in this target.
-/

open MeasureTheory
namespace Standalone.MeetingLoadingDimension

def statement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (q r : ℕ) (V : Ω → Fin r → ℝ) (Y : Ω → Fin q → ℝ)
  (Φ : (Fin q → ℝ) → Fin r → ℝ) (Z : Set (Fin q → ℝ)),
  AEMeasurable V μ → μ.map V ≪ volume → (∀ i, LocallyLipschitzOn Z fun y => Φ y i) →
  (∀ᵐ ω ∂μ, Y ω ∈ Z ∧ V ω = Φ (Y ω)) → r ≤ q

end Standalone.MeetingLoadingDimension

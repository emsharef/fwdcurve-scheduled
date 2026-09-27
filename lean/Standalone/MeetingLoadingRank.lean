import Standalone.MeetingLoadingHankel
import Standalone.MeetingLoadingDimension
import Standalone.MeetingLoadingLaw

/-! # Claim 029 (a): the rank bound from a realization

If the curve values `f` at `R+1` maturities are almost surely `c + H_{R,n} δ`
(the form (29.3)) for a random vector `δ` of `n+1` increments with an absolutely
continuous law, and almost surely equal `Ψ (Y)` for a state `Y` in a set
`Z ⊆ ℝ^q` on which every coordinate of `Ψ` is locally Lipschitz (the
regularity added to (R3); `Ψ (y)` stands for the values `G(y, D(t))(x_i)` at
the maturities), then `rank H_{R,n} ≤ q`. The proof projects onto the range of
`H_{R,n}` and applies the dimension step. The curve formula (29.3) itself is a
separate target.
-/

open MeasureTheory
open Standalone.MeetingLoadingHankel
namespace Standalone.MeetingLoadingRank

def statement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (a : ℕ → ℝ) (R n : ℕ) (δ : Ω → Fin (n+1) → ℝ),
  AEMeasurable δ μ → μ.map δ ≪ volume →
  ∀ (f : Ω → Fin (R+1) → ℝ) (c : Fin (R+1) → ℝ),
  (∀ᵐ ω ∂μ, f ω = c + (hankel029 a R n).mulVec (δ ω)) →
  ∀ (q : ℕ) (Y : Ω → Fin q → ℝ) (Z : Set (Fin q → ℝ)) (Ψ : (Fin q → ℝ) → Fin (R+1) → ℝ),
  (∀ i, LocallyLipschitzOn Z fun y => Ψ y i) →
  (∀ᵐ ω ∂μ, Y ω ∈ Z ∧ f ω = Ψ (Y ω)) →
  (hankel029 a R n).rank ≤ q

end Standalone.MeetingLoadingRank

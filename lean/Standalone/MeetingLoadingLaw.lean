import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-! # Claim 029 (a): the law of the projected past increments

`piStatement`: a product of laws on `ℝ` each absolutely continuous with respect
to Lebesgue measure is absolutely continuous on `ℝ^m`. `affineStatement`: the
image of such a law under `x ↦ c + A x`, with `A` a surjective linear map onto
`ℝ^r`, is absolutely continuous on `ℝ^r`. `lawStatement`: for a pre-Brownian
motion (Mathlib's `IsPreBrownianReal`) and strictly increasing times
`τ_0 < ... < τ_m`, the increment vector `(W_{τ_{l+1}} − W_{τ_l})_l`, and hence
`c + A` of it, has an absolutely continuous law. With `A` the rows of
`H_{R,n}` that are linearly independent, this is the absolute continuity of
the law of `V = P(c + H_{R,n} ΔW)` in Claim 029(a).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Standalone.MeetingLoadingLaw

def piStatement : Prop := ∀ (m : ℕ) (ρ : Fin m → Measure ℝ), (∀ i, SigmaFinite (ρ i)) →
  (∀ i, ρ i ≪ volume) → Measure.pi ρ ≪ volume

def affineStatement : Prop := ∀ (m r : ℕ) (ν : Measure (Fin m → ℝ))
  (A : (Fin m → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (c : Fin r → ℝ),
  ν ≪ volume → Function.Surjective A → ν.map (fun x => c + A x) ≪ volume

def lawStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω)
  (W : ℝ≥0 → Ω → ℝ), IsPreBrownianReal W μ →
  ∀ (m r : ℕ) (τ : Fin (m+1) → ℝ≥0), StrictMono τ →
  ∀ (A : (Fin m → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (c : Fin r → ℝ), Function.Surjective A →
    μ.map (fun ω => c + A (fun l => W (τ l.succ) ω - W (τ l.castSucc) ω)) ≪ volume

def statement : Prop := piStatement ∧ affineStatement ∧ lawStatement

end Standalone.MeetingLoadingLaw

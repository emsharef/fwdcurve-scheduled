import Standalone.ContinuousAggregationAmericanLower

/-! # Claim 054 (e): the American value (54.6)

Claim 046's model, **conditional on `GaussLaw`**, with the definitions of
`Standalone.ContinuousAggregationAmericanLower`: the exercise times `𝒯[A, S]` (`modelTimes`), the
value `U` (`Uval`), the post-cutoff filtration `σ(Y′, Ξ′_{≤t})` (`postFilt`), and the integrand
`Pay = e^{−Λ_{V_A}} Φ`.

`americanStatement`, (54.6): under the envelope (54.5), `|e^{−Λ_{V_A}(t, y, ξ)} Φ(t, y, ξ)| ≤ D(y, ξ)`
on `[A, S]` with `D` integrable under `N(0, V_A) ⊗ λ_post`,
`U = P(0, A) · sup_{ρ ∈ 𝒯̃[A, S]} ∫ e^{−Λ_{V_A}(ρ, ·)} Φ(ρ, ·) d(N(0, V_A) ⊗ λ_post)`.
Here `𝒯̃[A, S]` are the stopping times of the usual augmentation of `postFilt` under
`N(0, V_A) ⊗ λ_post` (`Sectioning.times`), and the supremum is `Sectioning.value₂`. No assumption
`V_A > 0` is made.
-/

open MeasureTheory ProbabilityTheory Set

namespace Standalone.ContinuousAggregationAmerican
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw)
open Standalone.DiffusionMeetingPricing (Qacc P0)
open Standalone.ContinuousAggregationEuropean (State Xi)
open Standalone.ContinuousAggregationSectioning (value₂)
open Standalone.ContinuousAggregationAmericanLower (Uval postFilt Pay)

def americanStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ A S : ℝ, 0 ≤ A → A ≤ S → S ≤ H →
  ∀ (Φ : ℝ × (ℝ × State N A H) → ℝ) (D : ℝ × State N A H → ℝ), Measurable Φ → Measurable D →
    Integrable D ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))) →
    (∀ t ∈ Icc A S, ∀ p, |Pay M A H Φ (t, p)| ≤ D p) →
    Uval M Q A S H Φ = P0 M A * value₂ ((gaussianReal 0 (Qacc M A).toNNReal).prod
      (Q.map (Xi M A H))) (postFilt M A H S) A S (Pay M A H Φ)

def statement : Prop := americanStatement

end Standalone.ContinuousAggregationAmerican

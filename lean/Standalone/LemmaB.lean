import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 001 (Lemma B): statement only

Let `μ` be a probability measure, `X` a real random variable, and `λ ≠ 0`. If
`exp (-λ * X)` and `exp (-λ / 2 * X)` are both integrable with expectation `1`,
then `X = 0` almost surely.

Finiteness of the expectations in (1.1) and (1.2) of `math/claims/001-lemma-b.md` is
encoded as `Integrable`. No measurability hypothesis on `X` is needed: for `λ ≠ 0`,
integrability of `exp (-λ * X)` already makes `X` almost-everywhere measurable.
-/

open MeasureTheory Real

namespace Standalone.LemmaB

def statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (l : ℝ), l ≠ 0 →
    Integrable (fun ω ↦ exp (-l * X ω)) μ → ∫ ω, exp (-l * X ω) ∂μ = 1 →
    Integrable (fun ω ↦ exp (-l / 2 * X ω)) μ → ∫ ω, exp (-l / 2 * X ω) ∂μ = 1 →
    ∀ᵐ ω ∂μ, X ω = 0

end Standalone.LemmaB

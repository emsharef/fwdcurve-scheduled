import Standalone.JumpShapeProfile
import Mathlib.Probability.Kernel.Basic

/-! # Claim 045 (a): the characterization with one null set

`(Ω, m₀, P)` is a probability space and `G ≤ m₀` a sub-σ-algebra. `X` is the level jump and
`h : ℝ → Ω → ℝ` the compensating shape, `B ⊗ G`-measurable (`uncurry h`, with `ℝ` first), and
integrable on `[0, τ]` for every `τ ∈ [0, L)` and every `ω`.

`κ` is a regular conditional distribution of `X` given `G`: a Markov kernel from `(Ω, G)` to `ℝ`
that computes conditional expectations of nonnegative functions (`RegCond`),
`∫ f · g(X) dP = ∫ f(ω) ∫ g dκ(ω) dP` for `G`-measurable `f ≥ 0` and measurable `g ≥ 0`.
This is the property the claim uses. Its existence is standard and not asserted here.

`HypH` is (H), (45.3): `E[exp(−∫_0^τ ξ) | G] = 1` for every `τ ∈ [0, L)`, with `ξ(u) = X + h(u)`
(45.1), stated through its defining property as a `[0, ∞]`-valued conditional expectation:
`∫_D exp(−∫_0^τ ξ) dP = P(D)` for every `D ∈ G`. No integrability is assumed.

* `charStatement` is (a): (H) holds iff there is a `G`-measurable `P`-null set `N` such that for
  every `ω ∉ N`, `M(ω, ·) < ∞` on `[0, L)` and `H(ω, τ) = K(ω, τ)` for every `τ ∈ [0, L)` (45.4).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeCond
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile

/-- `κ` computes conditional expectations of nonnegative functions of `X` given `G`. -/
def RegCond {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (G : MeasurableSpace Ω)
    (X : Ω → ℝ) (κ : @Kernel Ω ℝ G _) : Prop :=
  ∀ (f : Ω → ℝ≥0∞) (g : ℝ → ℝ≥0∞), Measurable[G] f → Measurable g →
    ∫⁻ ω, f ω * g (X ω) ∂P = ∫⁻ ω, f ω * ∫⁻ x, g x ∂(κ ω) ∂P

/-- (H), (45.3), through set integrals over `G`. -/
def HypH {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (G : MeasurableSpace Ω) (X : Ω → ℝ)
    (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ τ, InI L τ → ∀ D : Set Ω, MeasurableSet[G] D →
    ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-∫ u in (0:ℝ)..τ, (X ω + h u ω))) ∂P = P D

def charStatement : Prop := ∀ (Ω : Type) [m₀ : MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P] (G : MeasurableSpace Ω), G ≤ m₀ → ∀ (X : Ω → ℝ), Measurable[m₀] X →
  ∀ (h : ℝ → Ω → ℝ), @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _
    (Function.uncurry h) →
  ∀ L : ℝ≥0∞, (∀ ω τ, InI L τ → IntervalIntegrable (fun u => h u ω) volume 0 τ) →
  ∀ (κ : @Kernel Ω ℝ G _), @IsMarkovKernel Ω ℝ G _ κ → RegCond P G X κ →
  (HypH P G X h L ↔ ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
    ∀ ω ∉ N, LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L)

def statement : Prop := charStatement

end Standalone.JumpShapeCond

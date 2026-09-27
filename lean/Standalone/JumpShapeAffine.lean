import Standalone.JumpShapeProfile
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Claim 045 (c1): the affine shape, for one conditional law

For one `ω`, `ν = κ(ω, ·)` and the shape `h(u) = c + y u`, with `c = c(ω)`, `y = y(ω)`.
`affineStatement` is (45.8) at `ω`: `M < ∞` on `[0, L)` and `H = K` there (45.4) if and only if
`y ≥ 0` and `ν = N(−c, y)`. Taken over `ω`, with (a), this is (c1).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeAffine
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile

def affineStatement : Prop := ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ≥0∞) (c y : ℝ),
  0 < L → ((LapFinite ν L ∧ ShapeEq ν (fun u => c + y * u) L) ↔
    (0 ≤ y ∧ ν = gaussianReal (-c) y.toNNReal))

def statement : Prop := affineStatement

end Standalone.JumpShapeAffine

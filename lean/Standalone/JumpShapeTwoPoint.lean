import Standalone.JumpShapeProfile
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Convex.Deriv

/-! # Claim 045 (c2): a two-point level jump

`G` is trivial and `L = ∞`. The level jump is `Δ ≠ 0` with probability `p ∈ (0, 1)` and `0` otherwise
(`twoPoint p Δ`). `qTwo p Δ τ = p e^{−τΔ} / (1 − p + p e^{−τΔ})` is the tilted probability of the
jump, `hTwo = −Δ q` (45.9), `h1Two = Δ² q (1 − q)` and `h2Two = −Δ³ q (1 − q)(1 − 2q)`.

* `shapeStatement`: `M < ∞` on `[0, ∞)`, `∫_0^τ hTwo = K(τ)` (45.4), and `hTwo = −Ẽ_τ[X]`, so `hTwo`
  is the continuous shape of (b). `hTwo′ = h1Two > 0` and `h1Two′ = h2Two`.
* `concavityStatement`: if `Δ(1 − 2p) ≥ 0`, `hTwo` is strictly concave on `[0, ∞)`. Otherwise
  `τ* = log(p/(1 − p))/Δ > 0`, and `hTwo` is strictly convex on `[0, τ*]` and strictly concave on
  `[τ*, ∞)`. In every case `hTwo` is not affine on `[0, ∞)`.
* `halfStatement`: for `p = ½`, `hTwo(τ) = −(Δ/2)(1 − tanh(Δτ/2))`.
* `gaussianStatement`: `N(pΔ, p(1 − p)Δ²)` has, by (c1), the ramp `hG(τ) = −pΔ + p(1 − p)Δ² τ`, which
  is `hTwo(0) + hTwo′(0) τ`. If `Δ(1 − 2p) ≥ 0`, the gap `g = hG − hTwo` is nonnegative and
  nondecreasing on `[0, ∞)`.
* `gapStatement`, (45.10): for `p = ½`, `g(τ) = (|Δ|/2)(z − tanh z)` with `z = |Δ|τ/2`, so
  `0 ≤ g(τ) ≤ |Δ|⁴ τ³/48`, and `0 ≤ (1/τ) ∫_0^τ g ≤ |Δ|⁴ τ³/192` for `τ > 0`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeTwoPoint
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile

/-- `X = Δ` with probability `p`, `X = 0` with probability `1 − p`. -/
noncomputable def twoPoint (p Δ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac Δ

/-- The tilted probability of the jump. -/
noncomputable def qTwo (p Δ τ : ℝ) : ℝ := p * Real.exp (-τ * Δ) / (1 - p + p * Real.exp (-τ * Δ))

noncomputable def hTwo (p Δ τ : ℝ) : ℝ := -Δ * qTwo p Δ τ

noncomputable def h1Two (p Δ τ : ℝ) : ℝ := Δ ^ 2 * qTwo p Δ τ * (1 - qTwo p Δ τ)

noncomputable def h2Two (p Δ τ : ℝ) : ℝ :=
  -Δ ^ 3 * qTwo p Δ τ * (1 - qTwo p Δ τ) * (1 - 2 * qTwo p Δ τ)

/-- The tangent Gaussian ramp `−pΔ + p(1 − p)Δ² τ`. -/
def hGauss (p Δ τ : ℝ) : ℝ := -p * Δ + p * (1 - p) * Δ ^ 2 * τ

def shapeStatement : Prop := ∀ p Δ : ℝ, 0 < p → p < 1 → Δ ≠ 0 →
  IsProbabilityMeasure (twoPoint p Δ) ∧ LapFinite (twoPoint p Δ) ⊤ ∧
  ShapeEq (twoPoint p Δ) (hTwo p Δ) ⊤ ∧ (∀ τ, hTwo p Δ τ = -tiltMean (twoPoint p Δ) τ) ∧
  ∀ τ, HasDerivAt (hTwo p Δ) (h1Two p Δ τ) τ ∧ HasDerivAt (h1Two p Δ) (h2Two p Δ τ) τ ∧
    0 < h1Two p Δ τ

def concavityStatement : Prop := ∀ p Δ : ℝ, 0 < p → p < 1 → Δ ≠ 0 →
  (0 ≤ Δ * (1 - 2 * p) → StrictConcaveOn ℝ (Ici 0) (hTwo p Δ)) ∧
  (Δ * (1 - 2 * p) < 0 → 0 < Real.log (p / (1 - p)) / Δ ∧
    StrictConvexOn ℝ (Icc 0 (Real.log (p / (1 - p)) / Δ)) (hTwo p Δ) ∧
    StrictConcaveOn ℝ (Ici (Real.log (p / (1 - p)) / Δ)) (hTwo p Δ)) ∧
  ¬ ∃ a b : ℝ, ∀ τ, 0 ≤ τ → hTwo p Δ τ = a + b * τ

def halfStatement : Prop := ∀ Δ τ : ℝ, hTwo (1 / 2) Δ τ = -(Δ / 2) * (1 - Real.tanh (Δ * τ / 2))

def gaussianStatement : Prop := ∀ p Δ : ℝ, 0 < p → p < 1 → Δ ≠ 0 →
  LapFinite (gaussianReal (p * Δ) (p * (1 - p) * Δ ^ 2).toNNReal) ⊤ ∧
  ShapeEq (gaussianReal (p * Δ) (p * (1 - p) * Δ ^ 2).toNNReal) (hGauss p Δ) ⊤ ∧
  (∀ τ, hGauss p Δ τ = hTwo p Δ 0 + h1Two p Δ 0 * τ) ∧
  (0 ≤ Δ * (1 - 2 * p) → (∀ τ, 0 ≤ τ → 0 ≤ hGauss p Δ τ - hTwo p Δ τ) ∧
    MonotoneOn (fun τ => hGauss p Δ τ - hTwo p Δ τ) (Ici 0))

def gapStatement : Prop := ∀ Δ τ : ℝ, 0 ≤ τ →
  hGauss (1 / 2) Δ τ - hTwo (1 / 2) Δ τ =
    |Δ| / 2 * (|Δ| * τ / 2 - Real.tanh (|Δ| * τ / 2)) ∧
  0 ≤ hGauss (1 / 2) Δ τ - hTwo (1 / 2) Δ τ ∧
  hGauss (1 / 2) Δ τ - hTwo (1 / 2) Δ τ ≤ |Δ| ^ 4 * τ ^ 3 / 48 ∧
  (0 < τ → 0 ≤ (1 / τ) * ∫ s in (0:ℝ)..τ, (hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s) ∧
    (1 / τ) * ∫ s in (0:ℝ)..τ, (hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s) ≤ |Δ| ^ 4 * τ ^ 3 / 192)

def statement : Prop := shapeStatement ∧ concavityStatement ∧ halfStatement ∧
  gaussianStatement ∧ gapStatement

end Standalone.JumpShapeTwoPoint

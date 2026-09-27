import Mathlib.Probability.Moments.MGFAnalytic

/-! # Claim 045: the Laplace transform of one conditional law

For one `ω`, `ν` is the law `κ(ω, ·)` of the level jump `X` given `G`. `Mlap ν τ = ∫ e^{−τx} ν(dx)`
is `M(ω, τ)` and `Klap ν = log Mlap ν` is `K(ω, ·)` (45.2). `tiltMean ν τ` and `tiltVar ν τ` are the
mean `Ẽ_τ[X]` and the variance `Ṽ_τ[X]` of the tilted law `e^{−τx} ν(dx) / M(τ)`. `L ∈ (0, ∞]` is an
extended real. `InI L τ` is `τ ∈ [0, L)`, `InIo L τ` is `τ ∈ (0, L)`, and `LapFinite ν L` is
`M(τ) < ∞` on `[0, L)`.

* `derivStatement` is (45.5): `K` is real-analytic on `(0, L)` (so `C^∞`), with `K′ = −Ẽ_τ[X]`
  and `K″ = −(Ẽ_·[X])′ = Ṽ_τ[X] ≥ 0`. `Ṽ_τ[X] = 0` at some `τ ∈ (0, L)` iff `ν` is a Dirac mass.
* `uniqueStatement` is the pointwise step of (b)'s uniqueness: two laws with the same finite
  Laplace transform on `[0, L)` are equal.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeKernel

/-- `M(τ) = ∫ e^{−τx} ν(dx)`. -/
noncomputable def Mlap (ν : Measure ℝ) (τ : ℝ) : ℝ := ∫ x, Real.exp (-τ * x) ∂ν

/-- `K(τ) = log M(τ)`. -/
noncomputable def Klap (ν : Measure ℝ) (τ : ℝ) : ℝ := Real.log (Mlap ν τ)

/-- The tilted mean `Ẽ_τ[X] = ∫ x e^{−τx} ν(dx) / M(τ)`. -/
noncomputable def tiltMean (ν : Measure ℝ) (τ : ℝ) : ℝ :=
  (∫ x, x * Real.exp (-τ * x) ∂ν) / Mlap ν τ

/-- The tilted variance `Ṽ_τ[X] = ∫ (x − Ẽ_τ[X])² e^{−τx} ν(dx) / M(τ)`. -/
noncomputable def tiltVar (ν : Measure ℝ) (τ : ℝ) : ℝ :=
  (∫ x, (x - tiltMean ν τ) ^ 2 * Real.exp (-τ * x) ∂ν) / Mlap ν τ

/-- `τ ∈ [0, L)`. -/
def InI (L : ℝ≥0∞) (τ : ℝ) : Prop := 0 ≤ τ ∧ ENNReal.ofReal τ < L

/-- `τ ∈ (0, L)`. -/
def InIo (L : ℝ≥0∞) (τ : ℝ) : Prop := 0 < τ ∧ ENNReal.ofReal τ < L

/-- `M(τ) < ∞` for every `τ ∈ [0, L)`. -/
def LapFinite (ν : Measure ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ τ, InI L τ → Integrable (fun x => Real.exp (-τ * x)) ν

def derivStatement : Prop := ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ≥0∞),
  LapFinite ν L → AnalyticOnNhd ℝ (Klap ν) {τ | InIo L τ} ∧
  ∀ τ, InIo L τ → HasDerivAt (Klap ν) (-tiltMean ν τ) τ ∧
    HasDerivAt (tiltMean ν) (-tiltVar ν τ) τ ∧ 0 ≤ tiltVar ν τ ∧
    (tiltVar ν τ = 0 ↔ ∃ a : ℝ, ν = Measure.dirac a)

def uniqueStatement : Prop := ∀ (ν ν' : Measure ℝ) [IsProbabilityMeasure ν]
  [IsProbabilityMeasure ν'] (L : ℝ≥0∞), 0 < L → LapFinite ν L → LapFinite ν' L →
  (∀ τ, InI L τ → Mlap ν τ = Mlap ν' τ) → ν = ν'

def statement : Prop := derivStatement ∧ uniqueStatement

end Standalone.JumpShapeKernel

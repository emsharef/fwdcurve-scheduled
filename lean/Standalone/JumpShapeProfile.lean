import Standalone.JumpShapeKernel

/-! # Claim 045 (b): the compensating shape for one conditional law

For one `ω`, `ν = κ(ω, ·)` and `h = h(ω, ·)`. `LocInt h L` says that `h` is integrable on `[0, τ]`
for every `τ ∈ [0, L)`. `ShapeEq ν h L` is (45.4) at `ω`: `H(τ) = ∫_0^τ h = K(τ)` on `[0, L)`.

* `shapeStatement` is (45.6): `h = −Ẽ_τ[X]` for almost every `τ ∈ (0, L)`, and at every
  `τ ∈ (0, L)` where `h` is right-continuous. `τ ↦ −Ẽ_τ[X]` is nondecreasing on `(0, L)`, and
  strictly increasing unless `ν` is a Dirac mass.
* `converseStatement` is (b)'s converse at `ω`: if `M < ∞` on `[0, L)` and `h = −Ẽ_τ[X]` almost
  everywhere on `(0, L)`, then `H = K` on `[0, L)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeProfile
open Standalone.JumpShapeKernel

/-- `h` is integrable on `[0, τ]` for every `τ ∈ [0, L)`. -/
def LocInt (h : ℝ → ℝ) (L : ℝ≥0∞) : Prop := ∀ τ, InI L τ → IntervalIntegrable h volume 0 τ

/-- (45.4) at one `ω`: `∫_0^τ h = K(τ)` for every `τ ∈ [0, L)`. -/
def ShapeEq (ν : Measure ℝ) (h : ℝ → ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ τ, InI L τ → ∫ u in (0:ℝ)..τ, h u = Klap ν τ

def shapeStatement : Prop := ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ≥0∞) (h : ℝ → ℝ),
  LapFinite ν L → LocInt h L → ShapeEq ν h L →
  (∀ᵐ τ ∂volume, InIo L τ → h τ = -tiltMean ν τ) ∧
  (∀ τ, InIo L τ → ContinuousWithinAt h (Ici τ) τ → h τ = -tiltMean ν τ) ∧
  MonotoneOn (fun τ => -tiltMean ν τ) {τ | InIo L τ} ∧
  ((¬ ∃ a : ℝ, ν = Measure.dirac a) → StrictMonoOn (fun τ => -tiltMean ν τ) {τ | InIo L τ})

def converseStatement : Prop := ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ≥0∞)
  (h : ℝ → ℝ), LapFinite ν L → LocInt h L →
  (∀ᵐ τ ∂volume, InIo L τ → h τ = -tiltMean ν τ) → ShapeEq ν h L

def statement : Prop := shapeStatement ∧ converseStatement

end Standalone.JumpShapeProfile

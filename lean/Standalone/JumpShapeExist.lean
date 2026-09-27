import Standalone.JumpShapeCondB

/-! # Claim 045 (b): existence of the shape

Suppose `M(ω, ·) < ∞` on `[0, L)` for `P`-almost every `ω`. Let `LapSet κ L` be the set of `ω` where
this holds, and `hExist κ L τ ω = K′(ω, τ) = −Ẽ_τ[X](ω)` for `ω` in it and `τ ∈ (0, L)`, and `0`
elsewhere.

* `existStatement`: `LapSet κ L` is `G`-measurable with a `P`-null complement; `hExist` is
  `B ⊗ G`-measurable and integrable on `[0, τ]` for every `τ ∈ [0, L)` and every `ω`; and (H)
  holds for `X` with the shape `hExist`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeExist
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond

/-- The `ω` where `M(ω, ·) < ∞` on `[0, L)`. -/
def LapSet {Ω : Type*} {G : MeasurableSpace Ω} (κ : @Kernel Ω ℝ G _) (L : ℝ≥0∞) : Set Ω :=
  {ω | LapFinite (κ ω) L}

open Classical in
/-- `K′(ω, τ)` on `LapSet × (0, L)`, and `0` elsewhere. -/
noncomputable def hExist {Ω : Type*} {G : MeasurableSpace Ω} (κ : @Kernel Ω ℝ G _)
    (L : ℝ≥0∞) (τ : ℝ) (ω : Ω) : ℝ :=
  if ω ∈ LapSet κ L ∧ InIo L τ then -tiltMean (κ ω) τ else 0

def existStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _),
  IsProbabilityMeasure P → G ≤ m₀ → Measurable[m₀] X → @IsMarkovKernel Ω ℝ G _ κ →
  RegCond P G X κ → (∀ᵐ ω ∂P, LapFinite (κ ω) L) →
  MeasurableSet[G] (LapSet κ L) ∧ P (LapSet κ L)ᶜ = 0 ∧
  @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _ (Function.uncurry (hExist κ L)) ∧
  (∀ ω τ, InI L τ → IntervalIntegrable (fun u => hExist κ L u ω) volume 0 τ) ∧
  HypH P G X (hExist κ L) L

def statement : Prop := existStatement

end Standalone.JumpShapeExist

import Standalone.JumpShapeCond
import Standalone.JumpShapeAffine

/-! # Claim 045 (b) and (c1), over `ω`

`Setting P G X h L κ` collects the hypotheses of (a) (`JumpShapeCond.charStatement`):
`P` a probability measure, `G ≤ m₀`, `X` measurable, `h` `B ⊗ G`-measurable and integrable on
`[0, τ]` for `τ ∈ [0, L)`, and `κ` a regular conditional distribution of `X` given `G` (`RegCond`).

* `shapeCondStatement` is (45.5)–(45.6) under (H): off one `G`-measurable null set `N`,
  `K(ω, ·)` has `K′ = −Ẽ_τ[X]`, `K″ = Ṽ_τ[X] ≥ 0` on `(0, L)`; `h(ω, ·) = −Ẽ_τ[X]` almost
  everywhere and at every point of right-continuity; and `−Ẽ_·[X]` is nondecreasing.
* `converseCondStatement` is (b)'s converse: if, for `P`-almost every `ω`, `M(ω, ·) < ∞` on
  `[0, L)` and `h(ω, τ) = −Ẽ_τ[X](ω)` for almost every `τ ∈ (0, L)`, then (H) holds.
* `uniqueCondStatement` is (b)'s uniqueness: two level jumps satisfying (H) with the same `G` and
  the same shape have regular conditional distributions that agree for `P`-almost every `ω`.
* `affineCondStatement` is (c1): for `h(u) = c + y u` with `G`-measurable `c`, `y`, (H) holds iff
  `y ≥ 0` and `κ(ω, ·) = N(−c(ω), y(ω))` for `P`-almost every `ω`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeCondB
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond

/-- The hypotheses of (a). -/
def Setting {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (G : MeasurableSpace Ω)
    (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _) : Prop :=
  IsProbabilityMeasure P ∧ G ≤ m₀ ∧ Measurable[m₀] X ∧
  @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _ (Function.uncurry h) ∧
  (∀ ω τ, InI L τ → IntervalIntegrable (fun u => h u ω) volume 0 τ) ∧
  @IsMarkovKernel Ω ℝ G _ κ ∧ RegCond P G X κ

def shapeCondStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _),
  Setting P G X h L κ → HypH P G X h L →
  ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧ ∀ ω ∉ N,
    LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L ∧
    (∀ τ, InIo L τ → HasDerivAt (Klap (κ ω)) (-tiltMean (κ ω) τ) τ ∧
      HasDerivAt (tiltMean (κ ω)) (-tiltVar (κ ω) τ) τ ∧ 0 ≤ tiltVar (κ ω) τ) ∧
    (∀ᵐ τ ∂volume, InIo L τ → h τ ω = -tiltMean (κ ω) τ) ∧
    (∀ τ, InIo L τ → ContinuousWithinAt (fun u => h u ω) (Ici τ) τ →
      h τ ω = -tiltMean (κ ω) τ) ∧
    MonotoneOn (fun τ => -tiltMean (κ ω) τ) {τ | InIo L τ}

def converseCondStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _),
  Setting P G X h L κ →
  (∀ᵐ ω ∂P, LapFinite (κ ω) L ∧ ∀ᵐ τ ∂volume, InIo L τ → h τ ω = -tiltMean (κ ω) τ) →
  HypH P G X h L

def uniqueCondStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X X' : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞)
  (κ κ' : @Kernel Ω ℝ G _), 0 < L → Setting P G X h L κ → Setting P G X' h L κ' →
  HypH P G X h L → HypH P G X' h L → ∀ᵐ ω ∂P, κ ω = κ' ω

def affineCondStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (c y : Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _),
  0 < L → Setting P G X (fun u ω => c ω + y ω * u) L κ →
  (HypH P G X (fun u ω => c ω + y ω * u) L ↔
    ∀ᵐ ω ∂P, 0 ≤ y ω ∧ κ ω = gaussianReal (-c ω) (y ω).toNNReal)

def statement : Prop := shapeCondStatement ∧ converseCondStatement ∧ uniqueCondStatement ∧
  affineCondStatement

end Standalone.JumpShapeCondB

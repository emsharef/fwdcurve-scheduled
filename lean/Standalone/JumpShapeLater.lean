import Standalone.JumpShapeCondB
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Claim 045 (e): later intervals

`S` is the exponent accumulated before a later date, with `E[e^{−S} | G] = 1` (stated through set
integrals over `G`). `tiltS P S = e^{−S} · P` is `P_S`. On the later interval the jump is
`X + h(u)`. `HypS` is the displayed condition of (e): `E[exp(−S − ∫_0^τ (X + h)) | G] = 1` for every
`τ ∈ [0, L)`.

* `laterStatement`: `P_S` is a probability measure equal to `P` on `G`, and the condition of (e)
  holds iff (H) holds for `X` under `P_S`.
* `laterCharStatement`: with `κ` a regular conditional distribution of `X` given `G` under `P_S`,
  the condition of (e) holds iff (a) holds for `X` under `P_S`: off one `G`-measurable `P`-null set,
  `M < ∞` on `[0, L)` and `H = K`. Then `h(τ) = −Ẽ^{P_S}_τ[X]` for almost every `τ ∈ (0, L)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeLater
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB

/-- `P_S = e^{−S} · P`. -/
noncomputable def tiltS {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (S : Ω → ℝ) :
    Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (Real.exp (-S ω))

/-- The condition of (e). -/
def HypS {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (G : MeasurableSpace Ω)
    (S X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ τ, InI L τ → ∀ D : Set Ω, MeasurableSet[G] D →
    ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-S ω - ∫ u in (0:ℝ)..τ, (X ω + h u ω))) ∂P = P D

def laterStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (G : MeasurableSpace Ω), G ≤ m₀ → ∀ S : Ω → ℝ, Measurable[m₀] S →
  (∀ D : Set Ω, MeasurableSet[G] D →
    ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-S ω)) ∂P = P D) →
  IsProbabilityMeasure (tiltS P S) ∧ (∀ D : Set Ω, MeasurableSet[G] D → tiltS P S D = P D) ∧
  ∀ (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞), HypS P G S X h L ↔ HypH (tiltS P S) G X h L

def laterCharStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (G : MeasurableSpace Ω), G ≤ m₀ → ∀ S : Ω → ℝ, Measurable[m₀] S →
  (∀ D : Set Ω, MeasurableSet[G] D →
    ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-S ω)) ∂P = P D) →
  ∀ (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (L : ℝ≥0∞) (κ : @Kernel Ω ℝ G _),
  Setting (tiltS P S) G X h L κ →
  (HypS P G S X h L ↔ ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
    ∀ ω ∉ N, LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L) ∧
  (HypS P G S X h L → ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
    ∀ ω ∉ N, ∀ᵐ τ ∂volume, InIo L τ → h τ ω = -tiltMean (κ ω) τ)

def statement : Prop := laterStatement ∧ laterCharStatement

end Standalone.JumpShapeLater

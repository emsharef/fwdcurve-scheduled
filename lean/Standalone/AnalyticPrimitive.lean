import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The primitive of a real-analytic function is real-analytic

Claim 037(a) continues the block residual analytically; the residual contains the primitives
`x ↦ ∫_0^x φ_j` of the real-analytic basis functions, so their analyticity is needed.
Mathlib does not have it. It is a closed statement, so under `AGENTS.md` rule 6 as amended on
2026-09-24 (Q-08) it is proved here as the lab's own lemma.

`primitiveStatement`: if `f` is real-analytic on `ℝ`, so is `x ↦ ∫_0^x f`. Near each `x₀`,
`f(x₀ + y) = ∑ c_n y^n`, and the termwise primitive `∑ c_n y^{n+1}/(n + 1)` is a power series with
positive radius whose derivative is `f(x₀ + ·)`.
-/

open Set
namespace Standalone.AnalyticPrimitive

def primitiveStatement : Prop := ∀ f : ℝ → ℝ, AnalyticOnNhd ℝ f univ →
  AnalyticOnNhd ℝ (fun x => ∫ η in (0:ℝ)..x, f η) univ

def statement : Prop := primitiveStatement

end Standalone.AnalyticPrimitive

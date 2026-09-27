import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Claim 037 (b): the Nelson–Siegel block in the uncorrelated splice

The Nelson–Siegel family of [filipovic1999note] with the exponent `β > 0` held fixed is
`F(x, z) = z_1 + (z_2 + z_3 x) e^{−βx}`, with basis `φ = (1, e^{−βx}, x e^{−βx})` (`phiNS`). The
indices here start at `0`: `z 0` is the level `z_1`, `z 1` is `z_2`, `z 2` is `z_3`, and likewise for
`b` and `a`. The block residual (37.1) is
`R(x) = ∑_i b_i φ_i(x) − ∑_{i,j} a_{ij} φ_i(x) ∫_0^x φ_j − ∂_x F(x, z)` (`residualNS`).

* `nsStatement` is (b): for `a` nonnegative definite, `R` is affine on `[0, ∞)` if and only if `a`
  is supported on the single entry `a_{11}` (the level's), `b_2 = z_3 − β z_2` and
  `b_3 = −β z_3`; `a_{11} ≥ 0` and `b_1` are arbitrary.
* `residualStatement`: in that case `R(x) = b_1 − a_{11} x`, which the front end absorbs by (a).
-/

namespace Standalone.SpliceAffineOverlapNS

/-- The Nelson–Siegel basis `1, e^{−βx}, x e^{−βx}`. -/
noncomputable def phiNS (β : ℝ) : Fin 3 → ℝ → ℝ :=
  ![fun _ => 1, fun x => Real.exp (-β * x), fun x => x * Real.exp (-β * x)]

/-- `F(x, z) = ∑_i z_i φ_i(x)`. -/
noncomputable def FNS (β : ℝ) (z : Fin 3 → ℝ) (x : ℝ) : ℝ := ∑ i, z i * phiNS β i x

/-- The block residual (37.1). -/
noncomputable def residualNS (β : ℝ) (z b : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (x : ℝ) : ℝ :=
  ∑ i, b i * phiNS β i x - ∑ i, ∑ j, a i j * phiNS β i x * (∫ η in (0:ℝ)..x, phiNS β j η) -
    deriv (FNS β z) x

def nsStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 3 → ℝ) (a : Matrix (Fin 3) (Fin 3) ℝ),
  a.PosSemidef →
  ((∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residualNS β z b a x = c₀ + c₁ * x) ↔
    ((∀ i j, a i j ≠ 0 → i = 0 ∧ j = 0) ∧ b 1 = z 2 - β * z 1 ∧ b 2 = -β * z 2))

def residualStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ),
  (∀ i j, a i j ≠ 0 → i = 0 ∧ j = 0) → b 1 = z 2 - β * z 1 → b 2 = -β * z 2 →
  ∀ x : ℝ, residualNS β z b a x = b 0 - a 0 0 * x

def statement : Prop := nsStatement ∧ residualStatement

end Standalone.SpliceAffineOverlapNS

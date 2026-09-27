import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousOn

/-! # Claim 038: Svensson with fixed exponents in the uncorrelated splice

The Svensson family with fixed exponents `β₁ ≠ β₂`, both positive, is
`F(x, z) = z_1 + (z_2 + z_3 x) e^{−β₁x} + z_4 x e^{−β₂x}` (38.1), with basis
`φ = (1, e^{−β₁x}, x e^{−β₁x}, x e^{−β₂x})` (`phiSv`). The indices here start at `0`: `z 0` is the
level `z_1`, `z 1` is `z_2`, `z 2` is `z_3`, `z 3` is `z_4`, and likewise for `b` and `a`. The block
residual (37.1) is `R(x) = ∑_i b_i φ_i(x) − ∑_{i,j} a_{ij} φ_i(x) ∫_0^x φ_j − ∂_x F(x, z)`
(`residualSv`). By Claim 037(a) the splice is consistent exactly when `R` is affine, and the block
alone exactly when `R = 0`. Everything is at one parameter point `(z, a, b)`.

* `nonresonantStatement` is (a): if `β₂ ≠ 2β₁` and `z_4 ≠ 0`, no nonnegative definite `a` and no
  `b` make `R` affine on `[0, ∞)`.
* `pathStatement` is (a) for a process, the step of Claim 036(e). Take a path `t ↦ Z_t` whose `z_4`
  coordinate is right-continuous at `t₀` with `Z^4_{t₀} ≠ 0`. Then for no `δ > 0` can `R` be affine,
  with some nonnegative definite `a_t` and some `b_t`, at almost every `t ∈ (t₀, t₀ + δ)`. This
  covers both the splice and the block alone, where `R = 0`.
* `ResonantConditions` lists (b)'s conditions, with `β₁ = β` and `β₂ = 2β`: every entry of `a`
  involving `z_3` or `z_4` is zero, `a_{22} = β z_4`, `b_2 = z_3 + z_4 − β z_2 − a_{12}/β`,
  `b_3 = a_{12} − β z_3` and `b_4 = −2β z_4`.
* `resonantStatement` is (b): for `a` nonnegative definite, `R` is affine on `[0, ∞)` if and only if
  `ResonantConditions` hold. `residualStatement`: then `R(x) = b_1 − a_{12}/β − a_{11} x`.
* `aloneStatement` is (b) alone: `R = 0` on `[0, ∞)` if and only if in addition `a_{11} = 0`,
  `a_{12} = 0` and `b_1 = 0` ([filipovic2000exponential] §9.2, case ii).
* (c): `levelStatement` says that in the splice `z_4 ≥ 0` and the level's correlation with `z_2` obeys
  the Cauchy–Schwarz bound `a_{12}² ≤ a_{11} · β z_4`. `correlatedStatement` says the bound leaves
  room: for `z_4 > 0` there is a consistent splice point whose level factor is correlated with `z_2`,
  `a_{12} ≠ 0`.
-/

namespace Standalone.SvenssonSplice

/-- The Svensson basis `1, e^{−β₁x}, x e^{−β₁x}, x e^{−β₂x}`. -/
noncomputable def phiSv (β₁ β₂ : ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun _ => 1, fun x => Real.exp (-β₁ * x), fun x => x * Real.exp (-β₁ * x),
    fun x => x * Real.exp (-β₂ * x)]

/-- `F(x, z) = ∑_i z_i φ_i(x)`. -/
noncomputable def FSv (β₁ β₂ : ℝ) (z : Fin 4 → ℝ) (x : ℝ) : ℝ := ∑ i, z i * phiSv β₁ β₂ i x

/-- The block residual (37.1). -/
noncomputable def residualSv (β₁ β₂ : ℝ) (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ) (x : ℝ) : ℝ :=
  ∑ i, b i * phiSv β₁ β₂ i x -
    ∑ i, ∑ j, a i j * phiSv β₁ β₂ i x * (∫ η in (0:ℝ)..x, phiSv β₁ β₂ j η) - deriv (FSv β₁ β₂ z) x

def nonresonantStatement : Prop := ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ → β₁ ≠ β₂ → β₂ ≠ 2 * β₁ →
  ∀ (z b : Fin 4 → ℝ) (a : Matrix (Fin 4) (Fin 4) ℝ), z 3 ≠ 0 → a.PosSemidef →
  ¬ ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residualSv β₁ β₂ z b a x = c₀ + c₁ * x

def pathStatement : Prop := ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ → β₁ ≠ β₂ → β₂ ≠ 2 * β₁ →
  ∀ (Z : ℝ → Fin 4 → ℝ) (a : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (b : ℝ → Fin 4 → ℝ) (t₀ δ : ℝ), 0 < δ →
  ContinuousWithinAt (fun t => Z t 3) (Set.Ici t₀) t₀ → Z t₀ 3 ≠ 0 →
  ¬ ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo t₀ (t₀ + δ))), (a t).PosSemidef ∧
      ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residualSv β₁ β₂ (Z t) (b t) (a t) x = c₀ + c₁ * x

/-- (b)'s conditions for `β₁ = β`, `β₂ = 2β`. -/
def ResonantConditions (β : ℝ) (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i j : Fin 4, (2 ≤ i ∨ 2 ≤ j) → a i j = 0) ∧ a 1 1 = β * z 3 ∧
  b 1 = z 2 + z 3 - β * z 1 - a 0 1 / β ∧ b 2 = a 0 1 - β * z 2 ∧ b 3 = -2 * β * z 3

def resonantStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 4 → ℝ)
  (a : Matrix (Fin 4) (Fin 4) ℝ), a.PosSemidef →
  ((∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residualSv β (2 * β) z b a x = c₀ + c₁ * x) ↔
    ResonantConditions β z b a)

def residualStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ),
  a 1 0 = a 0 1 → ResonantConditions β z b a →
  ∀ x : ℝ, residualSv β (2 * β) z b a x = b 0 - a 0 1 / β - a 0 0 * x

def aloneStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 4 → ℝ)
  (a : Matrix (Fin 4) (Fin 4) ℝ), a.PosSemidef →
  ((∀ x : ℝ, 0 ≤ x → residualSv β (2 * β) z b a x = 0) ↔
    (ResonantConditions β z b a ∧ a 0 0 = 0 ∧ a 0 1 = 0 ∧ b 0 = 0))

def levelStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (z b : Fin 4 → ℝ)
  (a : Matrix (Fin 4) (Fin 4) ℝ), a.PosSemidef → ResonantConditions β z b a →
  0 ≤ z 3 ∧ a 0 1 ^ 2 ≤ a 0 0 * (β * z 3)

def correlatedStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ z : Fin 4 → ℝ, 0 < z 3 →
  ∃ (a : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℝ), a.PosSemidef ∧ a 0 1 ≠ 0 ∧
    ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residualSv β (2 * β) z b a x = c₀ + c₁ * x

def statement : Prop :=
  nonresonantStatement ∧ pathStatement ∧ resonantStatement ∧ residualStatement ∧ aloneStatement ∧
  levelStatement ∧ correlatedStatement

end Standalone.SvenssonSplice

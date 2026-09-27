import Standalone.SharefFilipovicIndependence
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 034 (a): the block's residual vanishes for all `x ≥ 0`

The biexponential-polynomial family (34.1) is `F(x, z) = ∑_i z_i φ_i(x)`, linear in the parameter
`z`, with the basis `φ_{1,μ}(x) = x^μ e^{−βx}` (`μ ≤ n₁`) and `φ_{2,μ}(x) = x^μ e^{−2βx}` (`μ ≤ n₂`)
(`phi034`). So `∂_{z_i} F = φ_i`, and `∂²_{z_i z_j} F = 0`, and the residual of the consistency
equation (34.3) at a parameter value `z` with drift `b` and diffusion matrix `a` is
`R(x) = −∂_x F(x, z) + ∑_i b_i φ_i(x) − ∑_{i,j} a_{ij} φ_i(x) ∫_0^x φ_j(η) dη` (`residual034`).

`residualStatement` is the step of (a) after (34.5). Let `β > 0`. If `R` agrees with a polynomial
on an open interval of positive length (for a maturity interval of the front end, the right side
of (34.5) is a polynomial there), then `R(x) = 0` for every real `x`, not only for `x ≤ H − t`. The
proof shows that `R` is `∑_{k=1}^{4} Q_k(x) e^{−kβx}` with polynomials `Q_k` and no exponent-zero
term, and applies the independence step (`SharefFilipovicIndependence`).
-/

open Set Polynomial
namespace Standalone.SharefFilipovicResidual

/-- The basis `x^μ e^{−βx}`, `x^μ e^{−2βx}` of (34.1). -/
noncomputable def phi034 (β : ℝ) (n₁ n₂ : ℕ) : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ → ℝ :=
  Sum.elim (fun μ x => x ^ (μ : ℕ) * Real.exp (-β * x)) (fun μ x => x ^ (μ : ℕ) * Real.exp (-(2 * β) * x))

/-- The family (34.1), `F(x, z) = ∑_i z_i φ_i(x)`. -/
noncomputable def F034 (β : ℝ) (n₁ n₂ : ℕ) (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, z i * phi034 β n₁ n₂ i x

/-- The residual of (34.3); the term with `∂²_z F` vanishes since `F` is linear in `z`. -/
noncomputable def residual034 (β : ℝ) (n₁ n₂ : ℕ) (z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (x : ℝ) : ℝ :=
  -deriv (F034 β n₁ n₂ z) x + ∑ i, b i * phi034 β n₁ n₂ i x -
    ∑ i, ∑ j, a i j * phi034 β n₁ n₂ i x * ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η

def residualStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ : ℕ)
  (z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
  (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (P : ℝ[X]) (c d : ℝ),
  c < d → (∀ x ∈ Ioo c d, residual034 β n₁ n₂ z b a x = P.eval x) →
  ∀ x : ℝ, residual034 β n₁ n₂ z b a x = 0

def statement : Prop := residualStatement

end Standalone.SharefFilipovicResidual

import Standalone.UnifiedSpliceAlgebra
import Mathlib.Basic.Complex.Basic

/-! # Claim 049 (b2): a diagonalizable exponential part

`A` is invertible and diagonalizable over `ℂ`: `A P = P diag(λ)` with `P` invertible. `(A, c)` is
observable. The residual is `R` (`resid`, `UnifiedSpliceAlgebra`), with any level rows `Hp`.

`diagStatement`: if `x ↦ R(x)` is affine on `ℝ`, then `H^ζ H^{0,μ⊤} = 0` for every `μ = 0, …, d`.
The proof is the claim's, in the eigenbasis:
* observability makes the `λ_i` distinct and every `(cP)_i ≠ 0`; invertibility makes `λ_i ≠ 0`;
* every term of `R` other than the polynomial–exponential covariances is a polynomial, or a
  constant times `e^{λ_i x}` or `e^{(λ_i + λ_j) x}`, with no power of `x`;
* so, by the independence of exponential polynomials (`UnifiedSpliceExpPoly`), the coefficient of
  `x^k e^{λ_i x}` for `k ≥ 1` vanishes. It is
  `−(cP)_i[(P⁻¹ H^ζ H^{0,k⊤})_i / λ_i + (P⁻¹ H^ζ H^{0,k−1⊤})_i / k]`, with the first term absent for
  `k = d + 1`. Descending from `k = d + 1` gives the claim.

`effectiveStatement` is (49.6): applied to `R♯`, the residual with the effective level
`H^{0,0} + V`, it gives `H^ζ H^{0,μ⊤} = 0` for `μ = 1, …, d` and `H^ζ (H^{0,0} + V)^⊤ = 0`.
-/

open Matrix NormedSpace

namespace Standalone.UnifiedSpliceDiag
open Standalone.UnifiedSpliceAlgebra

def diagStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  (∃ (P : Matrix (Fin r) (Fin r) ℂ) (lam : Fin r → ℂ), IsUnit P.det ∧
    A.map Complex.ofReal * P = P * diagonal lam) →
  ∀ (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ),
    (∃ α β : ℝ, ∀ x, resid Hp Hz c A d bP zP bZ z x = α + β * x) →
    ∀ μ ≤ d, Hz *ᵥ Hp μ = 0

def effectiveStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  (∃ (P : Matrix (Fin r) (Fin r) ℂ) (lam : Fin r → ℂ), IsUnit P.det ∧
    A.map Complex.ofReal * P = P * diagonal lam) →
  ∀ (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (V : Fin k → ℝ),
    (∃ α β : ℝ, ∀ x, resid (sharp Hp V) Hz c A d bP zP bZ z x = α + β * x) →
    (∀ μ, 1 ≤ μ → μ ≤ d → Hz *ᵥ Hp μ = 0) ∧ Hz *ᵥ (Hp 0 + V) = 0

def statement : Prop := diagStatement ∧ effectiveStatement

end Standalone.UnifiedSpliceDiag

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Claim 044: quasi-exponentials with nonzero exponents are independent of the polynomials

`quasiPolyStatement` is the linear-independence step of (a). Let `A` be invertible, so every
exponent is nonzero. If `g(T) = c e^{AT}(y + T z)` equals a polynomial `P` on an open interval, then
`P = 0` and `g ≡ 0`. With `χ` the characteristic polynomial of `A`, the operator `χ(D)²` kills `g`,
by Cayley–Hamilton. It sends `P` to `det(A)² P` plus terms of lower degree, so `P = 0`.
-/

open Matrix NormedSpace Polynomial Set
namespace Standalone.SpliceExponentZeroQuasiPoly

def quasiPolyStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c y z : Fin r → ℝ) (P : ℝ[X]) (d₁ d₂ : ℝ), d₁ < d₂ →
  (∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) = P.eval T) →
  P = 0 ∧ ∀ T : ℝ, c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) = 0

def statement : Prop := quasiPolyStatement

end Standalone.SpliceExponentZeroQuasiPoly

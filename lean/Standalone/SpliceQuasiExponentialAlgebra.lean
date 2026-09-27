import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Claim 035 (b): the deterministic core

`affineStatement` is the step of (b) that uses the nonzero exponents. Let `A` be invertible and
`g(T) = c e^{AT} (y + T z)`, a quasi-exponential with only nonzero exponents and at most a linear
factor. If `g` is affine on an open interval of positive length, then `g` vanishes on that
interval. In (b) this applies to the jump (35.2) minus its constant part, with
`y = (A^{−1} − T_m) v` and `z = v`, and gives `c e^{AT} (T I + B) v = 0` on the interval, which is
all (b) uses: at any point `T₀` of it, `c e^{AT₀}` takes the place of `c` below.

`vanishingStatement` is the last step of (b). If `c B = 0` and `c (A B + I) = 0` for
`B = A^{−1} − T_m I`, with `A` invertible, then `c = 0`. These two conditions are what
`c e^{AT} (T I + B) = 0` near a point gives there, and after one differentiation, with `c` replaced by
`c e^{AT₀}` and `T_m` by `T_m − T₀`.
-/

open Matrix NormedSpace Set
namespace Standalone.SpliceQuasiExponentialAlgebra

def affineStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c y z : Fin r → ℝ) (d₁ d₂ k₀ k₁ : ℝ), d₁ < d₂ →
  (∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) = k₀ + k₁ * T) →
  ∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) = 0

def vanishingStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (Tm : ℝ),
  c ᵥ* (A⁻¹ - Tm • (1 : Matrix (Fin r) (Fin r) ℝ)) = 0 →
  c ᵥ* (A * (A⁻¹ - Tm • (1 : Matrix (Fin r) (Fin r) ℝ)) + 1) = 0 → c = 0

def statement : Prop := affineStatement ∧ vanishingStatement

end Standalone.SpliceQuasiExponentialAlgebra

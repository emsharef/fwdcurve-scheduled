import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Claim 040, Lemma 040-A: observability

The block is `F(x, z) = c e^{Ax} z` (40.1) with `A` invertible and `(A, c)` observable:
`c e^{Ax} y = 0` for every `x` only for `y = 0`.

`observabilityStatement` is Lemma 040-A: for `v ∈ ℝ^r` and any real `T_m`, if
`g(T) = c e^{AT} (T I + A^{−1} − T_m I) v` vanishes on an open interval, then `v = 0`. The claim
states it for `g` vanishing identically; an open interval suffices, since `g` is real-analytic,
and it is what (a) uses. The proof is the claim's: with `k(T) = c e^{AT} A^{−1} v`,
`g = d/dT [(T − T_m) k(T)]`, so `(T − T_m) k` is constant, hence `0`, so `k ≡ 0`, and
observability gives `A^{−1} v = 0`.
-/

open Matrix NormedSpace Set
namespace Standalone.SpliceStateBlockObservability

def observabilityStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (Tm d₁ d₂ : ℝ) (v : Fin r → ℝ), d₁ < d₂ →
  (∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ
    ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ v)) = 0) → v = 0

def statement : Prop := observabilityStatement

end Standalone.SpliceStateBlockObservability

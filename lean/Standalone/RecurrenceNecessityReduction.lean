import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Claim 032: the reduction to a controllable pair and (32.3)

A quasi-exponential shape is `λ(x) = c e^{xA} b` with `A` an `r × r` matrix.
`reductionStatement` is the claim's reduction, written without passing to a subspace: there are
an `r × r` matrix `C` and vectors `b'`, `c'` with `λ(x) = c' e^{xC} b'` for every `x`, such that
every matrix `Γ_δ = ∫_0^δ e^{uC} b' b'ᵀ e^{uCᵀ} du` of (32.3) (`gamma032`) with `δ > 0` is positive
definite, and `c' ≠ 0` unless `λ` vanishes identically. (The construction takes the Krylov
matrix `Q = [b, Ab, ..., A^{r−1}b]` and the companion matrix `C` of the characteristic
polynomial of `A`, so that `A Q = Q C` by Cayley–Hamilton; then `e^{xA} Q = Q e^{xC}`, `b' = e₁`
and `c' = c Q`, and `(C, e₁)` is controllable.) `e^{C}` is invertible, as the matrix exponential is.
-/

open Matrix NormedSpace
namespace Standalone.RecurrenceNecessityReduction

/-- `Γ_δ = ∫_0^δ e^{uC} b bᵀ e^{uCᵀ} du`. -/
noncomputable def gamma032 {r : ℕ} (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (δ : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => ∫ u in (0:ℝ)..δ, (exp (u • C) *ᵥ b) i * (exp (u • C) *ᵥ b) j

def reductionStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  ∃ (C : Matrix (Fin r) (Fin r) ℝ) (b' c' : Fin r → ℝ),
    (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ b) = c' ⬝ᵥ (exp (x • C) *ᵥ b')) ∧
    (∀ δ : ℝ, 0 < δ → (gamma032 C b' δ).PosDef) ∧
    ((∃ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ b) ≠ 0) → c' ≠ 0)

def statement : Prop := reductionStatement

end Standalone.RecurrenceNecessityReduction

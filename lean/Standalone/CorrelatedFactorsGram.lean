import Standalone.CorrelatedFactorsReduction

/-! # Claim 036 (b): the image of the positive definite cone

The notation is `CorrelatedFactorsReduction`'s: `P_ν` (`Pnu`) and, for a symmetric
`(n + 1) × (n + 1)` matrix `A`, `S_A = ∑_{μ,ν ≤ n} A_{μν} P_μ P_ν` (`SAn`).

`gramStatement` is the step of (b) that the positive definite `A` give exactly the interior `U` of
the cone of nonnegative polynomials of degree at most `2n`:
`{S_A : A positive definite} = {S : deg S ≤ 2n, S > 0 on ℝ, s_{2n} > 0}`.
The inclusion `⊆` holds because `S_A(x) = v(x)ᵀ A v(x)` with `v(x) = (P_ν(x))_ν ≠ 0`, and the
top coefficient is `A_{nn}/β²`. For `⊇`, `S − ε ∑_ν P_ν²` is nonnegative for small `ε > 0`, so it
is a sum of squares (`NonnegPolySOS`) of polynomials of degree at most `n`. Those are
combinations of `P_0, …, P_n`, which gives `S = S_{B + ε I}` with `B` positive semidefinite.
-/

open Polynomial
namespace Standalone.CorrelatedFactorsGram
open Standalone.CorrelatedFactorsReduction

/-- `S_A = ∑_{μ,ν ≤ n} A_{μν} P_μ P_ν`. -/
noncomputable def SAn (β : ℝ) (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ[X] :=
  ∑ μ : Fin (n + 1), ∑ ν : Fin (n + 1), C (A μ ν) * Pnu β μ * Pnu β ν

def gramStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n : ℕ) (S : ℝ[X]),
  (∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, A.PosDef ∧ S = SAn β n A) ↔
    (S.natDegree ≤ 2 * n ∧ (∀ x : ℝ, 0 < S.eval x) ∧ 0 < S.coeff (2 * n))

def statement : Prop := gramStatement

end Standalone.CorrelatedFactorsGram

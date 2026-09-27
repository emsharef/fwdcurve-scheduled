import Standalone.CorrelatedFactorsReduction

/-! # Claim 036 (b): the exact condition, second (Hankel) form

The notation is `CorrelatedFactorsReduction`'s: `t_k(S) = β s_k − (k + 1) s_{k+1}/2` (`tk`). For a
finite set `K_0 ⊆ {0, …, 2n}` of integers, no two consecutive, and `λ` on `K_0`, the functional
`ℓ = ∑_{k ∈ K_0} λ_k t_k` on coefficient sequences has coefficients
`ℓ_j = β λ_j [j ∈ K_0] − (j/2) λ_{j−1} [j − 1 ∈ K_0]` (`ellOf`), and its Hankel matrix is
`(ℓ_{i+j})_{0 ≤ i,j ≤ n}`.

`hankelStatement` is the equivalence of (b)'s two forms. There is a polynomial `S` with
`deg S ≤ 2n`, `S > 0` on `ℝ`, `s_{2n} > 0` and `t_k(S) = r_k` for every `k ∈ K_0` if and only if
there is no `λ ≠ 0` on `K_0` whose `ℓ` has a positive semidefinite Hankel matrix and
`∑_k λ_k r_k ≤ 0`. The proof is the separation argument of the Statement's proof of (b), in the
space of coefficient vectors.
-/

open Polynomial
namespace Standalone.CorrelatedFactorsHankel
open Standalone.CorrelatedFactorsReduction

/-- `ℓ_j` for `ℓ = ∑_{k ∈ K_0} λ_k t_k`. -/
noncomputable def ellOf (β : ℝ) (K0 : Finset ℕ) (lam : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if j ∈ K0 then β * lam j else 0) -
    (if 0 < j ∧ j - 1 ∈ K0 then (j : ℝ) / 2 * lam (j - 1) else 0)

def hankelStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n : ℕ) (K0 : Finset ℕ) (r : ℕ → ℝ),
  (∀ k ∈ K0, k ≤ 2 * n) → (∀ k ∈ K0, k + 1 ∉ K0) →
  ((∃ S : ℝ[X], S.natDegree ≤ 2 * n ∧ (∀ x : ℝ, 0 < S.eval x) ∧ 0 < S.coeff (2 * n) ∧
      ∀ k ∈ K0, tk β S k = r k) ↔
    ¬ ∃ lam : ℕ → ℝ, (∃ k ∈ K0, lam k ≠ 0) ∧
      (Matrix.of fun i j : Fin (n + 1) => ellOf β K0 lam (i + j)).PosSemidef ∧
      ∑ k ∈ K0, lam k * r k ≤ 0)

def statement : Prop := hankelStatement

end Standalone.CorrelatedFactorsHankel

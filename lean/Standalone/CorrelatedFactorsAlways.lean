import Standalone.CorrelatedFactorsExists
import Standalone.CorrelatedFactorsHankel

/-! # Claim 036 (c): always solvable when `2n ∉ K_0`

The notation is `CorrelatedFactorsHankel`'s and `CorrelatedFactorsExists`'s.

* `noLambdaStatement` is the Hankel step of (c). If `K_0 ⊆ {0, …, 2n}` has no two consecutive
  elements and `2n ∉ K_0`, then no `λ ≠ 0` on `K_0` gives `ℓ = ∑ λ_k t_k` a positive semidefinite
  Hankel matrix. By (b)'s second form (`CorrelatedFactorsHankel`), the system `t_k(S) = r_k`,
  `k ∈ K_0`, then has a solution in `U` for every `r`.
* `alwaysStatement` is (c). Let `n = ⌊n₂/2⌋ ≤ n₁` (C1), let (C3) hold (`z_{2,i} ≠ 0` or
  `z_{2,i+1} ≠ 0` for `i ≤ 2n`), and let `z_{2,2n} ≠ 0`; this covers `n₂ = 2n` too, since then
  `z_{2,2n} = z_{2,n₂} ≠ 0`. Then there are a nonnegative definite `a` whose block `A` is positive
  definite and a drift `b` (zero on `K_0`) with `(z, a, b)` satisfying (34.3) for all `x ≥ 0`:
  a solution with `n + 1` nondegenerate, generally correlated, factors.
-/

open Polynomial
namespace Standalone.CorrelatedFactorsAlways
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsHankel Standalone.CorrelatedFactorsExists

def noLambdaStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n : ℕ) (K0 : Finset ℕ),
  (∀ k ∈ K0, k ≤ 2 * n) → (∀ k ∈ K0, k + 1 ∉ K0) → 2 * n ∉ K0 →
  ∀ lam : ℕ → ℝ, (Matrix.of fun i j : Fin (n + 1) => ellOf β K0 lam (i + j)).PosSemidef →
    ∀ k ∈ K0, lam k = 0

def alwaysStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ : ℕ) (hn : n₂ / 2 ≤ n₁)
  (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ),
  (∀ i, i ≤ 2 * (n₂ / 2) → c2 z i ≠ 0 ∨ c2 z (i + 1) ≠ 0) → c2 z (2 * (n₂ / 2)) ≠ 0 →
  ∃ (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ)
    (b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ), a.PosSemidef ∧ (blockA (n₂ / 2) hn a).PosDef ∧
    (∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 → b (Sum.inr k) = 0) ∧
    ∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ z b a x = 0

def statement : Prop := noLambdaStatement ∧ alwaysStatement

end Standalone.CorrelatedFactorsAlways

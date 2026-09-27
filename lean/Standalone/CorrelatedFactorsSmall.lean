import Standalone.CorrelatedFactorsExists

/-! # Claim 036 (d): the exact condition for `n = 0` and `n = 1`

The setting is `CorrelatedFactorsExists`'s. Here `n₂ = 2n + 1` and `z_{2,2n} = 0`, so `2n ∈ K_0`.
"A solution" means a nonnegative definite `a` whose block `A` is positive definite and a drift `b`
(with `b_{2,k} = 0` on `K_0`) such that `(z, a, b)` satisfies (34.3) for all `x ≥ 0`.

* `zeroStatement` (`n = 0`, `n₂ = 1`): there is a solution if and only if `z_{2,1} > 0`.
* `oneStatement` (`n = 1`, `n₂ = 3`, `n₁ ≥ 1`): with `z_{2,1} ≠ 0`, which (C3) gives since
  `z_{2,2} = 0`, there is a solution if and only if `z_{2,3} > 0` and, when also `z_{2,0} = 0`,
  `3 z_{2,3} + 4β² z_{2,1} > 0`.
-/

namespace Standalone.CorrelatedFactorsSmall
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsExists

/-- A solution with `n + 1` nondegenerate factors, as in `existsStatement`. -/
def Solvable (β : ℝ) (n₁ n₂ : ℕ) (hn : n₂ / 2 ≤ n₁) (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) : Prop :=
  ∃ (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ)
    (b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ), a.PosSemidef ∧ (blockA (n₂ / 2) hn a).PosDef ∧
    (∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 → b (Sum.inr k) = 0) ∧
    ∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ z b a x = 0

def zeroStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ : ℕ) (z : Fin (n₁ + 1) ⊕ Fin (1 + 1) → ℝ),
  z (Sum.inr 0) = 0 → (Solvable β n₁ 1 (by omega) z ↔ 0 < z (Sum.inr 1))

def oneStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ : ℕ) (hn : 1 ≤ n₁)
  (z : Fin (n₁ + 1) ⊕ Fin (3 + 1) → ℝ), z (Sum.inr 2) = 0 → z (Sum.inr 1) ≠ 0 →
  (Solvable β n₁ 3 (by omega) z ↔
    (0 < z (Sum.inr 3) ∧ (z (Sum.inr 0) = 0 → 0 < 3 * z (Sum.inr 3) + 4 * β ^ 2 * z (Sum.inr 1))))

def statement : Prop := zeroStatement ∧ oneStatement

end Standalone.CorrelatedFactorsSmall

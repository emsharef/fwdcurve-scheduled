import Standalone.CorrelatedFactorsGram

/-! # Claim 036 (b): the exact condition, first form

The setting is `CorrelatedFactorsReduction`'s, with `n = ⌊n₂/2⌋ ≤ n₁` (condition (C1)). For `a` on
the whole index set, `blockA a` is the `(n + 1) × (n + 1)` block
`A = (a_{(1,μ),(1,ν)})_{μ,ν ≤ n}`. "`n + 1` nondegenerate factors" means `A` positive definite.

`existsStatement` is the first form of (b). There are a nonnegative definite `a` with `A` positive
definite and a drift `b` (with `b_{2,k} = 0` on `K_0`) such that `(z, a, b)` satisfies (34.3) for
all `x ≥ 0` if and only if there is a polynomial `S` of degree at most `2n` with `S > 0` on `ℝ`,
`s_{2n} > 0`, and `t_k(S) = r_k = (k + 1) z_{2,k+1}` for every `k ∈ K_0`. The proof combines (a)
(`CorrelatedFactorsReduction`) with the image of the positive definite cone
(`CorrelatedFactorsGram`); the drifts are those of (36.3).
-/

open Polynomial
namespace Standalone.CorrelatedFactorsExists
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsGram

/-- The block `A = (a_{(1,μ),(1,ν)})_{μ,ν ≤ n}`. -/
def blockA {n₁ n₂ : ℕ} (n : ℕ) (hn : n ≤ n₁)
    (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun μ ν => a (Sum.inl (Fin.castLE (by omega) μ)) (Sum.inl (Fin.castLE (by omega) ν))

def existsStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ : ℕ) (hn : n₂ / 2 ≤ n₁)
  (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ),
  (∃ (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ)
      (b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ), a.PosSemidef ∧ (blockA (n₂ / 2) hn a).PosDef ∧
      (∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 → b (Sum.inr k) = 0) ∧
      ∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ z b a x = 0) ↔
    (∃ S : ℝ[X], S.natDegree ≤ 2 * (n₂ / 2) ∧ (∀ x : ℝ, 0 < S.eval x) ∧
      0 < S.coeff (2 * (n₂ / 2)) ∧
      ∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 →
        tk β S k = ((k : ℝ) + 1) * c2 z (k + 1))

def statement : Prop := existsStatement

end Standalone.CorrelatedFactorsExists

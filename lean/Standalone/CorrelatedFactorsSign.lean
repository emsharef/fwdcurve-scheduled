import Standalone.CorrelatedFactorsReduction

/-! # Claim 036 (d), necessity, and (e)

The setting and notation are `CorrelatedFactorsReduction`'s (Claim 036(a)).

* `signStatement` is (d)'s necessary condition. Let `n₂ = 2n + 1` and `z_{2,2n} = 0`, so
  `2n ∈ K_0`. If `(z, a, b)` satisfies (34.3) for all `x ≥ 0` with `a` nonnegative definite and
  its last factor nontrivial, `a_{(1,n),(1,n)} > 0` (for example, `A` positive definite), then
  `z_{2,2n+1} > 0`. The top coefficient of `S_A` is `a_{nn}/β²`, and (36.1) at `k = 2n` reads
  `β s_{2n} = (2n + 1) z_{2,2n+1}`.
* `counterexampleStatement` is (e): at `β = 1`, `n₁ = 0`, `n₂ = 1`, `z_1 = (1)`, `z_2 = (0, −1)`,
  conditions (C1)–(C3) and `z_{2,n₂} ≠ 0` hold, but no nonnegative definite `a` and no `b` (with
  the structurally absent `b_{2,0} = 0`) satisfy (34.3) for all `x ≥ 0`: (36.1) would read
  `a_{00} = −1`. So the central proposition of [sharef2004conditions] §4.2 is false as stated.
  The further step of the proof, that no consistent Itô process passes through this point, is
  not part of this statement.
-/

namespace Standalone.CorrelatedFactorsSign
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction

def signStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n : ℕ) (_hn : n ≤ n₁),
  ∀ (z b : Fin (n₁ + 1) ⊕ Fin (2 * n + 1 + 1) → ℝ)
  (a : Matrix (Fin (n₁ + 1) ⊕ Fin (2 * n + 1 + 1)) (Fin (n₁ + 1) ⊕ Fin (2 * n + 1 + 1)) ℝ),
  a.PosSemidef →
  (∀ k : Fin (2 * n + 1 + 1), (k : ℕ) ≤ 2 * ((2 * n + 1) / 2) → z (Sum.inr k) = 0 →
    b (Sum.inr k) = 0) →
  z (Sum.inr ⟨2 * n, by omega⟩) = 0 →
  (∀ x : ℝ, 0 ≤ x → residual034 β n₁ (2 * n + 1) z b a x = 0) →
  0 < a (Sum.inl ⟨n, by omega⟩) (Sum.inl ⟨n, by omega⟩) →
  0 < z (Sum.inr ⟨2 * n + 1, by omega⟩)

/-- The source's point: `z_1 = (1)`, `z_2 = (0, −1)`. -/
noncomputable def zEx : Fin (0 + 1) ⊕ Fin (1 + 1) → ℝ := Sum.elim ![1] ![0, -1]

def counterexampleStatement : Prop :=
  (0 ≤ 0 ∧ (∀ i : Fin (0 + 1), zEx (Sum.inl i) ≠ 0) ∧
    (zEx (Sum.inr 0) ≠ 0 ∨ zEx (Sum.inr 1) ≠ 0) ∧ zEx (Sum.inr 1) ≠ 0) ∧
  ∀ (b : Fin (0 + 1) ⊕ Fin (1 + 1) → ℝ)
    (a : Matrix (Fin (0 + 1) ⊕ Fin (1 + 1)) (Fin (0 + 1) ⊕ Fin (1 + 1)) ℝ),
    a.PosSemidef → b (Sum.inr 0) = 0 → ¬ ∀ x : ℝ, 0 ≤ x → residual034 1 0 1 zEx b a x = 0

def statement : Prop := signStatement ∧ counterexampleStatement

end Standalone.CorrelatedFactorsSign

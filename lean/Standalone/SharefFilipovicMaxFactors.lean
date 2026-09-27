import Standalone.SharefFilipovicResidual
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # AX-14, proved: at most `min(n₁, ⌊n₂/2⌋) + 1` nontrivial factors

This is the first proposition of [sharef2004conditions] §4.2 (`pacmmaxfactors`), proved here as
the lab's own lemma under `AGENTS.md` rule 6 as amended on 2026-09-24 (Q-08); the source is prior
art, and `ledger/AXIOMS.md` AX-14 is its citation and audit record. The source's reduced system for
its later central proposition carries the wrong sign on the `e^{−2βx}` terms in `a`
(`pacmremcons`, `pacmq2k`), as AX-14 records; that proposition is not used.

For the family (34.1), `F(x, z) = ∑_μ z_{1,μ} x^μ e^{−βx} + ∑_μ z_{2,μ} x^μ e^{−2βx}`, the consistency
equation of [sharef2004conditions] §2.1 at a parameter point `(z, a, b)` says that the residual
`residual034` vanishes (the term with `∂²_z F` is zero, `F` being linear in `z`).
`maxFactorsStatement`: let `β > 0` and `a` be symmetric nonnegative definite. If the residual
vanishes for every `x ≥ 0`, then every nonzero entry `a_{(i,μ),(j,ν)}` has `i = j = 1` and
`μ, ν ≤ ⌊n₂/2⌋` (and `μ, ν ≤ n₁` by the index range). So at most `min(n₁, ⌊n₂/2⌋) + 1` components
`Z^{1,k}` have nonzero diffusion, and none of the `Z^{2,k}`.
-/

open Matrix
namespace Standalone.SharefFilipovicMaxFactors
open Standalone.SharefFilipovicResidual

def maxFactorsStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ : ℕ)
  (z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
  (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ), a.PosSemidef →
  (∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ z b a x = 0) →
  ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
    (μ : ℕ) ≤ n₂ / 2 ∧ (ν : ℕ) ≤ n₂ / 2

def statement : Prop := maxFactorsStatement

end Standalone.SharefFilipovicMaxFactors

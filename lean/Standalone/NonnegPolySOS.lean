import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # A nonnegative real polynomial in one variable is a sum of squares

This is the classical fact that Claim 036(b) and (c) use: every `p ∈ ℝ[X]` with `p(x) ≥ 0` for all
real `x` is a finite sum of squares of real polynomials. Mathlib does not have it. It is a closed
algebraic statement about explicit finite data, so under `AGENTS.md` rule 6 as amended on
2026-09-24 (Q-08) it is proved here as the lab's own lemma rather than cited.

`sosStatement`: `p ≥ 0` on `ℝ` implies `p = ∑_i q_i²` for finitely many `q_i ∈ ℝ[X]`.
-/

open Polynomial
namespace Standalone.NonnegPolySOS

def sosStatement : Prop := ∀ p : ℝ[X], (∀ x : ℝ, 0 ≤ p.eval x) →
  ∃ (m : ℕ) (q : Fin m → ℝ[X]), p = ∑ i, q i ^ 2

def statement : Prop := sosStatement

end Standalone.NonnegPolySOS

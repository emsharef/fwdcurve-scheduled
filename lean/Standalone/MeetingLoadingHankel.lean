import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic

/-! # Claim 029 (b), (c): Hankel rank, linear recurrences, harmonic loadings

`hankel029 a R n` is the Hankel section `H_{R,n}` with entries `a (i + l)`.
`recurrenceStatement` is the linear-algebra step of (b): if every section has
rank at most `q`, the loadings satisfy a linear recurrence (29.4) of order
`L ≤ q`. Order `L = 0` is allowed and means `a ≡ 0`; this covers the claim's
separate case `a ≡ 0` without raising the order above `q`.
`harmonicStatement` is (c): the harmonic ordinal loadings
`a_i = ∑_{h=1}^i 1/h` satisfy no recurrence of any order, and
`unboundedStatement` combines the two: their Hankel sections have unbounded
rank. The probabilistic part (a), which bounds the rank by a realization's
state dimension, is not in this target.
-/

open scoped BigOperators
namespace Standalone.MeetingLoadingHankel

/-- The Hankel section `H_{R,n}`. -/
def hankel029 (a : ℕ → ℝ) (R n : ℕ) : Matrix (Fin (R+1)) (Fin (n+1)) ℝ :=
  fun i l => a (i + l)

/-- A linear recurrence (29.4) of order `L`. -/
def Recurrence029 (a : ℕ → ℝ) (L : ℕ) (c : Fin L → ℝ) : Prop :=
  ∀ i : ℕ, a (i + L) = ∑ l : Fin L, c l * a (i + l)

/-- The harmonic ordinal loadings, `a_i = ∑_{h=1}^i 1/h`. -/
noncomputable def harmonic029 (i : ℕ) : ℝ := ∑ h ∈ Finset.range i, 1 / ((h : ℝ) + 1)

def recurrenceStatement : Prop := ∀ (a : ℕ → ℝ) (q : ℕ),
  (∀ R n, (hankel029 a R n).rank ≤ q) → ∃ L ≤ q, ∃ c : Fin L → ℝ, Recurrence029 a L c

def harmonicStatement : Prop := ∀ (L : ℕ) (c : Fin L → ℝ), ¬ Recurrence029 harmonic029 L c

def unboundedStatement : Prop := ∀ q : ℕ, ∃ R n, q < (hankel029 harmonic029 R n).rank

def statement : Prop := recurrenceStatement ∧ harmonicStatement ∧ unboundedStatement

end Standalone.MeetingLoadingHankel

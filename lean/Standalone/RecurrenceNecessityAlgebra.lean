import Standalone.MeetingLoadingHankel

/-! # Claim 032 (b): block Hankel rank forces a recurrence

`blockHankel032 a c E R n` is `ℋ_{R,n}` of (32.2): `R+1` rows and `n` blocks of
width `r`, the block in row `i` and column `l = 1, ..., n` (indexed `0, ..., n−1`)
being `h_{i+l} = a_{i+l} c E^{i+l}`. `recurrenceStatement` is the linear algebra
of (b): if `c ≠ 0`, `E` is invertible and every section has rank at most `q`,
then the loadings satisfy a recurrence (29.4) of order at most `q + 1`. The
Gaussian part (a), which bounds the rank by the state dimension, is not in this
target.
-/

open Matrix
namespace Standalone.RecurrenceNecessityAlgebra
open Standalone.MeetingLoadingHankel

/-- The block Hankel section `ℋ_{R,n}` of (32.2). -/
noncomputable def blockHankel032 {r : ℕ} (a : ℕ → ℝ) (c : Fin r → ℝ)
    (E : Matrix (Fin r) (Fin r) ℝ) (R n : ℕ) : Matrix (Fin (R+1)) (Fin n × Fin r) ℝ :=
  fun i ls => a (i + ls.1 + 1) * (c ᵥ* (E ^ ((i:ℕ) + ls.1 + 1))) ls.2

def recurrenceStatement : Prop := ∀ (r : ℕ) (a : ℕ → ℝ) (c : Fin r → ℝ)
  (E : Matrix (Fin r) (Fin r) ℝ), c ≠ 0 → IsUnit E.det → ∀ q : ℕ,
  (∀ R n, (blockHankel032 a c E R n).rank ≤ q) →
  ∃ L ≤ q + 1, ∃ coef : Fin L → ℝ, Recurrence029 a L coef

def statement : Prop := recurrenceStatement

end Standalone.RecurrenceNecessityAlgebra

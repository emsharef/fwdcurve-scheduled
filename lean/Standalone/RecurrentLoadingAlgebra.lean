import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Claim 030: loadings, meeting counts and the factorization (30.7)

A schedule is a finite set `Tm` of meeting dates. `count030 Tm s t` is the
number of meetings in `(s, t]`, `dist030 Tm t` the set of distances `D(t)` from
`t` to the remaining meetings, and `idx030 x D` the number `i(x, D)` of
distances at most `x`. The loadings of (H2) are `loading030 u v M i = u M^i v`,
the quasi-exponential shape of (H1) is `shape030 c b A x = c e^{xA} b`, and the
volatility (30.1) is `sigma030`. The Kronecker vectors `k(x,D)` and `w(s,t)` of
(30.2) and (30.6) are functions on `Fin p × Fin r`.

`companionStatement` and `cayleyStatement` are the two directions of (H2);
`countStatement` is the count identity used in (30.7); `factorStatement` is
(30.7). The state equations (30.3)–(30.5) are not in this target.
-/

open Matrix NormedSpace
namespace Standalone.RecurrentLoadingAlgebra

/-- A linear recurrence (29.4) of order `L`. -/
def Recurrence030 (a : ℕ → ℝ) (L : ℕ) (c : Fin L → ℝ) : Prop :=
  ∀ i : ℕ, a (i + L) = ∑ l : Fin L, c l * a (i + l)

/-- (H2): `a_i = u M^i v`. -/
def loading030 {p : ℕ} (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (i : ℕ) : ℝ :=
  u ⬝ᵥ ((M ^ i) *ᵥ v)

/-- (H1): `λ(x) = c e^{xA} b`. -/
noncomputable def shape030 {r : ℕ} (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ) : ℝ :=
  c ⬝ᵥ (exp (x • A) *ᵥ b)

/-- The number of meetings in `(s, t]`. -/
noncomputable def count030 (Tm : Finset ℝ) (s t : ℝ) : ℕ :=
  (Tm.filter fun τ => s < τ ∧ τ ≤ t).card

/-- `D(t)`: the distances from `t` to the remaining meetings. -/
noncomputable def dist030 (Tm : Finset ℝ) (t : ℝ) : Finset ℝ :=
  (Tm.filter fun τ => t < τ).image fun τ => τ - t

/-- `i(x, D)`: the number of distances at most `x`. -/
noncomputable def idx030 (x : ℝ) (D : Finset ℝ) : ℕ := (D.filter fun d => d ≤ x).card

/-- The volatility (30.1). -/
noncomputable def sigma030 {p r : ℕ} (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (s T : ℝ) : ℝ :=
  loading030 u v M (count030 Tm s T) * shape030 c b A (T - s)

/-- `k(x, D) = (u M^{i(x,D)}) ⊗ (c e^{Ax})`. -/
noncomputable def k030 {p r : ℕ} (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ) (D : Finset ℝ) :
    Fin p × Fin r → ℝ := fun ij =>
  (u ᵥ* (M ^ idx030 x D)) ij.1 * (c ᵥ* exp (x • A)) ij.2

/-- `w(s, t) = (M^{n(s,t)} v) ⊗ (e^{A(t-s)} b)`. -/
noncomputable def w030 {p r : ℕ} (Tm : Finset ℝ) (v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (s t : ℝ) : Fin p × Fin r → ℝ := fun ij =>
  ((M ^ count030 Tm s t) *ᵥ v) ij.1 * (exp ((t - s) • A) *ᵥ b) ij.2

/-- (H2), recurrence to matrix form (the companion construction). -/
def companionStatement : Prop := ∀ (a : ℕ → ℝ) (L : ℕ) (c : Fin L → ℝ),
  Recurrence030 a L c →
  ∃ (u v : Fin L → ℝ) (M : Matrix (Fin L) (Fin L) ℝ), ∀ i, a i = loading030 u v M i

/-- (H2), matrix form to recurrence (Cayley–Hamilton), of order `p`. -/
def cayleyStatement : Prop := ∀ (p : ℕ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ),
  ∃ c : Fin p → ℝ, Recurrence030 (loading030 u v M) p c

/-- Meeting counts add, and `i(x, D(t)) = n(t, t + x)`. -/
def countStatement : Prop := ∀ (Tm : Finset ℝ) (s t T x : ℝ),
  (s ≤ t → t ≤ T → count030 Tm s T = count030 Tm s t + count030 Tm t T) ∧
  idx030 x (dist030 Tm t) = count030 Tm t (t + x)

/-- (30.7): `σ(s, T) = k(T - t, D(t)) · w(s, t)` for `s ≤ t ≤ T`. -/
def factorStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s t T : ℝ),
  s ≤ t → t ≤ T →
  sigma030 Tm u v M c b A s T = k030 u M c A (T - t) (dist030 Tm t) ⬝ᵥ w030 Tm v M b A s t

def statement : Prop :=
  companionStatement ∧ cayleyStatement ∧ countStatement ∧ factorStatement

end Standalone.RecurrentLoadingAlgebra

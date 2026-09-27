import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Claim 002 (Lemma A): statement only

Scheduled dates `τ 0 = 0 < τ 1 < … < τ N` (the claim's `T_0, …, T_N`; `τ` avoids a clash
with the maturity `T`), values `s 0, …, s N` in `ℝ^d`, and a step function `σ` equal to
`s k` on the `k`-th scheduled interval `I_k`. For `t ∈ I_j`, `T ∈ I_k`, `t ≤ T`:

* (2.3) `j ≤ k` and `∫_t^T σ = c_{jk}(t) + (T - max (T_k, t)) • s_k`, with `c_{jk}(t)` as
  in (2.4) of `math/claims/002-lemma-a.md`;
* (2.6) for fixed `t ∈ I_j` and `k ≥ j`, `T ↦ ⟪s_k, ∫_t^T σ⟫` is affine on `I_k ∩ [t, ∞)`
  with slope `‖s_k‖²`.

Encoding choices. `I_N = [T_N, ∞)` is `Set.Ici (τ N)` directly, so no extended reals enter.
The step function is any `σ : ℝ → ℝ^d` with `σ u = s k` for `u ∈ I_k`, `k ≤ N` (this is
(2.2); values of `σ` outside `[0, ∞)` are irrelevant, since `t ≥ τ 0 = 0` for `t ∈ I_j`).
The integral is Mathlib's interval integral against Lebesgue measure. The claim's `d ≥ 1`
is not assumed: for `d = 0` every vector is `0` and both identities are trivial.
-/

namespace Standalone.LemmaA

/-- (2.1)–(2.2): the scheduled interval `I_k = [T_k, T_{k+1})` for `k < N`, and
`I_N = [T_N, ∞)`. Only `k ≤ N` is ever used. -/
def I (τ : ℕ → ℝ) (N k : ℕ) : Set ℝ :=
  if k < N then Set.Ico (τ k) (τ (k + 1)) else Set.Ici (τ k)

/-- (2.4): `c_{jk}(t) = s_j (T_{j+1} - t) + ∑_{m=j+1}^{k-1} s_m (T_{m+1} - T_m)` for `k > j`,
and `c_{jj}(t) = 0`. It does not mention `T`. -/
def c {E : Type*} [AddCommGroup E] [Module ℝ E] (τ : ℕ → ℝ) (s : ℕ → E) (j k : ℕ) (t : ℝ) :
    E :=
  if j < k then (τ (j + 1) - t) • s j + ∑ m ∈ Finset.Ico (j + 1) k, (τ (m + 1) - τ m) • s m
  else 0

def statement : Prop :=
  ∀ (N d : ℕ) (τ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d)),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    (∀ k ≤ N, ∀ u ∈ I τ N k, σ u = s k) →
    -- Lemma A, (2.3)
    (∀ t T : ℝ, t ≤ T → ∀ j ≤ N, ∀ k ≤ N, t ∈ I τ N j → T ∈ I τ N k →
        j ≤ k ∧ ∫ u in t..T, σ u = c τ s j k t + (T - max (τ k) t) • s k) ∧
    -- Corollary (affine drift), (2.6)
    (∀ t : ℝ, ∀ j ≤ N, ∀ k ≤ N, t ∈ I τ N j → j ≤ k →
        ∃ a : ℝ, ∀ T : ℝ, T ∈ I τ N k → t ≤ T →
          inner ℝ (s k) (∫ u in t..T, σ u) = a + ‖s k‖ ^ 2 * T)

end Standalone.LemmaA

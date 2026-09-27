import Standalone.LemmaA

/-!
# Claim 004 (step drift and volatility vanish): statement only

Scheduled dates `τ 0 = 0 < τ 1 < … < τ N` with the intervals `I_k` of Claim 002
(`Standalone.LemmaA.I`), a current date `t ∈ I_j`, step values `μ k ∈ ℝ` and `s k ∈ ℝ^d`, and
step functions `α : ℝ → ℝ`, `σ : ℝ → ℝ^d` equal to `μ k`, `s k` on `I_k` (4.2). The integrated
drift condition (4.4) at a maturity `T` is `∫_t^T α = ½ ‖∫_t^T σ‖²`, with Mathlib's interval
integrals and the Euclidean norm.

The statement bundles the two parts of `math/claims/004-step-drift-vanish.md`:

* **Refinement**: (4.4) assumed on a set `M` satisfying (4.5), i.e. for every `j ≤ k ≤ N` the
  set `M` contains two distinct points of `(m_k, T_{k+1})` with `m_k = max (T_k, t)`; a point of
  that open interval is encoded as a point of `I_k` strictly greater than `m_k`;
* **Claim**: (4.4) assumed for every real `T ≥ t`.

Each concludes `μ k = 0` and `s k = 0` for every `j ≤ k ≤ N`.

Encoding choices. As in Claim 002, `α` and `σ` are any functions equal to the step values on
each `I_k`; values off `[0, ∞)` are irrelevant since only `u ≥ t ≥ 0` is integrated. The
claim's `d ≥ 1` is not assumed: for `d = 0` every vector is `0` and the conclusion `s k = 0` is
trivial while `μ k = 0` still follows. The Refinement's instances (the maturities
`m_k + h_k`, `m_k + h_k / 2` of (4.3), or the rationals in `(t, ∞)`) are particular sets `M`;
the Claim is proved through the first of them.
-/

open MeasureTheory

namespace Standalone.StepDriftVanish

/-- (4.4) at the maturity `T`: `∫_t^T α = ½ ‖∫_t^T σ‖²`. -/
def driftCondition {d : ℕ} (α : ℝ → ℝ) (σ : ℝ → EuclideanSpace ℝ (Fin d)) (t T : ℝ) :
    Prop :=
  ∫ u in t..T, α u = (1 / 2 : ℝ) * ‖∫ u in t..T, σ u‖ ^ 2

def statement : Prop :=
  ∀ (N d : ℕ) (τ : ℕ → ℝ) (μ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d))
    (α : ℝ → ℝ) (σ : ℝ → EuclideanSpace ℝ (Fin d)),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    -- (4.2): the drift and the volatility are step functions of maturity
    (∀ k ≤ N, ∀ u ∈ LemmaA.I τ N k, α u = μ k) →
    (∀ k ≤ N, ∀ u ∈ LemmaA.I τ N k, σ u = s k) →
    ∀ j ≤ N, ∀ t ∈ LemmaA.I τ N j,
    -- Refinement: (4.4) on a set `M` satisfying (4.5)
    ((∀ M : Set ℝ,
        (∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, T₁ ≠ T₂ ∧
          T₁ ∈ LemmaA.I τ N k ∧ max (τ k) t < T₁ ∧ T₂ ∈ LemmaA.I τ N k ∧ max (τ k) t < T₂) →
        (∀ T ∈ M, driftCondition α σ t T) →
        ∀ k, j ≤ k → k ≤ N → μ k = 0 ∧ s k = 0) ∧
    -- Claim: (4.4) for every `T ≥ t`
    ((∀ T : ℝ, t ≤ T → driftCondition α σ t T) →
        ∀ k, j ≤ k → k ≤ N → μ k = 0 ∧ s k = 0))

end Standalone.StepDriftVanish

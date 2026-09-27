import Standalone.LemmaA
import Standalone.StepDriftVanish
import Standalone.PiecewiseAffineIntegral

/-!
# Claim 007 (ramp drift identified): statement only

Within the step-plus-ramp family with a step volatility, the integrated drift condition at
three maturities per interval holds if and only if the drift is the differentiated HJM drift
(`math/claims/007-ramp-drift-identified.md`).

Scheduled dates `τ 0 = 0 < … < τ N` with the intervals `I_k` of Claim 002, a current date
`t ∈ I_j`, `m_k = max (T_k, t)`; a step volatility `σ` with values `s k ∈ ℝ^d` (2.2) and a
piecewise-affine drift `α` with data `a k, b k ∈ ℝ` ((6.2) with `d = 1`). `C_k = c_{jk}(t)` is
the Lemma A constant `Standalone.LemmaA.c`. The differentiated HJM drift (7.3) is
`u ↦ ⟪σ u, ∫_t^u σ⟫`, whose data (7.4) are `bStar s k = ‖s k‖²` and
`aStar τ s j k t = ⟪s k, C_k⟫ - ‖s k‖² (m_k - T_k)`.

The four conditions of the claim, for the fixed `t ∈ I_j`:

* (A) the integrated drift condition (`Standalone.StepDriftVanish.driftCondition`) for every
  `T ≥ t`;
* (A′) the condition on a set `M ⊆ [t, ∞)` containing three distinct points of each open
  interval `(m_k, T_{k+1})`, `j ≤ k ≤ N` (a point of that interval is encoded as a point of
  `I_k` strictly greater than `m_k`);
* (B) `a k = a*_k` and `b k = b*_k` for every `j ≤ k ≤ N`;
* (B′) `α u = ⟪σ u, ∫_t^u σ⟫` for every `u ≥ t`.

The statement is the cycle (A) ⇒ (A′) ⇒ (B) ⇒ (A) of the claim's proof together with
(B) ⇔ (B′), which is "the following are equivalent". Encoding choices as in Claims 002, 004
and 006: `σ` and `α` are any functions equal to the pieces on each `I_k`; `d ≥ 1` is not
assumed. The Consequences paragraph of the claim is not part of the claim.
-/

open MeasureTheory

namespace Standalone.RampDriftIdentified

open Standalone.LemmaA Standalone.StepDriftVanish

/-- (7.4): `b*_k = |s_k|²`. -/
noncomputable def bStar {d : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) : ℝ := ‖s k‖ ^ 2

/-- (7.4): `a*_k = ⟨s_k, C_k⟩ - |s_k|² (m_k - T_k)`, with `C_k = c_{jk}(t)` of (2.4). -/
noncomputable def aStar {d : ℕ} (τ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d)) (j k : ℕ)
    (t : ℝ) : ℝ :=
  inner ℝ (s k) (c τ s j k t) - ‖s k‖ ^ 2 * (max (τ k) t - τ k)

def statement : Prop :=
  ∀ (N d : ℕ) (τ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℕ → ℝ) (α : ℝ → ℝ),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    -- (2.2): the volatility is a step function of maturity
    (∀ k ≤ N, ∀ u ∈ I τ N k, σ u = s k) →
    -- (6.2) with `d = 1`: the drift is piecewise affine in maturity
    (∀ k ≤ N, ∀ u ∈ I τ N k, α u = a k + (u - τ k) * b k) →
    ∀ j ≤ N, ∀ t ∈ I τ N j,
    let A : Prop := ∀ T : ℝ, t ≤ T → driftCondition α σ t T
    let A' : Prop := ∃ M : Set ℝ, M ⊆ Set.Ici t ∧
      (∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, ∃ T₃ ∈ M,
        T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₂ ≠ T₃ ∧
        (T₁ ∈ I τ N k ∧ max (τ k) t < T₁) ∧ (T₂ ∈ I τ N k ∧ max (τ k) t < T₂) ∧
        (T₃ ∈ I τ N k ∧ max (τ k) t < T₃)) ∧
      ∀ T ∈ M, driftCondition α σ t T
    let B : Prop := ∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k
    let B' : Prop := ∀ u : ℝ, t ≤ u → α u = inner ℝ (σ u) (∫ v in t..u, σ v)
    (A → A') ∧ (A' → B) ∧ (B → A) ∧ (B ↔ B')

end Standalone.RampDriftIdentified

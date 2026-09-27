import Standalone.LemmaA
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 005 (Theorem 1): statement only

Under AX-01 and AX-02 the maturity-step family carries no drift, no volatility and no curve
jumps (`math/claims/005-theorem-1-step-family.md`).

The setting is that of `ledger/AXIOMS.md` as encoded in `lean/Upstream/HJMScheduled.lean`. A
statement-only file may import Mathlib and `Standalone` only, so the fields of that structure
that the theorem uses are restated here as hypotheses, spelled exactly as the structure's
fields: the dates `τ 0 = 0 < … < τ N`, the vanishing of `α`, `σ`, `ξ n` before the current date
(S7), AX-01 (`drift_integrated`) and AX-02 (`jump_martingale`), the latter with an abstract
sub-σ-algebra `G n` in place of `ℱ_(T_n)⁻`. The proof file
`lean/Novel/Theorem1Proof.lean` also states the theorem for an `Upstream.HJMScheduled`
instance, as the claim's "Lean shape" asks.

Family hypothesis (5.2)–(5.3): step values `μ k t ω ∈ ℝ` (the claim's `μ_k(t)(ω)`),
`s k t ω ∈ ℝ^d`, and random variables `X n k`, with `α t T ω = μ k t ω`, `σ t T ω = s k t ω`
for `t ≤ T ∈ I_k`, and `ξ n u ω = X n k ω` for `u ∈ I_k`, `n ≤ k`.

Conclusions. (5.4): `X n k = 0` a.s. for `1 ≤ n ≤ k ≤ N`, and for each `n`, on one almost-sure
event, `ξ n u = 0` for every `u`. (5.5): for `(Q ⊗ dt)`-a.e. `(ω, t) ∈ Ω × [0, ∞)`, with `t ∈ I_j`,
`μ k t ω = 0` and `s k t ω = 0` for every `j ≤ k ≤ N`, and `α t T ω = 0`, `σ t T ω = 0` for every
`T`. The Corollary (the curve does not move) is not a Lean target of the claim.

Encoding choices. The claim's `d ≥ 1` and `N ≥ 1` are not assumed: for `N = 0` the jump leg is
vacuous and the drift leg is unchanged. The measure `P` is the ledger's `Q` (the structure's
`μ`; the letter `μ` is kept for the drift step values as in the claim). No measurability of
`μ`, `s`, `X` is assumed, as in the claim.
-/

open MeasureTheory

namespace Standalone.Theorem1

def statement : Prop :=
  ∀ {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (τ : ℕ → ℝ)
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (ξ : ℕ → ℝ → Ω → ℝ)
    (G : ℕ → MeasurableSpace Ω)
    (μ : ℕ → ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (X : ℕ → ℕ → Ω → ℝ),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    (∀ n, G n ≤ m₀) →
    -- (S7)
    (∀ t T ω, T < t → α t T ω = 0) →
    (∀ t T ω, T < t → σ t T ω = 0) →
    (∀ n, 1 ≤ n → n ≤ N → ∀ u ω, u < τ n → ξ n u ω = 0) →
    -- AX-01
    (∀ T : ℝ, 0 < T → ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc 0 T))),
      ∫ u in p.2..T, α p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..T, σ p.2 u p.1‖ ^ 2) →
    -- AX-02
    (∀ n, 1 ≤ n → n ≤ N → ∀ T : ℝ, τ n ≤ T →
      P[fun ω => Real.exp (-(∫ u in τ n..T, ξ n u ω)) | G n] =ᵐ[P] 1) →
    -- (5.2)
    (∀ ω t T, t ≤ T → ∀ k ≤ N, T ∈ LemmaA.I τ N k → α t T ω = μ k t ω) →
    (∀ ω t T, t ≤ T → ∀ k ≤ N, T ∈ LemmaA.I τ N k → σ t T ω = s k t ω) →
    -- (5.3)
    (∀ ω n k, 1 ≤ n → n ≤ k → k ≤ N → ∀ u ∈ LemmaA.I τ N k, ξ n u ω = X n k ω) →
    -- (5.4), the jump leg
    ((∀ n k, 1 ≤ n → n ≤ k → k ≤ N → ∀ᵐ ω ∂P, X n k ω = 0) ∧
      (∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂P, ∀ u, ξ n u ω = 0)) ∧
    -- (5.5), the drift and volatility leg
    (∀ᵐ p ∂(P.prod (volume.restrict (Set.Ici 0))),
      (∀ j ≤ N, p.2 ∈ LemmaA.I τ N j → ∀ k, j ≤ k → k ≤ N →
        μ k p.2 p.1 = 0 ∧ s k p.2 p.1 = 0) ∧
      ∀ T, α p.2 T p.1 = 0 ∧ σ p.2 T p.1 = 0)

end Standalone.Theorem1

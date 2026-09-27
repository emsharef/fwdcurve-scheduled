import Standalone.LemmaA
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 003 (step jumps vanish): statement only

Scheduled dates `τ 0 = 0 < τ 1 < … < τ N` with the intervals `I_k` of Claim 002
(`Standalone.LemmaA.I`), a date index `1 ≤ n ≤ N`, random values `X n, …, X N`, and a jump
`ξ : ℝ → Ω → ℝ` that is the step function (3.2): `ξ u ω = X k ω` for `u ∈ I_k` with `k ≥ n`
and `0` for `u ∈ I_k` with `k < n`. `Y τ n ξ T` is the random variable
`exp (-∫_{T_n}^T ξ(u, ω) du)` of (3.3), with Mathlib's interval integral.

The statement bundles the three parts of `math/claims/003-step-jumps-vanish.md`:

* **Refinement**: (3.3) assumed only at the maturities (3.4), `T_k + h_k` and `T_k + h_k / 2`
  for `n ≤ k ≤ N`, with `h_k = (T_{k+1} - T_k) / 2` for `k < N` and `h_N = 1` (`gapHalf`);
* **Claim**: (3.3) assumed for every real `T ≥ T_n`;
* **Corollary**: (3.5), `μ[Y_T | m] = 1` a.e. for every `T ≥ T_n` and a sub-σ-algebra `m`.

Each concludes `X k = 0` a.s. for every `n ≤ k ≤ N`.

Encoding choices. As in Claim 002, `ξ` is any function equal to the step values on each `I_k`;
its values off `[0, ∞)` are irrelevant since only `u ≥ T_n ≥ 0` is integrated. "Integrable with
expectation 1" is `Integrable` plus the Bochner integral equal to `1`, as in Claim 001. Mathlib's
`condExp` is `0` on non-integrable functions, so (3.5) as spelled already forces integrability
of `Y_T`, and the `[0, ∞]`-valued reading of the claim is not needed. The hypothesis `1 ≤ n` is
part of the claim's setting and is carried although the proof does not use it.
-/

open MeasureTheory Real

namespace Standalone.StepJumpsVanish

/-- (3.4): `h_k = (T_{k+1} - T_k) / 2` for `k < N`, and `h_N = 1`. -/
noncomputable def gapHalf (τ : ℕ → ℝ) (N k : ℕ) : ℝ :=
  if k < N then (τ (k + 1) - τ k) / 2 else 1

/-- (3.3): `Y_T(ω) = exp (-∫_{T_n}^T ξ(u, ω) du)`. -/
noncomputable def Y {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (ξ : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  exp (-(∫ u in τ n..T, ξ u ω))

def statement : Prop :=
  ∀ {Ω : Type} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N n : ℕ) (τ : ℕ → ℝ) (X : ℕ → Ω → ℝ) (ξ : ℝ → Ω → ℝ),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → 1 ≤ n → n ≤ N →
    -- (3.2): the jump is a step function of maturity
    (∀ k ≤ N, ∀ u ∈ LemmaA.I τ N k, ∀ ω, ξ u ω = if n ≤ k then X k ω else 0) →
    -- Refinement: (3.3) at the maturities (3.4) only
    ((∀ k, n ≤ k → k ≤ N → ∀ T : ℝ,
        (T = τ k + gapHalf τ N k ∨ T = τ k + gapHalf τ N k / 2) →
        Integrable (Y τ n ξ T) μ ∧ ∫ ω, Y τ n ξ T ω ∂μ = 1) →
      ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂μ, X k ω = 0) ∧
    -- Claim: (3.3) for every `T ≥ T_n`
    ((∀ T : ℝ, τ n ≤ T → Integrable (Y τ n ξ T) μ ∧ ∫ ω, Y τ n ξ T ω ∂μ = 1) →
      ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂μ, X k ω = 0) ∧
    -- Corollary: (3.5), the conditional form
    (∀ m : MeasurableSpace Ω, m ≤ m₀ →
      (∀ T : ℝ, τ n ≤ T → μ[Y τ n ξ T | m] =ᵐ[μ] 1) →
      ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂μ, X k ω = 0)

end Standalone.StepJumpsVanish

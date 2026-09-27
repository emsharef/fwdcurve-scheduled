import Standalone.LemmaA
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 008 (jump law, tilted Gaussian): statement only

The jump martingale condition for a piecewise-affine curve jump with `G`-measurable slopes
characterizes the level jumps (`math/claims/008-jump-law-tilted-gaussian.md`).

Setting: a probability space `(Ω, m₀, P)`, a sub-σ-algebra `G ≤ m₀`, dates `τ 0 = 0 < … < τ N`
with the intervals `I_k` of Claim 002, a date index `1 ≤ n ≤ N`, level jumps `X k` and
`G`-measurable slope jumps `y k` (`n ≤ k ≤ N`), and the piecewise-affine jump (8.1)
`ξ u ω = X k ω + y k ω (u - T_k)` on `I_k`, `ξ u ω = 0` for `u < T_n`. `L k = T_{k+1} - T_k`,
`S k = ∑_{m=n}^{k-1} (X m L m + ½ y m L m²)`, `R k = exp (-∑_{m<k} L m X m)`,
`Z k = exp (∑_{m<k} ½ y m L m²)`, `D k = R k / Z k`.

Encoding of the conditional expectations. The claim takes conditional expectations of
nonnegative random variables in `[0, ∞]`. Mathlib's `condExp` is the `L¹` conditional
expectation, zero on non-integrable functions, so:

* the hypothesis (H) is written with `condExp`, exactly as AX-02 is in
  `lean/Upstream/HJMScheduled.lean`; as recorded there, this forces integrability of
  `exp (-∫ ξ)`, which the claim's `[0, ∞]` reading also yields (its expectation is `1`);
* (8.3), `E[R_k | G] = Z_k` in `[0, ∞]`, is encoded by its defining property,
  `∫⁻_A R_k dP = ∫⁻_A Z_k dP` for every `A ∈ G` (`R_k` need not be integrable);
* (8.5), the regular conditional distribution of `X_k` given `G` under the tilted measure
  `P_k = D_k · P` is `N(0, y_k)`, is encoded through the abstract Bayes formula (8.8) of the
  claim's Step 1 with indicator test functions, in the same `[0, ∞]` form as (8.3): for every
  Borel `B` and every `A ∈ G`, `∫⁻_A D_k 1_B(X_k) dP = ∫⁻_A N(0, y_k)(B) dP`. For every fixed
  `B` this is what "`κ_k(ω, B) = N(0, y_k(ω))(B)` a.s." says, and a regular conditional
  distribution is determined a.s. by countably many `B`;
* in Part (c), "conditionally on `G` the vector `X` is Gaussian with `G`-measurable mean `μ`
  and covariance `Σ`" is encoded by its conditional moment generating function in `[0, ∞]`:
  for every `θ` and every `A ∈ G`, `∫⁻_A exp ⟨θ, X⟩ dP = ∫⁻_A exp (⟨θ, μ⟩ + ½ ⟨θ, Σ θ⟩) dP`,
  with `Σ` symmetric (a covariance matrix is; the moment generating function only sees the
  symmetric part, so this pins down the `Σ_{km}` of (8.6)).

The variance of `gaussianReal` is an `ℝ≥0`; `(y k ω).toNNReal` is used, which is `y k ω` on
the almost-sure event (8.4) where `y k ω ≥ 0`, and `N(0, 0) = δ_0` as in the claim.

Part (d) is an existence statement; its witnesses are the claim's construction. The claim's
`N ≥ 1` is implied by `1 ≤ n ≤ N`.
-/

open MeasureTheory ProbabilityTheory Real

namespace Standalone.JumpLawTiltedGaussian

open Standalone.LemmaA

/-- `L k = T_{k+1} - T_k`. -/
def L (τ : ℕ → ℝ) (k : ℕ) : ℝ := τ (k + 1) - τ k

/-- `S k = ∑_{m=n}^{k-1} (X m L m + ½ y m L m²)` of (8.2). -/
noncomputable def S {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (X y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.Ico n k, (X m ω * L τ m + y m ω * L τ m ^ 2 / 2)

/-- `R k = exp (-∑_{m=n}^{k-1} L m X m)`. -/
noncomputable def R {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  exp (-∑ m ∈ Finset.Ico n k, L τ m * X m ω)

/-- `Z k = exp (∑_{m=n}^{k-1} ½ y m L m²)`. -/
noncomputable def Z {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  exp (∑ m ∈ Finset.Ico n k, y m ω * L τ m ^ 2 / 2)

/-- `D k = R k / Z k`, the density of the tilted measure `P_k`. -/
noncomputable def D {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (X y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  R τ n X k ω / Z τ n y k ω

/-- Hypothesis (H): AX-02 for the jump at `T_n` with `G = ℱ_(T_n)⁻`. -/
def H {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure[m₀] Ω) (G : MeasurableSpace Ω) (τ : ℕ → ℝ)
    (n : ℕ) (ξ : ℝ → Ω → ℝ) : Prop :=
  ∀ T : ℝ, τ n ≤ T → P[fun ω => exp (-(∫ u in τ n..T, ξ u ω)) | G] =ᵐ[P] 1

/-- (8.3): `E[R_k | G] = Z_k` in `[0, ∞]`, as an identity of integrals over `G`-sets. -/
def cond83 {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure[m₀] Ω) (G : MeasurableSpace Ω) (τ : ℕ → ℝ)
    (n N : ℕ) (X y : ℕ → Ω → ℝ) : Prop :=
  ∀ k, n ≤ k → k ≤ N → ∀ A : Set Ω, MeasurableSet[G] A →
    ∫⁻ ω in A, ENNReal.ofReal (R τ n X k ω) ∂P = ∫⁻ ω in A, ENNReal.ofReal (Z τ n y k ω) ∂P

/-- (8.4): `y_k ≥ 0` a.s. -/
def cond84 {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure[m₀] Ω) (n N : ℕ) (y : ℕ → Ω → ℝ) : Prop :=
  ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂P, 0 ≤ y k ω

/-- (8.5): the conditional law of `X_k` given `G` under `P_k = D_k · P` is `N(0, y_k)`,
through (8.8) with indicator test functions, as an identity of integrals over `G`-sets:
`E[D_k 1_B(X_k) | G] = N(0, y_k)(B)` in `[0, ∞]`. -/
def cond85 {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure[m₀] Ω) (G : MeasurableSpace Ω) (τ : ℕ → ℝ)
    (n N : ℕ) (X y : ℕ → Ω → ℝ) : Prop :=
  ∀ k, n ≤ k → k ≤ N → ∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω, MeasurableSet[G] A →
    ∫⁻ ω in A, ENNReal.ofReal (D τ n X y k ω) * (X k ⁻¹' B).indicator 1 ω ∂P =
      ∫⁻ ω in A, gaussianReal 0 (y k ω).toNNReal B ∂P

def statement : Prop :=
  -- Parts (a), (b), (c), with (8.2) recorded first.
  (∀ {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (N n : ℕ) (τ : ℕ → ℝ) (X y : ℕ → Ω → ℝ) (ξ : ℝ → Ω → ℝ),
    G ≤ m₀ → τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → 1 ≤ n → n ≤ N →
    (∀ k, n ≤ k → k ≤ N → Measurable[m₀] (X k)) →
    (∀ k, n ≤ k → k ≤ N → Measurable[G] (y k)) →
    -- (8.1)
    (∀ k, n ≤ k → k ≤ N → ∀ u ∈ I τ N k, ∀ ω, ξ u ω = X k ω + y k ω * (u - τ k)) →
    (∀ u ω, u < τ n → ξ u ω = 0) →
    -- (8.2), by Lemma C
    (∀ ω k, n ≤ k → k ≤ N → ∀ T ∈ I τ N k,
      ∫ u in τ n..T, ξ u ω = S τ n X y k ω + X k ω * (T - τ k) + y k ω * (T - τ k) ^ 2 / 2) ∧
    -- Part (a), necessity
    (H P G τ n ξ → cond83 P G τ n N X y ∧ cond84 P n N y ∧ cond85 P G τ n N X y) ∧
    -- Part (b), sufficiency
    (cond83 P G τ n N X y → cond84 P n N y → cond85 P G τ n N X y → H P G τ n ξ) ∧
    -- Part (c), the jointly Gaussian case
    (∀ (μ : ℕ → Ω → ℝ) (C : ℕ → ℕ → Ω → ℝ),
      (∀ k, Measurable[G] (μ k)) → (∀ k m, Measurable[G] (C k m)) →
      (∀ k m, C k m = C m k) →
      (∀ θ : ℕ → ℝ, ∀ A : Set Ω, MeasurableSet[G] A →
        ∫⁻ ω in A, ENNReal.ofReal (exp (∑ m ∈ Finset.Icc n N, θ m * X m ω)) ∂P =
          ∫⁻ ω in A, ENNReal.ofReal (exp (∑ m ∈ Finset.Icc n N, θ m * μ m ω +
            (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N, θ m * θ m' * C m m' ω) / 2)) ∂P) →
      (H P G τ n ξ ↔ ∀ᵐ ω ∂P, ∀ k, n ≤ k → k ≤ N →
        μ k ω = ∑ m ∈ Finset.Ico n k, L τ m * C k m ω ∧ y k ω = C k k ω))) ∧
  -- Part (d), sharpness: a non-Gaussian level jump on the second interval
  (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (τ : ℕ → ℝ) (X : ℕ → Ω → ℝ) (y : ℕ → ℝ) (ξ : ℝ → Ω → ℝ),
    τ 0 = 0 ∧ StrictMonoOn τ (Set.Iic 2) ∧ 0 < y 1 ∧ 0 < y 2 ∧
    (∀ k, 1 ≤ k → k ≤ 2 → ∀ u ∈ I τ 2 k, ∀ ω, ξ u ω = X k ω + y k * (u - τ k)) ∧
    (∀ u ω, u < τ 1 → ξ u ω = 0) ∧
    H P ⊥ τ 1 ξ ∧
    HasLaw (X 1) (gaussianReal 0 (y 1).toNNReal) P ∧
    ¬ ∃ (m : ℝ) (v : NNReal), HasLaw (X 2) (gaussianReal m v) P)

end Standalone.JumpLawTiltedGaussian

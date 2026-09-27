import Standalone.ZeroMeanReversionUpstreamBridge
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.BrownianMotion.Basic

/-! # Claim 032, Lemma 032-A: Gaussian Wiener integrals

`gaussianStatement` is Lemma 032-A. Let the driver `B_k` be a pre-Brownian motion (Mathlib's
`IsPreBrownianReal`), and let `F : [0, ∞) → ℝ^N` be Borel and bounded, continuous at almost every
time of `(0, τ]`; this contains the claim's integrands, bounded with finitely many pieces on
each of which they are continuous. Then every coordinate is in (U4), and the vector
`I(F)_τ = ∫_0^τ F dW`, taken coordinatewise, has the centered Gaussian law with covariance
`gram032 F τ = ∫_0^τ F Fᵀ ds` (Mathlib's `multivariateGaussian`).

`acStatement`: a multivariate Gaussian law with positive definite covariance is absolutely
continuous with respect to Lebesgue measure, which (a) applies to `(ξ_0, ..., ξ_n)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Standalone.RecurrenceNecessityGaussian
open Standalone.ZeroMeanReversionUpstreamBridge

/-- The covariance `∫_0^τ F Fᵀ`. -/
noncomputable def gram032 {N : ℕ} (F : ℝ≥0 → Fin N → ℝ) (τ : ℝ≥0) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∫ s in (0:ℝ)..τ, F (Real.toNNReal s) i * F (Real.toNNReal s) j

def gaussianStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (N : ℕ) (F : ℝ≥0 → Fin N → ℝ), (∀ j, Measurable fun s => F s j) →
  ∀ C : ℝ, (∀ s j, |F s j| ≤ C) → ∀ τ : ℝ≥0,
  (∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) →
    ∀ j, ContinuousAt (fun s => F s j) (Real.toNNReal s)) →
  (∀ j, U4 S.ℱ S.μ fun s _ => F s j) ∧
  S.μ.map (fun ω => WithLp.toLp 2 fun j => S.I k (fun s _ => F s j) τ ω) =
    multivariateGaussian 0 (gram032 F τ)

def acStatement : Prop := ∀ (n : ℕ) (μ : EuclideanSpace ℝ (Fin n))
  (S : Matrix (Fin n) (Fin n) ℝ), S.PosDef → multivariateGaussian μ S ≪ volume

def statement : Prop := gaussianStatement ∧ acStatement

end Standalone.RecurrenceNecessityGaussian

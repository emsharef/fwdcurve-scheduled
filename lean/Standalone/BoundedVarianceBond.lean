import Standalone.BoundedVarianceIndependence

/-! # Claim 025: identification of the actual discounted bond

The scalar solution is the one constructed from (25.0) in the existence theorem.
This target derives the price identity from its equation and the cited integral
interfaces. No field asserts a bond-price or martingale conclusion for the model.
-/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIndependence
namespace Standalone.BoundedVarianceBond

/-- The actual discounted bond, held at its maturity after time T. -/
noncomputable def D025 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i : Fin S.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) (tau T t : ℝ≥0) (ω : Ω) : ℝ :=
  let Z := fun s => z025 S i lam Y (Real.toNNReal s) ω
  P025 lam tau Z (min t T) T / B025 lam tau Z (min t T)

def identityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_P : Predictability S.ℱ) (i j : Fin S.m), i ≠ j →
  (∀ k l t, S.c k l t = if k = l then 1 else 0) →
  ∀ lam : ℝ, 0 < lam → ∀ Y : ℝ≥0 → Ω → ℝ,
  ScalarSolution025 S j lam Y → (∀ ω, Continuous fun t => Y t ω) →
  ∀ tau T : ℝ≥0, 0 < tau → tau ≤ T →
  ∀ᵐ ω ∂S.μ, ∀ t, D025 S i lam Y tau T t ω =
    exponential10 S (H025 i j lam ((T:ℝ)-tau) (fun s ω => Y (Real.toNNReal s) ω)) tau t ω

def martingaleStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_P : Predictability S.ℱ) (_E : ExponentialMartingale S) (i j : Fin S.m), i ≠ j →
  (∀ k l t, S.c k l t = if k = l then 1 else 0) →
  ∀ lam : ℝ, 0 < lam → ∀ Y : ℝ≥0 → Ω → ℝ,
  ScalarSolution025 S j lam Y → (∀ ω, Continuous fun t => Y t ω) →
  ∀ tau T : ℝ≥0, 0 < tau → Martingale (D025 S i lam Y tau T) S.ℱ S.μ

def statement : Prop := identityStatement ∧ martingaleStatement

end Standalone.BoundedVarianceBond

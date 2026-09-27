import Standalone.BoundedVarianceBond
import Standalone.BoundedVarianceIto
import Standalone.BoundedVarianceUniqueness

/-! # Claim 025: the three remaining stochastic conclusions for one constructed state

All model conclusions below refer to the same coordinate. The supplied calculus
interfaces are precisely the conditional inputs in (25.0), not model conclusions.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIndependence Standalone.BoundedVarianceBond
open Standalone.BoundedVarianceIto Standalone.BoundedVarianceUniqueness
namespace Standalone.BoundedVarianceCompletion

/-- The joint-filtration conclusions for the coordinate constructed in R and S. -/
def C025 {Ω : Type} [MeasurableSpace Ω] (S R : ItoCalculus Ω)
    (i k : Fin S.m) (l : Fin R.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ScalarSolution025 R l lam Y ∧ ScalarSolution025 S k lam Y ∧
  (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) ∧
  U4 S.ℱ S.μ (fun s ω => g025 (Y s ω)) ∧
  (∀ᵐ ω ∂S.μ, ∀ t, v025 (Y t ω) = 2 +
    (∫ s in (0:ℝ)..(t:ℝ), h025 lam (Y (Real.toNNReal s) ω)) +
    S.I k (fun s ω => g025 (Y s ω)) t ω) ∧
  (∀ tau T : ℝ≥0, 0 < tau → Martingale (D025 S i lam Y tau T) S.ℱ S.μ) ∧
  (∀ tau : ℝ≥0,
    Martingale (fun t ω => (S.I k (fun s ω => a025 (Y s ω)) (min t tau) ω)^2 -
      ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), v025 (Y (Real.toNNReal s) ω)) S.ℱ S.μ ∧
    Martingale (fun t ω => (S.I k (fun s ω => g025 (Y s ω)) (min t tau) ω)^2 -
      ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ),
        (1-(Real.tanh (Y (Real.toNNReal s) ω))^2)^2*v025 (Y (Real.toNNReal s) ω)) S.ℱ S.μ) ∧
  (∀ tau : ℝ≥0, Solution6 S (b025Stopped lam tau) (a025Stopped k tau) (fun _ _ => 0)
    (fun t ω (_ : Fin 1) => Y (min t tau) ω)) ∧
  (∀ tau : ℝ≥0, ∀ X : ℝ≥0 → Ω → Fin 1 → ℝ,
    Solution6 S (b025Stopped lam tau) (a025Stopped k tau) (fun _ _ => 0) X →
    ∀ᵐ ω ∂S.μ, ∀ t, X t ω = fun _ => Y (min t tau) ω) ∧
  (∀ tau : ℝ≥0, 0 < tau →
    IndepFun (S.B i tau) (S.I k (fun s ω => a025 (Y s ω)) tau) S.μ ∧
    (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S i lam Y tau ω) tau =
      S.B i tau ω + S.I k (fun s ω => a025 (Y s ω)) tau ω) ∧
    (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S i lam Y tau ω) tau ≠ 0)) ∧
  (∀ᵐ ω ∂S.μ, (∀ j : Fin 3, Continuous fun s : ℝ => z025 S i lam Y (Real.toNNReal s) ω j) ∧
    z025 S i lam Y 0 ω = 0)

def constructionStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω) (_E : LipschitzSDE R) (_ES : LipschitzSDE S)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_D : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation R)
  (_P : Predictability S.ℱ) (_Q : Predictability R.ℱ) (_M : ExponentialMartingale S),
  BrownianDrivers6 R → BrownianDrivers6 S →
  ∀ (i k : Fin S.m) (l : Fin R.m), i ≠ k → (∀ j, j = l) →
  R.μ = S.μ → S.B k = R.B l → (∀ t, R.ℱ t ≤ S.ℱ t) →
  (∀ j j' t, S.c j j' t = if j = j' then 1 else 0) →
  IsBrownianReal (S.B i) S.μ →
  IndepFun (fun ω t => S.B i t ω) (fun ω t => R.B l t ω) S.μ →
  (∀ t, R.ℱ t ≤ m025 S.μ (R.B l)) →
  ∀ lam : ℝ, 0 < lam → ∃ Y, C025 S R i k l lam Y

def statement : Prop := Standalone.BoundedVarianceState.statement ∧
  Standalone.BoundedVarianceBond.statement ∧ Standalone.BoundedVarianceIto.statement ∧
  Standalone.BoundedVarianceUniqueness.statement ∧ constructionStatement

end Standalone.BoundedVarianceCompletion

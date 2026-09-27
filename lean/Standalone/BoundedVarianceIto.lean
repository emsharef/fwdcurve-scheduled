import Standalone.BoundedVarianceExistence

/-! # Claim 025: the variance-state Itô equation and its covariation density -/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
namespace Standalone.BoundedVarianceIto

noncomputable def g025 (z : ℝ) : ℝ := (1-(Real.tanh z)^2)*a025 z
noncomputable def h025 (lam z : ℝ) : ℝ :=
  (1-(Real.tanh z)^2)*b025 lam z - Real.tanh z*(1-(Real.tanh z)^2)*v025 z
noncomputable def F025 (p : ℝ × (Fin 1 → ℝ)) : ℝ := v025 (p.2 0)

def itoStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (R : ItoCalculus Ω) (_P : Predictability R.ℱ) (k : Fin R.m), (∀ j, j = k) →
  (∀ t, R.c k k t = 1) → ∀ lam : ℝ, 0 < lam →
  ∀ Y : ℝ≥0 → Ω → ℝ, ScalarSolution025 R k lam Y →
  (∀ ω, Continuous fun t => Y t ω) →
  U4 R.ℱ R.μ (fun s ω => g025 (Y s ω)) ∧
  (∀ᵐ ω ∂R.μ, ∀ t, v025 (Y t ω) = 2 +
    (∫ s in (0:ℝ)..(t:ℝ), h025 lam (Y (Real.toNNReal s) ω)) +
    R.I k (fun s ω => g025 (Y s ω)) t ω)

def densityStatement : Prop := ∀ z : ℝ,
  (a025 z)^2 = v025 z ∧ (g025 z)^2 = (1-(Real.tanh z)^2)^2*v025 z ∧
  0 < (g025 z)^2 ∧ (g025 z)^2 ≤ 4

def covariationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_P : Predictability S.ℱ) (k : Fin S.m),
  (∀ t, S.c k k t = 1) → ∀ Y : ℝ≥0 → Ω → ℝ,
  Adapted S.ℱ Y → (∀ ω, Continuous fun t => Y t ω) → ∀ tau : ℝ≥0,
  Martingale (fun t ω => (S.I k (fun s ω => a025 (Y s ω)) (min t tau) ω)^2 -
    ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), v025 (Y (Real.toNNReal s) ω)) S.ℱ S.μ ∧
  Martingale (fun t ω => (S.I k (fun s ω => g025 (Y s ω)) (min t tau) ω)^2 -
    ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ),
      (1-(Real.tanh (Y (Real.toNNReal s) ω))^2)^2*v025 (Y (Real.toNNReal s) ω)) S.ℱ S.μ

def transferStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_D : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation R)
  (_P : Predictability S.ℱ) (_Q : Predictability R.ℱ) (k : Fin S.m) (l : Fin R.m),
  (∀ j, j = l) → R.μ = S.μ → S.B k = R.B l → (∀ t, R.ℱ t ≤ S.ℱ t) →
  (∀ t, R.c l l t = 1) → ∀ lam : ℝ, 0 < lam →
  ∀ Y : ℝ≥0 → Ω → ℝ, ScalarSolution025 R l lam Y →
  (∀ ω, Continuous fun t => Y t ω) →
  U4 S.ℱ S.μ (fun s ω => g025 (Y s ω)) ∧
  (∀ᵐ ω ∂S.μ, ∀ t, v025 (Y t ω) = 2 +
    (∫ s in (0:ℝ)..(t:ℝ), h025 lam (Y (Real.toNNReal s) ω)) +
    S.I k (fun s ω => g025 (Y s ω)) t ω)

def derivativeStatement : Prop := ∀ (Y : ℝ → ℝ), Continuous Y → ∀ tau t : ℝ, t < tau →
  HasDerivAt (fun u => ∫ s in (0:ℝ)..min u tau, v025 (Y s)) (v025 (Y t)) t ∧
  HasDerivAt (fun u => ∫ s in (0:ℝ)..min u tau,
    (1-(Real.tanh (Y s))^2)^2*v025 (Y s)) ((1-(Real.tanh (Y t))^2)^2*v025 (Y t)) t ∧
  0 < (1-(Real.tanh (Y t))^2)^2*v025 (Y t)

def statement : Prop := itoStatement ∧ densityStatement ∧ covariationStatement ∧
  transferStatement ∧ derivativeStatement

end Standalone.BoundedVarianceIto

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic

/-! # Claim 025: analytic and algebraic components

This partial target proves the coefficient bounds, three-exponent curve algebra,
HJM and bond-drift cancellations, coefficient recovery and deterministic scheduled
breakpoint. It also proves the actual bond/discounting formulas, their deterministic
bound on the time integral, and the nonzero-jump deduction conditional on the scalar SDE identity and
independence from the other Brownian driver. SDE existence, that independence for the actual
integral, and true bond martingales still require the inputs recorded in the claim.
-/

open Matrix MeasureTheory
open scoped NNReal
namespace Standalone.BoundedVarianceState

noncomputable def v025 (z : ℝ) : ℝ := 2 + Real.tanh z
noncomputable def b025 (lam z : ℝ) : ℝ := Real.tanh z / (2 * lam)
noncomputable def a025 (z : ℝ) : ℝ := Real.sqrt (v025 z)
noncomputable def e025 (lam k x : ℝ) : ℝ := Real.exp (-k * lam * x)
noncomputable def A025 (lam k x : ℝ) : ℝ := (1 - e025 lam k x) / (k * lam)
noncomputable def f025 (lam tau : ℝ) (z : Fin 3 → ℝ) (T : ℝ) : ℝ :=
  if T < tau then 0 else
    z 0 * e025 lam 1 (T-tau) + z 1 * e025 lam 2 (T-tau) + z 2 * e025 lam 4 (T-tau)

noncomputable def M025 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; 1/2, 1/4, 1/16; 1/4, 1/16, 1/256]

/-- Bounds and derivatives for the scalar equation, its variance state and inverse. -/
def coefficientStatement : Prop := ∀ lam : ℝ, 0 < lam →
  (∀ z, 1 < v025 z ∧ v025 z < 3 ∧
    |b025 lam z| ≤ 1/(2*lam) ∧ 1 < a025 z ∧ a025 z < Real.sqrt 3 ∧
    HasDerivAt (b025 lam) ((1-Real.tanh z ^ 2)/(2*lam)) z ∧
    HasDerivAt a025 ((1-Real.tanh z ^ 2)/(2*a025 z)) z ∧
    0 < (1-Real.tanh z ^ 2)^2 * v025 z ∧
    z = (1/2:ℝ) * Real.log ((v025 z-1)/(3-v025 z))) ∧
  (∀ x y, |b025 lam x-b025 lam y| ≤ (1/(2*lam))*|x-y|) ∧
  (∀ x y, |a025 x-a025 y| ≤ (1/2:ℝ)*|x-y|)

/-- The bounded exponential shapes and their exact maturity primitives. -/
def shapeStatement : Prop := ∀ lam k : ℝ, 0 < lam → 0 < k →
  (∀ x, HasDerivAt (A025 lam k) (e025 lam k x) x) ∧
  A025 lam k 0 = 0 ∧
  (∀ x, 0 ≤ x → 0 < e025 lam k x ∧ e025 lam k x ≤ 1 ∧
    0 ≤ A025 lam k x ∧ A025 lam k x ≤ 1/(k*lam) ∧
    (∫ u in (0:ℝ)..x, e025 lam k u) = A025 lam k x)

/-- Fixed-maturity HJM drift, integrated bond drift and the uniform bound on the
squared bond-volatility coefficient. These are algebraic identities, not a martingale theorem. -/
def driftStatement : Prop := ∀ lam v x : ℝ, 0 < lam → 0 ≤ v →
  e025 lam 1 x / lam + (v-2)*e025 lam 2 x/(2*lam) - v*e025 lam 4 x/(2*lam) =
    e025 lam 1 x * A025 lam 1 x +
      (Real.sqrt v * e025 lam 2 x) * (Real.sqrt v * A025 lam 2 x) ∧
  A025 lam 1 x / lam + (v-2)*A025 lam 2 x/(2*lam) - v*A025 lam 4 x/(2*lam) =
    (1/2:ℝ) * ((A025 lam 1 x)^2 + v*(A025 lam 2 x)^2) ∧
  1/lam + (v-2)/(2*lam) - v/(2*lam) = 0 ∧
  (0 ≤ x → v ≤ 3 → (A025 lam 1 x)^2 + v*(A025 lam 2 x)^2 ≤ 7/(4*lam^2))

/-- Boundedness is pointwise in the coefficient vector; the breakpoint has its right value. -/
def curveStatement : Prop := ∀ lam tau : ℝ, 0 ≤ lam → ∀ z : Fin 3 → ℝ,
  (∀ T, |f025 lam tau z T| ≤ |z 0|+|z 1|+|z 2|) ∧
  (∀ T, T < tau → f025 lam tau z T = 0) ∧
  f025 lam tau z tau = z 0+z 1+z 2 ∧
  (∀ x, z 0*e025 lam 1 x + z 1*e025 lam 2 x =
    (z 0+z 1)*e025 lam 1 x - z 1*(e025 lam 1 x-e025 lam 2 x))

/-- The three stated maturities recover the curve coefficients and thus the variance state. -/
def recoveryStatement : Prop := ∀ lam tau : ℝ, 0 < lam →
  M025.det = -(21/1024:ℝ) ∧
  (∀ z : Fin 3 → ℝ,
    (fun i : Fin 3 => f025 lam tau z (tau+(i:ℕ)*Real.log 2/lam)) = M025.mulVec z) ∧
  Function.Injective (fun z : Fin 3 → ℝ =>
    fun i : Fin 3 => f025 lam tau z (tau+(i:ℕ)*Real.log 2/lam))

/-- With any continuous coordinates stopped at the fixed date, fixed-maturity curves
are continuous and frozen after the date, while the short rate has left limit zero. -/
def pathStatement : Prop := ∀ lam tau : ℝ, ∀ Z : ℝ → Fin 3 → ℝ,
  (∀ i, Continuous fun t => Z t i) →
  (∀ T, Continuous fun t => f025 lam tau (Z (min t tau)) T) ∧
  (∀ T t, tau ≤ t → f025 lam tau (Z (min t tau)) T = f025 lam tau (Z tau) T) ∧
  Filter.Tendsto (fun t => f025 lam tau (Z (min t tau)) t) (nhdsWithin tau (Set.Iio tau)) (nhds 0) ∧
  f025 lam tau (Z (min tau tau)) tau = Z tau 0+Z tau 1+Z tau 2

/-- The integrated three-exponent curve to the right of its breakpoint. -/
noncomputable def L025 (lam : ℝ) (z : Fin 3 → ℝ) (x : ℝ) : ℝ :=
  z 0*A025 lam 1 x + z 1*A025 lam 2 x + z 2*A025 lam 4 x

/-- The actual maturity-integral bond and time-integral bank account for stopped coordinates. -/
noncomputable def P025 (lam tau : ℝ) (Z : ℝ → Fin 3 → ℝ) (t T : ℝ) : ℝ :=
  Real.exp (-(∫ u in t..T, f025 lam tau (Z (min t tau)) u))
noncomputable def B025 (lam tau : ℝ) (Z : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ u in (0:ℝ)..t, f025 lam tau (Z (min u tau)) u)

/-- Actual bond and discounting formulas in all time regimes. This is pathwise calculus;
it does not assert a martingale property. -/
def bondStatement : Prop := ∀ lam tau : ℝ, 0 < lam → 0 < tau →
  ∀ Z : ℝ → Fin 3 → ℝ, ∀ t T : ℝ, 0 ≤ t → t ≤ T →
    0 < P025 lam tau Z t T ∧ 0 < B025 lam tau Z t ∧
    (T ≤ tau → P025 lam tau Z t T / B025 lam tau Z t = 1) ∧
    (t ≤ tau → tau ≤ T → P025 lam tau Z t T / B025 lam tau Z t =
      Real.exp (-L025 lam (Z t) (T-tau))) ∧
    (tau ≤ t → P025 lam tau Z t T =
      Real.exp (L025 lam (Z tau) (t-tau)-L025 lam (Z tau) (T-tau)) ∧
      P025 lam tau Z t T / B025 lam tau Z t = Real.exp (-L025 lam (Z tau) (T-tau))) ∧
    P025 lam tau Z T T = 1 ∧
    (Z 0 = 0 → P025 lam tau Z 0 T = 1)

/-- The deterministic time-integral bound used for the stochastic exponential.
Identifying this integral with quadratic variation is a separate stochastic step. -/
def integralBoundStatement : Prop := ∀ lam tau x : ℝ, 0 < lam → 0 ≤ tau → 0 ≤ x →
  ∀ Y : ℝ → ℝ, Continuous Y → ∀ t : ℝ, 0 ≤ t →
    (∫ s in (0:ℝ)..(min t tau), (A025 lam 1 x)^2 + v025 (Y s)*(A025 lam 2 x)^2) ≤
      7*tau/(4*lam^2)

open ProbabilityTheory in
/-- The nonzero-jump deduction for the given scalar SDE at the meeting. Existence of
that scalar solution and independence of its integral from the other driver are explicit
premises here; neither is asserted to follow from the analytic components. -/
def scheduledJumpStatement : Prop :=
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (W : ℝ≥0 → Ω → ℝ), IsBrownianReal W μ →
  ∀ (lam : ℝ) (tau : ℝ≥0), 0 < lam → 0 < tau →
  ∀ (Y : ℝ → Ω → ℝ) (J : Ω → ℝ),
    (∀ᵐ ω ∂μ, Continuous fun s => Y s ω) → AEMeasurable J μ →
    IndepFun (W tau) J μ →
    (∀ᵐ ω ∂μ, Y tau ω = (∫ s in (0:ℝ)..tau, b025 lam (Y s ω)) + J ω) →
  let z := fun ω => ![(tau:ℝ)/lam + W tau ω, Y tau ω,
    -(∫ s in (0:ℝ)..tau, v025 (Y s ω)/(2*lam))]
  (∀ᵐ ω ∂μ, f025 lam tau (z ω) tau = W tau ω + J ω) ∧
  (∀ᵐ ω ∂μ, f025 lam tau (z ω) tau ≠ 0)

def statement : Prop := coefficientStatement ∧ shapeStatement ∧ driftStatement ∧
  curveStatement ∧ recoveryStatement ∧ pathStatement ∧ bondStatement ∧ integralBoundStatement ∧ scheduledJumpStatement

end Standalone.BoundedVarianceState

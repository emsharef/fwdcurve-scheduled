import Standalone.BoundedVarianceIntegralComparison

/-! # Claim 025: scalar strong existence and uniqueness

AX-06 is restated verbatim over the standalone calculus structure. The target
applies it to the claim's coefficients, without assuming a solution exists.
The probability basis and its single Brownian driver remain supplied.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.BoundedVarianceState
namespace Standalone.BoundedVarianceExistence

/-- The Brownian-vector premises in AX-06, relative to the supplied filtration. -/
def BrownianDrivers6 {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop :=
  (∀ k, IsBrownianReal (h.B k) h.μ) ∧
  (∀ s t : ℝ≥0, s ≤ t →
    iIndepFun (fun k ω => h.B k t ω - h.B k s ω) h.μ) ∧
  (∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω (k : Fin h.m) => h.B k t ω - h.B k s ω)
      inferInstance) (h.ℱ s) h.μ) ∧
  (∀ k l t, h.c k l t = if k = l then 1 else 0)

/-- Borel coefficients, a uniform global Lipschitz constant, and local bounds. -/
def Coefficients6 {m n : ℕ} (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ)
    (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin m → ℝ) : Prop :=
  Measurable b ∧ Measurable σ ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ t x y,
    ‖b (t,x) - b (t,y)‖ ≤ K * ‖x-y‖ ∧
    ‖σ (t,x) - σ (t,y)‖ ≤ K * ‖x-y‖) ∧
  (∀ T : ℝ≥0, ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, t ≤ T → ∀ x, ‖x‖ ≤ R → ‖b (t,x)‖ ≤ C ∧ ‖σ (t,x)‖ ≤ C)

/-- The solution class with the given integral operator and initial random vector. -/
def Solution6 {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) {n : ℕ}
    (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ)
    (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin h.m → ℝ)
    (ξ : Ω → Fin n → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  Adapted h.ℱ X ∧ (∀ᵐ ω ∂h.μ, Continuous fun t => X t ω) ∧
  (∀ i k, U4 h.ℱ h.μ (fun t ω => σ (t, X t ω) i k)) ∧
  (∀ i, LocallyIntegrableDrift h.ℱ h.μ (fun t ω => b (t, X t ω) i)) ∧
  (∀ᵐ ω ∂h.μ, ∀ t i, X t ω i = ξ ω i +
    (∑ k, h.I k (fun s ω => σ (s, X s ω) i k) t ω) +
    ∫ s in (0:ℝ)..(t:ℝ), b (Real.toNNReal s, X (Real.toNNReal s) ω) i)

/-- The two published AX-06 conclusions over an existing calculus structure. -/
structure LipschitzSDE {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop where
  lipschitz_existence : BrownianDrivers6 h → ∀ (n : ℕ)
    (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ)
    (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin h.m → ℝ),
    Coefficients6 b σ → ∀ x : Fin n → ℝ,
    ∃ X : ℝ≥0 → Ω → Fin n → ℝ, Solution6 h b σ (fun _ => x) X
  lipschitz_uniqueness : BrownianDrivers6 h → ∀ (n : ℕ)
    (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ)
    (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin h.m → ℝ),
    Coefficients6 b σ → ∀ X X' : ℝ≥0 → Ω → Fin n → ℝ,
    Solution6 h b σ (X 0) X → Solution6 h b σ (X' 0) X' →
    X 0 =ᵐ[h.μ] X' 0 → ∀ᵐ ω ∂h.μ, ∀ t, X t ω = X' t ω


noncomputable def drift025 (lam : ℝ) (p : ℝ≥0 × (Fin 1 → ℝ)) : Fin 1 → ℝ :=
  fun _ => b025 lam (p.2 0)

noncomputable def diffusion025 (m : ℕ) (p : ℝ≥0 × (Fin 1 → ℝ)) : Fin 1 → Fin m → ℝ :=
  fun _ _ => a025 (p.2 0)

/-- The zero-initial scalar equation on a supplied single-driver basis. -/
def ScalarSolution025 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted S.ℱ Y ∧ (∀ᵐ ω ∂S.μ, Continuous fun t => Y t ω) ∧
  U4 S.ℱ S.μ (fun t ω => a025 (Y t ω)) ∧
  LocallyIntegrableDrift S.ℱ S.μ (fun t ω => b025 lam (Y t ω)) ∧
  (∀ᵐ ω ∂S.μ, ∀ t, Y t ω = S.I k (fun s ω => a025 (Y s ω)) t ω +
    ∫ s in (0:ℝ)..(t:ℝ), b025 lam (Y (Real.toNNReal s) ω))

def coefficientStatement : Prop := ∀ lam : ℝ, 0 < lam → ∀ m : ℕ,
  Coefficients6 (drift025 lam) (diffusion025 m)

def existenceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_E : LipschitzSDE S), BrownianDrivers6 S →
  ∀ k : Fin S.m, (∀ j, j = k) → ∀ lam : ℝ, 0 < lam →
  ∃ Y : ℝ≥0 → Ω → ℝ, ScalarSolution025 S k lam Y

def uniquenessStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_E : LipschitzSDE S), BrownianDrivers6 S →
  ∀ k : Fin S.m, (∀ j, j = k) → ∀ lam : ℝ, 0 < lam →
  ∀ Y Y' : ℝ≥0 → Ω → ℝ, ScalarSolution025 S k lam Y → ScalarSolution025 S k lam Y' →
  ∀ᵐ ω ∂S.μ, ∀ t, Y t ω = Y' t ω

/-- The almost-sure solution admits an everywhere-continuous adapted version
with zero initial value everywhere, satisfying the same scalar integral equation. -/
def versionStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_P : Standalone.BoundedVarianceMartingale.Predictability S.ℱ)
  (k : Fin S.m) (lam : ℝ), 0 < lam → ∀ Y : ℝ≥0 → Ω → ℝ,
  ScalarSolution025 S k lam Y → ∃ Y' : ℝ≥0 → Ω → ℝ,
    ScalarSolution025 S k lam Y' ∧ (∀ ω, Continuous fun t => Y' t ω) ∧
    (∀ ω, Y' 0 ω = 0) ∧ (∀ᵐ ω ∂S.μ, ∀ t, Y' t ω = Y t ω)

/-- Construct in the smaller single-driver filtration, then derive the same
scalar equation in a supplied larger filtration using AX-11. -/
def transferStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω) (_E : LipschitzSDE R)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_D : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation R)
  (_P : Standalone.BoundedVarianceMartingale.Predictability S.ℱ)
  (_Q : Standalone.BoundedVarianceMartingale.Predictability R.ℱ),
  BrownianDrivers6 R → ∀ (k : Fin S.m) (l : Fin R.m), (∀ j, j = l) →
  R.μ = S.μ → S.B k = R.B l → (∀ t, R.ℱ t ≤ S.ℱ t) →
  ∀ lam : ℝ, 0 < lam → ∃ Y : ℝ≥0 → Ω → ℝ,
    ScalarSolution025 R l lam Y ∧ ScalarSolution025 S k lam Y ∧
    (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0)

def statement : Prop := coefficientStatement ∧ existenceStatement ∧ uniquenessStatement ∧
  versionStatement ∧ transferStatement

end Standalone.BoundedVarianceExistence

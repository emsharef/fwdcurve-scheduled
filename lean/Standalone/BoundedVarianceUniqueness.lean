import Standalone.BoundedVarianceExistence

/-! # Claim 025: uniqueness for the stopped equation in the joint filtration -/
open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
namespace Standalone.BoundedVarianceUniqueness

noncomputable def b025Stopped (lam : ℝ) (tau : ℝ≥0)
    (p : ℝ≥0 × (Fin 1 → ℝ)) : Fin 1 → ℝ :=
  if p.1 ≤ tau then drift025 lam p else 0
noncomputable def a025Stopped {m : ℕ} (k : Fin m) (tau : ℝ≥0)
    (p : ℝ≥0 × (Fin 1 → ℝ)) : Fin 1 → Fin m → ℝ :=
  fun _ j => if p.1 ≤ tau ∧ j = k then a025 (p.2 0) else 0

def stoppedStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_P : Predictability S.ℱ) (k : Fin S.m)
  (lam : ℝ), 0 < lam → ∀ tau : ℝ≥0, ∀ Y : ℝ≥0 → Ω → ℝ,
  ScalarSolution025 S k lam Y → (∀ ω, Continuous fun t => Y t ω) →
  Solution6 S (b025Stopped lam tau) (a025Stopped k tau) (fun _ _ => 0)
    (fun t ω (_ : Fin 1) => Y (min t tau) ω)

def uniquenessStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_E : LipschitzSDE S), BrownianDrivers6 S →
  ∀ (k : Fin S.m) (lam : ℝ), 0 < lam → ∀ tau : ℝ≥0,
  ∀ X X' : ℝ≥0 → Ω → Fin 1 → ℝ,
  Solution6 S (b025Stopped lam tau) (a025Stopped k tau) (fun _ _ => 0) X →
  Solution6 S (b025Stopped lam tau) (a025Stopped k tau) (fun _ _ => 0) X' →
  ∀ᵐ ω ∂S.μ, ∀ t, X t ω = X' t ω

def statement : Prop := stoppedStatement ∧ uniquenessStatement

end Standalone.BoundedVarianceUniqueness

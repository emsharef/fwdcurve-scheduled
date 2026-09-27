import Standalone.BoundedVarianceExistence

/-! # Claim 025: independence of the noise integral and the constructed jump

The explicit filtration bound uses the second driver's entire path sigma-algebra
augmented by ambient null sets. A completed natural filtration satisfies this
bound; identification of the supplied filtration remains a basis premise.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence
namespace Standalone.BoundedVarianceIndependence

/-- The second path's sigma-algebra augmented by all ambient null sets. -/
@[instance_reducible]
def m025 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (V : ℝ≥0 → Ω → ℝ) :
    MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {s | MeasurableSet[MeasurableSpace.comap
    (fun ω t => V t ω) inferInstance] s ∨ μ s = 0}

/-- The right-continuous augmentation of the raw natural filtration, as
sigma-algebras; containment in the ambient measurable space is not asserted here. -/
@[instance_reducible]
def n025 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (V : ℝ≥0 → Ω → ℝ)
    (hV : ∀ t, StronglyMeasurable (V t)) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨅ u, ⨅ (_ : t < u), MeasurableSpace.generateFrom
    {s | MeasurableSet[Filtration.natural V hV u] s ∨ μ s = 0}

def filtrationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (μ : Measure Ω) (V : ℝ≥0 → Ω → ℝ) (hV : ∀ t, StronglyMeasurable (V t))
  (t : ℝ≥0), n025 μ V hV t ≤ m025 μ V

def independenceStatement : Prop := ∀ (Ω : Type) (m _mΩ : MeasurableSpace Ω)
  (μ : Measure Ω) (W V : ℝ≥0 → Ω → ℝ),
  IndepFun (fun ω t => W t ω) (fun ω t => V t ω) μ →
  ∀ tau : ℝ≥0, m ≤ m025 μ V →
  ∀ J : Ω → ℝ, Measurable[m] J → IndepFun (W tau) J μ

noncomputable def z025 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i : Fin S.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) (tau : ℝ≥0) (ω : Ω) : Fin 3 → ℝ :=
  ![(tau:ℝ)/lam + S.B i tau ω, Y tau ω,
    -(∫ s in (0:ℝ)..(tau:ℝ), v025 (Y (Real.toNNReal s) ω)/(2*lam))]

def jumpStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω) (_E : LipschitzSDE R)
  (_A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
  (_D : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation R)
  (_P : Standalone.BoundedVarianceMartingale.Predictability S.ℱ)
  (_Q : Standalone.BoundedVarianceMartingale.Predictability R.ℱ),
  BrownianDrivers6 R → ∀ (i k : Fin S.m) (l : Fin R.m), (∀ j, j = l) →
  R.μ = S.μ → S.B k = R.B l → (∀ t, R.ℱ t ≤ S.ℱ t) →
  IsBrownianReal (S.B i) S.μ →
  IndepFun (fun ω t => S.B i t ω) (fun ω t => R.B l t ω) S.μ →
  (∀ t, R.ℱ t ≤ m025 S.μ (R.B l)) →
  ∀ lam : ℝ, 0 < lam → ∃ Y : ℝ≥0 → Ω → ℝ,
    ScalarSolution025 R l lam Y ∧ ScalarSolution025 S k lam Y ∧
    (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) ∧
    ∀ tau : ℝ≥0, 0 < tau →
      IndepFun (S.B i tau) (S.I k (fun s ω => a025 (Y s ω)) tau) S.μ ∧
      (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S i lam Y tau ω) tau =
        S.B i tau ω + S.I k (fun s ω => a025 (Y s ω)) tau ω) ∧
      (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S i lam Y tau ω) tau ≠ 0)

def statement : Prop := filtrationStatement ∧ independenceStatement ∧ jumpStatement

end Standalone.BoundedVarianceIndependence

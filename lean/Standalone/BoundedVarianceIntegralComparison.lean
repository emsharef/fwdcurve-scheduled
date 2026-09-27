import Standalone.BoundedVarianceMartingale
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Claim 025: comparison of the natural- and joint-filtration integrals

AX-11 is restated verbatim over the existing standalone calculus interface.
The target compares the two limits of the same sums for a common measure,
driver and integrand. The calculus structures and the required domain premises
are supplied; the target does not construct the strong solution or filtrations.
-/

open MeasureTheory Filter
open scoped NNReal Topology
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.BoundedVarianceState Standalone.BoundedVarianceMartingale
namespace Standalone.BoundedVarianceIntegralComparison

/-- The exact finite sum (AX-11.2), with nonnegative-real grid points (AX-11.1). -/
noncomputable def leftEndpoint11 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (k : Fin h.m) (H : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n),
    H ((i : ℝ≥0) * T / (2 : ℝ≥0)^n) ω *
      (h.B k (((i + 1 : ℕ) : ℝ≥0) * T / (2 : ℝ≥0)^n) ω -
        h.B k ((i : ℝ≥0) * T / (2 : ℝ≥0)^n) ω)

/-- The sole published input AX-11, over the existing calculus interface. -/
structure IntegralApproximation {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) : Prop where
  left_endpoint_tendstoInMeasure : ∀ (k : Fin h.m) (H : ℝ≥0 → Ω → ℝ),
    Adapted h.ℱ H → (∀ ω, Continuous fun t => H t ω) →
    (∃ K : ℝ, 0 ≤ K ∧ ∀ t ω, |H t ω| ≤ K) → U4 h.ℱ h.μ H →
    ∀ T : ℝ≥0,
      TendstoInMeasure h.μ (fun n => leftEndpoint11 h k H n T) atTop (h.I k H T)

/-- Two admissible integrals of the same process against the same driver agree
outside one null set at every nonnegative time, even if the filtrations differ. -/
def comparisonStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω) (_A : IntegralApproximation S) (_D : IntegralApproximation R)
  (k : Fin S.m) (l : Fin R.m), R.μ = S.μ → S.B k = R.B l →
  ∀ H : ℝ≥0 → Ω → ℝ, Adapted S.ℱ H → Adapted R.ℱ H →
  (∀ ω, Continuous fun t => H t ω) →
  (∃ K : ℝ, 0 ≤ K ∧ ∀ t ω, |H t ω| ≤ K) →
  U4 S.ℱ S.μ H → U4 R.ℱ R.μ H →
  ∀ᵐ ω ∂S.μ, ∀ t, S.I k H t ω = R.I l H t ω

/-- The comparison for Claim 025's bounded diffusion coefficient. AX-09 supplies
predictability in each filtration from the given adapted continuous coordinate. -/
def coefficientStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S R : ItoCalculus Ω) (_A : IntegralApproximation S) (_D : IntegralApproximation R)
  (_P : Predictability S.ℱ) (_Q : Predictability R.ℱ)
  (k : Fin S.m) (l : Fin R.m), R.μ = S.μ → S.B k = R.B l →
  ∀ Y : ℝ≥0 → Ω → ℝ,
  (∀ t, Measurable[S.ℱ t] (Y t)) → (∀ t, Measurable[R.ℱ t] (Y t)) →
  (∀ ω, Continuous fun t => Y t ω) →
  ∀ᵐ ω ∂S.μ, ∀ t,
    S.I k (fun s ω => a025 (Y s ω)) t ω = R.I l (fun s ω => a025 (Y s ω)) t ω

/-- The constant-integrand identity needed for Claim 025's first coordinate. -/
def constantStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_A : IntegralApproximation S) (k : Fin S.m),
  ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun _ _ => 1) t ω = S.B k t ω

def statement : Prop := comparisonStatement ∧ coefficientStatement ∧ constantStatement

end Standalone.BoundedVarianceIntegralComparison

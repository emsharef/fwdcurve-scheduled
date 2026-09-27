import Standalone.BoundedVarianceState
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 025: the bounded stochastic exponential

AX-09 and AX-10 are restated over the existing standalone calculus interface.
The target proves its integrand-domain and deterministic-bound premises for
Claim 025's two bond-volatility coefficients. Predictability and path continuity
of the supplied variance coordinate are explicit premises; existence of that
coordinate and identification with the discounted bond remain separate steps.
-/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.BoundedVarianceState
namespace Standalone.BoundedVarianceMartingale

/-- AX-10.2, with the same real-time integration convention as AX-03 to AX-05. -/
noncomputable def quadraticVariation10 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (H : Fin h.m → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
    H k (Real.toNNReal s) ω * H l (Real.toNNReal s) ω * h.c k l (Real.toNNReal s)

/-- AX-10.3, including stopping of the integral and its quadratic variation. -/
noncomputable def exponential10 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (H : Fin h.m → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((∑ k, h.I k (H k) (min t T) ω) -
    (1 / 2 : ℝ) * quadraticVariation10 h H T t ω)

/-- The single published input AX-10, separate from the existing calculus interface. -/
structure ExponentialMartingale {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) : Prop where
  bounded_qv_exponential_martingale :
    ∀ (H : Fin h.m → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (C : ℝ),
      (∀ k, U4 h.ℱ h.μ (H k)) → 0 ≤ C →
      (∀ᵐ ω ∂h.μ, quadraticVariation10 h H T T ω ≤ C) →
      Martingale (exponential10 h H T) h.ℱ h.μ

/-- The two nonzero bond-volatility coefficients, embedded in the driver vector. -/
noncomputable def H025 {Ω : Type*} {m : ℕ} (i j : Fin m) (lam x : ℝ)
    (Y : ℝ → Ω → ℝ) (k : Fin m) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if k = i then -A025 lam 1 x else
    if k = j then -a025 (Y t ω) * A025 lam 2 x else 0

/-- The actual integral-domain and covariance-sum premises of AX-10, and its
martingale conclusion. This asserts neither SDE existence nor a price identity. -/
def predictableStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_E : ExponentialMartingale S)
  (i j : Fin S.m), i ≠ j →
  (∀ k l t, S.c k l t = if k = l then 1 else 0) →
  ∀ (lam x : ℝ) (tau : ℝ≥0), 0 < lam → 0 ≤ x →
  ∀ Y : ℝ → Ω → ℝ,
  IsStronglyPredictable S.ℱ (fun t ω => a025 (Y t ω)) →
  (∀ᵐ ω ∂S.μ, Continuous fun s => Y s ω) →
  (∀ k, U4 S.ℱ S.μ (H025 i j lam x Y k)) ∧
  (∀ᵐ ω ∂S.μ, ∀ t,
    quadraticVariation10 S (H025 i j lam x Y) tau t ω =
      ∫ s in (0:ℝ)..((min t tau : ℝ≥0):ℝ),
        (A025 lam 1 x)^2 + v025 (Y s ω)*(A025 lam 2 x)^2) ∧
  (∀ᵐ ω ∂S.μ, ∀ t,
    quadraticVariation10 S (H025 i j lam x Y) tau t ω ≤ 7*tau/(4*lam^2)) ∧
  Martingale (exponential10 S (H025 i j lam x Y) tau) S.ℱ S.μ

/-- The already audited continuous-process specialization AX-09. -/
structure Predictability {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) : Prop where
  continuous_predictable : ∀ (X : ℝ≥0 → Ω → ℝ),
    (∀ t, Measurable[ℱ t] (X t)) → (∀ ω, Continuous fun t => X t ω) →
    IsStronglyPredictable ℱ X

/-- AX-09 supplies the preceding predictability premise for any given everywhere
continuous adapted coordinate. This does not construct the SDE solution. -/
def adaptedStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (_E : ExponentialMartingale S) (_P : Predictability S.ℱ)
  (i j : Fin S.m), i ≠ j →
  (∀ k l t, S.c k l t = if k = l then 1 else 0) →
  ∀ (lam x : ℝ) (tau : ℝ≥0), 0 < lam → 0 ≤ x →
  ∀ Y : ℝ → Ω → ℝ,
  (∀ t : ℝ≥0, Measurable[S.ℱ t] (Y t)) →
  (∀ ω, Continuous fun s => Y s ω) →
  (∀ k, U4 S.ℱ S.μ (H025 i j lam x Y k)) ∧
  Martingale (exponential10 S (H025 i j lam x Y) tau) S.ℱ S.μ

def statement : Prop := predictableStatement ∧ adaptedStatement

end Standalone.BoundedVarianceMartingale

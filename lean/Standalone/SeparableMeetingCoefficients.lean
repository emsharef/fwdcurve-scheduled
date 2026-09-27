import Standalone.SeparableMeetingShapes
import Standalone.SeparableMeetingIntegrals

/-! # Claim 026: coefficients built from predictable scales

Ordinary integrals use the same masked scale as the stochastic integral. The
finite-energy premise is (U4), without any expected-energy assumption.
-/
open MeasureTheory ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open scoped NNReal
namespace Standalone.SeparableMeetingCoefficients

noncomputable def D026 {Ω : Type*} (H : ℝ≥0 → Ω → ℝ) (G : ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ := ∫ s in (0:ℝ)..t, H (Real.toNNReal s) ω ^ 2 * G s

noncomputable def M0262 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0) (G : ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  J026 S k chi lo hi (Real.toNNReal t) ω - D026 (H026 chi lo hi) G t ω

def ordinaryStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (H : ℝ≥0 → Ω → ℝ), U4 S.ℱ S.μ H →
  ∀ (G : ℝ → ℝ), Continuous G →
  (∀ t : ℝ≥0, Measurable[S.ℱ t] (D026 H G t)) ∧
  (∀ T : ℝ≥0, ∀ᵐ ω ∂S.μ,
    IntervalIntegrable (fun s => H (Real.toNNReal s) ω ^ 2 * G s) volume 0 T ∧
    ContinuousOn (fun t => D026 H G t ω) (Set.Icc (0:ℝ) T) ∧
    BoundedVariationOn (fun t => D026 H G t ω) (Set.Icc (0:ℝ) T))

def coefficientStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0),
  lo ≤ hi → U4 S.ℱ S.μ chi → ∀ (G : ℝ → ℝ), Continuous G →
  (∀ t : ℝ≥0, Measurable[S.ℱ t] (M0262 S k chi lo hi G t)) ∧
  (∀ T : ℝ≥0, ∀ᵐ ω ∂S.μ,
    ContinuousOn (fun t => M0262 S k chi lo hi G t ω) (Set.Icc (0:ℝ) T)) ∧
  (∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    (t ≤ lo → M0262 S k chi lo hi G t ω = 0) ∧
    (hi ≤ t → M0262 S k chi lo hi G t ω = M0262 S k chi lo hi G hi ω))

def varianceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (n : ℕ) (H : Fin n → ℝ≥0 → Ω → ℝ)
  (a : Fin n → ℝ), (∀ k, U4 S.ℱ S.μ (H k)) → ∀ T : ℝ≥0,
  ∀ᵐ ω ∂S.μ,
  let V := fun t => ∑ k, a k ^ 2 * D026 (H k) (fun _ => 1) t ω
  V 0 = 0 ∧ (∀ t, 0 ≤ t → 0 ≤ V t) ∧
  MonotoneOn V (Set.Icc (0:ℝ) T) ∧ ContinuousOn V (Set.Icc (0:ℝ) T) ∧
  BoundedVariationOn V (Set.Icc (0:ℝ) T) ∧
  (∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Icc (0:ℝ) T →
    HasDerivAt V (∑ k, a k ^ 2 * H k (Real.toNNReal t) ω ^ 2) t)

def statement : Prop := ordinaryStatement ∧ coefficientStatement ∧ varianceStatement
end Standalone.SeparableMeetingCoefficients

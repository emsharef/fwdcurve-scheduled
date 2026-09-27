import Standalone.SeparableMeetingMarkovProperty

/-! # Claim 028 (b), (c): several times

`severalStatement` is the general step: for an adapted process with the
single-time Markov property of (28.5), for every deterministic `s` and times
`t_1, ..., t_r ≥ s` (in any order) and every bounded Borel `F` of
`(X_{t_1}, ..., X_{t_r})`, the conditional expectation given `ℱ s` is almost
surely a Borel function of `X_s`. `markovStatement` applies it to the frozen
state `X^H` of (a), whose single-time property is (b) at one time, and
`curveStatement` is (c) for finitely many curve values `Lambda028 (X^H_{t_i}) T_i`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization Standalone.SeparableMeetingMarkovSolution
open Standalone.SeparableMeetingMarkovProperty
namespace Standalone.SeparableMeetingMarkovSeveral

def severalStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (ℱ : Filtration ℝ≥0 _mΩ) (n : ℕ) (X : ℝ≥0 → Ω → Fin n → ℝ),
  (∀ t, Measurable[ℱ t] (X t)) →
  (∀ s t : ℝ≥0, s ≤ t → ∀ f : (Fin n → ℝ) → ℝ, BoundedBorel13 f →
    μ[f ∘ X t | ℱ s] =ᵐ[μ] μ[f ∘ X t | MeasurableSpace.comap (X s) inferInstance]) →
  ∀ (r : ℕ) (s : ℝ≥0) (t : Fin r → ℝ≥0), (∀ i, s ≤ t i) →
  ∀ F : (Fin r → Fin n → ℝ) → ℝ, Measurable F → (∃ C, ∀ x, |F x| ≤ C) →
    ∃ g : (Fin n → ℝ) → ℝ, Measurable g ∧
      μ[fun ω => F (fun i => X (t i) ω) | ℱ s] =ᵐ[μ] g ∘ X s

/-- (b), several times, for the frozen state. -/
def markovStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → MarkovTime S → BrownianDrivers6 S →
  ∀ (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ),
  Setting028 S p d N Td Hor beta Sigma psi g z0 Z →
  ∀ (r : ℕ) (s : ℝ≥0) (t : Fin r → ℝ≥0), (∀ i, s ≤ t i) →
  ∀ F : (Fin r → Fin (dim028 p d N) → ℝ) → ℝ, Measurable F → (∃ C, ∀ x, |F x| ≤ C) →
    ∃ gts : (Fin (dim028 p d N) → ℝ) → ℝ, Measurable gts ∧
      S.μ[fun ω => F (fun i => XH028 S drv Td Hor psi g Z (t i) ω) | S.ℱ s] =ᵐ[S.μ]
        gts ∘ XH028 S drv Td Hor psi g Z s

/-- (c), finitely many curve values. -/
def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → MarkovTime S → BrownianDrivers6 S →
  ∀ (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ) (f0 : ℝ → ℝ),
  Setting028 S p d N Td Hor beta Sigma psi g z0 Z →
  ∀ (r : ℕ) (s : ℝ≥0) (t : Fin r → ℝ≥0) (T : Fin r → ℝ), (∀ i, s ≤ t i) →
  ∀ F : (Fin r → ℝ) → ℝ, Measurable F → (∃ C, ∀ y, |F y| ≤ C) →
    ∃ gts : (Fin (dim028 p d N) → ℝ) → ℝ, Measurable gts ∧
      S.μ[fun ω => F (fun i => Lambda028 f0 g
          (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k))
          (XH028 S drv Td Hor psi g Z (t i) ω) (T i)) | S.ℱ s] =ᵐ[S.μ]
        gts ∘ XH028 S drv Td Hor psi g Z s

def statement : Prop := severalStatement ∧ markovStatement ∧ curveStatement

end Standalone.SeparableMeetingMarkovSeveral

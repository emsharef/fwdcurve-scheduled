import Standalone.SeparableMeetingMarkovSolution
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Claim 028 (b): the Markov property of the frozen state

`MarkovTime` restates AX-13 (`Upstream.LipschitzMarkovTime`) over the standalone
calculus, field for field, with `BoundedBorel13` for the bounded Borel test
functions. Under the Brownian premise, (a) supplies every other premise of AX-13
for the frozen state `X^H`, whose initial value is deterministic. So for every
deterministic `s ≤ t` and bounded Borel `F`, (28.5) holds, and by Doob–Dynkin
the conditional expectation is a Borel function `g_{t,s}` of `X^H_s`
(`markovStatement`). `curveStatement` is the one-pair case of (c): for
`t ≤ T`, a bounded Borel function of `Lambda028 (X^H_t) T` has conditional
expectation given `ℱ s` equal to a Borel function of `X^H_s`.

Not in this target: the several-time extension of (b) and the several-pair
form of (c).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization Standalone.SeparableMeetingMarkovSolution
namespace Standalone.SeparableMeetingMarkovProperty

/-- Bounded Borel real functions of a finite-dimensional state. -/
def BoundedBorel13 {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

/-- AX-13 over the standalone calculus. -/
structure MarkovTime {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop where
  markov_property : BrownianDrivers6 h → ∀ (n : ℕ)
    (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ)
    (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin h.m → ℝ),
    Coefficients6 b σ → ∀ X : ℝ≥0 → Ω → Fin n → ℝ,
    Solution6 h b σ (X 0) X → MemLp (X 0) 2 h.μ →
    ∀ s t : ℝ≥0, s ≤ t → ∀ f, BoundedBorel13 f →
      h.μ[f ∘ X t | h.ℱ s] =ᵐ[h.μ] h.μ[f ∘ X t | MeasurableSpace.comap (X s) inferInstance]

/-- The common hypotheses of (a) and (b). -/
def Setting028 {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (p d N : ℕ)
    (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ) : Prop :=
  Monotone Td ∧ Td (Fin.last (N+1)) = Hor ∧ Coefficients6 beta Sigma ∧
  (∀ j, Continuous (psi j)) ∧ (∃ Kψ, ∀ j q, |psi j q| ≤ Kψ) ∧
  (∃ Lψ, ∀ j t z z', |psi j (t,z) - psi j (t,z')| ≤ Lψ * ‖z - z'‖) ∧
  (∀ j k x y, IntervalIntegrable (g j k) volume x y) ∧
  (∀ ω, Continuous fun t => Z t ω) ∧ Solution6 S beta Sigma (fun _ => z0) Z

/-- (b), one time: (28.5) and the Borel function `g_{t,s}`. -/
def markovStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → MarkovTime S → BrownianDrivers6 S →
  ∀ (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ),
  Setting028 S p d N Td Hor beta Sigma psi g z0 Z →
  ∀ (s t : ℝ≥0), s ≤ t → ∀ F : (Fin (dim028 p d N) → ℝ) → ℝ, BoundedBorel13 F →
    S.μ[F ∘ XH028 S drv Td Hor psi g Z t | S.ℱ s] =ᵐ[S.μ]
      S.μ[F ∘ XH028 S drv Td Hor psi g Z t |
        MeasurableSpace.comap (XH028 S drv Td Hor psi g Z s) inferInstance] ∧
    ∃ gts : (Fin (dim028 p d N) → ℝ) → ℝ, Measurable gts ∧
      S.μ[F ∘ XH028 S drv Td Hor psi g Z t | S.ℱ s] =ᵐ[S.μ]
        gts ∘ XH028 S drv Td Hor psi g Z s

/-- (c), one pair: a bounded Borel function of the curve value `Lambda028 (X^H_t) T`
has conditional expectation given `ℱ s` equal to a Borel function of `X^H_s`. -/
def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → MarkovTime S → BrownianDrivers6 S →
  ∀ (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ) (f0 : ℝ → ℝ),
  Setting028 S p d N Td Hor beta Sigma psi g z0 Z →
  ∀ (s t : ℝ≥0) (T : ℝ), s ≤ t → ∀ F : ℝ → ℝ, Measurable F → (∃ C, ∀ y, |F y| ≤ C) →
    ∃ gts : (Fin (dim028 p d N) → ℝ) → ℝ, Measurable gts ∧
      S.μ[fun ω => F (Lambda028 f0 g (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k))
          (XH028 S drv Td Hor psi g Z t ω) T) | S.ℱ s] =ᵐ[S.μ]
        gts ∘ XH028 S drv Td Hor psi g Z s

def statement : Prop := markovStatement ∧ curveStatement

end Standalone.SeparableMeetingMarkovProperty

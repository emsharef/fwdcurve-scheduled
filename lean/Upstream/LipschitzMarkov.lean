import Upstream.LipschitzSDE
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# AX-12: Markov property of autonomous globally Lipschitz SDE solutions

The field specializes [bauerschmidt2020stochastic], §6.3, definition and
Theorem p. 87, proof p. 88, as recorded in `ledger/AXIOMS.md`, AX-12. It is a
separate structure over an existing `ItoCalculus`, so no earlier consumer's
hypotheses change, and it reuses `BrownianDrivers6`, `Coefficients6` and
`Solution6` of AX-06 (`lean/Upstream/LipschitzSDE.lean`) unchanged: the full
Brownian-vector independence premise, identity covariation, Borel coefficients
with a global state-Lipschitz constant and local bounds, and the solution class
with its (U4) diffusion domains, local drift integrability and the equation with
the supplied integral. Autonomous coefficients enter through their
time-independent extensions `(t, x) ↦ b x` and `(t, x) ↦ σ x`.

`TransitionSemigroup12` packages the operators `P t` on the bounded Borel
functions `BoundedBorel12`: each `P t` maps them to bounded Borel functions and
is linear, positive, preserves the constant one, and is a contraction for the
sup norm (every bound of `|f|` bounds `|P t f|`); `P 0` is the identity and
`P (s + t) = P s ∘ P t`. The operators are functions on all real functions of
the state; the laws are asserted on bounded Borel functions only. The field
chooses one semigroup for the coefficients before quantifying over solutions,
test functions and deterministic times, and asserts (AX-12.1),
`E[f (X (s+t)) | ℱ s] = (P t f) (X s)` almost surely, for each of them
separately; no common null set is asserted. The initial value `X 0` may be
random. No curve formula, variance model, meeting transition or reset rule is
a field, and nothing here says Claim 026's coefficients are Markov.

The instance over `ItoCalculus.zeroDriverInstance` is vacuous: that base has
covariation density `c ≡ 0`, so the Brownian premise is false
(`LipschitzSDE.zeroDriver_not_brownian`) and the field holds for every
coefficient family without exercising any Markov property. This is permitted
by rule 6 as amended on 2026-09-23 (Q-06) only together with the following
separate checks of the conventions the field relies on:
(1) the identity family is a `TransitionSemigroup12` in every state dimension,
so the conclusion type is inhabited and its seven laws are consistent;
(2) zero autonomous coefficients satisfy `Coefficients6`, a constant state
satisfies every `Solution6` clause over the zero-driver base, and (AX-12.1)
holds for it with the identity semigroup, for every bounded Borel test
function and all times, using Mathlib's conditional expectation;
(3) every calculus of driver dimension zero satisfies `BrownianDrivers6`
(`LipschitzSDE.brownianDrivers6_of_dimension_zero`, restated below);
(4) the premise predicate `BoundedBorel12` holds, for every constant function
in every state dimension, and check (2)'s (AX-12.1) is instantiated at such a
test function, so it is not vacuous in the test function.
These checks give no nontrivial Brownian or Markov model. A faithful instance
would reconstruct textbook SDE theory, forbidden by Lean role duty 3b.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Upstream

/-- Bounded Borel real functions of a finite-dimensional state. -/
def BoundedBorel12 {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

/-- The transition operators of AX-12 and their laws on bounded Borel functions. -/
structure TransitionSemigroup12 (n : ℕ) where
  P : ℝ≥0 → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ
  boundedBorel : ∀ t f, BoundedBorel12 f → BoundedBorel12 (P t f)
  linear : ∀ t f g (a c : ℝ), BoundedBorel12 f → BoundedBorel12 g →
    P t (fun x => a * f x + c * g x) = fun x => a * P t f x + c * P t g x
  positive : ∀ t f, BoundedBorel12 f → (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P t f x
  one : ∀ t, P t (fun _ => 1) = fun _ => 1
  contraction : ∀ t f (C : ℝ), BoundedBorel12 f → (∀ x, |f x| ≤ C) →
    ∀ x, |P t f x| ≤ C
  zero : ∀ f, BoundedBorel12 f → P 0 f = f
  comp : ∀ s t f, BoundedBorel12 f → P (s + t) f = P s (P t f)

/-- The published AX-12 conclusion over an existing calculus structure. -/
structure LipschitzMarkov {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop where
  markov_semigroup : BrownianDrivers6 h → ∀ (n : ℕ)
    (b : (Fin n → ℝ) → Fin n → ℝ) (σ : (Fin n → ℝ) → Fin n → Fin h.m → ℝ),
    Coefficients6 (fun p => b p.2) (fun p => σ p.2) →
    ∃ P : TransitionSemigroup12 n, ∀ X : ℝ≥0 → Ω → Fin n → ℝ,
      Solution6 h (fun p => b p.2) (fun p => σ p.2) (X 0) X →
      ∀ f, BoundedBorel12 f → ∀ s t : ℝ≥0,
        h.μ[fun ω => f (X (s + t) ω) | h.ℱ s] =ᵐ[h.μ] fun ω => P.P t f (X s ω)

namespace LipschitzMarkov

/-- A genuine, but vacuous, model of the field over the zero-driver base: its
Brownian premise is false. No Markov conclusion is obtained from this instance. -/
theorem zeroDriverInstance : LipschitzMarkov ItoCalculus.zeroDriverInstance where
  markov_semigroup := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim

/-- Check (1): the identity family satisfies every semigroup law. -/
def identitySemigroup (n : ℕ) : TransitionSemigroup12 n where
  P := fun _ f => f
  boundedBorel := fun _ _ hf => hf
  linear := fun _ _ _ _ _ _ _ => rfl
  positive := fun _ _ _ hf => hf
  one := fun _ => rfl
  contraction := fun _ _ _ _ hC => hC
  zero := fun _ _ => rfl
  comp := fun _ _ _ _ => rfl

/-- Check (2): zero autonomous coefficients meet the coefficient premises. -/
lemma coefficients6_zero_check (n m : ℕ) :
    Coefficients6 (m := m) (fun p : ℝ≥0 × (Fin n → ℝ) => (fun _ : Fin n → ℝ => (0 : Fin n → ℝ)) p.2)
      (fun p => (fun _ : Fin n → ℝ => (0 : Fin n → Fin m → ℝ)) p.2) := by
  refine ⟨measurable_const, measurable_const, ⟨0, le_rfl, ?_⟩, ?_⟩
  · intro t x y
    simp
  · intro T R hR
    exact ⟨0, le_rfl, fun t ht x hx => by simp⟩

/-- Check (2): a constant state satisfies every solution-class clause over the
zero-driver base with zero autonomous coefficients. -/
lemma solution6_zero_check (x : Fin 1 → ℝ) : Solution6 ItoCalculus.zeroDriverInstance
    (fun _ => 0) (fun _ => 0) (fun _ => x) (fun _ _ => x) := by
  refine ⟨(fun _ => measurable_const), Filter.Eventually.of_forall (fun _ => continuous_const),
    ?_, ?_, ?_⟩
  · intro i k
    constructor
    · exact (measurable_const.comp
        (ItoCalculus.measurable_fst_predictable ItoCalculus.zeroDriverInstance.ℱ)).stronglyMeasurable
    · intro t
      exact Filter.Eventually.of_forall fun _ => by simp
  · intro i
    exact ⟨isStronglyProgressive_const _ 0, fun t =>
      Filter.Eventually.of_forall fun _ => by simp⟩
  · exact Filter.Eventually.of_forall fun ω => by
      intro t i
      simp [ItoCalculus.zeroDriverInstance]

/-- Check (2): (AX-12.1) holds for that solution with the identity semigroup,
for every bounded Borel test function and all deterministic times. -/
lemma markov_identity_check (x : Fin 1 → ℝ) (f : (Fin 1 → ℝ) → ℝ)
    (_hf : BoundedBorel12 f) (s t : ℝ≥0) :
    ItoCalculus.zeroDriverInstance.μ[fun ω => f ((fun _ _ => x : ℝ≥0 → Unit → Fin 1 → ℝ)
        (s + t) ω) | ItoCalculus.zeroDriverInstance.ℱ s] =ᵐ[ItoCalculus.zeroDriverInstance.μ]
      fun ω => (identitySemigroup 1).P t f
        ((fun _ _ => x : ℝ≥0 → Unit → Fin 1 → ℝ) s ω) := by
  rw [condExp_const (ItoCalculus.zeroDriverInstance.ℱ.le s)]
  rfl

/-- Check (4): the premise predicate holds; every constant is bounded Borel. -/
lemma boundedBorel12_const_check (n : ℕ) (c : ℝ) :
    BoundedBorel12 (fun _ : Fin n → ℝ => c) :=
  ⟨measurable_const, |c|, fun _ => le_rfl⟩

/-- Check (4): (AX-12.1) of check (2) at a test function known to satisfy the
premise, so that check is not vacuous in the test function. -/
lemma markov_identity_const_check (x : Fin 1 → ℝ) (c : ℝ) (s t : ℝ≥0) :
    ItoCalculus.zeroDriverInstance.μ[fun ω => (fun _ : Fin 1 → ℝ => c)
        ((fun _ _ => x : ℝ≥0 → Unit → Fin 1 → ℝ) (s + t) ω) |
          ItoCalculus.zeroDriverInstance.ℱ s] =ᵐ[ItoCalculus.zeroDriverInstance.μ]
      fun ω => (identitySemigroup 1).P t (fun _ => c)
        ((fun _ _ => x : ℝ≥0 → Unit → Fin 1 → ℝ) s ω) :=
  markov_identity_check x _ (boundedBorel12_const_check 1 c) s t

/-- Check (3): the empty driver vector satisfies every Brownian-vector premise. -/
lemma brownianDrivers6_dimension_zero_check {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (hm : h.m = 0) : BrownianDrivers6 h :=
  LipschitzSDE.brownianDrivers6_of_dimension_zero h hm

end LipschitzMarkov
end Upstream

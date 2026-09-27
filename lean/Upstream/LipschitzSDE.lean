import Upstream.ItoCalculus
import Mathlib.Probability.BrownianMotion.Basic

/-!
# AX-06: strong existence and pathwise uniqueness for Lipschitz SDEs

The two fields specialize [bauerschmidt2020stochastic], §5.2, pp. 68–71,
as recorded in `ledger/AXIOMS.md`, AX-06. Coefficients are arbitrary Borel,
locally bounded functions of time and a finite-dimensional state, globally
Lipschitz in the state with one uniform constant. The norm on finite function
spaces is the sup norm; finite-dimensional norm equivalence preserves this
coefficient class. Local bounds are expressed on bounded time/state boxes.

The supplied drivers must form a Brownian vector in the supplied filtration:
their increment vector is independent of the past, the coordinates of each
increment vector are jointly independent, and c is the identity density.
Adaptedness of the drivers is already a standing field of ItoCalculus.
AX-06c is the application with the chosen driver's completed natural filtration
and that structure's integral. There is no identification with another integral
operator, and no Claim 025-specific solution, price or jump is assumed.

The instance over ItoCalculus.zeroDriverInstance is degenerate: its sole driver
is identically zero and therefore cannot satisfy the Brownian premise. Both
implications hold for every coefficient family because this premise is false.
The field instance remains vacuous and exercises no SDE existence or uniqueness.
Two additional checks exercise the conventions separately: (1) zero drift and
constant unit diffusion satisfy Coefficients6, and a constant one-dimensional
state satisfies every Solution6 clause with the actual zero integral operator,
including predictable diffusion, local drift integrability and the equation;
(2) every calculus structure of driver dimension zero satisfies BrownianDrivers6,
including the independence of the empty increment vector from the past.
These checks provide no nontrivial Brownian or SDE model. A faithful instance
would reconstruct textbook SDE theory, forbidden by Lean role duty 3b. The Auditor checked
these fields and the repaired consistency checks at 6f663a6b5, recorded in
ledger/AUDIT_LOG.md. Acceptance as degenerate rests on Q-06 default (A); the
field instance itself remains vacuous, with the separate checks described above.

Re-synced with the ledger at 424b7708b: BrownianDrivers6 retains the coordinate
Brownian laws, independence of increment coordinates, independence of the
increment vector from the past, and identity covariation. Coefficients6 retains
Borel measurability, uniform state-Lipschitz bounds and local box bounds.
Solution6 retains adaptedness, almost-sure continuity, the diffusion and drift
domains, and the equation with the supplied integral. The two fields retain
exactly generic existence and pathwise uniqueness; AX-06c uses that same
interface in the chosen driver's completed natural filtration. No field or
instance proof changes in this synchronization.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Upstream

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

namespace LipschitzSDE

/-- The degenerate base has c = 0, whereas AX-06 requires identity covariation. -/
lemma zeroDriver_not_brownian : ¬ BrownianDrivers6 ItoCalculus.zeroDriverInstance := by
  classical
  intro h
  have hc := h.2.2.2 (0 : Fin 1) (0 : Fin 1) 0
  change (0 : ℝ) = 1 at hc
  exact zero_ne_one hc

/-- A genuine, but vacuous, model of both implications over the zero-driver base.
No nontrivial Brownian or SDE conclusion is obtained from this instance. -/
theorem zeroDriverInstance : LipschitzSDE ItoCalculus.zeroDriverInstance where
  lipschitz_existence := fun h => (zeroDriver_not_brownian h).elim
  lipschitz_uniqueness := fun h => (zeroDriver_not_brownian h).elim

/-- Check (1): zero drift and constant unit diffusion meet the coefficient premises. -/
lemma coefficients6_check : Coefficients6
    (fun _ : ℝ≥0 × (Fin 1 → ℝ) => (0 : Fin 1 → ℝ))
    (fun _ => (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ))) := by
  refine ⟨measurable_const, measurable_const, ⟨0, le_rfl, ?_⟩, ?_⟩
  · intro t x y
    simp
  · intro T R hR
    refine ⟨1, zero_le_one, ?_⟩
    intro t ht x hx
    simp

/-- Check (1): every solution-class clause holds for a constant state, with
nonzero diffusion coefficient but the actual zero integral operator. -/
lemma solution6_check (x : Fin 1 → ℝ) : Solution6 ItoCalculus.zeroDriverInstance
    (fun _ => 0) (fun _ => fun _ _ => 1) (fun _ => x) (fun _ _ => x) := by
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

/-- Check (2): the empty driver vector satisfies every Brownian-vector premise. -/
lemma brownianDrivers6_of_dimension_zero {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (hm : h.m = 0) : BrownianDrivers6 h := by
  let : IsEmpty (Fin h.m) := ⟨fun k => by have := k.isLt; omega⟩
  refine ⟨(fun k => isEmptyElim k), (fun s t hst => iIndepFun.of_subsingleton), ?_,
    (fun k => isEmptyElim k)⟩
  intro s t hst
  have heq : (fun ω (k : Fin h.m) => h.B k t ω - h.B k s ω) =
      (fun _ : Ω => (0 : Fin h.m → ℝ)) := by
    funext ω k
    exact isEmptyElim k
  rw [heq, MeasurableSpace.comap_const]
  exact indep_bot_left _

end LipschitzSDE
end Upstream

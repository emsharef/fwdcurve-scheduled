import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Supporting lemmas on moment generating functions

Backlog item: "[lean] Supporting Mathlib lemmas on moment generating functions
(existence, strict positivity, equality cases)."

Everything is stated for `ProbabilityTheory.mgf X μ t = μ[fun ω => exp (t * X ω)]` from
Mathlib, at the parameter `t` and its half `t / 2`. Mathlib already provides:

* `ProbabilityTheory.mgf_pos`: `0 < mgf X μ t` when `exp (t * X)` is integrable and `μ` is a
  probability measure (strict positivity at `t`);
* `ProbabilityTheory.integrable_exp_mul_of_le_of_le`: integrability on an interval of parameters;
* `ProbabilityTheory.variance_eq_sub`, `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero`.

This file specialises them to the pair `(t, t / 2)`:

* existence: `integrable_exp_mul_half`, `memLp_two_exp_mul_half`;
* strict positivity: `mgf_half_pos`;
* inequality and equality cases: `mgf_half_sq_le`, `ae_eq_of_mgf_half_sq_eq`,
  `ae_eq_const_of_mgf_half_sq_eq`.

Nothing here depends on the axiom ledger.
-/

open MeasureTheory Real
open scoped ProbabilityTheory

namespace Novel.MGF

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

/-- Pointwise: the square of the integrand at `t / 2` is the integrand at `t`. -/
lemma exp_half_mul_sq (t x : ℝ) : exp (t / 2 * x) ^ 2 = exp (t * x) := by
  rw [← exp_nat_mul]; push_cast; ring_nf

/-- Existence: if `exp (t * X)` is integrable, so is `exp (t / 2 * X)` (finite measure). -/
lemma integrable_exp_mul_half [IsFiniteMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Integrable (fun ω ↦ exp (t / 2 * X ω)) μ := by
  rcases le_total 0 t with h | h
  · exact ProbabilityTheory.integrable_exp_mul_of_nonneg_of_le ht (by linarith) (by linarith)
  · exact ProbabilityTheory.integrable_exp_mul_of_nonpos_of_ge ht (by linarith) (by linarith)

/-- Existence: if `exp (t * X)` is integrable then `exp (t / 2 * X)` is square-integrable. -/
lemma memLp_two_exp_mul_half [IsFiniteMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    MemLp (fun ω ↦ exp (t / 2 * X ω)) 2 μ := by
  rw [memLp_two_iff_integrable_sq (integrable_exp_mul_half ht).1]
  simpa only [exp_half_mul_sq] using ht

/-- The second moment of `exp (t / 2 * X)` is `mgf X μ t`. -/
lemma integral_exp_mul_half_sq :
    μ[(fun ω ↦ exp (t / 2 * X ω)) ^ 2] = ProbabilityTheory.mgf X μ t := by
  simp only [ProbabilityTheory.mgf, Pi.pow_apply, exp_half_mul_sq]

/-- Strict positivity at the half parameter. -/
lemma mgf_half_pos [IsProbabilityMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    0 < ProbabilityTheory.mgf X μ (t / 2) :=
  ProbabilityTheory.mgf_pos (integrable_exp_mul_half ht)

/-- The variance of `exp (t / 2 * X)` is `mgf X μ t - mgf X μ (t / 2) ^ 2`. -/
lemma variance_exp_mul_half [IsProbabilityMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Var[fun ω ↦ exp (t / 2 * X ω); μ]
      = ProbabilityTheory.mgf X μ t - ProbabilityTheory.mgf X μ (t / 2) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_two_exp_mul_half ht), integral_exp_mul_half_sq]
  rfl

/-- Inequality: `mgf X μ (t / 2) ^ 2 ≤ mgf X μ t` (Jensen for the square). -/
lemma mgf_half_sq_le [IsProbabilityMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ProbabilityTheory.mgf X μ (t / 2) ^ 2 ≤ ProbabilityTheory.mgf X μ t := by
  have h := ProbabilityTheory.variance_nonneg (fun ω ↦ exp (t / 2 * X ω)) μ
  rw [variance_exp_mul_half ht] at h
  linarith

/-- Equality case: if `mgf X μ (t / 2) ^ 2 = mgf X μ t` then `exp (t / 2 * X)` is almost surely
equal to its mean `mgf X μ (t / 2)`. -/
lemma ae_eq_of_mgf_half_sq_eq [IsProbabilityMeasure μ]
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (h : ProbabilityTheory.mgf X μ (t / 2) ^ 2 = ProbabilityTheory.mgf X μ t) :
    ∀ᵐ ω ∂μ, exp (t / 2 * X ω) = ProbabilityTheory.mgf X μ (t / 2) := by
  have hv : Var[fun ω ↦ exp (t / 2 * X ω); μ] = 0 := by
    rw [variance_exp_mul_half ht, h, sub_self]
  exact ProbabilityTheory.ae_eq_integral_of_variance_eq_zero (memLp_two_exp_mul_half ht) hv

/-- Equality case, solved for `X`: if `t ≠ 0` and `mgf X μ (t / 2) ^ 2 = mgf X μ t` then `X` is
almost surely the constant `(2 / t) * log (mgf X μ (t / 2))`. -/
lemma ae_eq_const_of_mgf_half_sq_eq [IsProbabilityMeasure μ] (ht0 : t ≠ 0)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (h : ProbabilityTheory.mgf X μ (t / 2) ^ 2 = ProbabilityTheory.mgf X μ t) :
    ∀ᵐ ω ∂μ, X ω = 2 / t * log (ProbabilityTheory.mgf X μ (t / 2)) := by
  filter_upwards [ae_eq_of_mgf_half_sq_eq ht h] with ω hω
  rw [← hω, log_exp]
  field_simp

end Novel.MGF

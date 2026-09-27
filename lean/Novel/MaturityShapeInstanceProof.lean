import Standalone.MaturityShapeInstance
import Novel.DiffusionMeetingInstanceProof

open MeasureTheory ProbabilityTheory Set
open Standalone.MaturityShapeGauss Standalone.MaturityShapeInstance
open Standalone.D3EventVariances
namespace Novel.MaturityShapeInstanceProof

lemma nonvacuityS : nonvacuityStatement := by
  intro N τ v hτ0 hτ φ hφ hC H
  have hT : ∀ i : Fin N, 0 < τ (i.val + 1) := fun i => by
    rw [← hτ0]
    exact hτ (by simp) (by simp only [mem_Iic]; omega) (by omega)
  refine ⟨hT, fun i => (v i).coe_nonneg, measurable_const, ⟨0, fun _ => by simp [model011s]⟩,
    fun _ => le_rfl, measurable_const, ⟨0, fun _ => by simp [model011s]⟩, hφ, hC, fun β f _ => ?_,
    fun f g c _ _ => Filter.Eventually.of_forall fun _ => by simp [model011s],
    fun i => measurable_pi_apply i, fun _ _ => measurable_const,
    fun _ _ _ => intervalIntegrable_const, fun _ _ _ _ => intervalIntegrable_const,
    fun _ _ _ _ => Filter.Eventually.of_forall fun _ => rfl,
    fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => by simp [model011s],
    fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => by simp [model011s],
    fun _ _ hst => (filt τ).mono hst, fun t => (filt τ).le t,
    fun i t hi => Novel.D3EventVariancesProof.measurable_coord (A := {j | τ (j.val + 1) ≤ t}) hi,
    fun _ _ _ => measurable_const, fun t β f hβ _ _ => ?_⟩
  · -- the law of `Σ β_i ω_i`
    have h := (Novel.BondOptionMeetingVariancesProof.law_L0149 (v := v) 0 β 0).map_eq
    have e : Standalone.BondOptionMeetingVariances.L0149 0 β = fun ω : Ω N => ∑ i, β i * ω i := by
      funext ω; simp [Standalone.BondOptionMeetingVariances.L0149]
    rw [Novel.DiffusionMeetingInstanceProof.Q0148_zero, e] at h
    simp only [zero_add, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
    simp only [model011s, add_zero, mul_zero, intervalIntegral.integral_zero]
    rw [h]
    congr 1
    rw [Real.toNNReal_sum_of_nonneg fun i _ => mul_nonneg (sq_nonneg _) (v i).coe_nonneg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.toNNReal_mul (sq_nonneg _), Real.toNNReal_coe, mul_comm]
  · -- independence from the past
    set A : Set (Fin N) := {i | t < τ (i.val + 1)}
    have hm : Measurable[Novel.D3EventVariancesProof.coordAlg A]
        fun ω : Ω N => ∑ i, β i * (model011s N τ v).Z i ω + (model011s N τ v).I f ω := by
      simp only [model011s, add_zero]
      refine Finset.measurable_sum _ fun i _ => ?_
      by_cases hb : β i = 0
      · simp only [hb, zero_mul]; exact measurable_const
      · exact measurable_const.mul (Novel.D3EventVariancesProof.measurable_coord (hβ i hb))
    refine indep_of_indep_of_le_left (Novel.D3EventVariancesProof.indep_algs ?_)
      (measurable_iff_comap_le.1 hm)
    exact Set.disjoint_left.2 fun j hj hj' =>
      (not_le_of_gt (show t < τ (j.val + 1) from hj)) (show τ (j.val + 1) ≤ t from hj')

theorem maturityShapeInstance : Standalone.MaturityShapeInstance.statement := nonvacuityS

end Novel.MaturityShapeInstanceProof

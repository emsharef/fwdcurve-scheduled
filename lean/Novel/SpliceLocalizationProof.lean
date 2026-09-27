import Standalone.SpliceLocalization
import Novel.UnifiedSpliceStep0Proof
import Novel.UnifiedSpliceQuantifiersProof
import Novel.UnifiedSpliceConverseAX01Proof
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Matrix NormedSpace Set
open Standalone.SpliceLocalization
namespace Novel.SpliceLocalizationProof

lemma carryOverS : carryOverStatement :=
  ⟨Novel.UnifiedSpliceStep0Proof.unifiedSpliceStep0,
    Novel.UnifiedSpliceQuantifiersProof.unifiedSpliceQuantifiers,
    Novel.UnifiedSpliceConverseAX01Proof.unifiedSpliceConverseAX01⟩

lemma productS : productStatement := by
  have e1 : EqOn (fun u : ℝ => u ^ (-(2:ℝ) / 3)) (fun u : ℝ => (u ^ (-(1:ℝ) / 3)) ^ 2) (Ioo 0 1) :=
    fun u hu => by
      simp only
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.1.le]; norm_num
  have e2 : EqOn (fun u : ℝ => (u ^ (-(1:ℝ) / 3) * u ^ (-(1:ℝ) / 3)) ^ 2)
      (fun u : ℝ => u ^ (-(4:ℝ) / 3)) (Ioo 0 1) := fun u hu => by
    simp only
    rw [← Real.rpow_add hu.1, ← Real.rpow_natCast, ← Real.rpow_mul hu.1.le]; norm_num
  refine ⟨((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by norm_num)).congr_fun e1
    measurableSet_Ioo, fun h => ?_⟩
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(4:ℝ) / 3) one_pos).1
    (h.congr_fun e2 measurableSet_Ioo)
  norm_num at this

lemma boundedFactorS : boundedFactorStatement := by
  intro s g I C hI hs hsm hgm hC
  refine (hs.const_mul (C ^ 2)).mono' ((hgm.mul hsm).pow 2) ?_
  refine (ae_restrict_iff' hI).2 (Filter.Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
  have : g u ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC u hu) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma rowProductS : rowProductStatement := by
  intro k x y I hx hy hx2 hy2
  have hint : IntegrableOn (fun u => ∑ l, (x u l ^ 2 + y u l ^ 2) / 2) I :=
    integrable_finsetSum _ fun l _ => ((hx2 l).add (hy2 l)).div_const 2
  have hmeas : AEStronglyMeasurable (fun u => x u ⬝ᵥ y u) (volume.restrict I) := by
    simp only [dotProduct]
    exact Finset.aestronglyMeasurable_fun_sum _ fun l _ => (hx l).mul (hy l)
  refine hint.mono' hmeas (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  nlinarith [sq_nonneg (|x u l| - |y u l|), sq_abs (x u l), sq_abs (y u l)]

lemma shiftS : shiftStatement := by
  intro r d c A zP z x h
  unfold F049
  congr 1
  · simp only [shiftP, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [add_pow, Finset.mul_sum]
    have hsub : Finset.range (μ + 1) ⊆ Finset.range (d + 1) :=
      Finset.range_subset_range.2 (by simpa [Nat.lt_succ_iff] using hμ)
    rw [← Finset.sum_subset hsub fun ν _ hν => by
      simp only [Finset.mem_range, not_lt] at hν
      simp only [show ¬ ν ≤ μ by omega, ite_false, zero_mul]]
    refine Finset.sum_congr rfl fun ν hν => ?_
    have hνμ : ν ≤ μ := by simpa [Nat.lt_succ_iff] using hν
    simp only [hνμ, ite_true]
    ring
  · rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _),
      ← mulVec_mulVec]

lemma frozenS : frozenStatement := by
  intro r d c A zP z τ t T
  rw [← shiftS r d c A zP z (T - t) (t - τ)]
  congr 1; ring

theorem spliceLocalization : Standalone.SpliceLocalization.statement := ⟨carryOverS, productS, boundedFactorS, rowProductS, shiftS, frozenS⟩

end Novel.SpliceLocalizationProof

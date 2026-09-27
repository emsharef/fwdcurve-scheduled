import Standalone.SeparableMeetingRepresentation
import Novel.SeparableMeetingCoefficientsProof

open MeasureTheory ProbabilityTheory Filter
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingCoefficients
open Novel.ZeroMeanReversionUpstreamBridgeProof
open scoped NNReal
namespace Novel.SeparableMeetingRepresentationProof

lemma path_aemeasurable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (T : ℝ≥0) (ω : Ω) :
    AEMeasurable (fun s : ℝ => ENNReal.ofReal (H (Real.toNNReal s) ω ^ 2))
      (volume.restrict (Set.Icc 0 (T:ℝ))) := by
  have hm : Measurable (fun s : ℝ => H (min (Real.toNNReal s) T) ω) := by
    have hc := Novel.SeparableMeetingCoefficientsProof.clipped_measurable S H hH T
    letI : MeasurableSpace Ω := S.ℱ T
    exact hc.comp measurable_prodMk_right
  refine ((hm.pow_const 2).ennreal_ofReal.aemeasurable).congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  simp only [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]

lemma domain_add {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H K : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (hK : U4 S.ℱ S.μ K) :
    U4 S.ℱ S.μ (fun s ω => H s ω + K s ω) := by
  refine ⟨hH.1.add hK.1, fun t => ?_⟩
  filter_upwards [hH.2 t, hK.2 t] with ω hω hω'
  have hb (s : ℝ) : (H (Real.toNNReal s) ω + K (Real.toNNReal s) ω)^2 ≤
      2 * ((H (Real.toNNReal s) ω)^2 + (K (Real.toNNReal s) ω)^2) := by
    nlinarith [sq_nonneg (H (Real.toNNReal s) ω - K (Real.toNNReal s) ω)]
  refine (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hb s)).trans_lt ?_
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left' (path_aemeasurable S H hH t ω)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hω, hω'⟩)

lemma domain_mul {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (a : ℝ) :
    U4 S.ℱ S.μ (fun s ω => a * H s ω) := by
  refine ⟨stronglyMeasurable_const.mul hH.1, fun t => ?_⟩
  filter_upwards [hH.2 t] with ω hω
  simp_rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg a)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω

lemma domain_sum {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    {n : ℕ} (H : Fin n → ℝ≥0 → Ω → ℝ) (a : Fin n → ℝ)
    (hH : ∀ i, U4 S.ℱ S.μ (H i)) (s : Finset (Fin n)) :
    U4 S.ℱ S.μ (fun t ω => ∑ i ∈ s, a i * H i t ω) := by
  induction s using Finset.induction with
  | empty => simpa using U4_zero S
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using domain_add S _ _ (domain_mul S (H i) (hH i) (a i)) ih

lemma integral_sum {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) {n : ℕ} (H : Fin n → ℝ≥0 → Ω → ℝ) (a : Fin n → ℝ)
    (hH : ∀ i, U4 S.ℱ S.μ (H i)) (s : Finset (Fin n)) (t : ℝ≥0) :
    S.I k (fun u ω => ∑ i ∈ s, a i * H i u ω) t =ᵐ[S.μ]
      fun ω => ∑ i ∈ s, a i * S.I k (H i) t ω := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact (zero_integral S k).mono (fun ω hω => hω t)
  | @insert i s hi ih =>
    have hlin := S.int_linear k (fun u ω => a i * H i u ω)
      (fun u ω => ∑ j ∈ s, a j * H j u ω) 1 1
      (domain_mul S (H i) (hH i) (a i)) (domain_sum S H a hH s) t
    have hmul := S.int_linear k (H i) (H i) (a i) 0 (hH i) (hH i) t
    have e1 : ((1:ℝ) • (fun u ω => a i * H i u ω) +
        (1:ℝ) • (fun u ω => ∑ j ∈ s, a j * H j u ω)) =
          fun u ω => ∑ j ∈ insert i s, a j * H j u ω := by
      funext u ω
      simp [Finset.sum_insert hi]
    have e2 : (a i • H i + (0:ℝ) • H i) = fun u ω => a i * H i u ω := by
      funext u ω
      simp
    rw [e1] at hlin
    rw [e2] at hmul
    filter_upwards [hlin, hmul, ih] with ω hl hm hs
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_mul, add_zero] at hl hm
    rw [hl, hm, hs, Finset.sum_insert hi]

lemma integral_sum_all {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) {n : ℕ} (H : Fin n → ℝ≥0 → Ω → ℝ) (a : Fin n → ℝ)
    (hH : ∀ i, U4 S.ℱ S.μ (H i)) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun u ω => ∑ i, a i * H i u ω) t ω =
      ∑ i, a i * S.I k (H i) t ω := by
  apply Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ _ _
    (S.int_continuous k _ (domain_sum S H a hH Finset.univ))
  · have hall : ∀ᵐ ω ∂S.μ, ∀ i, Continuous fun t => S.I k (H i) t ω :=
      ae_all_iff.2 fun i => S.int_continuous k (H i) (hH i)
    filter_upwards [hall] with ω hω
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hω i))
  · exact integral_sum S k H a hH Finset.univ

lemma representation : Standalone.SeparableMeetingRepresentation.statement := by
  intro Ω mΩ S k n H g B G hH hG
  refine ⟨domain_sum S H g hH Finset.univ, ?_⟩
  have hi : ∀ᵐ ω ∂S.μ, ∀ (N : ℕ) (i : Fin n),
      IntervalIntegrable (fun s => H i (Real.toNNReal s) ω ^ 2) volume 0 (N:ℝ) := by
    simp only [ae_all_iff]
    exact fun N i => Novel.SeparableMeetingCoefficientsProof.square_integrable S (H i) (hH i) N
  filter_upwards [integral_sum_all S k H g hH, hi] with ω hsum hint t
  obtain ⟨N, hN⟩ := exists_nat_ge (t:ℝ)
  have hq i : IntervalIntegrable (fun s => H i (Real.toNNReal s) ω ^ 2) volume 0 t :=
    (hint N i).mono_set (by
      rw [Set.uIcc_of_le t.coe_nonneg, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ N)]
      exact Set.Icc_subset_Icc le_rfl hN)
  have hqG i := (hq i).mul_continuousOn (hG i).continuousOn
  have hcoeff := Novel.SeparableMeetingShapesProof.coefficient n g B
    (fun i s => S.I k (H i) (Real.toNNReal s) ω)
    (fun i s => H i (Real.toNNReal s) ω ^ 2) G t hq hqG
  rw [hsum t]
  have he : (∫ s in (0:ℝ)..t, ∑ i, g i * H i (Real.toNNReal s) ω ^ 2 * (B i - G i s)) =
      (∑ i, g i * ((S.I k (H i) t ω - D026 (H i) (G i) t ω) +
        B i * D026 (H i) (fun _ => 1) t ω)) - ∑ i, g i * S.I k (H i) t ω := by
    have hc := hcoeff.1
    simp only [Standalone.SeparableMeetingShapes.C026, Standalone.SeparableMeetingShapes.M026,
      Standalone.SeparableMeetingShapes.A026, Real.toNNReal_coe] at hc
    simp only [D026, mul_one]
    linarith
  rw [he, add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem separableMeetingRepresentation : Standalone.SeparableMeetingRepresentation.statement := representation
end Novel.SeparableMeetingRepresentationProof

import Standalone.SeparableMeetingCoefficients
import Novel.SeparableMeetingShapesProof
import Novel.SeparableMeetingIntegralsProof

open MeasureTheory ProbabilityTheory Set Filter
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients
open scoped NNReal
namespace Novel.SeparableMeetingCoefficientsProof

lemma clipped_measurable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (T : ℝ≥0) :
    @Measurable (ℝ × Ω) ℝ ((inferInstance : MeasurableSpace ℝ).prod (S.ℱ T)) _
      (fun p => H (min (Real.toNNReal p.1) T) p.2) := by
  letI : MeasurableSpace Ω := S.ℱ T
  let f : ℝ × Ω → Iic T × Ω := fun p =>
    (⟨min (Real.toNNReal p.1) T, Set.mem_Iic.2 (min_le_right _ _)⟩, p.2)
  have hf : Measurable f :=
    (((continuous_real_toNNReal.min continuous_const).measurable.comp measurable_fst).subtype_mk).prodMk
      measurable_snd
  exact (hH.1.isStronglyProgressive T).measurable.comp hf

lemma square_integrable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (T : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, IntervalIntegrable (fun s => H (Real.toNNReal s) ω ^ 2) volume 0 T := by
  have hm (ω : Ω) : Measurable (fun s : ℝ => H (min (Real.toNNReal s) T) ω ^ 2) := by
    have hc := clipped_measurable S H hH T
    letI : MeasurableSpace Ω := S.ℱ T
    exact (hc.comp measurable_prodMk_right).pow_const 2
  filter_upwards [hH.2 T] with ω hω
  have he : EqOn (fun s : ℝ => H (min (Real.toNNReal s) T) ω ^ 2)
      (fun s => H (Real.toNNReal s) ω ^ 2) (Icc 0 (T:ℝ)) := by
    intro s hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hfin : HasFiniteIntegral (fun s : ℝ => H (min (Real.toNNReal s) T) ω ^ 2)
      (volume.restrict (Icc 0 (T:ℝ))) := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => sq_nonneg _)]
    convert hω using 1
    exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => congrArg ENNReal.ofReal (he hs))
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).2
  exact (Integrable.congr ⟨(hm ω).aestronglyMeasurable, hfin⟩
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => he hs)))

lemma ordinary_adapted {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (G : ℝ → ℝ) (hG : Continuous G)
    (t : ℝ≥0) : Measurable[S.ℱ t] (D026 H G t) := by
  have hc := clipped_measurable S H hH t
  letI : MeasurableSpace Ω := S.ℱ t
  have hm : Measurable (fun p : ℝ × Ω => H (min (Real.toNNReal p.1) t) p.2 ^ 2 * G p.1) :=
    (hc.pow_const 2).mul (hG.measurable.comp measurable_fst)
  have hi := hm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0:ℝ) t))
  have he : D026 H G t = fun ω =>
      ∫ s in Ioc (0:ℝ) t, H (min (Real.toNNReal s) t) ω ^ 2 * G s := by
    funext ω
    rw [D026, intervalIntegral.integral_of_le t.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  rw [he]
  exact hi.measurable

lemma ordinary : ordinaryStatement := by
  intro Ω mΩ S H hH G hG
  refine ⟨ordinary_adapted S H hH G hG, fun T => ?_⟩
  filter_upwards [square_integrable S H hH T] with ω hω
  have hi := hω.mul_continuousOn hG.continuousOn
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral (by simp : (0:ℝ) ∈ uIcc (0:ℝ) T)
  exact ⟨hi, by simpa [D026, uIcc_of_le T.coe_nonneg] using hac.continuousOn,
    by simpa [D026, uIcc_of_le T.coe_nonneg] using hac.boundedVariationOn⟩

lemma ordinary_before {Ω : Type*} (chi : ℝ≥0 → Ω → ℝ) (lo hi t : ℝ≥0)
    (hle : lo ≤ hi) (ht : t ≤ lo) (G : ℝ → ℝ) (ω : Ω) :
    D026 (H026 chi lo hi) G t ω = 0 := by
  rw [D026, intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro s hs
  rw [Novel.SeparableMeetingIntegralsProof.mask chi lo hi hle]
  have hslo : Real.toNNReal s ≤ lo := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
  simp [not_lt.mpr hslo]

lemma ordinary_after {Ω : Type*} (chi : ℝ≥0 → Ω → ℝ) (lo hi t : ℝ≥0)
    (hle : lo ≤ hi) (ht : hi ≤ t) (G : ℝ → ℝ) (ω : Ω)
    (hint : IntervalIntegrable (fun s => H026 chi lo hi (Real.toNNReal s) ω ^ 2 * G s)
      volume 0 t) : D026 (H026 chi lo hi) G t ω = D026 (H026 chi lo hi) G hi ω := by
  have h0hi := hint.mono_set (by
    rw [uIcc_of_le hi.coe_nonneg, uIcc_of_le t.coe_nonneg]
    exact Icc_subset_Icc le_rfl (show (hi:ℝ) ≤ t from ht))
  have hhit := hint.mono_set (by
    rw [uIcc_of_le (show (hi:ℝ) ≤ t from ht), uIcc_of_le t.coe_nonneg]
    exact Icc_subset_Icc hi.coe_nonneg le_rfl)
  have he : (∫ s in (hi:ℝ)..t, H026 chi lo hi (Real.toNNReal s) ω ^ 2 * G s) = 0 := by
    rw [intervalIntegral.integral_of_le (show (hi:ℝ) ≤ t from ht)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    rw [Novel.SeparableMeetingIntegralsProof.mask chi lo hi hle]
    have hshi : hi < Real.toNNReal s := by
      exact_mod_cast (show (hi:ℝ) < (Real.toNNReal s : ℝ) by
        rw [Real.coe_toNNReal s (hi.coe_nonneg.trans hs.1.le)]; exact hs.1)
    simp [not_le.mpr hshi]
  have had := intervalIntegral.integral_add_adjacent_intervals h0hi hhit
  simpa only [D026, he, add_zero] using had.symm

lemma coefficient : Standalone.SeparableMeetingCoefficients.coefficientStatement := by
  intro Ω mΩ S k chi lo hi hle hchi G hG
  have hdom := Novel.SeparableMeetingIntegralsProof.domain S chi lo hi hle hchi
  have ho := ordinary Ω mΩ S _ hdom G hG
  have hj := Novel.SeparableMeetingIntegralsProof.integrals Ω mΩ S k chi lo hi hle hchi
  refine ⟨?_, ?_, ?_⟩
  · intro t
    convert (hj.2.2.1 t).sub (ho.1 t) using 1
    ext ω
    simp [M0262]
  · intro T
    filter_upwards [hj.2.2.2.1, ho.2 T] with ω hJ hD
    exact ((hJ.comp continuous_real_toNNReal).continuousOn).sub hD.2.1
  · have hall : ∀ᵐ ω ∂S.μ, ∀ n : ℕ,
        IntervalIntegrable (fun s => H026 chi lo hi (Real.toNNReal s) ω ^ 2 * G s)
          volume 0 (n:ℝ) := by
      rw [ae_all_iff]
      intro n
      exact (ho.2 n).mono fun ω hω => hω.1
    filter_upwards [hall, hj.2.2.2.2.2.1] with ω hω hJ t
    constructor
    · intro ht
      simp only [M0262, Real.toNNReal_coe, (hJ t).1 ht,
        ordinary_before chi lo hi t hle ht G ω, sub_self]
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t:ℝ)
      have hint := (hω n).mono_set (by
        rw [uIcc_of_le t.coe_nonneg, uIcc_of_le (by positivity : (0:ℝ) ≤ n)]
        exact Icc_subset_Icc le_rfl hn)
      simp only [M0262, Real.toNNReal_coe, (hJ t).2 ht,
        ordinary_after chi lo hi t hle ht G ω hint]

lemma variance : varianceStatement := by
  intro Ω mΩ S n H a hH T
  have hall : ∀ᵐ ω ∂S.μ, ∀ k, IntervalIntegrable
      (fun s => H k (Real.toNNReal s) ω ^ 2) volume 0 T := by
    rw [ae_all_iff]
    exact fun k => square_integrable S (H k) (hH k) T
  filter_upwards [hall] with ω hω
  simpa only [Standalone.SeparableMeetingShapes.V026, Standalone.SeparableMeetingShapes.A026,
    D026, mul_one] using Novel.SeparableMeetingShapesProof.variance n a
      (fun k s => H k (Real.toNNReal s) ω ^ 2) T T.coe_nonneg hω (fun k s => sq_nonneg _)

theorem separableMeetingCoefficients : Standalone.SeparableMeetingCoefficients.statement :=
  ⟨ordinary, coefficient, variance⟩
end Novel.SeparableMeetingCoefficientsProof

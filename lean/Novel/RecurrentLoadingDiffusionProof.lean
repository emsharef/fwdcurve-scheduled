import Standalone.RecurrentLoadingDiffusion
import Novel.RecurrentLoadingDriftProof
import Novel.SeparableMeetingRepresentationProof

open MeasureTheory Matrix NormedSpace Filter
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingDiffusion Novel.RecurrentLoadingDriftProof
namespace Novel.RecurrentLoadingDiffusionProof

section U4
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- A bounded predictable scale times a Borel function of time bounded on compacts. -/
lemma U4_scaled (h : ℝ≥0 → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ h) (C : ℝ)
    (hC : ∀ s ω, |h s ω| ≤ C) (g : ℝ≥0 → ℝ) (hg : Measurable g)
    (hgb : ∀ T : ℝ≥0, ∃ B : ℝ, ∀ s ≤ T, |g s| ≤ B) :
    U4 S.ℱ S.μ (fun s ω => h s ω * g s) := by
  refine ⟨?_, fun T => Eventually.of_forall fun ω => ?_⟩
  · letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    have h1 : StronglyMeasurable (Function.uncurry h) := hP
    exact h1.mul (hg.comp (Upstream.ItoCalculus.measurable_fst_predictable S.ℱ)).stronglyMeasurable
  · obtain ⟨B, hB⟩ := hgb T
    calc (∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((h (Real.toNNReal s) ω *
          g (Real.toNNReal s)) ^ 2))
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((C * B) ^ 2) := by
          refine setLIntegral_mono measurable_const fun s hs => ENNReal.ofReal_le_ofReal ?_
          have hsT : Real.toNNReal s ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
          rw [← sq_abs, abs_mul]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul (hC _ _) (hB _ hsT) (abs_nonneg _)
            ((abs_nonneg _).trans (hC 0 ω))) 2
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

end U4

variable {p r : ℕ}

lemma sigma_time_measurable (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T : ℝ) :
    Measurable fun s : ℝ≥0 => sigma030 Tm u v M c b A s T :=
  (((measurable_from_nat (f := loading030 u v M)).comp
    ((count_anti Tm T).comp_monotone NNReal.coe_mono).measurable)).mul
    ((shape_continuous c b A).measurable.comp (measurable_const.sub NNReal.continuous_coe.measurable))

lemma sigma_time_bounded (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T : ℝ) (T' : ℝ≥0) :
    ∃ B : ℝ, ∀ s ≤ T', |sigma030 Tm u v M c b A s T| ≤ B := by
  obtain ⟨Sb, hSb⟩ := (isCompact_Icc (a := T - T') (b := T)).exists_bound_of_continuousOn
    (shape_continuous c b A).continuousOn
  refine ⟨loadBound Tm u v M * Sb, fun s hs => ?_⟩
  have hs' : (s:ℝ) ≤ T' := by exact_mod_cast hs
  rw [sigma030, abs_mul]
  have h2 := hSb (T - s) ⟨by linarith, by linarith [NNReal.coe_nonneg s]⟩
  rw [Real.norm_eq_abs] at h2
  exact mul_le_mul (loading_le Tm u v M _ (count_le_card Tm _ _)) h2 (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma w_time_measurable (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (a : Fin p × Fin r) :
    Measurable fun s : ℝ≥0 => Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s *
      w030 Tm v M b A s t a :=
  (measurable_const.indicator measurableSet_Iic).mul
    (((vec_measurable Tm v M t a.1).comp NNReal.continuous_coe.measurable).mul
      ((expv_continuous b A t a.2).measurable.comp NNReal.continuous_coe.measurable))

lemma w_time_bounded (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (a : Fin p × Fin r) (T' : ℝ≥0) :
    ∃ B : ℝ, ∀ s ≤ T', |Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s *
      w030 Tm v M b A s t a| ≤ B := by
  obtain ⟨Eb, hEb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T')).exists_bound_of_continuousOn
    (expv_continuous b A t a.2).continuousOn
  refine ⟨vecBound Tm v M * Eb, fun s hs => ?_⟩
  have hs' : (s:ℝ) ≤ T' := by exact_mod_cast hs
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 := hEb (s:ℝ) ⟨NNReal.coe_nonneg s, hs'⟩
  rw [Real.norm_eq_abs] at h2
  have hw : |w030 Tm v M b A s t a| ≤ vecBound Tm v M * Eb := by
    rw [w030, abs_mul]
    exact mul_le_mul (vec_le Tm v M _ (count_le_card Tm _ _) a.1) h2 (abs_nonneg _) hvb0
  by_cases hst : s ≤ t
  · simpa [Set.indicator_of_mem (show s ∈ {s | s ≤ t} from hst)] using hw
  · simp only [Set.indicator_of_notMem (show s ∉ {s | s ≤ t} from hst), zero_mul, abs_zero]
    exact (abs_nonneg _).trans hw

lemma diffusion : diffusionStatement := by
  intro Ω mΩ S k h hP C hC p r Tm u v M c b A t
  have hσU : ∀ T : ℝ, U4 S.ℱ S.μ (sigmaInt Tm u v M c b A h T) := fun T =>
    U4_scaled S h hP C hC _ (sigma_time_measurable Tm u v M c b A T)
      (sigma_time_bounded Tm u v M c b A T)
  have hxiU : ∀ a, U4 S.ℱ S.μ (xiInt Tm v M b A h t a) := by
    intro a
    have e : xiInt Tm v M b A h t a = fun s ω => h s ω *
        (Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * w030 Tm v M b A s t a) := by
      funext s ω; simp only [xiInt]; ring
    rw [e]
    exact U4_scaled S h hP C hC _ (w_time_measurable Tm v M b A t a)
      (w_time_bounded Tm v M b A t a)
  refine ⟨hσU, hxiU, fun x hx => ?_⟩
  set kx := k030 u M c A x (dist030 Tm t)
  have hst := S.int_stopped k (sigmaInt Tm u v M c b A h ((t:ℝ) + x)) (fun _ => t)
    (hσU _) (Novel.ZeroMeanReversionUpstreamBridgeProof.stopped_const S t) t
  -- reindex the Kronecker coordinates
  let e := (finProdFinEquiv : Fin p × Fin r ≃ Fin (p * r))
  let H : Fin (p * r) → ℝ≥0 → Ω → ℝ := fun j => xiInt Tm v M b A h t (e.symm j)
  let a' : Fin (p * r) → ℝ := fun j => kx (e.symm j)
  have hsum := Novel.SeparableMeetingRepresentationProof.integral_sum S k H a'
    (fun j => hxiU _) Finset.univ t
  have hpt : (fun s ω => Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s *
      sigmaInt Tm u v M c b A h ((t:ℝ) + x) s ω) = fun s ω => ∑ j ∈ Finset.univ, a' j * H j s ω := by
    funext s ω
    have hre : ∑ j ∈ Finset.univ, a' j * H j s ω =
        ∑ ab : Fin p × Fin r, kx ab * xiInt Tm v M b A h t ab s ω :=
      Fintype.sum_equiv e.symm _ _ (fun j => rfl)
    rw [hre]
    by_cases hs : s ≤ t
    · have hs' : (s:ℝ) ≤ t := by exact_mod_cast hs
      have hfac := Novel.RecurrentLoadingAlgebraProof.factor p r Tm u v M c b A s t (t + x) hs'
        (by linarith)
      rw [add_sub_cancel_left] at hfac
      simp only [sigmaInt, xiInt, Set.indicator_of_mem (show s ∈ {s | s ≤ t} from hs), one_mul,
        hfac, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ab _ => by ring
    · simp [sigmaInt, xiInt, Set.indicator_of_notMem (show s ∉ {s | s ≤ t} from hs)]
  filter_upwards [hst, hsum] with ω h1 h2
  have h1' : S.I k (sigmaInt Tm u v M c b A h ((t:ℝ) + x)) t ω =
      S.I k (fun s ω => ∑ j ∈ Finset.univ, a' j * H j s ω) t ω := by
    rw [← hpt]
    simpa only [min_self] using h1
  rw [h1', h2]
  exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)

theorem recurrentLoadingDiffusion : Standalone.RecurrentLoadingDiffusion.statement := diffusion

end Novel.RecurrentLoadingDiffusionProof

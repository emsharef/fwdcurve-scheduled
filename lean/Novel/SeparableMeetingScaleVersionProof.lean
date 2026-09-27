import Standalone.SeparableMeetingScaleVersion
import Novel.ZeroMeanReversionUpstreamBridgeProof

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingScaleVersion
namespace Novel.SeparableMeetingScaleVersionProof

lemma version : Standalone.SeparableMeetingScaleVersion.statement := by
  classical
  intro Ω mΩ S P p beta Sigma z0 Z' hcoef hsol
  obtain ⟨hbm, hSm, -, -⟩ := hcoef
  obtain ⟨had', hcont', hU4', hdrift', heq'⟩ := hsol
  -- the null set, in `ℱ 0` by the usual conditions
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont')
  have hN0 : MeasurableSet[S.ℱ 0] N := S.usual_null N hNmeas hNnull
  have hNt : ∀ t, MeasurableSet[S.ℱ t] N :=
    fun t => S.ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN0
  have hnotN : ∀ᵐ ω ∂S.μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hNnull
  set Z : ℝ≥0 → Ω → Fin p → ℝ := fun t => N.piecewise (fun _ => z0) (Z' t) with hZdef
  have hZN : ∀ t ω, ω ∈ N → Z t ω = z0 := fun t ω hω => Set.piecewise_eq_of_mem _ _ _ hω
  have hZnN : ∀ t ω, ω ∉ N → Z t ω = Z' t ω :=
    fun t ω hω => Set.piecewise_eq_of_notMem _ _ _ hω
  have hcont : ∀ ω, Continuous fun t => Z t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hZN _ ω hω]; exact continuous_const
    · simp only [hZnN _ ω hω]
      by_contra hc
      exact hω (hNsub hc)
  have hZm : ∀ t, Measurable[S.ℱ t] (Z t) :=
    fun t => Measurable.piecewise (hNt t) measurable_const (had' t)
  have hind : ∀ᵐ ω ∂S.μ, ∀ t, Z t ω = Z' t ω := by
    filter_upwards [hnotN] with ω hω t
    exact hZnN t ω hω
  -- predictability from AX-09
  have hpredi (i : Fin p) : IsStronglyPredictable S.ℱ (fun t ω => Z t ω i) :=
    P.continuous_predictable _ (fun t => (measurable_pi_apply i).comp (hZm t))
      (fun ω => (continuous_apply i).comp (hcont ω))
  have hZpred : Measurable[S.ℱ.predictable] (fun q : ℝ≥0 × Ω => Z q.1 q.2) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    exact measurable_pi_iff.2 fun i => (hpredi i).measurable
  have hpair : Measurable[S.ℱ.predictable] (fun q : ℝ≥0 × Ω => (q.1, Z q.1 q.2)) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    exact (Upstream.ItoCalculus.measurable_fst_predictable S.ℱ).prodMk hZpred
  have hSigmaPred (i : Fin p) (k : Fin S.m) :
      IsStronglyPredictable S.ℱ (fun t ω => Sigma (t, Z t ω) i k) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    exact ((measurable_pi_apply k).comp
      ((measurable_pi_apply i).comp (hSm.comp hpair))).stronglyMeasurable
  have hbetaPred (i : Fin p) : IsStronglyPredictable S.ℱ (fun t ω => beta (t, Z t ω) i) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    exact ((measurable_pi_apply i).comp (hbm.comp hpair)).stronglyMeasurable
  have hU4 (i : Fin p) (k : Fin S.m) : U4 S.ℱ S.μ (fun t ω => Sigma (t, Z t ω) i k) := by
    refine ⟨hSigmaPred i k, fun t => ?_⟩
    filter_upwards [(hU4' i k).2 t, hnotN] with ω hω hN
    simpa only [hZnN _ ω hN] using hω
  refine ⟨Z, hcont, hZm, hind, ⟨hZm,
    Eventually.of_forall hcont, hU4, fun i => ⟨(hbetaPred i).isStronglyProgressive, fun t => ?_⟩,
    ?_⟩, ?_⟩
  · filter_upwards [(hdrift' i).2 t, hnotN] with ω hω hN
    simpa only [hZnN _ ω hN] using hω
  · have hcongr : ∀ᵐ ω ∂S.μ, ∀ (i : Fin p) (k : Fin S.m) t,
        S.I k (fun s ω => Sigma (s, Z' s ω) i k) t ω =
          S.I k (fun s ω => Sigma (s, Z s ω) i k) t ω := by
      simp only [ae_all_iff]
      intro i k
      refine Novel.ZeroMeanReversionUpstreamBridgeProof.int_congr_ae S k _ _ (hU4' i k)
        (hU4 i k) ?_
      filter_upwards [hnotN] with ω hN s
      rw [hZnN s ω hN]
    filter_upwards [heq', hcongr, hnotN] with ω he hc hN t i
    rw [hZnN t ω hN, he t i]
    simp only [hc]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hZnN _ ω hN]
  · intro psi hpsi K hK
    refine ⟨P.continuous_predictable _ (fun t => hpsi.measurable.comp
      (measurable_const.prodMk (hZm t))) (fun ω => hpsi.comp
        (continuous_id.prodMk (hcont ω))), fun t => Eventually.of_forall fun ω => ?_⟩
    calc (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (psi (Real.toNNReal s,
          Z (Real.toNNReal s) ω) ^ 2))
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (K ^ 2) := by
          refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
          have h := hK (Real.toNNReal s, Z (Real.toNNReal s) ω)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

theorem separableMeetingScaleVersion : Standalone.SeparableMeetingScaleVersion.statement :=
  version

end Novel.SeparableMeetingScaleVersionProof

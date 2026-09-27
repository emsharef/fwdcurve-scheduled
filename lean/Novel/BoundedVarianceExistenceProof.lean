import Standalone.BoundedVarianceExistence
import Novel.BoundedVarianceIntegralComparisonProof
import Upstream.LipschitzSDE

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence
namespace Novel.BoundedVarianceExistenceProof

lemma coefficients : Standalone.BoundedVarianceExistence.coefficientStatement := by
  intro lam hl m
  obtain ⟨hbound, hb, ha⟩ := Novel.BoundedVarianceStateProof.coefficient lam hl
  have hbc : Continuous (b025 lam) := continuous_iff_continuousAt.2 fun z =>
    (hbound z).2.2.2.2.2.1.continuousAt
  have hac : Continuous a025 := continuous_iff_continuousAt.2 fun z =>
    (hbound z).2.2.2.2.2.2.1.continuousAt
  have hz : Continuous (fun p : ℝ≥0 × (Fin 1 → ℝ) => p.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have hpos : 0 ≤ 1 / (2 * lam) := by positivity
  refine ⟨(continuous_pi fun _ => hbc.comp hz).measurable,
    (continuous_pi fun _ => continuous_pi fun _ => hac.comp hz).measurable,
    ⟨1 / (2*lam) + 1, by positivity, ?_⟩, ?_⟩
  · intro t x y
    have hxy : |x 0 - y 0| ≤ ‖x-y‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x-y) 0
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      change |b025 lam (x 0) - b025 lam (y 0)| ≤ _
      calc
        _ ≤ (1/(2*lam))*|x 0-y 0| := hb _ _
        _ ≤ (1/(2*lam))*‖x-y‖ := mul_le_mul_of_nonneg_left hxy hpos
        _ ≤ _ := by nlinarith [norm_nonneg (x-y)]
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro k
      change |a025 (x 0) - a025 (y 0)| ≤ _
      calc
        _ ≤ (1/2:ℝ)*|x 0-y 0| := ha _ _
        _ ≤ (1/2:ℝ)*‖x-y‖ := mul_le_mul_of_nonneg_left hxy (by norm_num)
        _ ≤ _ := by nlinarith [norm_nonneg (x-y)]
  · intro T R hR
    refine ⟨1/(2*lam)+2, by positivity, ?_⟩
    intro t ht x hx
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      change |b025 lam (x 0)| ≤ _
      linarith [(hbound (x 0)).2.2.1]
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro k
      change |a025 (x 0)| ≤ _
      have hp := (hbound (x 0)).2.2.2.1
      have hu := (hbound (x 0)).2.2.2.2.1
      have hs : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      rw [abs_of_pos (by linarith)]
      linarith

lemma sum_single {m : ℕ} (k : Fin m) (hs : ∀ j, j = k) (f : Fin m → ℝ) :
    ∑ j, f j = f k := by
  classical
  exact Finset.sum_eq_single k (fun j _ hj => (hj (hs j)).elim) (by simp)

lemma existence : existenceStatement := by
  intro Ω mΩ S E hB k hs lam hl
  obtain ⟨X,hX⟩ := E.lipschitz_existence hB 1 (drift025 lam)
    (diffusion025 S.m) (coefficients lam hl S.m) 0
  refine ⟨(fun t ω => X t ω 0), ?_⟩
  refine ⟨(fun t => (measurable_pi_apply 0).comp (hX.1 t)), ?_, hX.2.2.1 0 k,
    hX.2.2.2.1 0, ?_⟩
  · filter_upwards [hX.2.1] with ω hx
    exact (continuous_apply 0).comp hx
  · filter_upwards [hX.2.2.2.2] with ω hx t
    simpa only [drift025, diffusion025, Pi.zero_apply, zero_add, sum_single k hs] using hx t 0

lemma scalar_zero {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) (hY : ScalarSolution025 S k lam Y) :
    Y 0 =ᵐ[S.μ] 0 := by
  filter_upwards [hY.2.2.2.2,S.int_zero k _ hY.2.2.1] with ω hy hz
  simpa [hz] using hy 0

lemma scalar_lift {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (hs : ∀ j, j = k) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hY : ScalarSolution025 S k lam Y) :
    Solution6 S (drift025 lam) (diffusion025 S.m) (fun ω _ => Y 0 ω)
      (fun t ω _ => Y t ω) := by
  refine ⟨?_, ?_, (fun _ _ => hY.2.2.1), (fun _ => hY.2.2.2.1), ?_⟩
  · intro t
    change Measurable[S.ℱ t] (fun ω (_ : Fin 1) => Y t ω)
    exact (continuous_pi (fun _ : Fin 1 => continuous_id)).measurable.comp (hY.1 t)
  · filter_upwards [hY.2.1] with ω hy
    exact continuous_pi fun _ => hy
  · filter_upwards [hY.2.2.2.2,scalar_zero S k lam Y hY] with ω hy hz t i
    simpa only [drift025, diffusion025, sum_single k hs, hz, Pi.zero_apply, zero_add] using hy t

lemma uniqueness : uniquenessStatement := by
  intro Ω mΩ S E hB k hs lam hl Y Y' hY hY'
  have hz : (fun ω (_ : Fin 1) => Y 0 ω) =ᵐ[S.μ] (fun ω _ => Y' 0 ω) := by
    filter_upwards [scalar_zero S k lam Y hY,scalar_zero S k lam Y' hY'] with ω hy hy'
    simp only [hy,hy']
  have he := E.lipschitz_uniqueness hB 1 (drift025 lam) (diffusion025 S.m)
    (coefficients lam hl S.m) (fun t ω _ => Y t ω) (fun t ω _ => Y' t ω)
    (scalar_lift S k hs lam Y hY) (scalar_lift S k hs lam Y' hY') hz
  filter_upwards [he] with ω h t
  exact congrFun (h t) 0

/-- The exact AX-06 fields transported to the standalone calculus data. -/
theorem ofUpstream {Ω : Type*} [MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (E : Upstream.LipschitzSDE S) :
    LipschitzSDE (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) where
  lipschitz_existence := E.lipschitz_existence
  lipschitz_uniqueness := E.lipschitz_uniqueness

/-- Scalar existence from the audited Upstream interface on a supplied Brownian basis. -/
theorem upstream_existence {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE S)
    (hB : Upstream.BrownianDrivers6 S) (k : Fin S.m) (hs : ∀ j, j = k)
    (lam : ℝ) (hl : 0 < lam) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) k lam Y :=
  existence Ω mΩ _ (ofUpstream S E) hB k hs lam hl

lemma version_data {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (Y : ℝ≥0 → Ω → ℝ) (hadapt : Adapted S.ℱ Y)
    (hcont : ∀ᵐ ω ∂S.μ, Continuous fun t => Y t ω) (hzero : Y 0 =ᵐ[S.μ] 0) :
    ∃ Y' : ℝ≥0 → Ω → ℝ, Adapted S.ℱ Y' ∧
      (∀ ω, Continuous fun t => Y' t ω) ∧ (∀ ω, Y' 0 ω = 0) ∧
      (∀ᵐ ω ∂S.μ, ∀ t, Y' t ω = Y t ω) := by
  classical
  have hgood : ∀ᵐ ω ∂S.μ, Continuous (fun t => Y t ω) ∧ Y 0 ω = 0 := hcont.and hzero
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hN0 := S.usual_null N hNm hNzero
  have hNt : ∀ t, MeasurableSet[S.ℱ t] N := fun t =>
    S.ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN0
  let Y' : ℝ≥0 → Ω → ℝ := fun t => N.piecewise (fun _ => 0) (Y t)
  have hnot (ω) (hω : ω ∉ N) : Continuous (fun t => Y t ω) ∧ Y 0 ω = 0 := by
    by_contra hn
    exact hω (hNsub hn)
  refine ⟨Y', (fun t => Measurable.piecewise (hNt t) measurable_const (hadapt t)), ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [Y',hω] using (continuous_const : Continuous fun _ : ℝ≥0 => (0:ℝ))
    · simpa [Y',hω] using (hnot ω hω).1
  · intro ω
    by_cases hω : ω ∈ N
    · simp [Y',hω]
    · simpa [Y',hω] using (hnot ω hω).2
  · filter_upwards [compl_mem_ae_iff.2 hNzero] with ω hω t
    exact Set.piecewise_eq_of_notMem _ _ _ hω

lemma version : versionStatement := by
  intro Ω mΩ S P k lam hl Y hY
  obtain ⟨Y',had,hc,hz,he⟩ := version_data S Y hY.1 hY.2.1 (scalar_zero S k lam Y hY)
  have hbc : Continuous (b025 lam) := continuous_iff_continuousAt.2 fun z =>
    (Novel.BoundedVarianceStateProof.coefficient lam hl).1 z |>.2.2.2.2.2.1.continuousAt
  have hac : Continuous a025 := continuous_iff_continuousAt.2 fun z =>
    (Novel.BoundedVarianceStateProof.coefficient lam hl).1 z |>.2.2.2.2.2.2.1.continuousAt
  have hU : U4 S.ℱ S.μ (fun t ω => a025 (Y' t ω)) := by
    refine ⟨P.continuous_predictable _ (fun t => hac.measurable.comp (had t))
      (fun ω => hac.comp (hc ω)), ?_⟩
    intro t
    filter_upwards [hY.2.2.1.2 t, he] with ω hω heq
    simpa only [heq] using hω
  have hD : LocallyIntegrableDrift S.ℱ S.μ (fun t ω => b025 lam (Y' t ω)) := by
    refine ⟨(P.continuous_predictable _ (fun t => hbc.measurable.comp (had t))
      (fun ω => hbc.comp (hc ω))).isStronglyProgressive, ?_⟩
    intro t
    filter_upwards [hY.2.2.2.1.2 t, he] with ω hω heq
    simpa only [heq] using hω
  have hI := Novel.ZeroMeanReversionUpstreamBridgeProof.int_congr_ae S k
    (fun t ω => a025 (Y' t ω)) (fun t ω => a025 (Y t ω)) hU hY.2.2.1
    (by filter_upwards [he] with ω heq t; rw [heq t])
  refine ⟨Y', ⟨had, Eventually.of_forall hc, hU, hD, ?_⟩, hc, hz, he⟩
  filter_upwards [hY.2.2.2.2,he,hI] with ω hy heq hi t
  simpa only [heq,hi] using hy t

/-- Construct the version required by AX-09 and the integral-comparison theorem. -/
theorem upstream_continuous_existence {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE S)
    (P : Upstream.Predictability S.ℱ) (hB : Upstream.BrownianDrivers6 S)
    (k : Fin S.m) (hs : ∀ j, j = k) (lam : ℝ) (hl : 0 < lam) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) k lam Y ∧
      (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) := by
  obtain ⟨Y,hY⟩ := upstream_existence S E hB k hs lam hl
  obtain ⟨Y',hY',hc,hz,_⟩ := version Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    ⟨P.continuous_predictable⟩ k lam hl Y hY
  exact ⟨Y',hY',hc,hz⟩

lemma transfer : transferStatement := by
  intro Ω mΩ S R E A D P Q hB k l hs hμ hdriver hRS lam hl
  obtain ⟨Y,hY⟩ := existence Ω mΩ R E hB l hs lam hl
  obtain ⟨Y',hY',hc,hz,_⟩ := version Ω mΩ R Q l lam hl Y hY
  have had : Adapted S.ℱ Y' := fun t => (hY'.1 t).mono (hRS t) le_rfl
  have hbc : Continuous (b025 lam) := continuous_iff_continuousAt.2 fun z =>
    (Novel.BoundedVarianceStateProof.coefficient lam hl).1 z |>.2.2.2.2.2.1.continuousAt
  have hac : Continuous a025 := continuous_iff_continuousAt.2 fun z =>
    (Novel.BoundedVarianceStateProof.coefficient lam hl).1 z |>.2.2.2.2.2.2.1.continuousAt
  have hU : U4 S.ℱ S.μ (fun t ω => a025 (Y' t ω)) := by
    refine ⟨P.continuous_predictable _ (fun t => hac.measurable.comp (had t))
      (fun ω => hac.comp (hc ω)), ?_⟩
    intro t
    rw [← hμ]
    exact hY'.2.2.1.2 t
  have hD : LocallyIntegrableDrift S.ℱ S.μ (fun t ω => b025 lam (Y' t ω)) := by
    refine ⟨(P.continuous_predictable _ (fun t => hbc.measurable.comp (had t))
      (fun ω => hbc.comp (hc ω))).isStronglyProgressive, ?_⟩
    intro t
    rw [← hμ]
    exact hY'.2.2.2.1.2 t
  have hI := Novel.BoundedVarianceIntegralComparisonProof.coefficient Ω mΩ S R A D P Q
    k l hμ hdriver Y' had hY'.1 hc
  have heq : ∀ᵐ ω ∂S.μ, ∀ t, Y' t ω =
      R.I l (fun s ω => a025 (Y' s ω)) t ω +
        ∫ s in (0:ℝ)..(t:ℝ), b025 lam (Y' (Real.toNNReal s) ω) := by
    rw [← hμ]
    exact hY'.2.2.2.2
  refine ⟨Y',hY',⟨had,Eventually.of_forall hc,hU,hD,?_⟩,hc,hz⟩
  filter_upwards [hI,heq] with ω hi he t
  rw [hi t]
  exact he t

/-- Existence in both supplied filtrations uses AX-06 only in the smaller one;
agreement of their integral operators for this integrand is proved from AX-11. -/
theorem upstream_transfer {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S R : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE R)
    (A : Upstream.IntegralApproximation S) (D : Upstream.IntegralApproximation R)
    (P : Upstream.Predictability S.ℱ) (Q : Upstream.Predictability R.ℱ)
    (hB : Upstream.BrownianDrivers6 R) (k : Fin S.m) (l : Fin R.m)
    (hs : ∀ j, j = l) (hμ : R.μ = S.μ) (hdriver : S.B k = R.B l)
    (hRS : ∀ t, R.ℱ t ≤ S.ℱ t) (lam : ℝ) (hl : 0 < lam) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R) l lam Y ∧
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) k lam Y ∧
      (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) :=
  transfer Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R) (ofUpstream R E)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream S A)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream R D)
    ⟨P.continuous_predictable⟩ ⟨Q.continuous_predictable⟩ hB k l hs hμ hdriver hRS lam hl

/-- The constructed coordinate supplies the earlier exponential-martingale
result for every nonnegative maturity distance and stopping horizon. Identifying
this exponential with the actual discounted bond remains a separate deduction. -/
theorem upstream_constructed_martingale {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S R : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE R)
    (M : Upstream.ExponentialMartingale S)
    (A : Upstream.IntegralApproximation S) (D : Upstream.IntegralApproximation R)
    (P : Upstream.Predictability S.ℱ) (Q : Upstream.Predictability R.ℱ)
    (hB : Upstream.BrownianDrivers6 R) (i k : Fin S.m) (l : Fin R.m)
    (hik : i ≠ k) (hs : ∀ j, j = l) (hμ : R.μ = S.μ) (hdriver : S.B k = R.B l)
    (hRS : ∀ t, R.ℱ t ≤ S.ℱ t)
    (hc : ∀ j j' t, S.c j j' t = if j = j' then 1 else 0)
    (lam : ℝ) (hl : 0 < lam) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R) l lam Y ∧
      ScalarSolution025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) k lam Y ∧
      (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) ∧
      ∀ (x : ℝ) (tau : ℝ≥0), 0 ≤ x →
        Martingale (Upstream.exponential10 S
          (Standalone.BoundedVarianceMartingale.H025 i k lam x
            (fun s ω => Y (Real.toNNReal s) ω)) tau) S.ℱ S.μ := by
  obtain ⟨Y,hR,hS,hcont,hzero⟩ := upstream_transfer S R E A D P Q hB k l hs hμ hdriver hRS lam hl
  refine ⟨Y,hR,hS,hcont,hzero,?_⟩
  intro x tau hx
  refine Novel.BoundedVarianceMartingaleProof.upstream_adapted S M P i k hik hc lam x tau hl hx
    (fun s ω => Y (Real.toNNReal s) ω) ?_ ?_
  · intro t
    rw [Real.toNNReal_coe]
    exact hS.1 t
  · intro ω
    exact (hcont ω).comp continuous_real_toNNReal

theorem boundedVarianceExistence : Standalone.BoundedVarianceExistence.statement :=
  ⟨coefficients,existence,uniqueness,version,transfer⟩

end Novel.BoundedVarianceExistenceProof

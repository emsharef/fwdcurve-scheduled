import Standalone.BoundedVarianceIto
import Novel.BoundedVarianceExistenceProof

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIto
open Novel.BoundedVarianceStateProof Novel.BoundedVarianceExistenceProof
namespace Novel.BoundedVarianceItoProof

lemma tanh_smooth : ContDiff ℝ 2 Real.tanh := by
  have h : Real.tanh = Real.sinh / Real.cosh := by
    funext z; exact Real.tanh_eq_sinh_div_cosh z
  rw [h]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun z => ne_of_gt (Real.cosh_pos z))

lemma F_smooth : ContDiff ℝ 2 F025 :=
  contDiff_const.add (tanh_smooth.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_snd))

lemma F_dT (s : ℝ) (x : Fin 1 → ℝ) : dT F025 (s,x) = 0 := by
  rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dT_general F025 F_smooth]
  exact deriv_const s (v025 (x 0))

lemma F_dX (s : ℝ) (x : Fin 1 → ℝ) : dX F025 (s,x) 0 = 1-(Real.tanh (x 0))^2 := by
  rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dX_general F025 F_smooth]
  simp only [F025, Function.update_self]
  exact ((tanh_derivative025 (x 0)).const_add 2).deriv

lemma F_dXX (s : ℝ) (x : Fin 1 → ℝ) :
    dXX F025 (s,x) 0 0 = -2*Real.tanh (x 0)*(1-(Real.tanh (x 0))^2) := by
  rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dXX_general F025 F_smooth]
  simp only [F025, Function.update_self]
  have he : deriv v025 = fun z => 1-(Real.tanh z)^2 :=
    funext fun z => ((tanh_derivative025 z).const_add 2).deriv
  change deriv (deriv v025) (x 0) = _
  rw [he]
  convert ((hasDerivAt_const (x 0) (1:ℝ)).sub ((tanh_derivative025 (x 0)).pow 2)).deriv using 1; ring

lemma density : densityStatement := by
  intro z
  have hv := bounds025 z
  have ha : (a025 z)^2 = v025 z := Real.sq_sqrt (by linarith [hv.1])
  have hg : (g025 z)^2 = (1-(Real.tanh z)^2)^2*v025 z := by rw [g025,mul_pow,ha]
  refine ⟨ha,hg,?_,?_⟩
  · rw [hg]
    exact mul_pos (sq_pos_of_pos hv.2.2) (by linarith [hv.1])
  · rw [hg]
    have hs := sq_nonneg (Real.tanh z)
    have hh : (1-(Real.tanh z)^2)^2 ≤ 1 := by nlinarith [hv.2.2]
    nlinarith [sq_nonneg (1-(Real.tanh z)^2),hv.1,hv.2.1]

lemma g_continuous : Continuous g025 :=
  (continuous_const.sub (tanh_smooth.continuous.pow 2)).mul
    (Real.continuous_sqrt.comp (continuous_const.add tanh_smooth.continuous))

lemma g_domain {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (P : Predictability S.ℱ)
    (Y : ℝ≥0 → Ω → ℝ) (hYa : Adapted S.ℱ Y) (hY : ∀ ω, Continuous fun t => Y t ω) :
    U4 S.ℱ S.μ (fun s ω => g025 (Y s ω)) := by
  apply Novel.BoundedVarianceMartingaleProof.bounded_U4 S _
    (P.continuous_predictable _ (fun t => g_continuous.measurable.comp (hYa t))
      (fun ω => g_continuous.comp (hY ω))) 2
  intro s ω
  norm_num only [show (2:ℝ)^2 = 4 by norm_num]
  exact (density (Y s ω)).2.2.2

lemma ito : Standalone.BoundedVarianceIto.itoStatement := by
  intro Ω mΩ R P k hsingle hc lam hl Y hsol hY
  let H : Fin 1 → Fin R.m → ℝ≥0 → Ω → ℝ := fun _ _ s ω => a025 (Y s ω)
  let K : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ s ω => b025 lam (Y s ω)
  let X := driverForm R.I (0 : Fin 1 → ℝ) H K
  have hH : ∀ i j, U4 R.ℱ R.μ (H i j) := fun _ _ => hsol.2.2.1
  have hK : ∀ i, LocallyIntegrableDrift R.ℱ R.μ (K i) := fun _ => hsol.2.2.2.1
  have hX : ∀ᵐ ω ∂R.μ, ∀ t, X t ω = fun _ => Y t ω := by
    filter_upwards [hsol.2.2.2.2] with ω he t
    funext i
    simpa only [X,driverForm,H,K,Pi.zero_apply,zero_add,sum_single k hsingle] using (he t).symm
  obtain ⟨hU,hIto⟩ := R.ito_formula 1 0 H K F025 hH hK F_smooth
  have hg := g_domain R P Y hsol.1 hY
  have he : ∀ᵐ ω ∂R.μ, ∀ s : ℝ≥0,
      dX F025 ((s:ℝ),X s ω) 0 * H 0 k s ω = g025 (Y s ω) := by
    filter_upwards [hX] with ω hX s
    rw [hX s, F_dX]
    rfl
  have hI := Novel.ZeroMeanReversionUpstreamBridgeProof.int_congr_ae R k _ _ (hU 0 k) hg he
  refine ⟨hg,?_⟩
  filter_upwards [hX,hI,hIto] with ω hX hI ht t
  have ht := ht t
  change F025 ((t:ℝ), X t ω) = _ at ht
  rw [hX t] at ht
  change v025 (Y t ω) = _ at ht
  simp only [Fin.sum_univ_one,sum_single k hsingle] at ht
  have hdr : (∫ s in (0:ℝ)..(t:ℝ),
      dT F025 (s, X (Real.toNNReal s) ω) +
      dX F025 (s, X (Real.toNNReal s) ω) 0 * K 0 (Real.toNNReal s) ω +
      (1/2:ℝ) * (dXX F025 (s, X (Real.toNNReal s) ω) 0 0 *
        H 0 k (Real.toNNReal s) ω * H 0 k (Real.toNNReal s) ω * R.c k k (Real.toNNReal s))) =
      ∫ s in (0:ℝ)..(t:ℝ), h025 lam (Y (Real.toNNReal s) ω) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hX _,F_dT,F_dX,F_dXX,hc]
    dsimp only [H,K,h025]
    have ha := (density (Y (Real.toNNReal s) ω)).1
    linear_combination -(Real.tanh (Y (Real.toNNReal s) ω)) *
      (1-(Real.tanh (Y (Real.toNNReal s) ω))^2) * ha
  change v025 (Y t ω) = F025 (0,0) + _ + _ at ht
  rw [hdr,hI t] at ht
  simpa only [F025,v025,Pi.zero_apply,Real.tanh_zero,add_zero] using ht

lemma bounded_U5 {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hU : U4 S.ℱ S.μ H)
    (hb : ∀ s ω, (H s ω)^2 ≤ 4) (T : ℝ≥0) : U5 S.ℱ S.μ H T := by
  refine ⟨hU,?_⟩
  have hle (ω : Ω) : (∫⁻ s in Set.Icc (0:ℝ) T, ENNReal.ofReal ((H (Real.toNNReal s) ω)^2)) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (T:ℝ) := by
    calc
      _ ≤ ∫⁻ _s in Set.Icc (0:ℝ) T, ENNReal.ofReal 4 :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hb _ _)
      _ = _ := by rw [setLIntegral_const,Real.volume_Icc,sub_zero]
  apply lt_of_le_of_lt (lintegral_mono hle)
  simp only [lintegral_const,measure_univ,mul_one]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma covariation : covariationStatement := by
  intro Ω mΩ S P k hc Y hYa hY tau
  have ha : Continuous a025 := Real.continuous_sqrt.comp
    (continuous_const.add tanh_smooth.continuous)
  have hUa : U4 S.ℱ S.μ (fun s ω => a025 (Y s ω)) := by
    apply Novel.BoundedVarianceMartingaleProof.bounded_U4 S _
      (P.continuous_predictable _ (fun t => ha.measurable.comp (hYa t))
        (fun ω => ha.comp (hY ω))) 2
    intro s ω
    dsimp only [Function.comp_apply]
    rw [(density (Y s ω)).1]
    linarith [(bounds025 (Y s ω)).2.1]
  have hUg := g_domain S P Y hYa hY
  have hVa := bounded_U5 S _ hUa (fun s ω => by
    rw [(density (Y s ω)).1]; linarith [(bounds025 (Y s ω)).2.1]) tau
  have hVg := bounded_U5 S _ hUg (fun s ω => (density (Y s ω)).2.2.2) tau
  have hMa := S.int_product_martingale k k _ _ tau hVa hVa
  have hMg := S.int_product_martingale k k _ _ tau hVg hVg
  have hea : (fun t ω => S.I k (fun s ω => a025 (Y s ω)) (min t tau) ω *
      S.I k (fun s ω => a025 (Y s ω)) (min t tau) ω -
      ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), a025 (Y (Real.toNNReal s) ω)*
        a025 (Y (Real.toNNReal s) ω)*S.c k k (Real.toNNReal s)) =
      fun t ω => (S.I k (fun s ω => a025 (Y s ω)) (min t tau) ω)^2 -
        ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), v025 (Y (Real.toNNReal s) ω) := by
    funext t ω
    rw [← pow_two]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hc,mul_one,← pow_two,(density _).1]
  have heg : (fun t ω => S.I k (fun s ω => g025 (Y s ω)) (min t tau) ω *
      S.I k (fun s ω => g025 (Y s ω)) (min t tau) ω -
      ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), g025 (Y (Real.toNNReal s) ω)*
        g025 (Y (Real.toNNReal s) ω)*S.c k k (Real.toNNReal s)) =
      fun t ω => (S.I k (fun s ω => g025 (Y s ω)) (min t tau) ω)^2 -
        ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ),
          (1-(Real.tanh (Y (Real.toNNReal s) ω))^2)^2*v025 (Y (Real.toNNReal s) ω) := by
    funext t ω
    rw [← pow_two]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hc,mul_one,← pow_two,(density _).2.1]
  rw [hea] at hMa
  rw [heg] at hMg
  exact ⟨hMa,hMg⟩

lemma transfer : Standalone.BoundedVarianceIto.transferStatement := by
  intro Ω mΩ S R A D P Q k l hsingle hμ hB hRS hc lam hl Y hsol hY
  have hYa : Adapted S.ℱ Y := fun t => (hsol.1 t).mono (hRS t) le_rfl
  have hUgS := g_domain S P Y hYa hY
  have hUgR := g_domain R Q Y hsol.1 hY
  have hcomp := Novel.BoundedVarianceIntegralComparisonProof.comparison Ω mΩ S R A D k l
    hμ hB (fun s ω => g025 (Y s ω))
    (fun t => g_continuous.measurable.comp (hYa t))
    (fun t => g_continuous.measurable.comp (hsol.1 t))
    (fun ω => g_continuous.comp (hY ω))
    ⟨2, by norm_num, fun t ω => (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
      (by simpa only [sq_abs,show (2:ℝ)^2 = 4 by norm_num] using (density (Y t ω)).2.2.2)⟩
    hUgS hUgR
  have hito := (ito Ω mΩ R Q l hsingle hc lam hl Y hsol hY).2
  rw [hμ] at hito
  refine ⟨hUgS,?_⟩
  filter_upwards [hcomp,hito] with ω he hi t
  rw [he t]
  exact hi t

lemma derivative : derivativeStatement := by
  intro Y hY tau t ht
  have hv : Continuous fun s => v025 (Y s) := continuous_const.add (tanh_smooth.continuous.comp hY)
  have hq : Continuous fun s => (1-(Real.tanh (Y s))^2)^2*v025 (Y s) :=
    ((continuous_const.sub ((tanh_smooth.continuous.comp hY).pow 2)).pow 2).mul hv
  have hd (f : ℝ → ℝ) (hf : Continuous f) :
      HasDerivAt (fun u => ∫ s in (0:ℝ)..min u tau, f s) (f t) t := by
    apply (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    rw [min_eq_left (le_of_lt hu)]
  refine ⟨hd _ hv,hd _ hq,?_⟩
  rw [← (density (Y t)).2.1]
  exact (density (Y t)).2.2.1

theorem boundedVarianceIto : Standalone.BoundedVarianceIto.statement :=
  ⟨ito,density,covariation,transfer,derivative⟩

end Novel.BoundedVarianceItoProof

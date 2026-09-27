import Standalone.BoundedVarianceBond
import Novel.BoundedVarianceIndependenceProof

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIndependence
open Novel.BoundedVarianceStateProof Novel.BoundedVarianceIntegralComparisonProof
set_option maxHeartbeats 1200000
open Standalone.BoundedVarianceBond
namespace Novel.BoundedVarianceBondProof

lemma drift_integral (lam x : ℝ) (hl : 0 < lam) (Y : ℝ → ℝ)
    (hY : Continuous Y) (u : ℝ) :
    (u / lam) * A025 lam 1 x +
      (∫ s in (0:ℝ)..u, b025 lam (Y s)) * A025 lam 2 x -
      (∫ s in (0:ℝ)..u, v025 (Y s)/(2*lam)) * A025 lam 4 x =
      (1/2:ℝ) * ∫ s in (0:ℝ)..u,
        (A025 lam 1 x)^2 + v025 (Y s)*(A025 lam 2 x)^2 := by
  have hv : Continuous fun s => v025 (Y s) := continuous_const.add
    ((continuous_iff_continuousAt.2 fun z => (tanh_derivative025 z).continuousAt).comp hY)
  have hb : Continuous fun s => b025 lam (Y s) := by
    exact ((continuous_iff_continuousAt.2 fun z =>
      ((coefficient lam hl).1 z).2.2.2.2.2.1.continuousAt).comp hY)
  have he : (fun s => A025 lam 1 x/lam + b025 lam (Y s)*A025 lam 2 x -
      v025 (Y s)/(2*lam)*A025 lam 4 x) =
      fun s => (1/2:ℝ)*((A025 lam 1 x)^2 + v025 (Y s)*(A025 lam 2 x)^2) := by
    funext s
    have h := (drift lam (v025 (Y s)) x hl (by linarith [(bounds025 (Y s)).1])).2.1
    dsimp [b025, v025] at *
    convert h using 1; ring
  have hi := congrArg (fun f : ℝ → ℝ => ∫ s in (0:ℝ)..u, f s) he
  have hbI : IntervalIntegrable (fun s => b025 lam (Y s)*A025 lam 2 x) volume 0 u :=
    (hb.intervalIntegrable 0 u).mul_const _
  have hvI : IntervalIntegrable (fun s => v025 (Y s)/(2*lam)*A025 lam 4 x) volume 0 u :=
    ((hv.div_const (2*lam)).intervalIntegrable 0 u).mul_const _
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hbI) hvI,
    intervalIntegral.integral_add intervalIntegrable_const hbI] at hi
  simp only [intervalIntegral.integral_const, sub_zero,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, smul_eq_mul] at hi
  convert hi using 1; ring

lemma integral_sum {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
    (i j : Fin S.m) (hij : i ≠ j) (lam x : ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hp : IsStronglyPredictable S.ℱ (fun t ω => a025 (Y t ω)))
    (hU : U4 S.ℱ S.μ (fun t ω => a025 (Y t ω))) :
    ∀ᵐ ω ∂S.μ, ∀ t,
      (∑ k, S.I k (H025 i j lam x (fun s ω => Y (Real.toNNReal s) ω) k) t ω) =
      -A025 lam 1 x * S.B i t ω - A025 lam 2 x * S.I j (fun s ω => a025 (Y s ω)) t ω := by
  classical
  let H := H025 i j lam x (fun s ω => Y (Real.toNNReal s) ω)
  have hp' : IsStronglyPredictable S.ℱ (fun t ω => a025 (Y (Real.toNNReal t) ω)) := by
    simpa only [Real.toNNReal_coe] using hp
  have hH : ∀ k, U4 S.ℱ S.μ (H k) :=
    Novel.BoundedVarianceMartingaleProof.domains S i j lam x
      (fun s ω => Y (Real.toNNReal s) ω) hp'
  have h1 : U4 S.ℱ S.μ (fun _ _ => (1:ℝ)) :=
    Novel.BoundedVarianceMartingaleProof.bounded_U4 S _ stronglyMeasurable_const 1 (by intros; simp)
  have hz := Novel.ZeroMeanReversionUpstreamBridgeProof.U4_zero S
  have hi : ∀ᵐ ω ∂S.μ, ∀ t, S.I i (H i) t ω = -A025 lam 1 x * S.B i t ω := by
    apply continuous_paths_eq S.μ _ _ (S.int_continuous i _ (hH i))
      ((S.B_continuous i).mono fun ω h => continuous_const.mul h)
    intro t
    filter_upwards [S.int_linear i (fun _ _ => 1) (fun _ _ => 0)
      (-A025 lam 1 x) 0 h1 hz t, constant Ω mΩ S A i] with ω he hc
    have hh : H i = (-A025 lam 1 x) • (fun (_ : ℝ≥0) (_ : Ω) => (1:ℝ)) +
        (0:ℝ) • (fun (_ : ℝ≥0) (_ : Ω) => (0:ℝ)) := by
      funext s ω
      simp only [H,H025,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        mul_one,zero_mul,add_zero]
    rw [hh]
    simpa only [Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul,zero_mul,add_zero,hc t] using he
  have hj : ∀ᵐ ω ∂S.μ, ∀ t, S.I j (H j) t ω =
      -A025 lam 2 x * S.I j (fun s ω => a025 (Y s ω)) t ω := by
    apply continuous_paths_eq S.μ _ _ (S.int_continuous j _ (hH j))
      ((S.int_continuous j _ hU).mono fun ω h => continuous_const.mul h)
    intro t
    filter_upwards [S.int_linear j (fun s ω => a025 (Y s ω)) (fun _ _ => 0)
      (-A025 lam 2 x) 0 hU hz t] with ω he
    have hh : H j = (-A025 lam 2 x) • (fun (s : ℝ≥0) (ω : Ω) => a025 (Y s ω)) +
        (0:ℝ) • (fun (_ : ℝ≥0) (_ : Ω) => (0:ℝ)) := by
      funext s ω
      simp only [H,H025,ite_eq_right (Ne.symm hij),ite_true,Pi.add_apply,Pi.smul_apply,
        smul_eq_mul,Real.toNNReal_coe,zero_mul,add_zero]
      ring
    rw [hh]
    simpa only [Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul,zero_mul,add_zero] using he
  have ho : ∀ᵐ ω ∂S.μ, ∀ k, k ≠ i → k ≠ j → ∀ t, S.I k (H k) t ω = 0 := by
    apply ae_all_iff.2
    intro k
    by_cases hki : k = i
    · exact Eventually.of_forall fun _ h => (h hki).elim
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ _ h => (h hkj).elim
    filter_upwards [Novel.ZeroMeanReversionUpstreamBridgeProof.zero_integral S k] with ω h _ _ t
    have hh : H k = fun _ _ => (0:ℝ) := by
      funext s ω; simp only [H,H025,ite_eq_right hki,ite_eq_right hkj]
    rw [hh]
    exact h t
  filter_upwards [hi,hj,ho] with ω hi hj ho t
  have he (k : Fin S.m) : S.I k (H k) t ω =
      (if k = i then -A025 lam 1 x * S.B i t ω else 0) +
      (if k = j then -A025 lam 2 x * S.I j (fun s ω => a025 (Y s ω)) t ω else 0) := by
    by_cases hki : k = i
    · subst k; simp [hi t, hij]
    by_cases hkj : k = j
    · subst k; simp [hj t, Ne.symm hij]
    simp [hki,hkj,ho k hki hkj t]
  change (∑ k, S.I k (H k) t ω) = _
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma exponential_identity {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (A : Standalone.BoundedVarianceIntegralComparison.IntegralApproximation S)
    (P : Predictability S.ℱ) (i j : Fin S.m) (hij : i ≠ j)
    (hc : ∀ k l t, S.c k l t = if k = l then 1 else 0)
    (lam x : ℝ) (hl : 0 < lam) (Y : ℝ≥0 → Ω → ℝ)
    (hsol : ScalarSolution025 S j lam Y)
    (hY : ∀ ω, Continuous fun t => Y t ω) (tau : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, ∀ t,
      exponential10 S (H025 i j lam x (fun s ω => Y (Real.toNNReal s) ω)) tau t ω =
      Real.exp (-L025 lam (z025 S i lam Y (min t tau) ω) x) := by
  have ha : Continuous a025 := Real.continuous_sqrt.comp
    (continuous_const.add (continuous_iff_continuousAt.2 fun z =>
      (tanh_derivative025 z).continuousAt))
  have hp := P.continuous_predictable (fun t ω => a025 (Y t ω))
    (fun t => ha.measurable.comp (hsol.1 t)) (fun ω => ha.comp (hY ω))
  filter_upwards [integral_sum S A i j hij lam x Y hp hsol.2.2.1,
    hsol.2.2.2.2] with ω hsum hsde t
  have hd := drift_integral lam x hl (fun s => Y (Real.toNNReal s) ω)
    ((hY ω).comp continuous_real_toNNReal) (min t tau)
  unfold exponential10
  rw [hsum (min t tau), Novel.BoundedVarianceMartingaleProof.covariance_sum
    S i j hij hc lam x (fun s ω => Y (Real.toNNReal s) ω) ω
    ((hY ω).comp continuous_real_toNNReal) tau t]
  apply congrArg Real.exp
  dsimp only [L025, z025, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const]
  rw [hsde (min t tau)]
  simp only [NNReal.coe_min]
  linear_combination hd

lemma price_formula {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i : Fin S.m) (lam : ℝ) (hl : 0 < lam) (Y : ℝ≥0 → Ω → ℝ)
    (tau T t : ℝ≥0) (htau : 0 < tau) (hT : tau ≤ T) (ω : Ω) :
    D025 S i lam Y tau T t ω =
      Real.exp (-L025 lam (z025 S i lam Y (min t tau) ω) ((T:ℝ)-tau)) := by
  have h := bond lam tau hl htau
    (fun s => z025 S i lam Y (Real.toNNReal s) ω)
    (min t T) T (min t T).coe_nonneg (NNReal.coe_le_coe.2 (min_le_right _ _))
  unfold D025
  by_cases ht : t ≤ tau
  · have htT := ht.trans hT
    simpa only [min_eq_left htT, min_eq_left (NNReal.coe_le_coe.2 htT), min_eq_left ht, Real.toNNReal_coe] using
      h.2.2.2.1 (NNReal.coe_le_coe.2 ((min_le_left t T).trans ht)) hT
  · have htu : tau ≤ min t T := le_min (le_of_not_ge ht) hT
    simpa only [min_eq_right (le_of_not_ge ht), Real.toNNReal_coe] using
      (h.2.2.2.2.1 htu).2

lemma identity : Standalone.BoundedVarianceBond.identityStatement := by
  intro Ω mΩ S A P i j hij hc lam hl Y hsol hY tau T htau hT
  filter_upwards [exponential_identity S A P i j hij hc lam ((T:ℝ)-tau) hl Y hsol hY tau]
    with ω he t
  rw [price_formula S i lam hl Y tau T t htau hT ω, he t]

lemma integral_adapted {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ) (hYa : Adapted S.ℱ Y)
    (hY : ∀ ω, Continuous fun t => Y t ω) (u : ℝ≥0) :
    Measurable[S.ℱ u] (fun ω => ∫ s in (0:ℝ)..(u:ℝ), v025 (Y (Real.toNNReal s) ω)/(2*lam)) := by
  have hv : Continuous v025 := continuous_const.add
    (continuous_iff_continuousAt.2 fun z => (tanh_derivative025 z).continuousAt)
  have hm0 (s : ℝ) : Measurable[S.ℱ u]
      (fun ω => v025 (Y (min (Real.toNNReal s) u) ω)/(2*lam)) :=
    (hv.measurable.comp ((hYa _).mono (S.ℱ.mono (min_le_right _ _)) le_rfl)).div_const _
  letI : MeasurableSpace Ω := S.ℱ u
  have hm : Measurable (fun p : ℝ × Ω => v025 (Y (min (Real.toNNReal p.1) u) p.2)/(2*lam)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hv.comp ((hY ω).comp (continuous_real_toNNReal.min continuous_const))).div_const _)
      hm0
  have hi := hm.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Set.Ioc (0:ℝ) u))
  have he : (fun ω => ∫ s in (0:ℝ)..(u:ℝ), v025 (Y (Real.toNNReal s) ω)/(2*lam)) =
      fun ω => ∫ s in Set.Ioc (0:ℝ) u, v025 (Y (min (Real.toNNReal s) u) ω)/(2*lam) := by
    funext ω
    rw [intervalIntegral.integral_of_le u.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  rw [he]
  exact hi.measurable

lemma price_adapted {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i : Fin S.m) (lam : ℝ) (hl : 0 < lam) (Y : ℝ≥0 → Ω → ℝ)
    (hYa : Adapted S.ℱ Y) (hY : ∀ ω, Continuous fun t => Y t ω)
    (tau T : ℝ≥0) (htau : 0 < tau) (hT : tau ≤ T) :
    StronglyAdapted S.ℱ (D025 S i lam Y tau T) := by
  intro t
  have hu : min t tau ≤ t := min_le_left _ _
  have hz1 : Measurable[S.ℱ t] (fun ω => ((min t tau:ℝ≥0):ℝ)/lam + S.B i (min t tau) ω) :=
    measurable_const.add ((S.B_adapted i _).mono (S.ℱ.mono hu) le_rfl)
  have hz2 := (hYa (min t tau)).mono (S.ℱ.mono hu) le_rfl
  have hz4 := (integral_adapted S lam Y hYa hY (min t tau)).neg.mono (S.ℱ.mono hu) le_rfl
  have hL := ((hz1.mul_const (A025 lam 1 ((T:ℝ)-tau))).add
    (hz2.mul_const (A025 lam 2 ((T:ℝ)-tau)))).add
    (hz4.mul_const (A025 lam 4 ((T:ℝ)-tau)))
  have he : D025 S i lam Y tau T t = fun ω =>
      Real.exp (-L025 lam (z025 S i lam Y (min t tau) ω) ((T:ℝ)-tau)) :=
    funext (price_formula S i lam hl Y tau T t htau hT)
  rw [he]
  exact hL.neg.exp.stronglyMeasurable

lemma martingale : Standalone.BoundedVarianceBond.martingaleStatement := by
  intro Ω mΩ S A P E i j hij hc lam hl Y hsol hY tau T htau
  by_cases hT : tau ≤ T
  · have hYa : ∀ t : ℝ≥0, Measurable[S.ℱ t] (Y (Real.toNNReal t)) := by
      intro t
      rw [Real.toNNReal_coe]
      exact hsol.1 t
    have hm := (Novel.BoundedVarianceMartingaleProof.adapted Ω mΩ S E P i j hij hc
      lam ((T:ℝ)-tau) tau hl (sub_nonneg.2 (NNReal.coe_le_coe.2 hT))
      (fun s ω => Y (Real.toNNReal s) ω) hYa
      (fun ω => (hY ω).comp continuous_real_toNNReal)).2
    apply hm.congr (price_adapted S i lam hl Y hsol.1 hY tau T htau hT)
    intro t
    exact (identity Ω mΩ S A P i j hij hc lam hl Y hsol hY tau T htau hT).mono
      fun ω h => (h t).symm
  · have he : D025 S i lam Y tau T = fun _ _ => (1:ℝ) := by
      funext t ω
      exact (bond lam tau hl htau (fun s => z025 S i lam Y (Real.toNNReal s) ω)
        (min t T) T (min t T).coe_nonneg (NNReal.coe_le_coe.2 (min_le_right _ _))).2.2.1
        (NNReal.coe_le_coe.2 (le_of_not_ge hT))
    rw [he]
    exact martingale_const S.ℱ S.μ (1:ℝ)

theorem boundedVarianceBond : Standalone.BoundedVarianceBond.statement := ⟨identity,martingale⟩

end Novel.BoundedVarianceBondProof

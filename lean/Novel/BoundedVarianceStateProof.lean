import Standalone.BoundedVarianceState
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open MeasureTheory Matrix Set Filter
open Standalone.BoundedVarianceState
open scoped NNReal
namespace Novel.BoundedVarianceStateProof

lemma tanh_derivative025 (z : ℝ) : HasDerivAt Real.tanh (1-Real.tanh z^2) z := by
  have h := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (ne_of_gt (Real.cosh_pos z))
  convert h using 1
  · ext x; exact Real.tanh_eq_sinh_div_cosh x
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

lemma bounds025 (z : ℝ) : 1 < v025 z ∧ v025 z < 3 ∧ 0 < 1-Real.tanh z^2 := by
  have h1 := Real.neg_one_lt_tanh z
  have h2 := Real.tanh_lt_one z
  have h3 := Real.tanh_sq_lt_one z
  dsimp [v025]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma coefficient : coefficientStatement := by
  intro lam hlam
  have hb (z) : HasDerivAt (b025 lam) ((1-Real.tanh z^2)/(2*lam)) z :=
    (tanh_derivative025 z).div_const _
  have ha (z) : HasDerivAt a025 ((1-Real.tanh z^2)/(2*a025 z)) z := by
    exact ((tanh_derivative025 z).const_add 2).sqrt (by have := (bounds025 z).1; dsimp [v025] at *; linarith)
  have hbb (z) : |(1-Real.tanh z^2)/(2*lam)| ≤ 1/(2*lam) := by
    rw [abs_of_nonneg (div_nonneg (bounds025 z).2.2.le (by positivity))]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (Real.tanh z)]) (by positivity)
  have hab (z) : |(1-Real.tanh z^2)/(2*a025 z)| ≤ (1/2:ℝ) := by
    have hv := bounds025 z
    have hs : 1 < a025 z := by dsimp [a025]; exact (Real.lt_sqrt (by norm_num)).2 (by nlinarith)
    rw [abs_of_nonneg (div_nonneg hv.2.2.le (by linarith))]
    apply (div_le_iff₀ (by linarith : 0 < 2*a025 z)).2
    nlinarith [sq_nonneg (Real.tanh z)]
  refine ⟨?_,?_,?_⟩
  · intro z
    have hv := bounds025 z
    have hs : 1 < a025 z := by dsimp [a025]; exact (Real.lt_sqrt (by norm_num)).2 (by nlinarith)
    refine ⟨hv.1,hv.2.1,?_,hs,?_,hb z,ha z,?_,?_⟩
    · dsimp [b025]
      rw [abs_div,abs_of_pos (by positivity : 0 < 2*lam)]
      exact div_le_div_of_nonneg_right (Real.abs_tanh_lt_one z).le (by positivity)
    · exact Real.sqrt_lt_sqrt (by linarith [hv.1]) hv.2.1
    · exact mul_pos (sq_pos_of_pos hv.2.2) (by linarith [hv.1])
    · have hi := Real.artanh_eq_half_log (x := Real.tanh z)
        (show Real.tanh z ∈ Icc (-1:ℝ) 1 from ⟨(Real.neg_one_lt_tanh z).le,(Real.tanh_lt_one z).le⟩)
      rw [Real.artanh_tanh] at hi
      have he : (v025 z-1)/(3-v025 z) = (1+Real.tanh z)/(1-Real.tanh z) := by
        congr 1 <;> dsimp [v025] <;> ring
      rw [he]
      exact hi
  · intro x y
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hb z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hbb z)
      convex_univ (mem_univ y) (mem_univ x)
    simpa only [Real.norm_eq_abs] using h
  · intro x y
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (ha z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hab z)
      convex_univ (mem_univ y) (mem_univ x)
    simpa only [Real.norm_eq_abs] using h

lemma shape : shapeStatement := by
  intro lam k hl hk
  have hn : k*lam ≠ 0 := ne_of_gt (mul_pos hk hl)
  have hd (x) : HasDerivAt (A025 lam k) (e025 lam k x) x := by
    have h := (((hasDerivAt_id x).const_mul (-k*lam)).exp.const_sub 1).div_const (k*lam)
    convert h using 1
    · rfl
    · dsimp [e025]
      field_simp
  refine ⟨hd,by simp [A025,e025],fun x hx => ?_⟩
  have he : e025 lam k x ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith [mul_pos hk hl]
  refine ⟨Real.exp_pos _,he,div_nonneg (sub_nonneg.2 he) (mul_pos hk hl).le,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by have := Real.exp_pos (-k*lam*x); dsimp [e025]; linarith) (mul_pos hk hl).le
  · have hc : Continuous (e025 lam k) := Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable 0 x)
    simpa [A025,e025] using h

lemma exp_double025 (lam k x : ℝ) : e025 lam (2*k) x = (e025 lam k x)^2 := by
  dsimp [e025]
  rw [show -(2*k)*lam*x = (-k*lam*x)+(-k*lam*x) by ring,Real.exp_add]
  ring

lemma drift : driftStatement := by
  intro lam v x hl hv
  have hn := ne_of_gt hl
  have h2 : e025 lam 2 x = (e025 lam 1 x)^2 := by simpa using exp_double025 lam 1 x
  have h4 : e025 lam 4 x = (e025 lam 2 x)^2 := by convert exp_double025 lam 2 x using 1; norm_num
  refine ⟨?_,?_,?_,?_⟩
  · have hs : (Real.sqrt v*e025 lam 2 x)*(Real.sqrt v*A025 lam 2 x) =
        v*e025 lam 2 x*A025 lam 2 x := by
      calc _ = (Real.sqrt v)^2*e025 lam 2 x*A025 lam 2 x := by ring
           _ = _ := by rw [Real.sq_sqrt hv]
    rw [hs]
    dsimp [A025]
    rw [h4,h2]
    field_simp
    ring
  · dsimp [A025]
    rw [h4,h2]
    field_simp
    ring
  · field_simp; ring
  · intro hx hv3
    have hA1 := (shape lam 1 hl (by norm_num)).2.2 x hx
    have hA2 := (shape lam 2 hl (by norm_num)).2.2 x hx
    have h1 : (A025 lam 1 x)^2 ≤ (1/lam)^2 := by
      have hb := hA1.2.2.2.1
      simp only [one_mul] at hb
      exact pow_le_pow_left₀ hA1.2.2.1 hb 2
    have h2' : (A025 lam 2 x)^2 ≤ (1/(2*lam))^2 := by nlinarith [hA2.2.2.1,hA2.2.2.2.1]
    have he : (1/lam)^2 + 3*(1/(2*lam))^2 = 7/(4*lam^2) := by field_simp; ring
    rw [← he]
    nlinarith [mul_nonneg hv (sub_nonneg.2 h2'),mul_nonneg (sub_nonneg.2 hv3) (sq_nonneg (1/(2*lam)))]

lemma curve : curveStatement := by
  intro lam tau hl z
  have he (k : ℝ) (hk : 0 ≤ k) (T : ℝ) (hT : tau ≤ T) : |e025 lam k (T-tau)| ≤ 1 := by
    dsimp only [e025]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.2
    have := mul_nonneg hk hl
    nlinarith
  refine ⟨fun T => ?_,fun T hT => by simp [f025,hT],by simp [f025,e025],fun x => by ring⟩
  by_cases hT : T < tau
  · simp only [f025,ite_eq_left hT,abs_zero]
    positivity
  · simp only [f025,ite_eq_right hT]
    calc
      _ ≤ |z 0*e025 lam 1 (T-tau)|+|z 1*e025 lam 2 (T-tau)|+|z 2*e025 lam 4 (T-tau)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |z 0|+|z 1|+|z 2| := by
        simp only [abs_mul]
        exact add_le_add (add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (he 1 (by norm_num) T (le_of_not_gt hT)))
          (mul_le_of_le_one_right (abs_nonneg _) (he 2 (by norm_num) T (le_of_not_gt hT))))
          (mul_le_of_le_one_right (abs_nonneg _) (he 4 (by norm_num) T (le_of_not_gt hT)))

lemma eval_exp025 (lam : ℝ) (hl : 0 < lam) (i k : ℕ) :
    e025 lam k ((i:ℝ)*Real.log 2/lam) = (1/2:ℝ)^(i*k) := by
  dsimp [e025]
  rw [show -(k:ℝ)*lam*((i:ℝ)*Real.log 2/lam) = -((i*k:ℕ):ℝ)*Real.log 2 by
    push_cast; field_simp]
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : 0 < (2:ℝ))]
  simp [inv_pow]

lemma recovery : recoveryStatement := by
  intro lam tau hl
  have hdet : M025.det = -(21/1024:ℝ) := by norm_num [M025,Matrix.det_fin_three]
  have he (z : Fin 3 → ℝ) :
      (fun i : Fin 3 => f025 lam tau z (tau+(i:ℕ)*Real.log 2/lam)) = M025.mulVec z := by
    funext i
    have hpos : 0 ≤ (i:ℕ)*Real.log 2/lam := by positivity
    simp only [f025,not_lt.mpr (show tau ≤ tau+(i:ℕ)*Real.log 2/lam by linarith),ite_false,add_sub_cancel_left]
    have h1 := eval_exp025 lam hl (i:ℕ) 1
    have h2 := eval_exp025 lam hl (i:ℕ) 2
    have h4 := eval_exp025 lam hl (i:ℕ) 4
    norm_num only [Nat.cast_ofNat] at h1 h2 h4
    rw [h1,h2,h4]
    fin_cases i <;> simp [M025,Matrix.mulVec,Fin.sum_univ_succ,dotProduct] <;> ring
  refine ⟨hdet,he,?_⟩
  intro z w h
  dsimp only at h
  rw [he z,he w] at h
  have hd : IsUnit M025.det := isUnit_iff_ne_zero.2 (by rw [hdet]; norm_num)
  exact (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det M025).2 hd)) h

lemma path : pathStatement := by
  intro lam tau Z hZ
  have hc (i : Fin 3) : Continuous fun t => Z (min t tau) i :=
    (hZ i).comp (continuous_id.min continuous_const)
  refine ⟨fun T => ?_,fun T t ht => by rw [min_eq_right ht],?_,?_⟩
  · by_cases hT : T < tau
    · simp only [f025,ite_eq_left hT]; exact continuous_const
    · simp only [f025,ite_eq_right hT]
      exact ((hc 0).mul continuous_const |>.add ((hc 1).mul continuous_const)).add ((hc 2).mul continuous_const)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [f025,show t < tau from ht]
  · simp [f025,e025]


lemma curve_integrable025 (lam tau : ℝ) (z : Fin 3 → ℝ) (a b : ℝ) :
    IntervalIntegrable (f025 lam tau z) volume a b := by
  let g := fun u => z 0*e025 lam 1 (u-tau)+z 1*e025 lam 2 (u-tau)+z 2*e025 lam 4 (u-tau)
  have hg : Continuous g := by dsimp [g,e025]; fun_prop
  have he : f025 lam tau z = (Ici tau).indicator g := by
    funext u
    by_cases hu : u < tau
    · simp [f025,hu]
    · simp [f025,hu,Set.indicator_of_mem (show u ∈ Ici tau from le_of_not_gt hu),g]
  rw [he]
  exact ⟨(hg.intervalIntegrable a b).1.indicator measurableSet_Ici,
    (hg.intervalIntegrable a b).2.indicator measurableSet_Ici⟩

lemma curve_integral_before025 (lam tau : ℝ) (z : Fin 3 → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hb : b ≤ tau) : (∫ u in a..b, f025 lam tau z u) = 0 := by
  calc
    _ = ∫ _u in a..b, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne tau] with u hu hI
      have hu' : u < tau := lt_of_le_of_ne ((by simpa [Set.uIoc_of_le hab] using hI : u ∈ Ioc a b).2.trans hb) hu
      simp [f025,hu']
    _ = 0 := by simp

lemma curve_integral_after025 (lam tau : ℝ) (hl : 0 < lam) (z : Fin 3 → ℝ)
    (a b : ℝ) (ha : tau ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, f025 lam tau z u) = L025 lam z (b-tau)-L025 lam z (a-tau) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have htu : tau ≤ u := ha.trans ((by simpa [Set.uIcc_of_le hab] using hu : u ∈ Icc a b).1)
    have hd (k : ℝ) (hk : 0 < k) :
        HasDerivAt (fun u => A025 lam k (u-tau)) (e025 lam k (u-tau)) u := by
      convert! ((shape lam k hl hk).1 (u-tau)).comp u ((hasDerivAt_id u).sub_const tau) using 1; simp
    convert! (((hd 1 (by norm_num)).const_mul (z 0)).add ((hd 2 (by norm_num)).const_mul (z 1))).add
        ((hd 4 (by norm_num)).const_mul (z 2)) using 1
    simp [f025,not_lt.mpr htu]
  · exact curve_integrable025 lam tau z a b

lemma curve_integral_cross025 (lam tau : ℝ) (hl : 0 < lam) (z : Fin 3 → ℝ)
    (a b : ℝ) (ha : a ≤ tau) (hb : tau ≤ b) :
    (∫ u in a..b, f025 lam tau z u) = L025 lam z (b-tau) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (curve_integrable025 lam tau z a tau) (curve_integrable025 lam tau z tau b),
    curve_integral_before025 lam tau z a tau ha le_rfl,
    curve_integral_after025 lam tau hl z tau b le_rfl hb]
  simp [L025,A025,e025]

lemma short_frozen025 (lam tau : ℝ) (Z : ℝ → Fin 3 → ℝ) :
    (fun u => f025 lam tau (Z (min u tau)) u) = f025 lam tau (Z tau) := by
  funext u
  by_cases hu : u < tau
  · simp [f025,hu]
  · rw [min_eq_right (le_of_not_gt hu)]

lemma bond : bondStatement := by
  intro lam tau hl htau Z t T ht hT
  have hB : B025 lam tau Z t = Real.exp (∫ u in (0:ℝ)..t, f025 lam tau (Z tau) u) := by
    rw [B025,short_frozen025]
  refine ⟨Real.exp_pos _,Real.exp_pos _,?_,?_,?_,by simp [P025],?_⟩
  · intro hTtau
    rw [P025,curve_integral_before025 lam tau _ t T hT hTtau,hB,
      curve_integral_before025 lam tau _ 0 t ht (hT.trans hTtau)]
    norm_num
  · intro htt htT
    rw [P025,min_eq_left htt,curve_integral_cross025 lam tau hl _ t T htt htT,hB,
      curve_integral_before025 lam tau _ 0 t ht htt]
    simp
  · intro htt
    have hp : P025 lam tau Z t T =
        Real.exp (L025 lam (Z tau) (t-tau)-L025 lam (Z tau) (T-tau)) := by
      rw [P025,min_eq_right htt,curve_integral_after025 lam tau hl _ t T htt hT]
      congr 1; ring
    refine ⟨hp,?_⟩
    rw [hp,hB,curve_integral_cross025 lam tau hl _ 0 t htau.le htt,← Real.exp_sub]
    congr 1; ring
  · intro hZ0
    simp [P025,min_eq_left htau.le,hZ0,f025]

lemma integralBound : integralBoundStatement := by
  intro lam tau x hl htau hx Y hY t ht
  have hct : Continuous Real.tanh := continuous_iff_continuousAt.2 fun z => (tanh_derivative025 z).continuousAt
  have hc : Continuous (fun s => (A025 lam 1 x)^2 + v025 (Y s)*(A025 lam 2 x)^2) :=
    continuous_const.add ((continuous_const.add (hct.comp hY)).mul continuous_const)
  have hb (s : ℝ) : (A025 lam 1 x)^2 + v025 (Y s)*(A025 lam 2 x)^2 ≤ 7/(4*lam^2) :=
    (drift lam (v025 (Y s)) x hl (by linarith [(bounds025 (Y s)).1])).2.2.2 hx (bounds025 (Y s)).2.1.le
  calc
    _ ≤ ∫ _s in (0:ℝ)..(min t tau), (7/(4*lam^2):ℝ) :=
      intervalIntegral.integral_mono_on (le_min ht htau) (hc.intervalIntegrable _ _)
        intervalIntegrable_const (fun s _ => hb s)
    _ = (min t tau)*(7/(4*lam^2)) := by simp [mul_div_assoc]
    _ ≤ tau*(7/(4*lam^2)) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = _ := by ring

lemma sum_drift_integral025 (lam : ℝ) (hl : 0 < lam) (Y : ℝ → ℝ)
    (hY : Continuous Y) (tau : ℝ) :
    tau/lam + (∫ s in (0:ℝ)..tau, b025 lam (Y s)) -
      (∫ s in (0:ℝ)..tau, v025 (Y s)/(2*lam)) = 0 := by
  have hct : Continuous Real.tanh := continuous_iff_continuousAt.2 fun z => (tanh_derivative025 z).continuousAt
  have hb : Continuous (fun s => b025 lam (Y s)) :=
    (hct.comp hY).div_const _
  have hv : Continuous (fun s => v025 (Y s)/(2*lam)) :=
    (continuous_const.add (hct.comp hY)).div_const _
  have he : (fun s => b025 lam (Y s)-v025 (Y s)/(2*lam)) = fun _ => -(1/lam) := by
    funext s
    dsimp [b025,v025]
    field_simp
    ring
  rw [add_sub_assoc,← intervalIntegral.integral_sub (hb.intervalIntegrable 0 tau) (hv.intervalIntegrable 0 tau),he]
  simp
  ring

open ProbabilityTheory in
lemma independent_gaussian_sum025 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W J : Ω → ℝ) (tau : ℝ≥0)
    (ht : tau ≠ 0) (hW : HasLaw W (gaussianReal 0 tau) μ)
    (hJ : AEMeasurable J μ) (hi : IndepFun W J μ) :
    ∀ᵐ ω ∂μ, W ω+J ω ≠ 0 := by
  let E : Set (ℝ × ℝ) := {p | p.1+p.2 = 0}
  have hE : MeasurableSet E := measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  have hp := hi.map_prod_eq_prod_map_map hW.aemeasurable hJ
  have hprob : μ {ω | W ω+J ω = 0} = 0 := by
    rw [show {ω | W ω+J ω = 0} = (fun ω => (W ω,J ω)) ⁻¹' E by rfl,
      ← Measure.map_apply_of_aemeasurable (hW.aemeasurable.prodMk hJ) hE,hp,hW.map_eq,
      Measure.prod_apply_symm hE]
    have := nullSingletonClass_gaussianReal (μ := 0) ht
    have hs (y : ℝ) : (fun x => (x,y)) ⁻¹' E = {-y} := by
      ext x
      simp only [E,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp_rw [hs,measure_singleton]
    simp
  simpa only [ae_iff,not_not] using hprob

lemma scheduledJump : scheduledJumpStatement := by
  intro Ω mΩ μ hμ W hW lam tau hl ht Y J hY hJ hi hsde z
  let := hμ
  have he : ∀ᵐ ω ∂μ, f025 lam tau (z ω) tau = W tau ω+J ω := by
    filter_upwards [hY,hsde] with ω hc hs
    have hd := sum_drift_integral025 lam hl (fun s => Y s ω) hc tau
    simp only [f025,lt_self_iff_false,ite_false,sub_self,e025,mul_zero,Real.exp_zero,mul_one]
    change (tau:ℝ)/lam + W tau ω + Y tau ω +
      (-(∫ s in (0:ℝ)..tau, v025 (Y s ω)/(2*lam))) = W tau ω + J ω
    rw [hs]
    linarith
  refine ⟨he,?_⟩
  have hn := independent_gaussian_sum025 μ (W tau) J tau (ne_of_gt ht)
    (hW.toIsPreBrownianReal.hasLaw_eval tau) hJ hi
  filter_upwards [he,hn] with ω he hn
  rwa [he]

theorem boundedVarianceState : Standalone.BoundedVarianceState.statement :=
  ⟨coefficient,shape,drift,curve,recovery,path,bond,integralBound,scheduledJump⟩

end Novel.BoundedVarianceStateProof

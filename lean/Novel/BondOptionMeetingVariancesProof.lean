import Standalone.BondOptionMeetingVariances
import Novel.D3EventVariancesProof
import Novel.MGFUniqueness

open MeasureTheory ProbabilityTheory Set
open Standalone.D3EventVariances Standalone.BondOptionMeetingVariances

namespace Novel.BondOptionMeetingVariancesProof

variable {N : ℕ} {v : Fin N → NNReal}

lemma integral_exp_sum (a : Fin N → ℝ) (b : ℝ) :
    ∫ ω : Ω N, Real.exp (b + ∑ i, a i * ω i) ∂Q v =
      Real.exp (b + ∑ i, (v i : ℝ) * a i ^ 2 / 2) := by
  have hi : iIndepFun (fun i (ω : Ω N) => Real.exp (a i * ω i)) (Q v) :=
    D3EventVariancesProof.indep.comp (fun i x => Real.exp (a i * x)) (by intro i; fun_prop)
  have hp := hi.integral_fun_prod_eq_prod_integral (fun i =>
    (by fun_prop : Measurable (fun ω : Ω N => Real.exp (a i * ω i))).aestronglyMeasurable)
  have hm (i : Fin N) : ∫ ω : Ω N, Real.exp (a i * ω i) ∂Q v =
      Real.exp ((v i : ℝ) * a i ^ 2 / 2) := by
    simpa [mgf] using mgf_gaussianReal (D3EventVariancesProof.law (v := v) i) (a i)
  simp_rw [hm] at hp
  simp_rw [← Real.exp_sum] at hp
  simp_rw [Real.exp_add]
  rw [integral_const_mul, hp]

lemma integrable_exp_sum (a : Fin N → ℝ) (b : ℝ) :
    Integrable (fun ω : Ω N => Real.exp (b + ∑ i, a i * ω i)) (Q v) := by
  by_contra h
  have he := integral_exp_sum (v := v) a b
  rw [integral_undef h] at he
  exact (Real.exp_ne_zero _).symm he

lemma integral_D0148 (a : Fin N → ℝ) : ∫ ω, D0148 v a ω ∂Q v = 1 := by
  have he : D0148 v a = fun ω =>
      Real.exp (-(∑ i, (v i : ℝ) * a i ^ 2 / 2) + ∑ i, a i * ω i) := by
    funext ω
    simp only [D0148, Finset.sum_sub_distrib]
    congr 1
    ring
  rw [he, integral_exp_sum]
  simp

lemma integrable_D0148 (a : Fin N → ℝ) : Integrable (D0148 v a) (Q v) := by
  by_contra h
  have he := integral_D0148 (v := v) a
  rw [integral_undef h] at he
  exact zero_ne_one he

instance (a : Fin N → ℝ) : IsProbabilityMeasure (Q0148 v a) := by
  constructor
  rw [Q0148, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_D0148 a)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_D0148]
  simp

lemma integral_Q0148 (a : Fin N → ℝ) (g : Ω N → ℝ) :
    ∫ ω, g ω ∂Q0148 v a = ∫ ω, D0148 v a ω * g ω ∂Q v := by
  rw [Q0148, integral_withDensity_eq_integral_toReal_smul
    (by unfold D0148; fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [D0148, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

lemma mgf_L0149 (a c : Fin N → ℝ) (b t : ℝ) :
    mgf (L0149 b c) (Q0148 v a) t = Real.exp
      ((b + ∑ i, c i * (v i : ℝ) * a i) * t + (∑ i, (v i : ℝ) * c i ^ 2) * t^2 / 2) := by
  rw [mgf, integral_Q0148]
  have he : (fun ω => D0148 v a ω * Real.exp (t * L0149 b c ω)) =
      fun ω => Real.exp ((t*b - ∑ i, (v i : ℝ)*a i^2/2) +
        ∑ i, (a i+t*c i)*ω i) := by
    funext ω
    rw [D0148, L0149, ← Real.exp_add]
    congr 1
    simp only [Finset.sum_sub_distrib, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    ring
  rw [he, integral_exp_sum]
  congr 1
  simp only [Finset.sum_mul, Finset.sum_div]
  rw [sub_add_eq_add_sub, add_sub_assoc, ← Finset.sum_sub_distrib]
  have he (i : Fin N) : (v i : ℝ) * (a i+t*c i)^2/2 - (v i : ℝ)*a i^2/2 =
      c i*(v i : ℝ)*a i*t + (v i : ℝ)*c i^2*t^2/2 := by ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_mul]
  ring

lemma law_L0149 (a c : Fin N → ℝ) (b : ℝ) :
    HasLaw (L0149 b c)
      (gaussianReal (b + ∑ i, c i * (v i : ℝ) * a i)
        (∑ i, v i * (c i ^ 2).toNNReal))
      (Q0148 v a) := by
  refine ⟨(by unfold L0149; exact (by fun_prop : Measurable _).aemeasurable), ?_⟩
  have hint (t : ℝ) : Integrable (fun ω => Real.exp (t * L0149 b c ω)) (Q0148 v a) := by
    rw [← mgf_pos_iff, mgf_L0149]
    exact Real.exp_pos _
  have h := MGFUniqueness.map_eq_of_mgf_eqOn_Ico (X := L0149 b c) (Y := id)
    (μ' := gaussianReal (b + ∑ i, c i * (v i : ℝ) * a i)
      (∑ i, v i * (c i ^ 2).toNNReal))
    (by unfold L0149; fun_prop) measurable_id (L := 1) (by norm_num)
    (fun t _ => hint (-t)) (fun t _ => integrable_exp_mul_gaussianReal (-t))
    (fun t _ => by rw [mgf_L0149, mgf_id_gaussianReal]; simp only [NNReal.coe_sum, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)])
  simpa using h


noncomputable def a0148 (τ : ℕ → ℝ) (S : ℝ) (i : Fin N) : ℝ :=
  if i ∈ past τ S then -(S - τ (i.val+1)) else 0

noncomputable def c0149 (τ : ℕ → ℝ) (S U : ℝ) (i : Fin N) : ℝ :=
  if i ∈ past τ S then -(U-S) else 0

noncomputable def b0149 (τ : ℕ → ℝ) (v : Fin N → NNReal) (S U : ℝ) : ℝ :=
  -∑ i ∈ past τ S, (v i : ℝ) * ((U-S)*(S-τ (i.val+1))+(U-S)^2/2)

lemma density_eq (τ : ℕ → ℝ) (S : ℝ) (ω : Ω N) :
    D0148 v (a0148 τ S) ω = Real.exp (-logB τ v S ω) := by
  classical
  unfold D0148 a0148 logB
  congr 1
  simp only [ite_mul, mul_ite, ite_pow, neg_sq, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_mul, ite_div, zero_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.sum_neg_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma logbond_eq (τ : ℕ → ℝ) (S U : ℝ) (ω : Ω N) :
    Real.log (bond τ v S U ω) = L0149 (b0149 τ v S U) (c0149 τ S U) ω := by
  classical
  rw [bond, Real.log_exp, D3EventVariancesProof.integral_forward]
  unfold L0149 b0149 c0149 X
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.mul_sum]
  simp only [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma mean_eq (τ : ℕ → ℝ) (S U : ℝ) :
    b0149 τ v S U + ∑ i, c0149 τ S U i * (v i : ℝ) * a0148 τ S i =
      -(q τ v S U : ℝ)/2 := by
  classical
  unfold b0149 c0149 a0148 q z
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self,
    NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma variance_eq (τ : ℕ → ℝ) (S U : ℝ) :
    ∑ i, v i * ((c0149 τ S U i)^2).toNNReal = q τ v S U := by
  classical
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
  simp only [q, z, NNReal.coe_mul, NNReal.coe_sum, Real.coe_toNNReal _ (sq_nonneg _),
    c0149, ite_pow, neg_sq, zero_pow (by omega : 2 ≠ 0),
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma law_logbond (τ : ℕ → ℝ) (S U : ℝ) :
    HasLaw (fun ω => Real.log (bond τ v S U ω))
      (gaussianReal (-(q τ v S U : ℝ)/2) (q τ v S U)) (Q0148 v (a0148 τ S)) := by
  have h := law_L0149 (v := v) (a0148 τ S) (c0149 τ S U) (b0149 τ v S U)
  rw [mean_eq, variance_eq] at h
  convert h using 1
  funext ω
  exact logbond_eq τ S U ω

lemma price_integral (τ : ℕ → ℝ) (S U K : ℝ) :
    C τ v S U K = ∫ x, max (Real.exp x-K) 0
      ∂gaussianReal (-(q τ v S U : ℝ)/2) (q τ v S U) := by
  have h := (law_logbond (v := v) τ S U).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (Real.exp x-K) 0) _)
  rw [integral_Q0148] at h
  convert h using 1
  unfold C
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [density_eq]
  simp only [Function.comp_def, bond, Real.log_exp]

lemma gaussian_exp_tilt (r : NNReal) :
    (gaussianReal (-(r : ℝ)/2) r).withDensity (fun x => ENNReal.ofReal (Real.exp x)) =
      gaussianReal ((r : ℝ)/2) r := by
  let μ := gaussianReal (-(r : ℝ)/2) r
  let ν := μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))
  have hi : Integrable Real.exp μ := by
    simpa using (integrable_exp_mul_gaussianReal (μ := -(r : ℝ)/2) (v := r) 1)
  have hn : ∫ x, Real.exp x ∂μ = 1 := by
    have h := mgf_fun_id_gaussianReal (μ := -(r : ℝ)/2) (v := r)
    have := congrFun h 1
    simpa [mgf, μ, neg_div] using this
  have : IsProbabilityMeasure ν := by
    constructor
    change (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
      fun x => (Real.exp_pos x).le), hn]
    simp
  have hm (t : ℝ) : mgf id ν t = Real.exp ((r : ℝ)/2*t+(r : ℝ)*t^2/2) := by
    change (∫ x, Real.exp (t*x) ∂μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul,
      ← Real.exp_add]
    have he : (fun x : ℝ => Real.exp (x+t*x)) = fun x => Real.exp ((1+t)*x) := by
      funext x; congr 1; ring
    rw [he]
    change mgf id (gaussianReal (-(r : ℝ)/2) r) (1+t) = _
    simp only [mgf_id_gaussianReal]
    ring_nf
  have h := MGFUniqueness.map_eq_of_mgf_eqOn_Ico (μ := ν)
    (μ' := gaussianReal ((r : ℝ)/2) r) (X := id) (Y := id)
    measurable_id measurable_id (L := 1) (by norm_num)
    (fun t _ => by rw [← mgf_pos_iff, hm]; exact Real.exp_pos _)
    (fun t _ => integrable_exp_mul_gaussianReal (-t))
    (fun t _ => by rw [hm, mgf_id_gaussianReal])
  simpa [ν, μ] using h

lemma normal_Ioi (x : ℝ) : (gaussianReal 0 1).real (Ioi x) = Φ (-x) := by
  rw [Φ, cdf_eq_real]
  have hn : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  conv_rhs => rw [← hn, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hs : (fun x : ℝ => -x) ⁻¹' Iic (-x) = Ici x := by ext y; simp
  rw [hs]
  apply congrArg ENNReal.toReal
  exact measure_congr (Ioi_ae_eq_Ici' ((gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0)) (by simp)))

lemma Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  rw [← normal_Ioi, Φ, cdf_eq_real]
  have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 1) (s := Iic x) measurableSet_Iic
  simp only [compl_Iic, probReal_univ] at h
  linarith

lemma Φ_zero : Φ 0 = 1/2 := by
  have h := Φ_neg 0
  simp only [neg_zero] at h
  linarith

lemma Φ_strictMono : StrictMono Φ := by
  intro x y hxy
  have hp : (gaussianReal 0 1) (Ioc x y) ≠ 0 := by
    intro hz
    have hz' := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)) hz
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hz'
    linarith
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc] at hp
  have hh : 0 < Φ y-Φ x := (ENNReal.ofReal_pos).1 (pos_iff_ne_zero.2 hp)
  linarith

lemma Φ_lt_one (x : ℝ) : Φ x < 1 :=
  (Φ_strictMono (show x < x+1 by linarith)).trans_le (cdf_le_one _ _)


lemma gaussian_Ioi (m x : ℝ) (r : NNReal) (hr : 0 < r) :
    (gaussianReal m r).real (Ioi x) = Φ ((m-x)/Real.sqrt r) := by
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt r * y + m) =
      gaussianReal m r := by
    have hv : NNReal.mk (Real.sqrt (r : ℝ)^2) (sq_nonneg _) = r := by
      apply NNReal.coe_injective
      exact Real.sq_sqrt r.coe_nonneg
    have hf : (fun y : ℝ => Real.sqrt r*y+m) = (fun y => y+m) ∘ (fun y => Real.sqrt r*y) := rfl
    rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      mul_zero, mul_one, hv, gaussianReal_map_add_const, zero_add]
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  have he : (fun y : ℝ => Real.sqrt r*y+m) ⁻¹' Ioi x = Ioi ((x-m)/Real.sqrt r) := by
    ext y
    simp only [mem_preimage, mem_Ioi, div_lt_iff₀ hs]
    constructor <;> intro hh <;> nlinarith
  rw [he, normal_Ioi]
  congr 1
  ring

lemma integral_call_gaussian (r : NNReal) {K : ℝ} (hK : 0 < K) (hr : 0 < r) :
    (∫ x, max (Real.exp x-K) 0 ∂gaussianReal (-(r : ℝ)/2) r) =
      Φ (((r : ℝ)/2-Real.log K)/Real.sqrt r) -
        K*Φ ((-(r : ℝ)/2-Real.log K)/Real.sqrt r) := by
  let μ := gaussianReal (-(r : ℝ)/2) r
  have hi : Integrable Real.exp μ := by
    simpa using (integrable_exp_mul_gaussianReal (μ := -(r : ℝ)/2) (v := r) 1)
  have he : (fun x : ℝ => max (Real.exp x-K) 0) =
      (Ioi (Real.log K)).indicator (fun x => Real.exp x-K) := by
    funext x
    by_cases hx : Real.log K < x
    · rw [indicator_of_mem (show x ∈ Ioi (Real.log K) from hx), max_eq_left]
      exact sub_nonneg.2 (le_of_lt ((Real.log_lt_iff_lt_exp hK).1 hx))
    · rw [indicator_of_notMem (show x ∉ Ioi (Real.log K) from hx), max_eq_right]
      exact sub_nonpos.2 ((Real.exp_le_exp.2 (le_of_not_gt hx)).trans_eq (Real.exp_log hK))
  have ht : ∫ x in Ioi (Real.log K), Real.exp x ∂μ =
      (gaussianReal ((r : ℝ)/2) r).real (Ioi (Real.log K)) := by
    rw [← gaussian_exp_tilt, measureReal_def, withDensity_apply _ measurableSet_Ioi]
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (Filter.Eventually.of_forall fun x => (Real.exp_pos x).le)]
    exact (ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos x).le)).symm
  rw [he, integral_indicator measurableSet_Ioi, integral_sub hi.integrableOn (integrable_const K),
    ht, integral_const]
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter]
  change (gaussianReal ((r : ℝ)/2) r).real (Ioi (Real.log K)) -
    (μ.real (Ioi (Real.log K))) * K = _
  rw [gaussian_Ioi _ _ _ hr]
  rw [show μ = gaussianReal (-(r : ℝ)/2) r from rfl, gaussian_Ioi _ _ _ hr]
  ring

lemma integral_call_zero (K : ℝ) :
    (∫ x, max (Real.exp x-K) 0 ∂gaussianReal 0 0) = max (1-K) 0 := by simp

lemma price_pos (τ : ℕ → ℝ) (S U : ℝ) {K : ℝ} (hK : 0 < K)
    (hq : 0 < q τ v S U) :
    C τ v S U K = Φ (((q τ v S U : ℝ)/2-Real.log K)/Real.sqrt (q τ v S U)) -
      K * Φ ((-(q τ v S U : ℝ)/2-Real.log K)/Real.sqrt (q τ v S U)) := by
  rw [price_integral]
  exact integral_call_gaussian _ hK hq

lemma price_zero (τ : ℕ → ℝ) (S U K : ℝ) (hq : q τ v S U = 0) :
    C τ v S U K = max (1-K) 0 := by
  rw [price_integral, hq]
  simp

lemma price_at_one (τ : ℕ → ℝ) (S U : ℝ) :
    C τ v S U 1 = 2*Φ (Real.sqrt (q τ v S U)/2)-1 := by
  by_cases hq : q τ v S U = 0
  · rw [price_zero τ S U 1 hq, hq]
    simp [Φ_zero]
  · have hr : 0 < q τ v S U := pos_iff_ne_zero.2 hq
    have hs : 0 < Real.sqrt (q τ v S U : ℝ) := Real.sqrt_pos.2 hr
    have he : (q τ v S U : ℝ)/2/Real.sqrt (q τ v S U) = Real.sqrt (q τ v S U)/2 := by
      apply (div_eq_iff hs.ne').2
      nlinarith [Real.sq_sqrt (q τ v S U).coe_nonneg]
    rw [price_pos τ S U (by norm_num) hr]
    simp only [Real.log_one, sub_zero, one_mul, neg_div, he, Φ_neg]
    ring

lemma price_at_one_injective (τ : ℕ → ℝ) (v w : Fin N → NNReal) (S U : ℝ)
    (hSU : S < U) : C τ v S U 1 = C τ w S U 1 ↔ z τ v S = z τ w S := by
  rw [price_at_one, price_at_one]
  constructor
  · intro h
    have he : Real.sqrt (q τ v S U : ℝ) = Real.sqrt (q τ w S U : ℝ) := by
      have hΦ : Φ (Real.sqrt (q τ v S U)/2) = Φ (Real.sqrt (q τ w S U)/2) := by linarith
      have hh := Φ_strictMono.injective hΦ
      linarith
    have hq : q τ v S U = q τ w S U := by
      apply NNReal.coe_injective
      exact (Real.sqrt_inj (q τ v S U).coe_nonneg (q τ w S U).coe_nonneg).1 he
    unfold q at hq
    exact mul_left_cancel₀ (by positivity : ((U-S)^2).toNNReal ≠ 0) hq
  · intro h
    rw [show q τ v S U = q τ w S U by unfold q; rw [h]]

lemma surface_iff (τ : ℕ → ℝ) (v w : Fin N → NNReal) (S : ℝ) :
    (∀ U K, S < U → 0 < K → C τ v S U K = C τ w S U K) ↔ z τ v S = z τ w S := by
  constructor
  · intro h
    exact (price_at_one_injective τ v w S (S+1) (by linarith)).1 (h (S+1) 1 (by linarith) (by norm_num))
  · intro hz U K _ _
    rw [price_integral, price_integral, show q τ v S U = q τ w S U by unfold q; rw [hz]]


lemma price_bounds (τ : ℕ → ℝ) (S U : ℝ) : C τ v S U 1 ∈ Ico (0 : ℝ) 1 := by
  rw [price_at_one]
  have h0 := Φ_strictMono.monotone (show (0 : ℝ) ≤ Real.sqrt (q τ v S U)/2 by positivity)
  rw [Φ_zero] at h0
  have h1 := Φ_lt_one (Real.sqrt (q τ v S U)/2)
  constructor <;> linarith

lemma recover_q (τ : ℕ → ℝ) (S U : ℝ) : q0147 (C τ v S U 1) = (q τ v S U : ℝ) := by
  rw [q0147, price_at_one]
  have he (x : ℝ) : (1+(2*x-1))/2 = x := by ring
  rw [he, Function.leftInverse_invFun Φ_strictMono.injective]
  nlinarith [Real.sq_sqrt (q τ v S U).coe_nonneg]

lemma recover_z (τ : ℕ → ℝ) (S U : ℝ) (hSU : S < U) :
    q0147 (C τ v S U 1)/(U-S)^2 = (z τ v S : ℝ) := by
  rw [recover_q, q, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
  field_simp [ne_of_gt (sub_pos.2 hSU)]

lemma past_separating (τ : ℕ → ℝ) (S : Fin N → ℝ)
    (hτ : StrictMonoOn τ (Iic N))
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (i j : Fin N) : j ∈ past τ (S i) ↔ j ≤ i := by
  classical
  simp only [past, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    by_contra hn
    have hij : i.val+2 ≤ j.val+1 := by omega
    have hiN : i.val+1 < N := by omega
    have hle := hτ.monotoneOn (show i.val+2 ∈ Iic N by simp only [mem_Iic]; omega)
      (show j.val+1 ∈ Iic N by simp only [mem_Iic]; omega) hij
    exact (not_lt_of_ge hj) ((hS i).2 hiN |>.trans_le hle)
  · intro hji
    exact (hτ.monotoneOn (show j.val+1 ∈ Iic N by simp only [mem_Iic]; omega)
      (show i.val+1 ∈ Iic N by simp only [mem_Iic]; omega) (by omega)).trans (hS i).1

lemma recover_all (τ : ℕ → ℝ) (S U : Fin N → ℝ)
    (hτ : StrictMonoOn τ (Iic N))
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (hU : ∀ i, S i < U i) (i : Fin N) :
    v0147 S U (fun j => C τ v (S j) (U j) 1) i = (v i : ℝ) := by
  classical
  have hz (j : Fin N) : z0147 S U (fun j => C τ v (S j) (U j) 1) j =
      ∑ k ∈ past τ (S j), (v k : ℝ) := by
    rw [z0147, recover_z τ (S j) (U j) (hU j), z, NNReal.coe_sum]
  unfold v0147
  rw [hz]
  split_ifs with hi
  · have hp : past τ (S i) = {i} := by
      ext j
      rw [past_separating τ S hτ hS, Finset.mem_singleton]
      constructor
      · intro h; apply Fin.ext; omega
      · intro h; subst j; exact le_rfl
    simp [hp]
  · let j : Fin N := ⟨i.val-1, by omega⟩
    have hp : past τ (S j) = (past τ (S i)).erase i := by
      ext k
      rw [past_separating τ S hτ hS, Finset.mem_erase, past_separating τ S hτ hS]
      constructor
      · intro hk
        constructor
        · intro he; subst k; simp only [Fin.le_iff_val_le_val, j] at hk; omega
        · simp only [Fin.le_iff_val_le_val, j] at *; omega
      · intro hk
        have hne : k.val ≠ i.val := fun he => hk.1 (Fin.ext he)
        simp only [Fin.le_iff_val_le_val, j] at *
        omega
    rw [hz, hp]
    have hh := Finset.sum_erase_add (s := past τ (S i)) (f := fun k => (v k : ℝ))
      ((past_separating τ S hτ hS i i).2 le_rfl)
    linarith

lemma separating_injective (τ : ℕ → ℝ) (v w : Fin N → NNReal) (S U : Fin N → ℝ)
    (hτ : StrictMonoOn τ (Iic N))
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (hU : ∀ i, S i < U i)
    (hC : ∀ i, C τ v (S i) (U i) 1 = C τ w (S i) (U i) 1) : v = w := by
  have he : (fun i => C τ v (S i) (U i) 1) = fun i => C τ w (S i) (U i) 1 := funext hC
  funext i
  apply NNReal.coe_injective
  rw [← recover_all τ S U hτ hS hU i, he, recover_all τ S U hτ hS hU i]

lemma example_distinct (ε : NNReal) (hε : 0 < ε) : v0146 ε ≠ w0146 ε := by
  intro h
  have he := congrArg (fun v : Fin 3 → NNReal => (v 0 : ℝ)) h
  simp [v0146, w0146] at he
  have hp : (0 : ℝ) < ε := hε
  linarith

lemma example_surface (ε : NNReal) :
    ∀ U K, (3 : ℝ) < U → 0 < K → C (fun n => n) (v0146 ε) 3 U K =
      C (fun n => n) (w0146 ε) 3 U K := by
  apply (surface_iff _ _ _ _).2
  have hp : past (N := 3) (fun n => (n : ℝ)) 3 = Finset.univ := by
    ext i
    simp only [past, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact_mod_cast (show i.val+1 ≤ 3 by omega)
  simp [z, hp, v0146, w0146, Fin.sum_univ_succ]
  ring

lemma initial_bond (τ : ℕ → ℝ) (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (U : ℝ) (ω : Ω N) : bond τ v 0 U ω = 1 := by
  have hp : past (N := N) τ 0 = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hi
    have hi' : τ (i.val+1) ≤ 0 := (Finset.mem_filter.1 hi).2
    have hh := hτ (show 0 ∈ Iic N by simp) (show i.val+1 ∈ Iic N by simp only [mem_Iic]; omega)
      (show 0 < i.val+1 by omega)
    rw [hτ0] at hh
    exact (not_lt_of_ge hi') hh
  rw [bond, D3EventVariancesProof.integral_forward]
  simp [X, hp]


lemma integrable_price (τ : ℕ → ℝ) (S U : ℝ) {K : ℝ} (hK : 0 < K) :
    Integrable (fun ω => Real.exp (-logB τ v S ω) * max (bond τ v S U ω-K) 0) (Q v) := by
  have hb : bond τ v S U = fun ω => Real.exp (L0149 (b0149 τ v S U) (c0149 τ S U) ω) := by
    funext ω
    rw [← logbond_eq, bond, Real.log_exp]
  refine (D3EventVariancesProof.integrable_prod (τ := τ) (v := v) U (past τ S)).mono' ?_ ?_
  · rw [hb]
    unfold logB L0149
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [] with ω
    have hp : 0 < bond τ v S U ω := Real.exp_pos _
    have hd : 0 < Real.exp (-logB τ v S ω) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd.le (le_max_right _ _))]
    change _ ≤ discounted τ v U S ω
    rw [← D3EventVariancesProof.bond_discounted]
    calc Real.exp (-logB τ v S ω) * max (bond τ v S U ω-K) 0
        ≤ Real.exp (-logB τ v S ω) * bond τ v S U ω := by
          apply mul_le_mul_of_nonneg_left _ hd.le
          exact max_le (by linarith) hp.le
      _ = bond τ v S U ω / Real.exp (logB τ v S ω) := by rw [Real.exp_neg]; ring

lemma price_formula (τ : ℕ → ℝ) (S U : ℝ) {K : ℝ} (hK : 0 < K)
    (hq : 0 < q τ v S U) :
    C τ v S U K =
      Φ ((-Real.log K+(q τ v S U : ℝ)/2)/Real.sqrt (q τ v S U)) -
      K*Φ (((-Real.log K+(q τ v S U : ℝ)/2)/Real.sqrt (q τ v S U)) -
        Real.sqrt (q τ v S U)) := by
  have hs : Real.sqrt (q τ v S U : ℝ) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have he : (-(q τ v S U : ℝ)/2-Real.log K)/Real.sqrt (q τ v S U) =
      ((-Real.log K+(q τ v S U : ℝ)/2)/Real.sqrt (q τ v S U)) -
        Real.sqrt (q τ v S U) := by
    apply (div_eq_iff hs).2
    field_simp
    nlinarith [Real.sq_sqrt (q τ v S U).coe_nonneg]
  rw [price_pos τ S U hK hq, he]
  congr 3
  ring

lemma QS_eq (τ : ℕ → ℝ) (S : ℝ) : QS τ v S = Q0148 v (a0148 τ S) := by
  unfold QS Q0148
  congr 1
  funext ω
  rw [density_eq]

theorem bondOptionMeetingVariances : Standalone.BondOptionMeetingVariances.statement := by
  constructor
  · intro N τ v
    refine ⟨?_, ?_, fun S U K hK => integrable_price τ S U hK,
      fun S U K hK hq => price_formula τ S U hK hq, price_zero τ,
      price_at_one τ, price_bounds τ, fun w S U hSU => price_at_one_injective τ v w S U hSU,
      fun w S => surface_iff τ v w S, recover_q τ, recover_z τ, ?_, initial_bond τ⟩
    · intro S
      rw [QS_eq]
      infer_instance
    · intro S U
      rw [QS_eq]
      exact law_logbond τ S U
    · intro S U hτ hS hU
      exact ⟨recover_all τ S U hτ hS hU, fun w hC => separating_injective τ v w S U hτ hS hU hC⟩
  · intro ε hε
    exact ⟨example_distinct ε hε, example_surface ε⟩

end Novel.BondOptionMeetingVariancesProof

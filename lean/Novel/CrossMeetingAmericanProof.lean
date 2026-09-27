import Standalone.CrossMeetingAmerican
import Novel.LateAmericanExerciseProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open Standalone.CrossMeetingAmerican
namespace Novel.CrossMeetingAmericanProof

lemma u_mem (q d z : ℝ) (hd : 0 ≤ d) : u0194 q d z ∈ Icc 0 d := by
  unfold u0194
  split_ifs
  · exact ⟨le_min hd (le_max_left _ _), min_le_left _ _⟩
  · exact ⟨le_rfl, hd⟩
  · exact ⟨hd, le_rfl⟩

lemma u_measurable (q d : ℝ) : Measurable (u0194 q d) := by
  classical
  unfold u0194
  split_ifs
  · fun_prop
  · exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const

lemma D_measurable (q d : ℝ) : Measurable (D0194 q d) := by
  have hu := u_measurable q d
  unfold D0194
  fun_prop

lemma quadratic_min_pos (V L x : ℝ) (hV : 0 < V) (hL : 0 ≤ L) (u : ℝ) (hu : u ∈ Icc 0 L) :
    x*min L (max 0 (-x/V))+V*(min L (max 0 (-x/V)))^2/2 ≤ x*u+V*u^2/2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hx) hV.le), min_eq_right hL]
    nlinarith [mul_nonneg hx hu.1, mul_nonneg hV.le (sq_nonneg u)]
  · have hx' : 0 ≤ -x/V := div_nonneg (neg_nonneg.2 (not_le.1 hx).le) hV.le
    rw [max_eq_right hx']
    by_cases h : -x/V ≤ L
    · rw [min_eq_right h]
      have he : x*u+V*u^2/2-(x*(-x/V)+V*(-x/V)^2/2) = V/2*(u+x/V)^2 := by
        field_simp
        ring
      have hn : 0 ≤ V/2*(u+x/V)^2 := mul_nonneg (by positivity) (sq_nonneg _)
      linarith
    · rw [min_eq_left (not_le.1 h).le]
      have hxL : x ≤ -V*L := by
        have := (le_div_iff₀ hV).1 (not_le.1 h).le
        nlinarith
      nlinarith [mul_nonneg (show 0 ≤ -(x+V*L) by linarith) (sub_nonneg.2 hu.2),
        mul_nonneg hV.le (sq_nonneg (u-L))]

lemma discount_max (q d z : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) (u : ℝ) (hu : u ∈ Icc 0 d) :
    Real.exp (-z*u-q*u^2/2) ≤ D0194 q d z := by
  apply Real.exp_le_exp.mpr
  by_cases hqp : 0 < q
  · have h := quadratic_min_pos q d z hqp hd u hu
    simp only [u0194, ite_eq_left hqp]
    linarith
  · have hq0 : q = 0 := le_antisymm (le_of_not_gt hqp) hq
    subst q
    simp only [u0194, lt_self_iff_false, ↓reduceIte, zero_mul, zero_div, sub_zero]
    split_ifs with hz
    · nlinarith [mul_nonneg hz hu.1]
    · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hz)) (sub_nonneg.mpr hu.2)]

lemma discount_bounds (q d z : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    1 ≤ D0194 q d z ∧ D0194 q d z ≤ Real.exp (d*|z|) := by
  constructor
  · simpa using discount_max q d z hq hd 0 ⟨le_rfl, hd⟩
  · apply Real.exp_le_exp.mpr
    have hu := u_mem q d z hd
    have h1 := mul_le_mul_of_nonneg_right (neg_le_abs z) hu.1
    have h2 := mul_le_mul_of_nonneg_left hu.2 (abs_nonneg z)
    have h3 := mul_nonneg hq (sq_nonneg (u0194 q d z))
    change -z*u0194 q d z-q*(u0194 q d z)^2/2 ≤ d*|z|
    nlinarith

lemma gaussian_exp_affine (m : ℝ) (v : NNReal) (a b : ℝ) :
    Integrable (fun z => Real.exp (a*z+b)) (gaussianReal m v) := by
  simp_rw [Real.exp_add]
  exact (integrable_exp_mul_gaussianReal a).mul_const _

lemma gaussian_exp_abs (m : ℝ) (v : NNReal) (a : ℝ) :
    Integrable (fun z => Real.exp (a*|z|)) (gaussianReal m v) := by
  apply ((integrable_exp_mul_gaussianReal a).add (integrable_exp_mul_gaussianReal (-a))).mono'
    (by fun_prop)
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-a*z)]
  · rw [abs_of_neg (lt_of_not_ge hz)]
    have : a*(-z) = -a*z := by ring
    rw [this]
    linarith [Real.exp_pos (a*z)]

lemma cash_measurable (V T a b K L : ℝ) :
    Measurable (fun y => max (fPlus0193 V T a b y-K) 0 * D0194 V L y) := by
  have hD := D_measurable V L
  unfold fPlus0193
  fun_prop

lemma cash_bound (V T a b K L y : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L) (hab : a < b) :
    |max (fPlus0193 V T a b y-K) 0 * D0194 V L y| ≤
      (Real.exp ((b-a)*(V*((a+b)/2-T)))/(b-a)+|K|) * Real.exp ((b-a+L)*|y|) := by
  have hδ : 0 < b-a := sub_pos.mpr hab
  have hD := discount_bounds V L y hV hL
  have hc : max (fPlus0193 V T a b y-K) 0 ≤
      Real.exp ((b-a)*(V*((a+b)/2-T)))/(b-a) * Real.exp ((b-a)*|y|)+|K| := by
    apply max_le
    · unfold fPlus0193
      have he : Real.exp ((b-a)*(y+V*((a+b)/2-T))) ≤
          Real.exp ((b-a)*(V*((a+b)/2-T))) * Real.exp ((b-a)*|y|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [le_abs_self y]
      have he' := div_le_div_of_nonneg_right he hδ.le
      have hh : (Real.exp ((b-a)*(V*((a+b)/2-T))) * Real.exp ((b-a)*|y|))/(b-a) =
          Real.exp ((b-a)*(V*((a+b)/2-T)))/(b-a) * Real.exp ((b-a)*|y|) := by ring
      rw [hh] at he'
      have hn : 0 ≤ 1/(b-a) := by positivity
      rw [sub_div]
      linarith [neg_le_abs K]
    · positivity
  have he1 : 1 ≤ Real.exp ((b-a)*|y|) := Real.one_le_exp (by positivity)
  rw [abs_of_nonneg (mul_nonneg (le_max_right _ _) (zero_le_one.trans hD.1))]
  calc
    _ ≤ (Real.exp ((b-a)*(V*((a+b)/2-T)))/(b-a) * Real.exp ((b-a)*|y|)+|K|) * Real.exp (L*|y|) :=
      mul_le_mul hc hD.2 (Real.exp_pos _).le (by positivity)
    _ ≤ ((Real.exp ((b-a)*(V*((a+b)/2-T)))/(b-a)+|K|) * Real.exp ((b-a)*|y|)) * Real.exp (L*|y|) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left he1 (abs_nonneg K)]
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma cash_integrable (m : ℝ) (v : NNReal) (V T a b K L : ℝ)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hab : a < b) :
    Integrable (fun y => max (fPlus0193 V T a b y-K) 0 * D0194 V L y) (gaussianReal m v) := by
  exact ((gaussian_exp_abs m v (b-a+L)).const_mul _).mono'
    (cash_measurable V T a b K L).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using cash_bound V T a b K L y hV hL hab)

lemma shifted_cash_integrable (q : ℝ) (w : NNReal) (A T S a b K x : ℝ)
    (hq : 0 ≤ q) (hTS : T ≤ S) (hab : a < b) :
    Integrable (fun z => max (fPlus0193 (q+w) T a b (x+q*(T-A)+z)-K) 0 *
      D0194 (q+w) (S-T) (x+q*(T-A)+z)) (gaussianReal 0 w) := by
  have hlaw : HasLaw (fun z : ℝ => x+q*(T-A)+z) (gaussianReal (x+q*(T-A)) w) (gaussianReal 0 w) :=
    ⟨by fun_prop, by simpa using gaussianReal_map_const_add (μ := 0) (v := w) (x+q*(T-A))⟩
  exact hlaw.integrable_comp (cash_integrable _ _ _ T a b K _ (by positivity) (sub_nonneg.mpr hTS) hab)

lemma averaged_future (q : ℝ) (w : NNReal) (A T a b x : ℝ) :
    (∫ z, fPlus0193 (q+w) T a b (x+q*(T-A)+z) ∂gaussianReal 0 w) =
      fMinus0193 q w A T a b x := by
  have he (z : ℝ) : (b-a)*(x+q*(T-A)+z+(q+w)*((a+b)/2-T)) =
      (b-a)*z+(b-a)*(x+q*(T-A)+(q+w)*((a+b)/2-T)) := by ring
  have hi := gaussian_exp_affine 0 w (b-a) ((b-a)*(x+q*(T-A)+(q+w)*((a+b)/2-T)))
  simp only [fPlus0193, he, Real.exp_add]
  rw [integral_div, integral_sub (by simpa only [Real.exp_add] using hi) (integrable_const 1), integral_mul_const]
  have hg : (∫ z, Real.exp ((b-a)*z) ∂gaussianReal 0 w) = Real.exp ((w : ℝ)*(b-a)^2/2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := w)) (b-a)
  rw [hg, ← Real.exp_add]
  simp only [integral_const, probReal_univ, one_smul, fMinus0193]
  congr 3
  ring

lemma p_measurable (q w A T a b K : ℝ) : Measurable (p0195 q w A T a b K) := by
  have hD := D_measurable q (T-A)
  unfold p0195 fMinus0193
  fun_prop

lemma c_measurable (q : ℝ) (w : NNReal) (A T S a b K : ℝ) :
    Measurable (c0195 q w A T S a b K) := by
  have hcash := cash_measurable (q+w) T a b K (S-T)
  have hj : Measurable (fun p : ℝ × ℝ =>
      max (fPlus0193 (q+w) T a b (p.1+q*(T-A)+p.2)-K) 0 *
        D0194 (q+w) (S-T) (p.1+q*(T-A)+p.2)) := hcash.comp (by fun_prop)
  exact (show Measurable (fun x : ℝ => Real.exp (-x*(T-A)-q*(T-A)^2/2)) by fun_prop).mul
    hj.stronglyMeasurable.integral_prod_right.measurable

lemma endpoint_bound (q : ℝ) (w : NNReal) (A T S a b K x : ℝ)
    (hq : 0 ≤ q) (hTS : T ≤ S) (hab : a < b) :
    Real.exp (-x*(T-A)-q*(T-A)^2/2) * max (fMinus0193 q w A T a b x-K) 0 ≤
      c0195 q w A T S a b K x := by
  let g := fun z => fPlus0193 (q+w) T a b (x+q*(T-A)+z)
  let h := fun z => max (g z-K) 0 * D0194 (q+w) (S-T) (x+q*(T-A)+z)
  have hh : Integrable h (gaussianReal 0 w) := shifted_cash_integrable q w A T S a b K x hq hTS hab
  have hg : Integrable g (gaussianReal 0 w) := by
    unfold g fPlus0193
    have he : (fun z : ℝ => Real.exp ((b-a)*(x+q*(T-A)+z+(q+w)*((a+b)/2-T)))) =
        (fun z => Real.exp ((b-a)*z+(b-a)*(x+q*(T-A)+(q+w)*((a+b)/2-T)))) := by
      funext z; congr 1; ring
    have hi : Integrable (fun z => Real.exp ((b-a)*(x+q*(T-A)+z+(q+w)*((a+b)/2-T))))
        (gaussianReal 0 w) := by
      rw [he]
      exact gaussian_exp_affine 0 w _ _
    exact (hi.sub (integrable_const 1)).div_const _
  have hb (z : ℝ) : max (g z-K) 0 ≤ h z := by
    exact le_mul_of_one_le_right (le_max_right _ _) (discount_bounds _ _ _ (by positivity) (sub_nonneg.mpr hTS)).1
  have h1 : (∫ z, g z ∂gaussianReal 0 w)-K ≤ ∫ z, h z ∂gaussianReal 0 w := by
    have hmono := integral_mono (hg.sub (integrable_const K)) hh (fun z => (le_max_left _ _).trans (hb z))
    simpa [integral_sub hg (integrable_const K)] using hmono
  have h2 : 0 ≤ ∫ z, h z ∂gaussianReal 0 w :=
    integral_nonneg (fun z => (le_max_right _ _).trans (hb z))
  have hmax := max_le h1 h2
  rw [averaged_future] at hmax
  exact mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le

lemma early_strict (q : ℝ) (w : NNReal) (A T S a b K x : ℝ)
    (hq : 0 ≤ q) (hAT : A < T) (hTS : T ≤ S) (hab : a < b)
    (h : c0195 q w A T S a b K x < p0195 q w A T a b K x) :
    u0194 q (T-A) x < T-A := by
  have hu := u_mem q (T-A) x (sub_nonneg.mpr hAT.le)
  apply lt_of_le_of_ne hu.2
  intro he
  have hb := endpoint_bound q w A T S a b K x hq hTS hab
  have hp : p0195 q w A T a b K x =
      Real.exp (-x*(T-A)-q*(T-A)^2/2) * max (fMinus0193 q w A T a b x-K) 0 := by
    simp only [p0195, D0194, he, mul_comm]
  rw [hp] at h
  exact (not_lt_of_ge hb) h

lemma rule_mem {Ω : Type} (q : ℝ) (w : NNReal) (A T S a b K : ℝ) (x y : Ω → ℝ)
    (hAT : A < T) (hTS : T ≤ S) (ω : Ω) : τ019 q w A T S a b K x y ω ∈ Icc A S := by
  have hx := u_mem q (T-A) (x ω) (sub_nonneg.mpr hAT.le)
  have hy := u_mem (q+w) (S-T) (y ω) (sub_nonneg.mpr hTS)
  unfold τ019
  split_ifs <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma rule_stopping {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ mΩ)
    (q : ℝ) (w : NNReal) (A T S a b K : ℝ) (x y : Ω → ℝ)
    (hq : 0 ≤ q) (hAT : A < T) (hTS : T ≤ S) (hab : a < b)
    (hx : Measurable[F A] x) (hy : Measurable[F T] y) :
    IsStoppingTime F (fun ω => (τ019 q w A T S a b K x y ω : WithTop ℝ)) := by
  classical
  let E := {ω | c0195 q w A T S a b K (x ω) < p0195 q w A T a b K (x ω)}
  have hE : MeasurableSet[F A] E :=
    measurableSet_lt ((c_measurable q w A T S a b K).comp hx) ((p_measurable q w A T a b K).comp hx)
  have hpre : Measurable[F A] (fun ω => A+u0194 q (T-A) (x ω)) :=
    measurable_const.add ((u_measurable q (T-A)).comp hx)
  have hpost : Measurable[F T] (fun ω => T+u0194 (q+w) (S-T) (y ω)) :=
    measurable_const.add ((u_measurable (q+w) (S-T)).comp hy)
  intro t
  simp only [WithTop.coe_le_coe]
  by_cases hAt : A ≤ t
  · by_cases htT : t < T
    · have he : {ω | τ019 q w A T S a b K x y ω ≤ t} =
          E ∩ {ω | A+u0194 q (T-A) (x ω) ≤ t} := by
        ext ω
        simp only [τ019, mem_inter_iff, mem_ofPred_eq, E]
        split_ifs with h
        · simp only [h, true_and]
        · have hnot : ¬T+u0194 (q+w) (S-T) (y ω) ≤ t := by
            have hh := (u_mem (q+w) (S-T) (y ω) (sub_nonneg.mpr hTS)).1
            linarith
          simp only [h, false_and, hnot]
      rw [he]
      exact F.mono hAt _ (hE.inter (measurableSet_le hpre measurable_const))
    · have hTt : T ≤ t := le_of_not_gt htT
      have he : {ω | τ019 q w A T S a b K x y ω ≤ t} =
          E ∪ (Eᶜ ∩ {ω | T+u0194 (q+w) (S-T) (y ω) ≤ t}) := by
        ext ω
        simp only [τ019, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, E]
        split_ifs with h
        · have hearly := early_strict q w A T S a b K (x ω) hq hAT hTS hab h
          have ht : A+u0194 q (T-A) (x ω) ≤ t := by linarith
          simp only [h, ht, not_true_eq_false, false_and, or_false]
        · simp only [h, not_false_eq_true, true_and, false_or]
      rw [he]
      exact (F.mono hAt _ hE).union ((F.mono hAt _ hE).compl.inter
        (F.mono hTt _ (measurableSet_le hpost measurable_const)))
  · have he : {ω | τ019 q w A T S a b K x y ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      have hh := (rule_mem q w A T S a b K x y hAT hTS ω).1
      exact not_le.mpr ((lt_of_not_ge hAt).trans_le hh)
    rw [he]
    exact @MeasurableSet.empty Ω (F t)

lemma before_measurable {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ mΩ)
    (A T : ℝ) (τ : Ω → ℝ) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ)))
    (hA : ∀ ω, A ≤ τ ω) (hF : ∀ t ∈ Ico A T, F t = F A) :
    MeasurableSet[F A] {ω | τ ω < T} := by
  have he : {ω | τ ω < T} = ⋃ r : ℚ, ⋃ (_ : A ≤ (r : ℝ) ∧ (r : ℝ) < T), {ω | τ ω ≤ r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨r, hr, hrT⟩ := exists_rat_btwn h
      exact ⟨r, ⟨(hA ω).trans hr.le, hrT⟩, hr.le⟩
    · rintro ⟨r, hr, hτr⟩
      exact hτr.trans_lt hr.2
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro hr
  have hm := hτ.measurableSet_le (r : ℝ)
  rw [hF r hr] at hm
  simpa only [WithTop.coe_le_coe] using hm

lemma past_date {N : ℕ} (τ : ℕ → ℝ) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A : ℝ) (hA : τ N ≤ A) (i : Fin N) : τ (i.val+1) ≤ A :=
  (hτ.monotoneOn (by simp only [mem_Iic]; omega) (by simp) (by omega)).trans hA

lemma last_date {N : ℕ} (τ : ℕ → ℝ) (hτ : StrictMonoOn τ (Iic (N+1)))
    (i : Fin (N+1)) : τ (i.val+1) ≤ τ (N+1) :=
  hτ.monotoneOn (by simp only [mem_Iic]; omega) (by simp) (by omega)

lemma reveal_frozen {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A t : ℝ) (hA : τ N ≤ A)
    (hAt : A ≤ t) (htT : t < τ (N+1)) : completedFilt τ v t = completedFilt τ v A := by
  have he (i : Fin (N+1)) : τ (i.val+1) ≤ t ↔ τ (i.val+1) ≤ A := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.val_last]
      exact iff_of_false (not_le.mpr htT) (not_le.mpr (hAt.trans_lt htT))
    · exact iff_of_true ((past_date τ hτ A hA i).trans hAt) (past_date τ hτ A hA i)
  have hf : filt (N := N+1) τ t = filt τ A := by
    change (⨆ i : Fin (N+1), ⨆ (_ : τ (i.val+1) ≤ t), _) = (⨆ i : Fin (N+1), ⨆ (_ : τ (i.val+1) ≤ A), _)
    simp only [he]
  change eventuallyMeasurableSpace (filt τ t) (ae (Q v)) = _
  rw [hf]
  rfl

lemma model_rate_measurable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) :
    Measurable[filt τ t] (r τ v t) := by
  apply Finset.measurable_sum
  intro i _
  by_cases h : τ (i.val+1) ≤ t
  · simp only [ite_eq_left h]
    have hi : Measurable[filt τ t] (fun ω : Ω N => ω i) :=
      measurable_iff_comap_le.mpr (le_iSup_of_le i (le_iSup_of_le h le_rfl))
    exact hi.add measurable_const
  · simpa only [ite_eq_right h] using (measurable_const (a := (0 : ℝ)))

lemma model_rate_completed_measurable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) :
    Measurable[completedFilt τ v t] (fun ω : Ωc v => r τ v t ω) := by
  intro E hE
  exact ⟨_, model_rate_measurable τ v t hE, EventuallyEq.refl _ _⟩

lemma rate_before_sum {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1))
    (ω : Ω (N+1)) : r τ v A ω =
      ∑ i : Fin N, (ω i.castSucc+(v i.castSucc : ℝ)*(A-τ (i.val+1))) := by
  simp [r, Fin.sum_univ_castSucc, past_date τ hτ A hA, not_le.mpr hAT]

lemma rate_at_last {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1))
    (ω : Ω (N+1)) : r τ v (τ (N+1)) ω = r τ v A ω + VMinus019 v*(τ (N+1)-A) + ω (Fin.last N) := by
  rw [rate_before_sum τ v hτ A hA hAT]
  simp only [r, ite_eq_left (last_date τ hτ _), Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    sub_self, mul_zero, add_zero, VMinus019, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma futures_before {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A t a b : ℝ) (hA : τ N ≤ A)
    (hAt : A ≤ t) (htT : t < τ (N+1)) (hTa : τ (N+1) ≤ a) (hab : a ≤ b)
    (ω : Ω (N+1)) : Standalone.CompoundedFuturesIdentification.G τ v t a b ω =
      Real.exp ((b-a)*(r τ v A ω+VMinus019 v*((a+b)/2-A)+(v (Fin.last N) : ℝ)*(b-τ (N+1)))) := by
  have ha (i : Fin (N+1)) := (last_date τ hτ i).trans hTa
  have hw (i : Fin (N+1)) : Standalone.CompoundedFuturesIdentification.w a b (τ (i.val+1)) = b-a := by
    simp only [Standalone.CompoundedFuturesIdentification.w,
      max_eq_left (sub_nonneg.mpr (ha i)), max_eq_left (sub_nonneg.mpr ((ha i).trans hab))]
    ring
  have hd (i : Fin (N+1)) : Standalone.CompoundedFuturesIdentification.d a b (τ (i.val+1)) =
      (b-a)*((a+b)/2-τ (i.val+1)) := by
    simp only [Standalone.CompoundedFuturesIdentification.d,
      max_eq_left (sub_nonneg.mpr (ha i)), max_eq_left (sub_nonneg.mpr ((ha i).trans hab))]
    ring
  rw [CompoundedFuturesIdentificationProof.futures_formula]
  simp only [hw, hd, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    ite_eq_left ((past_date τ hτ A hA _).trans hAt), ite_eq_right (not_le.mpr htT),
    Finset.sum_const_zero, zero_add, add_zero]
  rw [rate_before_sum τ v hτ A hA (hAt.trans_lt htT)]
  congr 1
  have he : (∑ i : Fin N, (b-a)*ω i.castSucc) +
      (∑ i : Fin N, (b-a)*((a+b)/2-τ (i.val+1))*(v i.castSucc : ℝ)) =
      (b-a)*((∑ i : Fin N, (ω i.castSucc+(v i.castSucc : ℝ)*(A-τ (i.val+1))))+
        VMinus019 v*((a+b)/2-A)) := by
    simp only [VMinus019, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linear_combination he

lemma model_future_measurable {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (A a b t : ℝ) (hAt : A ≤ t) :
    Measurable[completedFilt τ v t] (fun ω : Ωc v => F0192 τ v A a b t ω) := by
  unfold F0192
  split_ifs with h
  · have hx := (model_rate_completed_measurable τ v A).mono ((completedFilt τ v).mono hAt) le_rfl
    unfold fMinus0193
    fun_prop
  · have hy := (model_rate_completed_measurable τ v (τ (N+1))).mono
      ((completedFilt τ v).mono (le_of_not_gt h)) le_rfl
    unfold fPlus0193
    fun_prop

lemma model_future_condExp {N J : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (hJ : 0 < J)
    (u : Fin (J+1) → ℝ) (hu : StrictMono u) (A t : ℝ) (hA : τ N ≤ A)
    (hAt : A ≤ t) (hTa : τ (N+1) ≤ u 0) (h0 : 0 ≤ u 0) :
    (Qc v)[fun ω : Ωc v => R0192 τ v u ω | completedFilt τ v t] =ᵐ[Qc v]
      fun ω => F0192 τ v A (u 0) (u (Fin.last J)) t ω := by
  let : IsProbabilityMeasure (Qc v) := by change IsProbabilityMeasure (Standalone.LateAmericanExercise.Qc v); infer_instance
  have hT : ∀ i : Fin (N+1), τ (i.val+1) ≤ u 0 := fun i => (last_date τ hτ i).trans hTa
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  by_cases htT : t < τ (N+1)
  · let δ := u (Fin.last J)-u 0
    let f : Ωc v → ℝ := fun ω => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)
    have hf : Integrable f (Qc v) := (LateAmericanExerciseProof.completion_law v).integrable_comp
      (CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab)
    have hce := CompoundedFuturesIdentificationProof.futures_completed_condExp τ v hτ0 hτ _ _ h0 hab t
    have hscaled := condExp_smul (μ := Qc v) δ⁻¹ (f-1) (completedFilt τ v t)
    have hsub := condExp_sub hf (integrable_const 1) (completedFilt τ v t)
    rw [condExp_const ((completedFilt τ v).le t)] at hsub
    have he : (fun ω : Ωc v => R0192 τ v u ω) = δ⁻¹ • (f-1) := by
      funext ω
      have hh : (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0192 τ v u j ω)) =
          Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) :=
        LateAmericanExerciseProof.compound_eq τ v u hu hT ω
      change (_-1)/δ = _
      rw [hh]
      simp [f, div_eq_mul_inv, mul_comm]
    refine (condExp_congr_ae (EventuallyEq.of_eq he)).trans ?_
    filter_upwards [hscaled, hsub, hce] with ω hs hsub hce
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hs hsub
    change (Qc v)[f | completedFilt τ v t] ω = _ at hce
    change (Qc v)[f-1 | completedFilt τ v t] ω = (Qc v)[f | completedFilt τ v t] ω-1 at hsub
    rw [hs, hsub, hce]
    have hg := futures_before τ v hτ A t _ _ hA hAt htT hTa hab.le (ω : Ω (N+1))
    exact (congrArg (fun x : ℝ => δ⁻¹*(x-1)) hg).trans (by
      simp only [F0192, htT, ↓reduceIte, fMinus0193, δ, div_eq_mul_inv, mul_comm])
  · have hm : Measurable[completedFilt τ v t] (fun ω : Ωc v => R0192 τ v u ω) :=
      (LateAmericanExerciseProof.compound_rate_measurable τ v u hu (τ (N+1)) (last_date τ hτ) hTa).mono
        ((completedFilt τ v).mono (le_of_not_gt htT)) le_rfl
    have hi : Integrable (fun ω : Ωc v => R0192 τ v u ω) (Qc v) :=
      LateAmericanExerciseProof.compound_rate_completed_integrable τ v hτ0 hτ hJ u hu h0 hT
    rw [condExp_of_stronglyMeasurable ((completedFilt τ v).le t) hm.stronglyMeasurable hi]
    apply Eventually.of_forall
    intro ω
    have hr := LateAmericanExerciseProof.rate_formula τ v u hu (τ (N+1)) (last_date τ hτ) hTa ω
    exact hr.trans (by
      simp only [F0192, htT, ↓reduceIte, fPlus0193, mul_add, mul_assoc]
      rfl)

lemma bank_before_sum {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A t : ℝ) (hA : τ N ≤ A) (hAt : A ≤ t) (htT : t ≤ τ (N+1))
    (ω : Ω (N+1)) : logB τ v t ω =
      ∑ i : Fin N, ((t-τ (i.val+1))*ω i.castSucc + (v i.castSucc : ℝ)*(t-τ (i.val+1))^2/2) := by
  have ht0 : 0 ≤ t := by
    rw [← hτ0]
    exact (hτ.monotoneOn (by simp) (by simp) (Nat.zero_le N)).trans (hA.trans hAt)
  change Standalone.CompoundedFuturesIdentification.logB τ v t ω = _
  rw [CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ t ht0,
    CompoundedFuturesIdentificationProof.bank_positive_parts]
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    max_eq_left (sub_nonneg.mpr ((past_date τ hτ A hA _).trans hAt)),
    max_eq_right (sub_nonpos.mpr htT), zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div, add_zero]

lemma bank_before {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A t : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hAt : A ≤ t) (htT : t ≤ τ (N+1))
    (ω : Ω (N+1)) : logB τ v t ω = logB τ v A ω + r τ v A ω*(t-A) + VMinus019 v*(t-A)^2/2 := by
  rw [bank_before_sum τ v hτ0 hτ A t hA hAt htT,
    bank_before_sum τ v hτ0 hτ A A hA le_rfl hAT.le, rate_before_sum τ v hτ A hA hAT]
  simp only [VMinus019, Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma discounted_before_law {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1)) :
    HasLaw (r τ v A) (gaussianReal 0 (∑ i : Fin N, v i.castSucc)) (Q01912 τ v A) := by
  have h0 : 0 ≤ A := by
    rw [← hτ0]
    exact (hτ.monotoneOn (by simp) (by simp) (Nat.zero_le N)).trans hA
  change HasLaw _ _ (Standalone.CompoundedFuturesIdentification.QS τ v A)
  rw [CompoundedFuturesIdentificationProof.QS_eq τ v hτ0 hτ A h0]
  let c : Fin (N+1) → ℝ := Fin.lastCases 0 (fun _ => 1)
  let b : ℝ := ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1))
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v)
    (BondOptionMeetingVariancesProof.a0148 τ A) c b
  have hm : b + ∑ i, c i*(v i : ℝ)*BondOptionMeetingVariancesProof.a0148 τ A i = 0 := by
    simp only [b, c, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last,
      one_mul, zero_mul, add_zero, BondOptionMeetingVariancesProof.a0148,
      Standalone.D3EventVariances.past, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, ite_eq_left (past_date τ hτ A hA _), mul_neg]
    rw [Finset.sum_neg_distrib, add_neg_cancel]
  have hv : (∑ i, v i * (c i^2).toNNReal) = ∑ i : Fin N, v i.castSucc := by
    simp [c, Fin.sum_univ_castSucc]
  rw [hm, hv] at h
  apply h.congr
  apply Eventually.of_forall
  intro ω
  rw [rate_before_sum τ v hτ A hA hAT]
  simp only [Standalone.BondOptionMeetingVariances.L0149, c, b, Fin.sum_univ_castSucc,
    Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, zero_mul, add_zero, Finset.sum_add_distrib]
  ring

lemma model_specialization : modelStatement := by
  intro N J τ v hτ0 hτ hJ u hu A S hA hAT hTS hSa
  have hT0 : 0 ≤ τ (N+1) := by
    rw [← hτ0]
    exact hτ.monotoneOn (by simp) (by simp) (Nat.zero_le _)
  have hTa := hTS.le.trans hSa
  have h0 := hT0.trans hTa
  have hT : ∀ i : Fin (N+1), τ (i.val+1) ≤ u 0 := fun i => (last_date τ hτ i).trans hTa
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have hq : 0 ≤ VMinus019 v := Finset.sum_nonneg (fun i _ => (v i.castSucc).coe_nonneg)
  refine ⟨?_, rate_at_last τ v hτ A hA hAT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact reveal_frozen τ v hτ A t hA ht.1 ht.2
  · exact LateAmericanExerciseProof.compound_eq τ v u hu hT
  · exact LateAmericanExerciseProof.compound_rate_completed_integrable τ v hτ0 hτ hJ u hu h0 hT
  · exact LateAmericanExerciseProof.initial_condExp τ v hτ0 hτ hJ u hu h0 hT
  · intro t ht
    exact ⟨model_future_measurable τ v A _ _ t ht.1,
      model_future_condExp τ v hτ0 hτ hJ u hu A t hA ht.1 hTa h0⟩
  · intro K ω
    exact rule_mem _ _ _ _ _ _ _ K _ _ hAT hTS.le ω
  · intro K
    exact rule_stopping (completedFilt τ v) _ _ _ _ _ _ _ K _ _ hq hAT hTS.le hab
      (model_rate_completed_measurable τ v A) (model_rate_completed_measurable τ v (τ (N+1)))
  · intro σ hσ hσA
    exact before_measurable (completedFilt τ v) A (τ (N+1)) σ hσ hσA
      (fun t ht => reveal_frozen τ v hτ A t hA ht.1 ht.2)
  · intro t ht ω
    exact bank_before τ v hτ0 hτ A t hA hAT ht.1 ht.2 ω
  · intro t ht ω
    exact LateAmericanExerciseProof.bank_after τ v (τ (N+1)) t (last_date τ hτ) ht ω
  · have h := discounted_before_law τ v hτ0 hτ A hA hAT
    exact ⟨h, h.isProbabilityMeasure⟩

instance {N : ℕ} (v : Fin N → NNReal) : IsProbabilityMeasure (Q v) := by unfold Q; infer_instance
instance {N : ℕ} (v : Fin N → NNReal) : IsProbabilityMeasure (Qc v) :=
  ⟨by change (Q v) univ = 1; exact measure_univ⟩

lemma V_split {N : ℕ} (v : Fin (N+1) → NNReal) : V v = VMinus019 v + (v (Fin.last N) : ℝ) := by
  simp [V, VMinus019, Fin.sum_univ_castSucc]

lemma completed_measurable {N : ℕ} (v : Fin N → NNReal) (f : Ω N → ℝ) (hf : Measurable f) :
    Measurable (fun ω : Ωc v => f ω) := by
  intro E hE
  exact ⟨_, hf hE, EventuallyEq.refl _ _⟩

lemma date_nonneg {N : ℕ} (τ : ℕ → ℝ) (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (k : ℕ) (hk : k ≤ N+1) : 0 ≤ τ k := by
  rw [← hτ0]
  exact hτ.monotoneOn (by simp) (by simpa using hk) (Nat.zero_le k)

lemma g_measurable (V T S a b K : ℝ) : Measurable (g0195 V T S a b K) :=
  cash_measurable V T a b K (S-T)

/-- Freezing an independent shock: integrating out the independent coordinate inside a
product with a measurable function of the earlier information. -/
lemma freeze {Ω' : Type} (m₁ m₂ : MeasurableSpace Ω') [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω') [IsFiniteMeasure P]
    (hm₁ : m₁ ≤ mΩ') (hm₂ : m₂ ≤ mΩ') (hind : Indep m₁ m₂ P)
    (X Ψ Z : Ω' → ℝ) (hX : Measurable[m₁] X) (hΨ : Measurable[m₁] Ψ) (hZ : Measurable[m₂] Z)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hint : Integrable (fun ω => Ψ ω * g (X ω + Z ω)) P) :
    Integrable (fun ω => Ψ ω * ∫ z, g (X ω + z) ∂(P.map Z)) P ∧
    ∫ ω, Ψ ω * g (X ω + Z ω) ∂P = ∫ ω, Ψ ω * ∫ z, g (X ω + z) ∂(P.map Z) ∂P := by
  have hXΨ₁ : Measurable[m₁] (fun ω => (X ω, Ψ ω)) := hX.prodMk hΨ
  have hXΨ : Measurable[mΩ'] (fun ω => (X ω, Ψ ω)) := hXΨ₁.mono hm₁ le_rfl
  have hZ' : Measurable[mΩ'] Z := hZ.mono hm₂ le_rfl
  have hindf : IndepFun (fun ω => (X ω, Ψ ω)) Z P :=
    indep_of_indep_of_le_left (indep_of_indep_of_le_right hind (measurable_iff_comap_le.1 hZ))
      (measurable_iff_comap_le.1 hXΨ₁)
  have hmap := hindf.map_prod_eq_prod_map_map hXΨ.aemeasurable hZ'.aemeasurable
  let φ : (ℝ × ℝ) × ℝ → ℝ := fun p => p.1.2 * g (p.1.1 + p.2)
  have hφ : Measurable φ := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × ℝ => g (p.1.1 + p.2)) := hg.comp (by fun_prop)
    exact (measurable_snd.comp measurable_fst).mul h1
  have hpair : Measurable[mΩ'] (fun ω => ((X ω, Ψ ω), Z ω)) := hXΨ.prodMk hZ'
  have hφint : Integrable φ ((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hφ.aestronglyMeasurable hpair.aemeasurable).2 hint
  have hG : Measurable (fun x : ℝ => ∫ z, g (x + z) ∂(P.map Z)) :=
    (show Measurable (fun p : ℝ × ℝ => g (p.1 + p.2)) by
      exact hg.comp measurable_add).stronglyMeasurable.integral_prod_right.measurable
  have hΨG : Measurable (fun p : ℝ × ℝ => p.2 * ∫ z, g (p.1 + z) ∂(P.map Z)) :=
    measurable_snd.mul (hG.comp measurable_fst)
  have h1 : ∫ ω, Ψ ω * g (X ω + Z ω) ∂P =
      ∫ p, φ p ∂((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) := by
    rw [← hmap]
    exact (integral_map hpair.aemeasurable hφ.aestronglyMeasurable).symm
  have h2 : ∫ p, φ p ∂((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) =
      ∫ x, x.2 * ∫ z, g (x.1 + z) ∂(P.map Z) ∂(P.map (fun ω => (X ω, Ψ ω))) := by
    rw [integral_prod φ hφint]
    congr 1
    funext x
    exact integral_const_mul x.2 (fun z => g (x.1 + z))
  have h3 : ∫ x, x.2 * ∫ z, g (x.1 + z) ∂(P.map Z) ∂(P.map (fun ω => (X ω, Ψ ω))) =
      ∫ ω, Ψ ω * ∫ z, g (X ω + z) ∂(P.map Z) ∂P :=
    integral_map hXΨ.aemeasurable hΨG.aestronglyMeasurable
  refine ⟨?_, h1.trans (h2.trans h3)⟩
  have hi := hφint.integral_prod_left
  have hi' : Integrable (fun x : ℝ × ℝ => x.2 * ∫ z, g (x.1 + z) ∂(P.map Z))
      (P.map (fun ω => (X ω, Ψ ω))) :=
    hi.congr (Eventually.of_forall fun x => integral_const_mul x.2 (fun z => g (x.1 + z)))
  exact (integrable_map_measure hΨG.aestronglyMeasurable hXΨ.aemeasurable).1 hi'

lemma freeze_before {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1))
    (Ψ : Ω (N+1) → ℝ) (hΨ : Measurable[filt τ A] Ψ) (g : ℝ → ℝ) (hg : Measurable g)
    (hint : Integrable (fun ω => Ψ ω * g (r τ v (τ (N+1)) ω)) (Q v)) :
    Integrable (fun ω => Ψ ω * ∫ z, g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
      ∂gaussianReal 0 (v (Fin.last N))) (Q v) ∧
    ∫ ω, Ψ ω * g (r τ v (τ (N+1)) ω) ∂Q v =
      ∫ ω, Ψ ω * ∫ z, g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
        ∂gaussianReal 0 (v (Fin.last N)) ∂Q v := by
  have hind : Indep (filt τ A) (D3EventVariancesProof.coordAlg {Fin.last N}) (Q v) :=
    (D3EventVariancesProof.indep_before (Fin.last N) (by simpa using hAT)).symm
  have hX : Measurable[filt τ A] (fun ω => r τ v A ω + VMinus019 v*(τ (N+1)-A)) :=
    (model_rate_measurable τ v A).add measurable_const
  have hZ : Measurable[D3EventVariancesProof.coordAlg {Fin.last N}]
      (fun ω : Ω (N+1) => ω (Fin.last N)) :=
    D3EventVariancesProof.measurable_coord (mem_singleton _)
  have hlaw : (Q v).map (fun ω : Ω (N+1) => ω (Fin.last N)) = gaussianReal 0 (v (Fin.last N)) :=
    (D3EventVariancesProof.law (v := v) (Fin.last N)).map_eq
  have he : (fun ω => Ψ ω * g (r τ v (τ (N+1)) ω)) =
      fun ω => Ψ ω * g ((r τ v A ω + VMinus019 v*(τ (N+1)-A)) + ω (Fin.last N)) := by
    funext ω
    rw [rate_at_last τ v hτ A hA hAT]
  rw [he] at hint ⊢
  have h := freeze (filt τ A) _ (Q v) ((filt τ).le A) (D3EventVariancesProof.coordAlg_le _) hind
    _ Ψ _ hX hΨ hZ g hg hint
  rw [hlaw] at h
  exact h

lemma exp_abs_integrable {N : ℕ} (v : Fin N → NNReal) (M : ℝ) :
    Integrable (fun ω : Ω N => Real.exp (M * ∑ i, |ω i|)) (Q v) := by
  have he : (fun ω : Ω N => Real.exp (M * ∑ i, |ω i|)) =
      fun ω => ∏ i, Real.exp (M * |ω i|) := by
    funext ω
    rw [Finset.mul_sum, Real.exp_sum]
  rw [he]
  change Integrable _ (Measure.infinitePi fun i => gaussianReal 0 (v i))
  rw [Measure.infinitePi_eq_pi]
  exact Integrable.fintype_prod (f := fun _ x => Real.exp (M * |x|))
    (fun i => gaussian_exp_abs 0 (v i) M)

lemma dom_integrable {N : ℕ} (v : Fin N → NNReal) (f : Ω N → ℝ) (hf : Measurable f) (C M : ℝ)
    (hb : ∀ ω, |f ω| ≤ C * Real.exp (M * ∑ i, |ω i|)) : Integrable f (Q v) :=
  ((exp_abs_integrable v M).const_mul C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

lemma bank_lower {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1))
    (ω : Ω (N+1)) : -logB τ v A ω ≤ A * ∑ i, |ω i| := by
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  rw [bank_before_sum τ v hτ0 hτ A A hA le_rfl hAT.le, Fin.sum_univ_castSucc (f := fun i => |ω i|)]
  have hterm (i : Fin N) :
      -((A-τ (i.val+1))*ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))^2/2) ≤
        A*|ω i.castSucc| := by
    have h1 : 0 ≤ A-τ (i.val+1) := sub_nonneg.mpr (past_date τ hτ A hA i)
    have h2 : A-τ (i.val+1) ≤ A := by linarith [date_nonneg τ hτ0 hτ (i.val+1) (by omega)]
    have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (ω i.castSucc)) h1
    have h4 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (ω i.castSucc))
    have h5 : 0 ≤ (v i.castSucc : ℝ)*(A-τ (i.val+1))^2/2 := by positivity
    nlinarith
  calc -(∑ i : Fin N, ((A-τ (i.val+1))*ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))^2/2))
      = ∑ i : Fin N, -((A-τ (i.val+1))*ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))^2/2) := by
        rw [Finset.sum_neg_distrib]
    _ ≤ ∑ i : Fin N, A*|ω i.castSucc| := Finset.sum_le_sum fun i _ => hterm i
    _ ≤ A*((∑ i : Fin N, |ω i.castSucc|) + |ω (Fin.last N)|) := by
        rw [mul_add, Finset.mul_sum]
        linarith [mul_nonneg h0 (abs_nonneg (ω (Fin.last N)))]

lemma rate_last_abs {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (ω : Ω (N+1)) :
    |r τ v (τ (N+1)) ω| ≤ (∑ i, |ω i|) + ∑ i, (v i : ℝ)*(τ (N+1)-τ (i.val+1)) := by
  have he : r τ v (τ (N+1)) ω = ∑ i, (ω i + (v i : ℝ)*(τ (N+1)-τ (i.val+1))) := by
    simp only [r, ite_eq_left (last_date τ hτ _)]
  rw [he, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h : 0 ≤ (v i : ℝ)*(τ (N+1)-τ (i.val+1)) :=
    mul_nonneg (v i).coe_nonneg (sub_nonneg.mpr (last_date τ hτ i))
  calc |ω i + (v i : ℝ)*(τ (N+1)-τ (i.val+1))|
      ≤ |ω i| + |(v i : ℝ)*(τ (N+1)-τ (i.val+1))| := abs_add_le _ _
    _ = _ := by rw [abs_of_nonneg h]

lemma rate_before_abs {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1))
    (ω : Ω (N+1)) :
    |r τ v A ω| ≤ (∑ i, |ω i|) + ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1)) := by
  rw [rate_before_sum τ v hτ A hA hAT, Fin.sum_univ_castSucc (f := fun i => |ω i|)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hs : ∑ i : Fin N, |ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))| ≤
      ∑ i : Fin N, (|ω i.castSucc| + (v i.castSucc : ℝ)*(A-τ (i.val+1))) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h : 0 ≤ (v i.castSucc : ℝ)*(A-τ (i.val+1)) :=
      mul_nonneg (v _).coe_nonneg (sub_nonneg.mpr (past_date τ hτ A hA i))
    calc |ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))|
        ≤ |ω i.castSucc| + |(v i.castSucc : ℝ)*(A-τ (i.val+1))| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg h]
  rw [Finset.sum_add_distrib] at hs
  linarith [abs_nonneg (ω (Fin.last N))]

lemma call_discount_bound (δ c K q L x : ℝ) (hδ : 0 < δ) (hq : 0 ≤ q) (hL : 0 ≤ L) :
    |max ((Real.exp (δ*x+c)-1)/δ-K) 0 * D0194 q L x| ≤
      (Real.exp c/δ+|K|) * Real.exp ((δ+L)*|x|) := by
  have hD := discount_bounds q L x hq hL
  have hc : max ((Real.exp (δ*x+c)-1)/δ-K) 0 ≤ Real.exp c/δ * Real.exp (δ*|x|)+|K| := by
    apply max_le
    · have he : Real.exp (δ*x+c) ≤ Real.exp c * Real.exp (δ*|x|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [le_abs_self x]
      have he' := div_le_div_of_nonneg_right he hδ.le
      have hh : (Real.exp c * Real.exp (δ*|x|))/δ = Real.exp c/δ * Real.exp (δ*|x|) := by ring
      rw [hh] at he'
      have hn : 0 ≤ 1/δ := by positivity
      rw [sub_div]
      linarith [neg_le_abs K]
    · positivity
  have he1 : 1 ≤ Real.exp (δ*|x|) := Real.one_le_exp (by positivity)
  rw [abs_of_nonneg (mul_nonneg (le_max_right _ _) (zero_le_one.trans hD.1))]
  calc
    _ ≤ (Real.exp c/δ * Real.exp (δ*|x|)+|K|) * Real.exp (L*|x|) :=
      mul_le_mul hc hD.2 (Real.exp_pos _).le (by positivity)
    _ ≤ ((Real.exp c/δ+|K|) * Real.exp (δ*|x|)) * Real.exp (L*|x|) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left he1 (abs_nonneg K)]
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma p_bound (q w A T a b K x : ℝ) (hq : 0 ≤ q) (hAT : A ≤ T) (hab : a < b) :
    |p0195 q w A T a b K x| ≤
      (Real.exp ((b-a)*(q*((a+b)/2-A)+w*(b-T)))/(b-a)+|K|) * Real.exp ((b-a+(T-A))*|x|) := by
  have he : fMinus0193 q w A T a b x =
      (Real.exp ((b-a)*x+(b-a)*(q*((a+b)/2-A)+w*(b-T)))-1)/(b-a) := by
    unfold fMinus0193
    rw [show (b-a)*(x+q*((a+b)/2-A)+w*(b-T)) = (b-a)*x+(b-a)*(q*((a+b)/2-A)+w*(b-T)) by ring]
  unfold p0195
  rw [he]
  exact call_discount_bound (b-a) _ K q (T-A) x (sub_pos.mpr hab) hq (sub_nonneg.mpr hAT)

/-! ### Discounted payoff pieces -/

noncomputable def early019 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal) (A a b K : ℝ)
    (ω : Ω (N+1)) : ℝ :=
  Real.exp (-logB τ v A ω) * p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)
noncomputable def wait019 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal) (A S a b K : ℝ)
    (ω : Ω (N+1)) : ℝ :=
  Real.exp (-logB τ v A ω) * Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
    g0195 (V v) (τ (N+1)) S a b K (r τ v (τ (N+1)) ω)
noncomputable def cont019 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal) (A S a b K : ℝ)
    (ω : Ω (N+1)) : ℝ :=
  Real.exp (-logB τ v A ω) * c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω)
noncomputable def best019 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal) (A S a b K : ℝ)
    (ω : Ω (N+1)) : ℝ :=
  Real.exp (-logB τ v A ω) *
    max (p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω))
      (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω))
noncomputable def pay019 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal) (A a b K : ℝ)
    (σ : Ωc v → ℝ) (ω : Ωc v) : ℝ :=
  Real.exp (-logB τ v (σ ω) ω) * max (F0192 τ v A a b (σ ω) ω-K) 0

lemma c_eq {N : ℕ} (v : Fin (N+1) → NNReal) (A T S a b K x : ℝ) :
    c0195 (VMinus019 v) (v (Fin.last N)) A T S a b K x =
      Real.exp (-x*(T-A)-VMinus019 v*(T-A)^2/2) *
        ∫ z, g0195 (V v) T S a b K (x+VMinus019 v*(T-A)+z) ∂gaussianReal 0 (v (Fin.last N)) := by
  rw [V_split]
  rfl

section Model
variable {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)

lemma q_nonneg : 0 ≤ VMinus019 v := Finset.sum_nonneg fun i _ => (v i.castSucc).coe_nonneg
lemma V_nonneg : 0 ≤ V v := Finset.sum_nonneg fun i _ => (v i).coe_nonneg

lemma bank_filt_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1)) : Measurable[filt τ A] (logB τ v A) := by
  have he : logB τ v A = fun ω => ∑ i : Fin N,
      ((A-τ (i.val+1))*ω i.castSucc + (v i.castSucc : ℝ)*(A-τ (i.val+1))^2/2) :=
    funext (bank_before_sum τ v hτ0 hτ A A hA le_rfl hAT.le)
  rw [he]
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable[filt τ A] (fun ω : Ω (N+1) => ω i.castSucc) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le i.castSucc
      (le_iSup_of_le (past_date τ hτ A hA i) le_rfl))
  exact (measurable_const.mul hi).add measurable_const

lemma bank_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (logB τ v t) :=
  LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ t ht

lemma rate_measurable (t : ℝ) : Measurable (r τ v t) :=
  (model_rate_measurable τ v t).mono ((filt τ).le t) le_rfl

lemma waiting_bound (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    ∃ C : ℝ, ∀ ω : Ω (N+1),
      |Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
        g0195 (V v) (τ (N+1)) S a b K (r τ v (τ (N+1)) ω)| ≤
        C * Real.exp ((τ (N+1)-A+(b-a+(S-τ (N+1)))) * ∑ i, |ω i|) := by
  have hℓ : 0 ≤ τ (N+1)-A := sub_nonneg.mpr hAT.le
  have hκ : 0 ≤ b-a+(S-τ (N+1)) := add_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hTS)
  have hC₁ : 0 ≤ Real.exp ((b-a)*(V v*((a+b)/2-τ (N+1))))/(b-a)+|K| := by
    have : 0 < b-a := sub_pos.mpr hab
    positivity
  refine ⟨(Real.exp ((b-a)*(V v*((a+b)/2-τ (N+1))))/(b-a)+|K|) *
    Real.exp ((τ (N+1)-A)*(∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1))) +
      (b-a+(S-τ (N+1)))*(∑ i, (v i : ℝ)*(τ (N+1)-τ (i.val+1)))), fun ω => ?_⟩
  have hrA := rate_before_abs τ v hτ A hA hAT ω
  have hrT := rate_last_abs τ v hτ ω
  have hg := cash_bound (V v) (τ (N+1)) a b K (S-τ (N+1)) (r τ v (τ (N+1)) ω)
    (V_nonneg v) (sub_nonneg.mpr hTS) hab
  have h1 : Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) ≤
      Real.exp ((τ (N+1)-A)*((∑ i, |ω i|) + ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1)))) := by
    apply Real.exp_le_exp.mpr
    have h' := mul_le_mul_of_nonneg_left hrA hℓ
    have h'' := mul_le_mul_of_nonneg_right (neg_le_abs (r τ v A ω)) hℓ
    nlinarith [mul_nonneg (q_nonneg v) (sq_nonneg (τ (N+1)-A))]
  have h2 : Real.exp ((b-a+(S-τ (N+1)))*|r τ v (τ (N+1)) ω|) ≤
      Real.exp ((b-a+(S-τ (N+1)))*((∑ i, |ω i|) + ∑ i, (v i : ℝ)*(τ (N+1)-τ (i.val+1)))) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrT hκ)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc _ ≤ Real.exp ((τ (N+1)-A)*((∑ i, |ω i|) + ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1)))) *
        ((Real.exp ((b-a)*(V v*((a+b)/2-τ (N+1))))/(b-a)+|K|) *
          Real.exp ((b-a+(S-τ (N+1)))*((∑ i, |ω i|) + ∑ i, (v i : ℝ)*(τ (N+1)-τ (i.val+1))))) :=
        mul_le_mul h1 (hg.trans (mul_le_mul_of_nonneg_left h2 hC₁)) (abs_nonneg _) (Real.exp_pos _).le
    _ = (Real.exp ((b-a)*(V v*((a+b)/2-τ (N+1))))/(b-a)+|K|) *
        Real.exp ((τ (N+1)-A)*((∑ i, |ω i|) + ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1))) +
          (b-a+(S-τ (N+1)))*((∑ i, |ω i|) + ∑ i, (v i : ℝ)*(τ (N+1)-τ (i.val+1)))) := by
        rw [Real.exp_add]; ring
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

lemma discount_lift (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1)) (F : Ω (N+1) → ℝ) (C M : ℝ)
    (hF : ∀ ω, |F ω| ≤ C * Real.exp (M * ∑ i, |ω i|)) :
    ∀ ω, |Real.exp (-logB τ v A ω) * F ω| ≤ C * Real.exp ((A+M) * ∑ i, |ω i|) := by
  intro ω
  rw [abs_mul, abs_of_pos (Real.exp_pos _), add_mul, Real.exp_add]
  have h1 := Real.exp_le_exp.mpr (bank_lower τ v hτ0 hτ A hA hAT ω)
  calc _ ≤ Real.exp (A * ∑ i, |ω i|) * (C * Real.exp (M * ∑ i, |ω i|)) :=
        mul_le_mul h1 (hF ω) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

lemma early_bound (hτ : StrictMonoOn τ (Iic (N+1))) (A a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hab : a < b) :
    ∃ C : ℝ, ∀ ω : Ω (N+1),
      |p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)| ≤
        C * Real.exp ((b-a+(τ (N+1)-A)) * ∑ i, |ω i|) := by
  have hκ : 0 ≤ b-a+(τ (N+1)-A) := add_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hAT.le)
  have hC₂ : 0 ≤ Real.exp ((b-a)*(VMinus019 v*((a+b)/2-A)+(v (Fin.last N) : ℝ)*(b-τ (N+1))))/(b-a)+|K| := by
    have : 0 < b-a := sub_pos.mpr hab
    positivity
  refine ⟨(Real.exp ((b-a)*(VMinus019 v*((a+b)/2-A)+(v (Fin.last N) : ℝ)*(b-τ (N+1))))/(b-a)+|K|) *
    Real.exp ((b-a+(τ (N+1)-A))*(∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1)))), fun ω => ?_⟩
  have hp := p_bound (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)
    (q_nonneg v) hAT.le hab
  have hrA := rate_before_abs τ v hτ A hA hAT ω
  have h2 : Real.exp ((b-a+(τ (N+1)-A))*|r τ v A ω|) ≤
      Real.exp ((b-a+(τ (N+1)-A))*((∑ i, |ω i|) + ∑ i : Fin N, (v i.castSucc : ℝ)*(A-τ (i.val+1)))) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrA hκ)
  calc _ ≤ _ := hp.trans (mul_le_mul_of_nonneg_left h2 hC₂)
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

lemma wait_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    Integrable (wait019 τ v A S a b K) (Q v) := by
  obtain ⟨C, hC⟩ := waiting_bound τ v hτ A S a b K hA hAT hTS hab
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  have hb := bank_measurable τ v hτ0 hτ A h0
  have hx := rate_measurable τ v A
  have hy := rate_measurable τ v (τ (N+1))
  have hg := g_measurable (V v) (τ (N+1)) S a b K
  refine dom_integrable v _ (by unfold wait019; fun_prop) C
    (A+(τ (N+1)-A+(b-a+(S-τ (N+1))))) (fun ω => ?_)
  have := discount_lift τ v hτ0 hτ A hA hAT _ C _ hC ω
  simpa only [wait019, mul_assoc] using this

lemma bare_wait_integrable (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    Integrable (fun ω => Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
      g0195 (V v) (τ (N+1)) S a b K (r τ v (τ (N+1)) ω)) (Q v) := by
  obtain ⟨C, hC⟩ := waiting_bound τ v hτ A S a b K hA hAT hTS hab
  have hx := rate_measurable τ v A
  have hy := rate_measurable τ v (τ (N+1))
  have hg := g_measurable (V v) (τ (N+1)) S a b K
  exact dom_integrable v _ (by fun_prop) C _ hC

lemma early_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hab : a < b) :
    Integrable (early019 τ v A a b K) (Q v) := by
  obtain ⟨C, hC⟩ := early_bound τ v hτ A a b K hA hAT hab
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  have hb := bank_measurable τ v hτ0 hτ A h0
  have hx := rate_measurable τ v A
  have hp := p_measurable (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K
  exact dom_integrable v _ (by unfold early019; fun_prop) C _
    (discount_lift τ v hτ0 hτ A hA hAT _ C _ hC)

lemma cont_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    Integrable (cont019 τ v A S a b K) (Q v) := by
  have hΨ : Measurable[filt τ A] (fun ω : Ω (N+1) => Real.exp (-logB τ v A ω) *
      Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) := by
    have h1 := bank_filt_measurable τ v hτ0 hτ A hA hAT
    have h2 := model_rate_measurable τ v A
    fun_prop
  have h := (freeze_before τ v hτ A hA hAT _ hΨ _ (g_measurable (V v) (τ (N+1)) S a b K)
    (wait_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)).1
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [cont019]
  rw [c_eq, ← mul_assoc]

lemma best_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    Integrable (best019 τ v A S a b K) (Q v) := by
  refine ((early_integrable τ v hτ0 hτ A a b K hA hAT hab).sup
    (cont_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)).congr (Eventually.of_forall fun ω => ?_)
  show max (early019 τ v A a b K ω) (cont019 τ v A S a b K ω) = best019 τ v A S a b K ω
  simp only [early019, cont019, best019]
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]

lemma early_le_best (A S a b K : ℝ) (ω : Ω (N+1)) :
    early019 τ v A a b K ω ≤ best019 τ v A S a b K ω :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le

lemma cont_le_best (A S a b K : ℝ) (ω : Ω (N+1)) :
    cont019 τ v A S a b K ω ≤ best019 τ v A S a b K ω :=
  mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le

lemma waiting_setIntegral (hτ : StrictMonoOn τ (Iic (N+1))) (A : ℝ) (hA : τ N ≤ A)
    (hAT : A < τ (N+1)) (Ψ : Ω (N+1) → ℝ) (hΨ : Measurable[filt τ A] Ψ) (g : ℝ → ℝ)
    (hg : Measurable g) (hint : Integrable (fun ω => Ψ ω * g (r τ v (τ (N+1)) ω)) (Q v))
    (s : Set (Ωc v)) (hs : MeasurableSet[completedFilt τ v A] s) :
    ∫ ω in s, Ψ ω * g (r τ v (τ (N+1)) ω) ∂Qc v =
      ∫ ω in s, Ψ ω * ∫ z, g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
        ∂gaussianReal 0 (v (Fin.last N)) ∂Qc v := by
  obtain ⟨s', hs', hae⟩ := hs
  have hae' : s =ᵐ[Qc v] s' := hae
  rw [Measure.restrict_congr_set hae']
  let s'' : Set (Ω (N+1)) := s'
  have hs'm : @MeasurableSet (Ω (N+1)) MeasurableSpace.pi s'' := (filt τ).le A s' hs'
  have hΨ' : Measurable[filt τ A] (s''.indicator Ψ) := hΨ.indicator hs'
  have hint' : Integrable (fun ω => s''.indicator Ψ ω * g (r τ v (τ (N+1)) ω)) (Q v) := by
    refine (hint.indicator hs'm).congr (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ s'' <;> simp [h]
  have h := freeze_before τ v hτ A hA hAT _ hΨ' g hg hint'
  have h1 : ∫ ω in s', Ψ ω * g (r τ v (τ (N+1)) ω) ∂Qc v =
      ∫ ω in s'', Ψ ω * g (r τ v (τ (N+1)) ω) ∂Q v :=
    CompoundedFuturesIdentificationProof.completion_setIntegral v _ hint s'' hs'm
  have h2 : ∫ ω in s', Ψ ω * ∫ z, g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
        ∂gaussianReal 0 (v (Fin.last N)) ∂Qc v =
      ∫ ω in s'', Ψ ω * ∫ z, g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
        ∂gaussianReal 0 (v (Fin.last N)) ∂Q v :=
    CompoundedFuturesIdentificationProof.completion_setIntegral v _
      (freeze_before τ v hτ A hA hAT Ψ hΨ g hg hint).1 s'' hs'm
  rw [h1, h2, ← integral_indicator hs'm, ← integral_indicator hs'm]
  have e1 : (fun ω : Ω (N+1) => s''.indicator (fun ω => Ψ ω * g (r τ v (τ (N+1)) ω)) ω) =
      fun ω => s''.indicator Ψ ω * g (r τ v (τ (N+1)) ω) := by
    funext ω
    by_cases hω : ω ∈ s'' <;> simp [hω]
  have e2 : (fun ω : Ω (N+1) => s''.indicator (fun ω => Ψ ω * ∫ z,
      g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z) ∂gaussianReal 0 (v (Fin.last N))) ω) =
      fun ω => s''.indicator Ψ ω * ∫ z,
        g (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z) ∂gaussianReal 0 (v (Fin.last N)) := by
    funext ω
    by_cases hω : ω ∈ s'' <;> simp [hω]
  rw [e1, e2]
  exact h.2

lemma wait_setIntegral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b)
    (s : Set (Ωc v)) (hs : MeasurableSet[completedFilt τ v A] s) :
    ∫ ω in s, wait019 τ v A S a b K ω ∂Qc v = ∫ ω in s, cont019 τ v A S a b K ω ∂Qc v := by
  have hΨ : Measurable[filt τ A] (fun ω : Ω (N+1) => Real.exp (-logB τ v A ω) *
      Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) := by
    have h1 := bank_filt_measurable τ v hτ0 hτ A hA hAT
    have h2 := model_rate_measurable τ v A
    fun_prop
  have h := waiting_setIntegral τ v hτ A hA hAT _ hΨ _ (g_measurable (V v) (τ (N+1)) S a b K)
    (wait_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab) s hs
  have e2 : (fun ω : Ωc v => cont019 τ v A S a b K ω) = fun ω =>
      (Real.exp (-logB τ v A ω) * Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) *
        ∫ z, g0195 (V v) (τ (N+1)) S a b K (r τ v A ω + VMinus019 v*(τ (N+1)-A) + z)
          ∂gaussianReal 0 (v (Fin.last N)) := by
    funext ω
    simp only [cont019]
    rw [c_eq, ← mul_assoc]
  rw [e2]
  exact h

lemma waiting_condExp (_hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    (Qc v)[fun ω : Ωc v => Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
        g0195 (V v) (τ (N+1)) S a b K (r τ v (τ (N+1)) ω) | completedFilt τ v A] =ᵐ[Qc v]
      fun ω => c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω) := by
  have hint := bare_wait_integrable τ v hτ A S a b K hA hAT hTS hab
  have hΨ : Measurable[filt τ A] (fun ω : Ω (N+1) =>
      Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) := by
    have h2 := model_rate_measurable τ v A
    fun_prop
  have hfc : Integrable (fun ω : Ωc v =>
      Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
        g0195 (V v) (τ (N+1)) S a b K (r τ v (τ (N+1)) ω)) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp hint
  have hG := (freeze_before τ v hτ A hA hAT _ hΨ _ (g_measurable (V v) (τ (N+1)) S a b K) hint).1
  have hgc : Integrable (fun ω : Ωc v =>
      c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω)) (Qc v) := by
    refine ((LateAmericanExerciseProof.completion_law v).integrable_comp hG).congr
      (Eventually.of_forall fun ω => ?_)
    exact (c_eq v A (τ (N+1)) S a b K (r τ v A ω)).symm
  have hcm : Measurable[completedFilt τ v A] (fun ω : Ωc v =>
      c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω)) :=
    (c_measurable _ _ _ _ _ _ _ _).comp (model_rate_completed_measurable τ v A)
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((completedFilt τ v).le A) hfc
    (fun s _ _ => hgc.integrableOn) ?_ hcm.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  rw [waiting_setIntegral τ v hτ A hA hAT _ hΨ _ (g_measurable (V v) (τ (N+1)) S a b K) hint s hs]
  apply setIntegral_congr_fun ((completedFilt τ v).le A s hs)
  intro ω _
  exact c_eq v A (τ (N+1)) S a b K (r τ v A ω)

lemma early_payoff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A a b K t : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (ht : t ∈ Ico A (τ (N+1))) (ω : Ω (N+1)) :
    Real.exp (-logB τ v t ω) * max (F0192 τ v A a b t ω-K) 0 ≤ early019 τ v A a b K ω := by
  simp only [F0192, ite_eq_left ht.2, early019, p0195]
  rw [bank_before τ v hτ0 hτ A t hA hAT ht.1 ht.2.le ω,
    show -(logB τ v A ω + r τ v A ω*(t-A) + VMinus019 v*(t-A)^2/2) =
      -logB τ v A ω + (-r τ v A ω*(t-A)-VMinus019 v*(t-A)^2/2) by ring, Real.exp_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (discount_max (VMinus019 v) (τ (N+1)-A) (r τ v A ω)
    (q_nonneg v) (sub_nonneg.mpr hAT.le) (t-A) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩)
    (le_max_right _ _)

lemma late_payoff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K t : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (ht : t ∈ Icc (τ (N+1)) S)
    (ω : Ω (N+1)) :
    Real.exp (-logB τ v t ω) * max (F0192 τ v A a b t ω-K) 0 ≤ wait019 τ v A S a b K ω := by
  simp only [F0192, ite_eq_right (not_lt.mpr ht.1), wait019, g0195]
  have hb : logB τ v t ω = logB τ v (τ (N+1)) ω + r τ v (τ (N+1)) ω*(t-τ (N+1)) +
      V v*(t-τ (N+1))^2/2 :=
    LateAmericanExerciseProof.bank_after τ v (τ (N+1)) t (last_date τ hτ) ht.1 ω
  rw [hb, bank_before τ v hτ0 hτ A (τ (N+1)) hA hAT hAT.le le_rfl ω,
    show -(logB τ v A ω + r τ v A ω*(τ (N+1)-A) + VMinus019 v*(τ (N+1)-A)^2/2 +
        r τ v (τ (N+1)) ω*(t-τ (N+1)) + V v*(t-τ (N+1))^2/2) =
      (-logB τ v A ω + (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) +
        (-r τ v (τ (N+1)) ω*(t-τ (N+1))-V v*(t-τ (N+1))^2/2) by ring,
    Real.exp_add, Real.exp_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (discount_max (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω)
    (V_nonneg v) (sub_nonneg.mpr hTS) (t-τ (N+1)) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩)
    (le_max_right _ _)

lemma early_attained (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (ω : Ω (N+1))
    (hu : u0194 (VMinus019 v) (τ (N+1)-A) (r τ v A ω) < τ (N+1)-A) :
    Real.exp (-logB τ v (A+u0194 (VMinus019 v) (τ (N+1)-A) (r τ v A ω)) ω) *
      max (F0192 τ v A a b (A+u0194 (VMinus019 v) (τ (N+1)-A) (r τ v A ω)) ω-K) 0 =
      early019 τ v A a b K ω := by
  have hu0 := (u_mem (VMinus019 v) (τ (N+1)-A) (r τ v A ω) (sub_nonneg.mpr hAT.le)).1
  have htT : A+u0194 (VMinus019 v) (τ (N+1)-A) (r τ v A ω) < τ (N+1) := by linarith
  simp only [F0192, ite_eq_left htT, early019, p0195, D0194]
  rw [bank_before τ v hτ0 hτ A _ hA hAT (by linarith) htT.le ω, add_sub_cancel_left]
  set u := u0194 (VMinus019 v) (τ (N+1)-A) (r τ v A ω) with hu_def
  rw [show -(logB τ v A ω + r τ v A ω*u + VMinus019 v*u^2/2) =
      -logB τ v A ω + (-r τ v A ω*u-VMinus019 v*u^2/2) by ring, Real.exp_add]
  ring

lemma late_attained (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (ω : Ω (N+1)) :
    Real.exp (-logB τ v (τ (N+1)+u0194 (VMinus019 v+(v (Fin.last N) : ℝ)) (S-τ (N+1))
        (r τ v (τ (N+1)) ω)) ω) *
      max (F0192 τ v A a b (τ (N+1)+u0194 (VMinus019 v+(v (Fin.last N) : ℝ)) (S-τ (N+1))
        (r τ v (τ (N+1)) ω)) ω-K) 0 =
      wait019 τ v A S a b K ω := by
  rw [← V_split]
  have hu0 : 0 ≤ u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω) :=
    (u_mem _ _ _ (sub_nonneg.mpr hTS)).1
  have hTt : ¬ τ (N+1)+u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω) < τ (N+1) := by linarith
  have hb : logB τ v (τ (N+1)+u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω)) ω =
      logB τ v (τ (N+1)) ω + r τ v (τ (N+1)) ω*
        (τ (N+1)+u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω)-τ (N+1)) +
        V v*(τ (N+1)+u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω)-τ (N+1))^2/2 :=
    LateAmericanExerciseProof.bank_after τ v (τ (N+1)) _ (last_date τ hτ) (by linarith) ω
  simp only [F0192, ite_eq_right hTt, wait019, g0195, D0194]
  rw [hb, add_sub_cancel_left, bank_before τ v hτ0 hτ A (τ (N+1)) hA hAT hAT.le le_rfl ω]
  set u := u0194 (V v) (S-τ (N+1)) (r τ v (τ (N+1)) ω) with hu_def
  rw [show -(logB τ v A ω + r τ v A ω*(τ (N+1)-A) + VMinus019 v*(τ (N+1)-A)^2/2 +
        r τ v (τ (N+1)) ω*u + V v*u^2/2) =
      (-logB τ v A ω + (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2)) +
        (-r τ v (τ (N+1)) ω*u-V v*u^2/2) by ring, Real.exp_add, Real.exp_add]
  ring

lemma admissible_measurable (A S : ℝ) (σ : Ωc v → ℝ) (hσ : σ ∈ T0193 τ v A S) :
    Measurable σ := by
  have h := hσ.2.measurable_of_le (fun ω =>
    show (σ ω : WithTop ℝ) ≤ S from WithTop.coe_le_coe.mpr (hσ.1 ω).2)
  have h' := h.untopA.mono ((completedFilt τ v).le S) le_rfl
  simpa using h'

lemma payoff_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (σ : Ωc v → ℝ) (hσ : Measurable σ)
    (hσA : ∀ ω, A ≤ σ ω) : Measurable (pay019 τ v A a b K σ) := by
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  have hbA : Measurable (fun ω : Ωc v => logB τ v A ω) :=
    completed_measurable v _ (bank_measurable τ v hτ0 hτ A h0)
  have hbT : Measurable (fun ω : Ωc v => logB τ v (τ (N+1)) ω) :=
    completed_measurable v _ (bank_measurable τ v hτ0 hτ _ (date_nonneg τ hτ0 hτ (N+1) le_rfl))
  have hrA : Measurable (fun ω : Ωc v => r τ v A ω) := completed_measurable v _ (rate_measurable τ v A)
  have hrT : Measurable (fun ω : Ωc v => r τ v (τ (N+1)) ω) :=
    completed_measurable v _ (rate_measurable τ v (τ (N+1)))
  have hlt : MeasurableSet {ω : Ωc v | σ ω < τ (N+1)} := measurableSet_lt hσ measurable_const
  have he : (fun ω : Ωc v => logB τ v (σ ω) ω) = fun ω =>
      if σ ω < τ (N+1) then logB τ v A ω + r τ v A ω*(σ ω-A) + VMinus019 v*(σ ω-A)^2/2
      else logB τ v (τ (N+1)) ω + r τ v (τ (N+1)) ω*(σ ω-τ (N+1)) + V v*(σ ω-τ (N+1))^2/2 := by
    funext ω
    split_ifs with h
    · exact bank_before τ v hτ0 hτ A (σ ω) hA hAT (hσA ω) h.le ω
    · exact LateAmericanExerciseProof.bank_after τ v (τ (N+1)) (σ ω) (last_date τ hτ) (not_lt.mp h) ω
  have hm1 : Measurable (fun ω : Ωc v => logB τ v (σ ω) ω) := by
    rw [he]
    exact Measurable.ite hlt (by fun_prop) (by fun_prop)
  have hm2 : Measurable (fun ω : Ωc v => F0192 τ v A a b (σ ω) ω) := by
    refine Measurable.ite hlt ?_ ?_
    · unfold fMinus0193
      fun_prop
    · unfold fPlus0193
      fun_prop
  unfold pay019
  fun_prop

lemma pay_nonneg (A a b K : ℝ) (σ : Ωc v → ℝ) (ω : Ωc v) : 0 ≤ pay019 τ v A a b K σ ω :=
  mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

lemma payoff_le_dom (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (σ : Ωc v → ℝ)
    (hσ : ∀ ω, σ ω ∈ Icc A S) (ω : Ωc v) :
    pay019 τ v A a b K σ ω ≤
      {ω' : Ωc v | σ ω' < τ (N+1)}.indicator (fun ω : Ωc v => early019 τ v A a b K ω) ω +
      {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ.indicator (fun ω : Ωc v => wait019 τ v A S a b K ω) ω := by
  by_cases h : σ ω < τ (N+1)
  · rw [indicator_of_mem (show ω ∈ {ω' : Ωc v | σ ω' < τ (N+1)} from h),
      indicator_of_notMem (show ω ∉ {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ from fun h' => h' h), add_zero]
    exact early_payoff τ v hτ0 hτ A a b K (σ ω) hA hAT ⟨(hσ ω).1, h⟩ ω
  · rw [indicator_of_notMem (show ω ∉ {ω' : Ωc v | σ ω' < τ (N+1)} from h),
      indicator_of_mem (show ω ∈ {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ from h), zero_add]
    exact late_payoff τ v hτ0 hτ A S a b K (σ ω) hA hAT hTS ⟨not_lt.mp h, (hσ ω).2⟩ ω

lemma admissible_bound (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b)
    (σ : Ωc v → ℝ) (hσ : σ ∈ T0193 τ v A S) :
    Integrable (pay019 τ v A a b K σ) (Qc v) ∧
    ∫ ω, pay019 τ v A a b K σ ω ∂Qc v ≤ ∫ ω : Ωc v, best019 τ v A S a b K ω ∂Qc v := by
  have hS : MeasurableSet[completedFilt τ v A] {ω : Ωc v | σ ω < τ (N+1)} :=
    before_measurable (completedFilt τ v) A (τ (N+1)) σ hσ.2 (fun ω => (hσ.1 ω).1)
      (fun t ht => reveal_frozen τ v hτ A t hA ht.1 ht.2)
  have hS' : MeasurableSet {ω : Ωc v | σ ω < τ (N+1)} := (completedFilt τ v).le A _ hS
  have h1 : Integrable (fun ω : Ωc v => early019 τ v A a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (early_integrable τ v hτ0 hτ A a b K hA hAT hab)
  have h2 : Integrable (fun ω : Ωc v => wait019 τ v A S a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (wait_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)
  have h3 : Integrable (fun ω : Ωc v => cont019 τ v A S a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (cont_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)
  have h4 : Integrable (fun ω : Ωc v => best019 τ v A S a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (best_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)
  have hdom : Integrable (fun ω : Ωc v =>
      {ω' : Ωc v | σ ω' < τ (N+1)}.indicator (fun ω : Ωc v => early019 τ v A a b K ω) ω +
      {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ.indicator (fun ω : Ωc v => wait019 τ v A S a b K ω) ω) (Qc v) :=
    (h1.indicator hS').add (h2.indicator hS'.compl)
  have hpm := payoff_measurable τ v hτ0 hτ A a b K hA hAT σ
    (admissible_measurable τ v A S σ hσ) (fun ω => (hσ.1 ω).1)
  have hpay : Integrable (pay019 τ v A a b K σ) (Qc v) :=
    hdom.mono' hpm.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pay_nonneg τ v A a b K σ ω)]
      exact payoff_le_dom τ v hτ0 hτ A S a b K hA hAT hTS σ hσ.1 ω)
  refine ⟨hpay, ?_⟩
  calc ∫ ω, pay019 τ v A a b K σ ω ∂Qc v
      ≤ ∫ ω : Ωc v, {ω' : Ωc v | σ ω' < τ (N+1)}.indicator (fun ω : Ωc v => early019 τ v A a b K ω) ω +
          {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ.indicator (fun ω : Ωc v => wait019 τ v A S a b K ω) ω ∂Qc v :=
        integral_mono hpay hdom (payoff_le_dom τ v hτ0 hτ A S a b K hA hAT hTS σ hσ.1)
    _ = (∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}, early019 τ v A a b K ω ∂Qc v) +
        ∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ, wait019 τ v A S a b K ω ∂Qc v := by
        rw [integral_add (h1.indicator hS') (h2.indicator hS'.compl), integral_indicator hS',
          integral_indicator hS'.compl]
    _ = (∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}, early019 τ v A a b K ω ∂Qc v) +
        ∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ, cont019 τ v A S a b K ω ∂Qc v := by
        rw [wait_setIntegral τ v hτ0 hτ A S a b K hA hAT hTS hab _ hS.compl]
    _ ≤ (∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}, best019 τ v A S a b K ω ∂Qc v) +
        ∫ ω in {ω' : Ωc v | σ ω' < τ (N+1)}ᶜ, best019 τ v A S a b K ω ∂Qc v :=
        add_le_add (setIntegral_mono h1.integrableOn h4.integrableOn
            (fun ω => early_le_best τ v A S a b K ω))
          (setIntegral_mono h3.integrableOn h4.integrableOn
            (fun ω => cont_le_best τ v A S a b K ω))
    _ = _ := integral_add_compl hS' h4

lemma rule_value (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) ≤ S) (hab : a < b) :
    ∫ ω, pay019 τ v A a b K (τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K
      (r τ v A) (r τ v (τ (N+1)))) ω ∂Qc v = ∫ ω : Ωc v, best019 τ v A S a b K ω ∂Qc v := by
  let E : Set (Ωc v) := {ω | c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω) <
    p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)}
  have hE : MeasurableSet[completedFilt τ v A] E :=
    measurableSet_lt ((c_measurable _ _ _ _ _ _ _ _).comp (model_rate_completed_measurable τ v A))
      ((p_measurable _ _ _ _ _ _ _).comp (model_rate_completed_measurable τ v A))
  have hE' : MeasurableSet E := (completedFilt τ v).le A _ hE
  have h1 : Integrable (fun ω : Ωc v => early019 τ v A a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (early_integrable τ v hτ0 hτ A a b K hA hAT hab)
  have h2 : Integrable (fun ω : Ωc v => wait019 τ v A S a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (wait_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)
  have h4 : Integrable (fun ω : Ωc v => best019 τ v A S a b K ω) (Qc v) :=
    (LateAmericanExerciseProof.completion_law v).integrable_comp
      (best_integrable τ v hτ0 hτ A S a b K hA hAT hTS hab)
  have hpt : ∀ ω : Ωc v, pay019 τ v A a b K (τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K
      (r τ v A) (r τ v (τ (N+1)))) ω =
      E.indicator (fun ω : Ωc v => early019 τ v A a b K ω) ω +
      Eᶜ.indicator (fun ω : Ωc v => wait019 τ v A S a b K ω) ω := by
    intro ω
    by_cases h : c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω) <
        p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)
    · rw [indicator_of_mem (show ω ∈ E from h), indicator_of_notMem (show ω ∉ Eᶜ from fun h' => h' h),
        add_zero]
      have hu := early_strict (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω)
        (q_nonneg v) hAT hTS hab h
      simp only [pay019, τ019, gt_iff_lt, ite_eq_left h]
      exact early_attained τ v hτ0 hτ A a b K hA hAT ω hu
    · rw [indicator_of_notMem (show ω ∉ E from h), indicator_of_mem (show ω ∈ Eᶜ from h), zero_add]
      simp only [pay019, τ019, gt_iff_lt, ite_eq_right h]
      exact late_attained τ v hτ0 hτ A S a b K hA hAT hTS ω
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (h1.indicator hE') (h2.indicator hE'.compl), integral_indicator hE',
    integral_indicator hE'.compl, wait_setIntegral τ v hτ0 hτ A S a b K hA hAT hTS hab _ hE.compl,
    ← integral_add_compl hE' h4]
  congr 1
  · apply setIntegral_congr_fun hE'
    intro ω hω
    have hω' : c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω) <
        p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω) := hω
    simp only [early019, best019]
    rw [max_eq_left hω'.le]
  · apply setIntegral_congr_fun hE'.compl
    intro ω hω
    have hω' : ¬ (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K (r τ v A ω) <
        p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K (r τ v A ω)) := hω
    simp only [cont019, best019]
    rw [max_eq_right (not_lt.mp hω')]

lemma value_attained {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (hJ : 0 < J)
    (u : Fin (J+1) → ℝ) (hu : StrictMono u) (A S K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) < S) :
    U0193 τ v A S u K = ∫ ω : Ωc v, best019 τ v A S (u 0) (u (Fin.last J)) K ω ∂Qc v := by
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun ω => τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K
      (r τ v A) (r τ v (τ (N+1))) ω,
      ⟨fun ω => rule_mem _ _ _ _ _ _ _ K _ _ hAT hTS.le ω,
        rule_stopping (completedFilt τ v) _ _ _ _ _ _ _ K _ _ (q_nonneg v) hAT hTS.le hab
          (model_rate_completed_measurable τ v A) (model_rate_completed_measurable τ v (τ (N+1)))⟩,
      ?_⟩
    exact rule_value τ v hτ0 hτ A S (u 0) (u (Fin.last J)) K hA hAT hTS.le hab
  · rintro y ⟨σ, hσ, rfl⟩
    exact (admissible_bound τ v hτ0 hτ A S (u 0) (u (Fin.last J)) K hA hAT hTS.le hab σ hσ).2

lemma discounted_before_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1)))
    (A : ℝ) (hA : τ N ≤ A) (hAT : A < τ (N+1)) (G : ℝ → ℝ)
    (hG : AEStronglyMeasurable G (gaussianReal 0 (∑ i : Fin N, v i.castSucc))) :
    (∫ ω, Real.exp (-logB τ v A ω)*G (r τ v A ω) ∂Q v) =
      ∫ x, G x ∂gaussianReal 0 (∑ i : Fin N, v i.castSucc) := by
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  have h := (discounted_before_law τ v hτ0 hτ A hA hAT).integral_comp hG
  rw [Q01912, integral_withDensity_eq_integral_toReal_smul
    (by have hm := bank_measurable τ v hτ0 hτ A h0; fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, Function.comp_apply] using h

lemma best_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (A S a b K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) :
    ∫ ω : Ωc v, best019 τ v A S a b K ω ∂Qc v =
      ∫ x, max (p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K x)
        (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K x)
        ∂gaussianReal 0 (∑ i : Fin N, v i.castSucc) := by
  have h0 : 0 ≤ A := (date_nonneg τ hτ0 hτ N (by omega)).trans hA
  have hm : Measurable (fun x => max (p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b K x)
      (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S a b K x)) :=
    (p_measurable _ _ _ _ _ _ _).max (c_measurable _ _ _ _ _ _ _ _)
  have hb := bank_measurable τ v hτ0 hτ A h0
  have hx := rate_measurable τ v A
  have hbest : Measurable (best019 τ v A S a b K) :=
    (Real.measurable_exp.comp hb.neg).mul (hm.comp hx)
  have hc := (LateAmericanExerciseProof.completion_law v).integral_comp hbest.aestronglyMeasurable
  refine hc.trans ?_
  exact discounted_before_integral τ v hτ0 hτ A hA hAT _ hm.aestronglyMeasurable

lemma value_formula {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic (N+1))) (hJ : 0 < J)
    (u : Fin (J+1) → ℝ) (hu : StrictMono u) (A S K : ℝ)
    (hA : τ N ≤ A) (hAT : A < τ (N+1)) (hTS : τ (N+1) < S) :
    U0193 τ v A S u K =
      ∫ x, max (p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) (u 0) (u (Fin.last J)) K x)
        (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K x)
        ∂gaussianReal 0 (∑ i : Fin N, v i.castSucc) := by
  rw [value_attained τ v hτ0 hτ hJ u hu A S K hA hAT hTS]
  exact best_integral τ v hτ0 hτ A S _ _ K hA hAT

end Model

lemma valuation : valuationStatement := by
  intro N J τ v hτ0 hτ hJ u hu A S K hA hAT hTS hSa
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  refine ⟨waiting_condExp τ v hτ0 hτ A S (u 0) (u (Fin.last J)) K hA hAT hTS.le hab, ?_, ?_,
    value_formula τ v hτ0 hτ hJ u hu A S K hA hAT hTS⟩
  · intro σ hσ
    have h := admissible_bound τ v hτ0 hτ A S (u 0) (u (Fin.last J)) K hA hAT hTS.le hab σ hσ
    exact ⟨h.1, h.2.trans_eq (value_attained τ v hτ0 hτ hJ u hu A S K hA hAT hTS).symm⟩
  · refine ⟨fun ω => τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K
      (r τ v A) (r τ v (τ (N+1))) ω,
      ⟨fun ω => rule_mem _ _ _ _ _ _ _ K _ _ hAT hTS.le ω,
        rule_stopping (completedFilt τ v) _ _ _ _ _ _ _ K _ _ (q_nonneg v) hAT hTS.le hab
          (model_rate_completed_measurable τ v A) (model_rate_completed_measurable τ v (τ (N+1)))⟩,
      fun _ => rfl, ?_⟩
    rw [value_attained τ v hτ0 hτ hJ u hu A S K hA hAT hTS]
    exact rule_value τ v hτ0 hτ A S (u 0) (u (Fin.last J)) K hA hAT hTS.le hab

lemma example_pair : exampleStatement := by
  intro ε hε
  have hτ : StrictMonoOn (fun n : ℕ => (n : ℝ)) (Iic 4) := fun _ _ _ _ h => Nat.cast_lt.mpr h
  have hq : VMinus019 (v0198 ε) = VMinus019 (v0198' ε) := by
    simp [VMinus019, Fin.sum_univ_succ, v0198, v0198']
    ring
  have hw : v0198 ε (Fin.last 3) = v0198' ε (Fin.last 3) := by simp [v0198, v0198']
  have hV : V (v0198 ε) = V (v0198' ε) := by
    simp [V, Fin.sum_univ_succ, v0198, v0198']
    ring
  have hH : H (fun n : ℕ => (n : ℝ)) (v0198 ε) = H (fun n : ℕ => (n : ℝ)) (v0198' ε) := by
    simp [H, Fin.sum_univ_succ, v0198, v0198']
    ring
  have hsum : (∑ i : Fin 3, v0198 ε i.castSucc) = ∑ i : Fin 3, v0198' ε i.castSucc := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, VMinus019] using hq
  refine ⟨?_, ?_, hw, fun v U ω => CompoundedFuturesIdentificationProof.initial_bonds _ v
    (by norm_num) hτ U ω, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v0198, v0198', hε]
  · intro h
    have h0 := congrFun h 0
    simp only [v0198, v0198', Matrix.cons_val_zero] at h0
    have h1 := congrArg (fun x : NNReal => (x : ℝ)) h0
    push_cast at h1
    linarith [NNReal.coe_pos.mpr hε]
  · intro v i
    refine ⟨?_, fun t ht => LateAmericanExerciseProof.event_completed_variance _ v hτ i t ht⟩
    have he : Δr (fun n : ℕ => (n : ℝ)) v i = fun ω => ω i :=
      funext (CompoundedFuturesIdentificationProof.event_jump _ v hτ i)
    rw [he]
    exact D3EventVariancesProof.variance_coord i
  · intro J hJ u hu ha
    have hT : ∀ i : Fin 4, ((i.val+1 : ℕ) : ℝ) ≤ u 0 := by
      intro i
      have hi : ((i.val+1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i.val+1 ≤ 4 by omega)
      exact hi.trans ha
    have h1 : (Qc (v0198 ε))[fun ω : Ωc (v0198 ε) => R0192 (fun n : ℕ => (n : ℝ)) (v0198 ε) u ω |
        completedFilt (fun n : ℕ => (n : ℝ)) (v0198 ε) 0] =ᵐ[Qc (v0198 ε)]
        fun _ => (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V (v0198 ε)-
          H (fun n : ℕ => (n : ℝ)) (v0198 ε)))-1)/(u (Fin.last J)-u 0) :=
      LateAmericanExerciseProof.initial_condExp _ _ (by norm_num) hτ hJ u hu (by linarith) hT
    have h2 : (Qc (v0198' ε))[fun ω : Ωc (v0198' ε) => R0192 (fun n : ℕ => (n : ℝ)) (v0198' ε) u ω |
        completedFilt (fun n : ℕ => (n : ℝ)) (v0198' ε) 0] =ᵐ[Qc (v0198' ε)]
        fun _ => (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V (v0198' ε)-
          H (fun n : ℕ => (n : ℝ)) (v0198' ε)))-1)/(u (Fin.last J)-u 0) :=
      LateAmericanExerciseProof.initial_condExp _ _ (by norm_num) hτ hJ u hu (by linarith) hT
    rw [← hV, ← hH] at h2
    exact ⟨_, h1, h2⟩
  · intro J hJ u hu A S K hA hA4 h4S hSa
    rw [value_formula _ (v0198 ε) (by norm_num) hτ hJ u hu A S K (by simpa using hA)
        (by simpa using hA4) (by simpa using h4S),
      value_formula _ (v0198' ε) (by norm_num) hτ hJ u hu A S K (by simpa using hA)
        (by simpa using hA4) (by simpa using h4S), hq, hw, hsum]

theorem crossMeetingAmerican : Standalone.CrossMeetingAmerican.statement := by
  refine ⟨?_, ?_, ?_, ?_, valuation, example_pair⟩
  · intro q d hq hd
    exact ⟨u_measurable q d, D_measurable q d, fun z =>
      ⟨u_mem q d z hd, discount_max q d z hq hd, (discount_bounds q d z hq hd).1,
        (discount_bounds q d z hq hd).2⟩⟩
  · intro q w A T S a b K hq hAT hTS hab
    exact ⟨p_measurable q w A T a b K, c_measurable q w A T S a b K, fun x =>
      ⟨shifted_cash_integrable q w A T S a b K x hq hTS hab,
        averaged_future q w A T a b x, endpoint_bound q w A T S a b K x hq hTS hab,
        early_strict q w A T S a b K x hq hAT hTS hab⟩⟩
  · intro Ω mΩ F q w A T S a b K x y hq hAT hTS hab hx hy
    exact ⟨rule_mem q w A T S a b K x y hAT hTS,
      rule_stopping F q w A T S a b K x y hq hAT hTS hab hx hy,
      fun τ hτ hA hF => before_measurable F A T τ hτ hA hF⟩

  · exact model_specialization

end Novel.CrossMeetingAmericanProof

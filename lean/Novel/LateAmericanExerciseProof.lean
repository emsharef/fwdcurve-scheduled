import Standalone.LateAmericanExercise
import Novel.CompoundedFuturesIdentificationProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open Standalone.LateAmericanExercise
namespace Novel.LateAmericanExerciseProof
set_option maxHeartbeats 800000
variable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)

lemma r_after (A t : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (ht : A ≤ t) (ω : Ω N) :
    r τ v t ω = r τ v A ω+V v*(t-A) := by
  simp only [r, ite_eq_left (hA _), ite_eq_left ((hA _).trans ht), V, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma r_after_sum (A : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (ω : Ω N) :
    r τ v A ω = (∑ i, ω i)+A*V v-H τ v := by
  simp only [r, ite_eq_left (hA _), V, H, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma late_integral (A a b : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A)
    (hAa : A ≤ a) (hab : a ≤ b) (ω : Ω N) :
    (∫ s in a..b, r τ v s ω) = (b-a)*r τ v A ω+(b-a)*V v*((a+b)/2-A) := by
  have he : (∫ s in a..b, r τ v s ω) = ∫ s in a..b, r τ v A ω+V v*(s-A) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact r_after τ v A s hA (hAa.trans ((uIcc_of_le hab ▸ hs).1)) ω
  have hid : IntervalIntegrable (fun s : ℝ => s) volume a b := continuous_id.intervalIntegrable a b
  have hlin : IntervalIntegrable (fun s : ℝ => V v*(s-A)) volume a b :=
    ((show Continuous (fun s : ℝ => V v*(s-A)) by fun_prop).intervalIntegrable a b)
  rw [he, intervalIntegral.integral_add intervalIntegrable_const hlin,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hid intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

lemma bank_after (A t : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (ht : A ≤ t) (ω : Ω N) :
    logB τ v t ω = logB τ v A ω+r τ v A ω*(t-A)+V v*(t-A)^2/2 := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (CompoundedFuturesIdentificationProof.rate_integrable τ v 0 A ω)
    (CompoundedFuturesIdentificationProof.rate_integrable τ v A t ω)
  change logB τ v A ω+(∫ s in A..t, r τ v s ω) = logB τ v t ω at he
  rw [late_integral τ v A A t hA le_rfl ht ω] at he
  rw [← he]
  ring

lemma bond_after (a b : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ a) (hab : a ≤ b) (ω : Ω N) :
    (P τ v a b ω)⁻¹ = Real.exp (∫ s in a..b, r τ v s ω) := by
  have he : (∫ s in a..b, f τ v a s ω) = ∫ s in a..b, r τ v s ω := by
    apply intervalIntegral.integral_congr
    intro s hs
    have has : a ≤ s := (uIcc_of_le hab ▸ hs).1
    simp [f, r, hA, fun i => (hA i).trans has]
  simp [P, he, ← Real.exp_neg]

lemma u0186_mem (V L x : ℝ) (hL : 0 ≤ L) : u0186 V L x ∈ Icc 0 L :=
  ⟨le_min hL (le_max_left _ _), min_le_left _ _⟩

lemma quadratic_min (V L x : ℝ) (hV : 0 < V) (hL : 0 ≤ L) (u : ℝ) (hu : u ∈ Icc 0 L) :
    x*u0186 V L x+V*(u0186 V L x)^2/2 ≤ x*u+V*u^2/2 := by
  unfold u0186
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

lemma discount_max (V L x : ℝ) (hV : 0 < V) (hL : 0 ≤ L) (u : ℝ) (hu : u ∈ Icc 0 L) :
    Real.exp (-x*u-V*u^2/2) ≤ D0187 V L x := by
  apply Real.exp_le_exp.2
  have := quadratic_min V L x hV hL u hu
  linarith

lemma discount_cases (V L x : ℝ) (hV : 0 < V) (hL : 0 ≤ L) :
    D0187 V L x = if 0 ≤ x then 1 else if x ≤ -V*L then
      Real.exp (-x*L-V*L^2/2) else Real.exp (x^2/(2*V)) := by
  unfold D0187 u0186
  split_ifs with hx hxL
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hx) hV.le), min_eq_right hL]
    simp
  · have hx' : 0 ≤ -x/V := div_nonneg (neg_nonneg.2 (not_le.1 hx).le) hV.le
    have hLV : L ≤ -x/V := (le_div_iff₀ hV).2 (by nlinarith)
    rw [max_eq_right hx', min_eq_left hLV]
  · have hx' : 0 ≤ -x/V := div_nonneg (neg_nonneg.2 (not_le.1 hx).le) hV.le
    have hVL : -x/V ≤ L := (div_le_iff₀ hV).2 (by linarith)
    rw [max_eq_right hx', min_eq_right hVL]
    congr 1
    field_simp
    ring

lemma discount_bound (V L x : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L) :
    D0187 V L x ≤ Real.exp (L*|x|) := by
  apply Real.exp_le_exp.2
  have hu := u0186_mem V L x hL
  have h1 := mul_le_mul_of_nonneg_right (neg_le_abs x) hu.1
  have h2 := mul_le_mul_of_nonneg_left hu.2 (abs_nonneg x)
  have h3 := mul_nonneg hV (sq_nonneg (u0186 V L x))
  nlinarith

lemma discount_zero (V x : ℝ) : D0187 V 0 x = 1 := by
  simp [D0187, u0186]


lemma factor_eq {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) (j : Fin J) (ω : Ω N) :
    1+(u j.succ-u j.castSucc)*L0182 τ v u j ω =
      Real.exp (∫ s in u j.castSucc..u j.succ, r τ v s ω) := by
  have hj : u j.castSucc < u j.succ := hu (by simp)
  have h0 : u 0 ≤ u j.castSucc := hu.monotone (Fin.zero_le _)
  rw [← bond_after τ v _ _ (fun i => (hT i).trans h0) hj.le ω]
  unfold L0182
  field_simp [(sub_pos.mpr hj).ne']
  ring

lemma compound_eq {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) (ω : Ω N) :
    (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0182 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) := by
  simp_rw [factor_eq τ v u hu hT]
  rw [← Real.exp_sum]
  congr 1
  have he (j : Fin J) : (∫ s in u j.castSucc..u j.succ, r τ v s ω) =
      logB τ v (u j.succ) ω-logB τ v (u j.castSucc) ω := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (CompoundedFuturesIdentificationProof.rate_integrable τ v 0 (u j.castSucc) ω)
      (CompoundedFuturesIdentificationProof.rate_integrable τ v (u j.castSucc) (u j.succ) ω)
    change logB τ v (u j.castSucc) ω+(∫ s in u j.castSucc..u j.succ, r τ v s ω) = logB τ v (u j.succ) ω at h
    linarith
  simp_rw [he]
  have hsum : (∑ j : Fin J, (logB τ v (u j.succ) ω-logB τ v (u j.castSucc) ω)) =
      logB τ v (u (Fin.last J)) ω-logB τ v (u 0) ω := by
    have h := Fin.sum_univ_succ (fun j : Fin (J+1) => logB τ v (u j) ω)
    have h' := Fin.sum_univ_castSucc (fun j : Fin (J+1) => logB τ v (u j) ω)
    rw [Finset.sum_sub_distrib]
    linarith
  rw [hsum]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (CompoundedFuturesIdentificationProof.rate_integrable τ v 0 (u 0) ω)
    (CompoundedFuturesIdentificationProof.rate_integrable τ v (u 0) (u (Fin.last J)) ω)
  change logB τ v (u 0) ω+(∫ s in u 0..u (Fin.last J), r τ v s ω) = logB τ v (u (Fin.last J)) ω at h
  linarith

lemma rate_formula {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A : ℝ) (hT : ∀ i : Fin N, τ (i.val+1) ≤ A) (hA : A ≤ u 0) (ω : Ω N) :
    R0182 τ v u ω = (Real.exp ((u (Fin.last J)-u 0)*r τ v A ω+
      (u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A))-1)/(u (Fin.last J)-u 0) := by
  rw [R0182, compound_eq τ v u hu (fun i => (hT i).trans hA),
    late_integral τ v A _ _ hT hA (hu.monotone (Fin.zero_le _))]

lemma rate_measurable (A : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    Measurable[filt τ A] (r τ v A) := by
  have hc (i : Fin N) : Measurable[filt τ A] (fun ω : Ω N => ω i) := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup_of_le (hA i) le_rfl)
  have he : r τ v A = fun ω => ∑ i : Fin N, (ω i+(v i : ℝ)*(A-τ (i.val+1))) := by
    funext ω
    simp [r, hA]
  rw [he]
  exact Finset.measurable_sum _ (fun i _ => (hc i).add measurable_const)

lemma rate_completed_measurable (A : ℝ) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    Measurable[completedFilt τ v A] (fun ω : Ωc v => r τ v A ω) := by
  intro s hs
  exact ⟨_, (rate_measurable τ v A hA) hs, EventuallyEq.refl _ _⟩

lemma exercise_mem (A S : ℝ) (hAS : A ≤ S) (ω : Ω N) : τ0186 τ v A S ω ∈ Icc A S := by
  have h := u0186_mem (V v) (S-A) (r τ v A ω) (sub_nonneg.2 hAS)
  dsimp [τ0186]
  constructor <;> linarith [h.1, h.2]

lemma exercise_stopping (A S : ℝ) (hAS : A ≤ S) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    IsStoppingTime (completedFilt τ v) (fun ω : Ωc v => (τ0186 τ v A S ω : WithTop ℝ)) := by
  have hm : Measurable[completedFilt τ v A] (fun ω : Ωc v => τ0186 τ v A S ω) := by
    have hx := rate_completed_measurable τ v A hA
    unfold τ0186 u0186
    fun_prop
  intro t
  simp only [WithTop.coe_le_coe]
  by_cases ht : A ≤ t
  · exact (completedFilt τ v).mono ht _ (measurableSet_le hm measurable_const)
  · have he : {ω : Ωc v | τ0186 τ v A S ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le.2 ((not_le.1 ht).trans_le (exercise_mem τ v A S hAS ω).1)
    rw [he]
    exact @MeasurableSet.empty _ (completedFilt τ v t)

lemma exercise_payoff (hV : 0 < V v) (A S : ℝ) (hAS : A ≤ S)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (t : ℝ) (ht : t ∈ Icc A S) (p : ℝ) (hp : 0 ≤ p) (ω : Ω N) :
    Real.exp (-logB τ v t ω)*p ≤ Real.exp (-logB τ v A ω)*p*D0187 (V v) (S-A) (r τ v A ω) := by
  have he : Real.exp (-logB τ v t ω) = Real.exp (-logB τ v A ω)*
      Real.exp (-r τ v A ω*(t-A)-V v*(t-A)^2/2) := by
    rw [← Real.exp_add, bank_after τ v A t hA ht.1 ω]
    congr 1
    ring
  rw [he, mul_assoc, mul_comm (Real.exp _) p, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (discount_max (V v) (S-A) (r τ v A ω) hV (sub_nonneg.2 hAS) (t-A)
      ⟨sub_nonneg.2 ht.1, sub_le_sub_right ht.2 A⟩) (mul_nonneg (Real.exp_pos _).le hp)

lemma exercise_attained (A S : ℝ) (hAS : A ≤ S)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (p : ℝ) (ω : Ω N) :
    Real.exp (-logB τ v (τ0186 τ v A S ω) ω)*p =
      Real.exp (-logB τ v A ω)*p*D0187 (V v) (S-A) (r τ v A ω) := by
  rw [bank_after τ v A _ hA (exercise_mem τ v A S hAS ω).1 ω]
  simp only [τ0186, add_sub_cancel_left, D0187]
  rw [mul_assoc, mul_comm p, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring


instance : IsProbabilityMeasure (Q v) := by unfold Q; infer_instance
instance : IsProbabilityMeasure (Qc v) := ⟨by change (Q v) univ = 1; exact measure_univ⟩

lemma completion_law : HasLaw (Ω := Ωc v) (𝓧 := Ω N) (m𝓧 := MeasurableSpace.pi)
    (fun ω : Ωc v => (ω : Ω N)) (Q v) (Qc v) :=
  CompoundedFuturesIdentificationProof.completion_law v

lemma compound_rate_integrable {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u) (h0 : 0 ≤ u 0)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) : Integrable (R0182 τ v u) (Q v) := by
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have he : R0182 τ v u = fun ω =>
      (Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)-1)/(u (Fin.last J)-u 0) := by
    funext ω
    rw [R0182, compound_eq τ v u hu hT]
  rw [he]
  exact ((CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab).sub
    (integrable_const 1)).div_const _

lemma compound_rate_completed_integrable {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u) (h0 : 0 ≤ u 0)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) :
    Integrable (fun ω : Ωc v => R0182 τ v u ω) (Qc v) := by
  have hi := compound_rate_integrable τ v hτ0 hτ hJ u hu h0 hT
  exact (completion_law v).integrable_comp hi

lemma compound_rate_measurable {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A : ℝ) (hT : ∀ i : Fin N, τ (i.val+1) ≤ A) (hA : A ≤ u 0) :
    Measurable[completedFilt τ v A] (fun ω : Ωc v => R0182 τ v u ω) := by
  have he : (fun ω : Ωc v => R0182 τ v u ω) = fun ω : Ωc v =>
      (Real.exp ((u (Fin.last J)-u 0)*r τ v A ω+
      (u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A))-1)/(u (Fin.last J)-u 0) :=
    funext (rate_formula τ v u hu A hT hA)
  rw [he]
  have hx := rate_completed_measurable τ v A hT
  fun_prop

lemma compound_initial {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u) (h0 : 0 ≤ u 0)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) :
    (∫ ω : Ωc v, R0182 τ v u ω ∂Qc v) =
      (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v))-1)/(u (Fin.last J)-u 0) := by
  have hi := compound_rate_integrable τ v hτ0 hτ hJ u hu h0 hT
  have hec : (∫ ω : Ωc v, R0182 τ v u ω ∂Qc v) = ∫ ω, R0182 τ v u ω ∂Q v :=
    (completion_law v).integral_comp hi.aestronglyMeasurable
  rw [hec]
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have he : R0182 τ v u = fun ω =>
      (Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)-1)/(u (Fin.last J)-u 0) := by
    funext ω
    rw [R0182, compound_eq τ v u hu hT]
  have hexp : Integrable (fun ω : Ω N => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) (Q v) :=
    CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab
  rw [he, integral_div, integral_sub hexp (integrable_const 1)]
  simp only [integral_const, probReal_univ, one_smul]
  have hg := integral_congr_ae (CompoundedFuturesIdentificationProof.futures_condExp τ v hτ0 hτ _ _ h0 hab 0)
  rw [integral_condExp ((Standalone.CompoundedFuturesIdentification.filt τ).le 0)] at hg
  simp_rw [CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ,
    CompoundedFuturesIdentificationProof.p_after τ v _ _ hT hab.le] at hg
  simp only [integral_const, probReal_univ, one_smul] at hg
  have hg' : (∫ ω : Ω N, Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) ∂Q v) =
      Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v)) := hg
  rw [hg']

lemma discounted_rate_law (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (A : ℝ) (h0 : 0 ≤ A) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    HasLaw (r τ v A) (gaussianReal 0 (∑ i, v i)) (Q0188 τ v A) := by
  change HasLaw _ _ (Standalone.CompoundedFuturesIdentification.QS τ v A)
  rw [CompoundedFuturesIdentificationProof.QS_eq τ v hτ0 hτ A h0]
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v)
    (BondOptionMeetingVariancesProof.a0148 τ A) (fun _ => 1) (A*V v-H τ v)
  have hm : A*V v-H τ v + ∑ i, (1 : ℝ)*(v i : ℝ)*
      BondOptionMeetingVariancesProof.a0148 τ A i = 0 := by
    simp only [BondOptionMeetingVariancesProof.a0148, Standalone.D3EventVariances.past,
      Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left (hA _), one_mul,
      V, H, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    have he (i : Fin N) : A*(v i : ℝ)-τ (i.val+1)*(v i : ℝ)+(v i : ℝ)*(-(A-τ (i.val+1))) = 0 := by ring
    simp_rw [he]
    simp
  rw [hm] at h
  simpa only [one_pow, Real.toNNReal_one, mul_one] using h.congr
    (Eventually.of_forall fun ω => by
      rw [r_after_sum τ v A hA]
      simp only [Standalone.BondOptionMeetingVariances.L0149, one_mul]
      ring)

lemma bank_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (A : ℝ) (h0 : 0 ≤ A) : Measurable (logB τ v A) := by
  have he : logB τ v A = Standalone.D3EventVariances.logB τ v A :=
    funext (CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ A h0)
  rw [he]
  unfold Standalone.D3EventVariances.logB
  fun_prop

lemma discounted_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (A : ℝ) (h0 : 0 ≤ A) (hA : ∀ i : Fin N, τ (i.val+1) ≤ A)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (gaussianReal 0 (∑ i, v i))) :
    (∫ ω, Real.exp (-logB τ v A ω)*g (r τ v A ω) ∂Q v) =
      ∫ x, g x ∂gaussianReal 0 (∑ i, v i) := by
  have h := (discounted_rate_law τ v hτ0 hτ A h0 hA).integral_comp hg
  rw [Q0188, integral_withDensity_eq_integral_toReal_smul
    (by have hm := bank_measurable τ v hτ0 hτ A h0; fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, Function.comp_apply] using h

lemma p0188_integrable (W : NNReal) (L δ c K : ℝ) (hL : 0 ≤ L) (hδ : 0 < δ) :
    Integrable (p0188 W L δ c K) (gaussianReal 0 W) := by
  have h1 := integrable_exp_mul_abs_add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := W) (δ+L))
    (integrable_exp_mul_gaussianReal (μ := 0) (v := W) (δ-L))
  have h2 := integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (μ := 0) (v := W) L)
    (integrable_exp_mul_gaussianReal (μ := 0) (v := W) (-L))
  apply ((h1.const_mul (Real.exp c/δ)).add (h2.const_mul (1/δ+|K|))).mono'
    (by unfold p0188 D0187 u0186; fun_prop)
  filter_upwards [] with x
  have hp : max ((Real.exp (δ*x+c)-1)/δ-K) 0 ≤ Real.exp (δ*x+c)/δ+(1/δ+|K|) := by
    apply max_le
    · have hk := neg_le_abs K
      have hδ' : 0 ≤ 1/δ := by positivity
      rw [sub_div]
      linarith
    · positivity
  have hD := discount_bound (W : ℝ) L x W.coe_nonneg hL
  have hb := mul_le_mul hp hD (Real.exp_pos _).le (by positivity : 0 ≤ Real.exp (δ*x+c)/δ+(1/δ+|K|))
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold p0188 D0187; positivity)]
  refine hb.trans_eq ?_
  simp only [Real.exp_add, Pi.add_apply]
  ring

lemma optimized_integrable {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    Integrable (fun ω : Ωc v => Real.exp (-logB τ v A ω)*
      max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω)) (Qc v) := by
  have hδ : 0 < u (Fin.last J)-u 0 := sub_pos.mpr (hu (by change (0 : ℕ) < J; exact hJ))
  let g := p0188 (V v) (S-A) (u (Fin.last J)-u 0)
    ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K
  have hg : Integrable g (gaussianReal 0 (∑ i, v i)) := by
    simpa only [NNReal.coe_sum, g, V] using p0188_integrable (∑ i, v i) (S-A) _ _ K (sub_nonneg.mpr hAS) hδ
  have hi := (discounted_rate_law τ v hτ0 hτ A h0 hA).integrable_comp hg
  rw [Q0188] at hi
  have hd : Measurable (fun ω => ENNReal.ofReal (Real.exp (-logB τ v A ω))) := by
    have hm := bank_measurable τ v hτ0 hτ A h0
    fun_prop
  have hi' := (integrable_withDensity_iff_integrable_smul' hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, Function.comp_apply] at hi'
  have he : (fun ω : Ω N => Real.exp (-logB τ v A ω)*
      max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω)) =
      fun ω => Real.exp (-logB τ v A ω)*g (r τ v A ω) := by
    funext ω
    rw [rate_formula τ v u hu A hA (hAS.trans hSa)]
    exact mul_assoc _ _ _
  rw [← he] at hi'
  exact (completion_law v).integrable_comp hi'

lemma admissible_measurable (A S : ℝ) (σ : Ωc v → ℝ) (hσ : σ ∈ T0183 τ v A S) :
    Measurable σ := by
  have h := hσ.2.measurable_of_le (fun ω =>
    show (σ ω : WithTop ℝ) ≤ S from WithTop.coe_le_coe.mpr (hσ.1 ω).2)
  have h' := h.untopA.mono ((completedFilt τ v).le S) le_rfl
  simpa using h'

lemma exercise_integrable {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (hV : 0 < V v)
    (σ : Ωc v → ℝ) (hσ : σ ∈ T0183 τ v A S) :
    Integrable (fun ω : Ωc v => Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0) (Qc v) := by
  have hi := optimized_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA
  have hb : Measurable (fun ω : Ωc v => logB τ v A ω) :=
    (bank_measurable τ v hτ0 hτ A h0).comp
      (show @Measurable (Ωc v) (Ω N) inferInstance MeasurableSpace.pi (fun ω => ω) by
        intro E hE; exact ⟨E, hE, EventuallyEq.refl _ _⟩)
  have hx := (rate_completed_measurable τ v A hA).mono ((completedFilt τ v).le A) le_rfl
  have hr := (compound_rate_measurable τ v u hu A hA (hAS.trans hSa)).mono
    ((completedFilt τ v).le A) le_rfl
  have hs := admissible_measurable τ v A S σ hσ
  have he : (fun ω : Ωc v => logB τ v (σ ω) ω) =
      fun ω => logB τ v A ω+r τ v A ω*(σ ω-A)+V v*(σ ω-A)^2/2 :=
    funext (fun ω => bank_after τ v A (σ ω) hA (hσ.1 ω).1 ω)
  have hbm : Measurable (fun ω : Ωc v => logB τ v (σ ω) ω) := by rw [he]; fun_prop
  apply hi.mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact exercise_payoff τ v hV A S hAS hA (σ ω) (hσ.1 ω) _ (le_max_right _ _) ω

lemma optimized_value {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (_hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    (∫ ω : Ωc v, Real.exp (-logB τ v A ω)*
      max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω) ∂Qc v) =
      ∫ x, p0188 (V v) (S-A) (u (Fin.last J)-u 0)
        ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K x ∂gaussianReal 0 (∑ i, v i) := by
  let g := p0188 (V v) (S-A) (u (Fin.last J)-u 0)
    ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K
  have hm : Measurable g := by unfold g p0188 D0187 u0186; fun_prop
  have he : (fun ω : Ω N => Real.exp (-logB τ v A ω)*
      max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω)) =
      fun ω => Real.exp (-logB τ v A ω)*g (r τ v A ω) := by
    funext ω
    rw [rate_formula τ v u hu A hA (hAS.trans hSa)]
    exact mul_assoc _ _ _
  have hx := (rate_measurable τ v A hA).mono ((filt τ).le A) le_rfl
  have hb := bank_measurable τ v hτ0 hτ A h0
  have hc := (completion_law v).integral_comp
    (show AEStronglyMeasurable (fun ω : Ω N => Real.exp (-logB τ v A ω)*g (r τ v A ω)) (Q v) by fun_prop)
  rw [← he] at hc
  refine hc.trans ?_
  rw [he]
  exact discounted_integral τ v hτ0 hτ A h0 hA g hm.aestronglyMeasurable

lemma value_attained {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (hV : 0 < V v) :
    U0183 τ v A S u K = ∫ ω : Ωc v, Real.exp (-logB τ v A ω)*
      max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω) ∂Qc v := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun ω => τ0186 τ v A S ω,
      ⟨exercise_mem τ v A S hAS, exercise_stopping τ v A S hAS hA⟩, ?_⟩
    exact integral_congr_ae (Eventually.of_forall fun ω => exercise_attained τ v A S hAS hA _ ω)
  · rintro y ⟨σ, hσ, rfl⟩
    exact integral_mono (exercise_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA hV σ hσ)
      (optimized_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA)
      (fun ω => exercise_payoff τ v hV A S hAS hA (σ ω) (hσ.1 ω) _ (le_max_right _ _) ω)

lemma zero_coordinates (hV : V v = 0) : ∀ i, v i = 0 := by
  intro i
  apply NNReal.coe_injective
  have hi : (v i : ℝ) ≤ V v := Finset.single_le_sum (fun j _ => (v j).coe_nonneg) (Finset.mem_univ i)
  simpa using le_antisymm (hV ▸ hi) (v i).coe_nonneg

lemma zero_model_ae (hV : V v = 0) : ∀ᵐ ω : Ωc v ∂Qc v, ∀ i, ω i = 0 := by
  have h := completion_law v
  have he : Q v = Measure.dirac (fun _ : Fin N => (0 : ℝ)) := by
    simp [Q, zero_coordinates v hV, gaussianReal_zero_var]
  have h' : HasLaw (m𝓧 := MeasurableSpace.pi) (fun ω : Ωc v => (show Ω N from ω))
      (Measure.dirac (fun _ : Fin N => (0 : ℝ))) (Qc v) :=
    ⟨h.aemeasurable, h.map_eq.trans he⟩
  filter_upwards [h'.ae_eq_of_dirac] with ω hω
  exact fun i => congrFun hω i

lemma zero_payoff {J : ℕ} (hV : V v = 0) (u : Fin (J+1) → ℝ) (K : ℝ) (σ : Ωc v → ℝ) :
    (fun ω : Ωc v => Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0) =ᵐ[Qc v]
      fun _ => max (-K) 0 := by
  filter_upwards [zero_model_ae v hV] with ω hω
  have hr (t : ℝ) : r τ v t ω = 0 := by simp [r, hω, zero_coordinates v hV]
  have hf (t U : ℝ) : f τ v t U ω = 0 := by simp [f, hω, zero_coordinates v hV]
  have hb (t : ℝ) : logB τ v t ω = 0 := by simp [logB, hr]
  have hp (t U : ℝ) : P τ v t U ω = 1 := by simp [P, hf]
  have hR : R0182 τ v u ω = 0 := by simp [R0182, L0182, hp]
  rw [hb, hR]
  simp

lemma zero_value {J : ℕ} (hV : V v = 0) (A S : ℝ) (hAS : A ≤ S)
    (u : Fin (J+1) → ℝ) (K : ℝ) : U0183 τ v A S u K = max (-K) 0 := by
  have he (σ : Ωc v → ℝ) :
      (∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) = max (-K) 0 := by
    rw [integral_congr_ae (zero_payoff τ v hV u K σ)]
    simp
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨fun _ => A, ⟨fun _ => ⟨le_rfl, hAS⟩, isStoppingTime_const _ A⟩, he _⟩
  · rintro y ⟨σ, _, rfl⟩
    exact (he σ).le

lemma value_formula {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    U0183 τ v A S u K = ∫ x, p0188 (V v) (S-A) (u (Fin.last J)-u 0)
      ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K x ∂gaussianReal 0 (∑ i, v i) := by
  have hV : 0 ≤ V v := Finset.sum_nonneg (fun i _ => (v i).coe_nonneg)
  rcases hV.eq_or_lt with hV | hV
  · rw [zero_value τ v hV.symm A S hAS u K]
    have hv : (∑ i, v i) = 0 := by simp [zero_coordinates v hV.symm]
    simp [hv, ← hV, p0188, D0187]
  · rw [value_attained τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA hV]
    exact optimized_value τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA

lemma gaussian_strict (W : NNReal) (hW : 0 < W) (L δ c K : ℝ) (hL : 0 < L) (hδ : 0 < δ) :
    (∫ x, max ((Real.exp (δ*x+c)-1)/δ-K) 0 * Real.exp (-x*L-(W : ℝ)*L^2/2) ∂gaussianReal 0 W) <
      ∫ x, p0188 W L δ c K x ∂gaussianReal 0 W := by
  let f := fun x => max ((Real.exp (δ*x+c)-1)/δ-K) 0 * Real.exp (-x*L-(W : ℝ)*L^2/2)
  have hi := p0188_integrable W L δ c K hL.le hδ
  have hle (x : ℝ) : f x ≤ p0188 W L δ c K x :=
    mul_le_mul_of_nonneg_left (discount_max W L x hW hL.le L ⟨hL.le, le_rfl⟩) (le_max_right _ _)
  have hf : Integrable f (gaussianReal 0 W) := hi.mono' (by unfold f; fun_prop)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]; exact hle x)
  apply lt_of_le_of_ne (integral_mono hf hi hle)
  intro he
  have hae := (integral_eq_iff_of_ae_le hf hi (Eventually.of_forall hle)).mp he
  have hv := (gaussianReal_absolutelyContinuous' 0 hW.ne').ae_le hae
  let M := max 0 ((δ*K-c)/δ)
  have hs (x : ℝ) (hx : M < x) : f x < p0188 W L δ c K x := by
    have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
    have hxc : δ*K < δ*x+c := by
      have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hx)
      nlinarith
    have hpay : 0 < (Real.exp (δ*x+c)-1)/δ-K := by
      have hex := Real.add_one_le_exp (δ*x+c)
      apply sub_pos.mpr
      apply (lt_div_iff₀ hδ).mpr
      nlinarith
    have hd : Real.exp (-x*L-(W : ℝ)*L^2/2) < 1 := by
      rw [← Real.exp_zero, Real.exp_lt_exp]
      nlinarith [mul_pos hx0 hL, mul_nonneg W.coe_nonneg (sq_nonneg L)]
    have hcase := discount_cases W L x hW hL.le
    rw [ite_eq_left hx0.le] at hcase
    dsimp [f, p0188]
    rw [hcase, mul_one]
    exact mul_lt_of_lt_one_right (lt_max_of_lt_left hpay) hd
  have hnull : volume (Ioi M) = 0 := by
    apply measure_mono_null (t := {x | f x ≠ p0188 W L δ c K x})
    · intro x hx
      exact (hs x hx).ne
    · exact ae_iff.mp hv
  simp at hnull

lemma mandatory_value {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) :
    (∫ ω : Ωc v, Real.exp (-logB τ v S ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) =
      ∫ x, max ((Real.exp ((u (Fin.last J)-u 0)*x+
        (u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A))-1)/(u (Fin.last J)-u 0)-K) 0 *
        Real.exp (-x*(S-A)-V v*(S-A)^2/2) ∂gaussianReal 0 (∑ i, v i) := by
  let g := fun x => max ((Real.exp ((u (Fin.last J)-u 0)*x+
        (u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A))-1)/(u (Fin.last J)-u 0)-K) 0 *
        Real.exp (-x*(S-A)-V v*(S-A)^2/2)
  have hm : Measurable g := by unfold g; fun_prop
  have he : (fun ω : Ω N => Real.exp (-logB τ v S ω)*max (R0182 τ v u ω-K) 0) =
      fun ω => Real.exp (-logB τ v A ω)*g (r τ v A ω) := by
    funext ω
    rw [rate_formula τ v u hu A hA (hAS.trans hSa), bank_after τ v A S hA hAS]
    dsimp [g]
    rw [show -(logB τ v A ω+r τ v A ω*(S-A)+V v*(S-A)^2/2) =
      -logB τ v A ω+(-r τ v A ω*(S-A)-V v*(S-A)^2/2) by ring, Real.exp_add]
    ring
  have hx := (rate_measurable τ v A hA).mono ((filt τ).le A) le_rfl
  have hb := bank_measurable τ v hτ0 hτ A h0
  have hc := (completion_law v).integral_comp
    (show AEStronglyMeasurable (fun ω : Ω N => Real.exp (-logB τ v A ω)*g (r τ v A ω)) (Q v) by fun_prop)
  rw [← he] at hc
  refine hc.trans ?_
  rw [he]
  exact discounted_integral τ v hτ0 hτ A h0 hA g hm.aestronglyMeasurable

lemma strict_premium {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (A S K : ℝ) (h0 : 0 ≤ A) (hAS : A < S) (hSa : S ≤ u 0)
    (hA : ∀ i : Fin N, τ (i.val+1) ≤ A) (hV : 0 < V v) :
    (∫ ω : Ωc v, Real.exp (-logB τ v S ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) < U0183 τ v A S u K := by
  have hm := mandatory_value τ v hτ0 hτ u hu A S K h0 hAS.le hSa hA
  have hv := value_formula τ v hτ0 hτ hJ u hu A S K h0 hAS.le hSa hA
  refine hm.trans_lt (lt_of_lt_of_eq ?_ hv.symm)
  have hW : 0 < ∑ i, v i := by
    apply NNReal.coe_pos.mp
    simpa only [NNReal.coe_sum, V] using hV
  simpa only [NNReal.coe_sum, V] using gaussian_strict (∑ i, v i) hW (S-A)
    (u (Fin.last J)-u 0) ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K
    (sub_pos.mpr hAS) (sub_pos.mpr (hu (by change (0 : ℕ) < J; exact hJ)))

lemma initial_condExp {J : ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (hJ : 0 < J) (u : Fin (J+1) → ℝ) (hu : StrictMono u) (h0 : 0 ≤ u 0)
    (hT : ∀ i : Fin N, τ (i.val+1) ≤ u 0) :
    (Qc v)[fun ω : Ωc v => R0182 τ v u ω | completedFilt τ v 0] =ᵐ[Qc v]
      fun _ => (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v))-1)/(u (Fin.last J)-u 0) := by
  let δ := u (Fin.last J)-u 0
  let f : Ωc v → ℝ := fun ω => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have hf : Integrable f (Qc v) := (completion_law v).integrable_comp
    (CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab)
  have hce := CompoundedFuturesIdentificationProof.futures_completed_condExp τ v hτ0 hτ _ _ h0 hab 0
  have hscaled := condExp_smul (μ := Qc v) δ⁻¹ (f-1) (completedFilt τ v 0)
  have hsub := condExp_sub hf (integrable_const 1) (completedFilt τ v 0)
  rw [condExp_const ((completedFilt τ v).le 0)] at hsub
  have he : (fun ω : Ωc v => R0182 τ v u ω) = δ⁻¹ • (f-1) := by
    funext ω
    have hh := compound_eq τ v u hu hT ω
    change (_-1)/δ = _
    rw [hh]
    simp [f, div_eq_mul_inv, mul_comm]
  have hfirst : (Qc v)[fun ω : Ωc v => R0182 τ v u ω | completedFilt τ v 0] =ᵐ[Qc v]
      (Qc v)[δ⁻¹ • (f-1) | completedFilt τ v 0] := condExp_congr_ae (EventuallyEq.of_eq he)
  refine hfirst.trans ?_
  filter_upwards [hscaled, hsub, hce] with ω hs hsub hce
  have hinit := CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ (u 0) (u (Fin.last J)) ω
  have hp := CompoundedFuturesIdentificationProof.p_after τ v _ _ hT hab.le
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hs hsub
  change (Qc v)[f | completedFilt τ v 0] ω = _ at hce
  change (Qc v)[f-1 | completedFilt τ v 0] ω = (Qc v)[f | completedFilt τ v 0] ω-1 at hsub
  rw [hs, hsub, hce, hinit, hp]
  simp only [δ, div_eq_mul_inv, V, H, mul_comm]

lemma completed_condExp_constant (t : ℝ) (f : Ω N → ℝ) (hf : Integrable f (Q v))
    (c : ℝ) (hce : (Q v)[f | filt τ t] =ᵐ[Q v] fun _ => c) :
    (Qc v)[fun ω : Ωc v => f ω | completedFilt τ v t] =ᵐ[Qc v] fun _ => c := by
  have hfc := (completion_law v).integrable_comp hf
  apply (ae_eq_condExp_of_forall_setIntegral_eq ((completedFilt τ v).le t) hfc
    (fun _ _ _ => (integrable_const c).integrableOn) _ stronglyMeasurable_const.aestronglyMeasurable).symm
  intro E hE _
  obtain ⟨E', hE', hae⟩ := hE
  have hae' : E =ᵐ[Qc v] E' := hae
  rw [Measure.restrict_congr_set hae']
  have h1 := CompoundedFuturesIdentificationProof.completion_setIntegral v (fun _ : Ω N => c)
    (integrable_const c) E' ((filt τ).le t E' hE')
  have h2 := CompoundedFuturesIdentificationProof.completion_setIntegral v f hf E' ((filt τ).le t E' hE')
  refine h1.trans (Eq.trans ?_ h2.symm)
  have h3 : (∫ ω : Ω N in E', c ∂Q v) = ∫ ω : Ω N in E', (Q v)[f | filt τ t] ω ∂Q v :=
    integral_congr_ae (ae_restrict_of_ae hce.symm)
  exact h3.trans (setIntegral_condExp ((filt τ).le t) hf hE')

lemma event_completed_variance (hτ : StrictMonoOn τ (Iic N)) (i : Fin N) (t : ℝ)
    (ht : t < τ (i.val+1)) :
    Var[fun ω : Ωc v => Δr τ v i ω; Qc v | completedFilt τ v t] =ᵐ[Qc v] fun _ => (v i : ℝ) := by
  let c := ∫ ω : Ω N, ω i ∂Q v
  have hm : (Q v)[fun ω : Ω N => ω i | filt τ t] =ᵐ[Q v] fun _ => c :=
    condExp_indep_eq (D3EventVariancesProof.coordAlg_le {i}) ((filt τ).le t)
      (D3EventVariancesProof.measurable_coord (mem_singleton i)).stronglyMeasurable
      (D3EventVariancesProof.indep_before i ht)
  have hs := condExp_indep_eq (μ := Q v) (f := fun ω : Ω N => (ω i-c)^2)
    (D3EventVariancesProof.coordAlg_le {i}) ((filt τ).le t)
    (((D3EventVariancesProof.measurable_coord (mem_singleton i)).sub measurable_const).pow_const 2).stronglyMeasurable
    (D3EventVariancesProof.indep_before i ht)
  have h2 : MemLp (fun ω : Ω N => ω i) 2 (Q v) :=
    (D3EventVariancesProof.law i).memLp (memLp_id_gaussianReal 2)
  have hmc := completed_condExp_constant τ v t _ (h2.integrable one_le_two) c hm
  have hsc := completed_condExp_constant τ v t _ ((h2.sub (memLp_const c)).integrable_sq) _ hs
  have hj : (fun ω : Ωc v => Δr τ v i ω) = fun ω => ω i :=
    funext (CompoundedFuturesIdentificationProof.event_jump τ v hτ i)
  have he : Var[fun ω : Ωc v => Δr τ v i ω; Qc v | completedFilt τ v t] =ᵐ[Qc v]
      (Qc v)[fun ω : Ωc v => (ω i-c)^2 | completedFilt τ v t] := by
    change (Qc v)[((fun ω : Ωc v => Δr τ v i ω)-(Qc v)[fun ω : Ωc v => Δr τ v i ω | completedFilt τ v t])^2 |
      completedFilt τ v t] =ᵐ[Qc v] _
    have hmj : (Qc v)[fun ω : Ωc v => Δr τ v i ω | completedFilt τ v t] =ᵐ[Qc v] fun _ => c := by
      exact (condExp_congr_ae (EventuallyEq.of_eq hj)).trans hmc
    apply condExp_congr_ae
    filter_upwards [hmj] with ω hω
    simp only [Pi.pow_apply, Pi.sub_apply, hω, congrFun hj ω]
  have hv := variance_eq_integral (D3EventVariancesProof.law (v := v) i).aemeasurable
  rw [D3EventVariancesProof.variance_coord] at hv
  exact he.trans (hsc.trans (Eventually.of_forall fun _ => hv.symm))

lemma valuation : valuationStatement := by
  intro N J τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA
  have hV : 0 ≤ V v := Finset.sum_nonneg (fun i _ => (v i).coe_nonneg)
  refine ⟨initial_condExp τ v hτ0 hτ hJ u hu (h0.trans (hAS.trans hSa))
    (fun i => (hA i).trans (hAS.trans hSa)),
    discounted_rate_law τ v hτ0 hτ A h0 hA, ?_, ?_, ?_,
    value_formula τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA,
    fun hv has => strict_premium τ v hτ0 hτ hJ u hu A S K h0 has hSa hA hv⟩
  · simpa using discounted_integral τ v hτ0 hτ A h0 hA (fun _ => 1) (by fun_prop)
  · intro σ hσ
    by_cases hv : V v = 0
    · have he := zero_payoff τ v hv u K σ
      refine ⟨(integrable_const _).congr he.symm, ?_⟩
      have hi := integral_congr_ae he
      simp only [integral_const, probReal_univ, one_smul] at hi
      exact hi.le.trans_eq (zero_value τ v hv A S hAS u K).symm
    · refine ⟨exercise_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA (lt_of_le_of_ne hV (Ne.symm hv)) σ hσ, ?_⟩
      have hv' : 0 < V v := lt_of_le_of_ne hV (Ne.symm hv)
      rw [value_attained τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA hv']
      exact integral_mono
        (exercise_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA hv' σ hσ)
        (optimized_integrable τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA)
        (fun ω => exercise_payoff τ v hv' A S hAS hA (σ ω) (hσ.1 ω) _ (le_max_right _ _) ω)
  · by_cases hv : V v = 0
    · refine ⟨fun _ => A, ⟨fun _ => ⟨le_rfl, hAS⟩, isStoppingTime_const _ A⟩,
        fun _ => by simp [hv], ?_⟩
      have hi := integral_congr_ae (zero_payoff τ v hv u K (fun _ => A))
      simp only [integral_const, probReal_univ, one_smul] at hi
      exact hi.trans (zero_value τ v hv A S hAS u K).symm
    · refine ⟨fun ω => τ0186 τ v A S ω,
        ⟨exercise_mem τ v A S hAS, exercise_stopping τ v A S hAS hA⟩,
        fun _ => by simp [hv], ?_⟩
      have he := integral_congr_ae (μ := Qc v)
        (Eventually.of_forall fun ω => exercise_attained τ v A S hAS hA (max (R0182 τ v u ω-K) 0) ω)
      exact he.trans (value_attained τ v hτ0 hτ hJ u hu A S K h0 hAS hSa hA
        (lt_of_le_of_ne hV (Ne.symm hv))).symm

lemma zero_model : zeroStatement := by
  intro N J τ v hv
  refine ⟨zero_coordinates v hv, ?_, fun A S hAS u K => zero_value τ v hv A S hAS u K⟩
  filter_upwards [zero_model_ae v hv] with ω hω
  have hr (t : ℝ) : r τ v t ω = 0 := by simp [r, hω, zero_coordinates v hv]
  have hf (t U : ℝ) : f τ v t U ω = 0 := by simp [f, hω, zero_coordinates v hv]
  refine ⟨hω, fun t => ⟨hr t, by simp [logB, hr]⟩, ?_⟩
  intro u
  simp [R0182, L0182, P, hf]

lemma example_pair : exampleStatement := by
  intro ε hε
  have hτ : StrictMonoOn (fun n : ℕ => (n : ℝ)) (Iic 3) := fun _ _ _ _ h => Nat.cast_lt.mpr h
  have hm := CompoundedFuturesIdentificationProof.example_moments ε
  have hV : V (v0189 ε) = V (v0189' ε) := hm.1.1.trans hm.2.1.symm
  have hH : H (fun n : ℕ => (n : ℝ)) (v0189 ε) = H (fun n : ℕ => (n : ℝ)) (v0189' ε) :=
    hm.1.2.trans hm.2.2.symm
  have hsum : (∑ i, v0189 ε i) = ∑ i, v0189' ε i := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, V] using hV
  refine ⟨?_, CompoundedFuturesIdentificationProof.example_distinct ε hε,
    fun v U ω => CompoundedFuturesIdentificationProof.initial_bonds _ v (by norm_num) hτ U ω, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v0189, v0189', hε]
  · intro v i
    refine ⟨?_, fun t ht => event_completed_variance _ v hτ i t ht⟩
    have he : Δr (fun n : ℕ => (n : ℝ)) v i = fun ω => ω i :=
      funext (CompoundedFuturesIdentificationProof.event_jump _ v hτ i)
    rw [he]
    exact D3EventVariancesProof.variance_coord i
  · intro J hJ u hu ha
    have hT : ∀ i : Fin 3, ((i.val+1 : ℕ) : ℝ) ≤ u 0 := by
      intro i
      have hi : ((i.val+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show i.val+1 ≤ 3 by omega)
      exact hi.trans ha
    rw [compound_initial _ _ (by norm_num) hτ hJ u hu (by linarith) hT,
      compound_initial _ _ (by norm_num) hτ hJ u hu (by linarith) hT, hV, hH]
  · intro J hJ u hu A S K hA hAS hSa
    have hT : ∀ i : Fin 3, ((i.val+1 : ℕ) : ℝ) ≤ A := by
      intro i
      have hi : ((i.val+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show i.val+1 ≤ 3 by omega)
      exact hi.trans hA
    rw [value_formula _ _ (by norm_num) hτ hJ u hu A S K (by linarith) hAS hSa hT,
      value_formula _ _ (by norm_num) hτ hJ u hu A S K (by linarith) hAS hSa hT, hV, hsum]

theorem lateAmericanExercise : Standalone.LateAmericanExercise.statement := by
  refine ⟨?_, ?_, ?_, valuation, zero_model, example_pair⟩
  · intro N J τ v hτ0 hτ hJ u hu A h0 hT hA
    have hi := compound_rate_completed_integrable τ v hτ0 hτ hJ u hu (h0.trans hA)
      (fun i => (hT i).trans hA)
    have hm := compound_rate_measurable τ v u hu A hT hA
    refine ⟨?_, compound_eq τ v u hu (fun i => (hT i).trans hA),
      rate_formula τ v u hu A hT hA, hi, hm, ?_,
      compound_initial τ v hτ0 hτ hJ u hu (h0.trans hA) (fun i => (hT i).trans hA)⟩
    · intro j ω
      rw [factor_eq τ v u hu (fun i => (hT i).trans hA)]
      exact Real.exp_pos _
    · intro t ht
      exact condExp_of_stronglyMeasurable ((completedFilt τ v).le t)
        (hm.mono ((completedFilt τ v).mono ht) le_rfl).stronglyMeasurable hi
  · intro V L x hV hL
    refine ⟨u0186_mem V L x hL, discount_max V L x hV hL, discount_cases V L x hV hL,
      discount_bound V L x hV.le hL, ?_, discount_zero V x⟩
    simpa using discount_max V L x hV hL 0 ⟨le_rfl, hL⟩
  · intro N J τ v hV A S hAS hA
    refine ⟨exercise_mem τ v A S hAS, exercise_stopping τ v A S hAS hA, ?_⟩
    intro u K ω
    exact ⟨fun t ht => exercise_payoff τ v hV A S hAS hA t ht _ (le_max_right _ _) ω,
      exercise_attained τ v A S hAS hA _ ω⟩

end Novel.LateAmericanExerciseProof

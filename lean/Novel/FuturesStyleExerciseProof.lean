import Standalone.FuturesStyleExercise
import Novel.PreWindowVarianceAggregatesProof
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory Set Filter
open Standalone.CompoundedFuturesIdentification (Ω Q filt r w d h p q L0175 G F C0177)
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)
open Standalone.PreWindowVarianceAggregates (L0202 R0202 Vk Hk past)
open Standalone.FuturesStyleExercise

namespace Novel.FuturesStyleExerciseProof

variable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)

/-! ### (a) the conditional futures rate -/

lemma F_eq (t a b : ℝ) : F τ v t a b = fun ω => (b - a)⁻¹ * (G τ v t a b ω - 1) := by
  funext ω
  simp [F, div_eq_inv_mul]

lemma G_sq (t a b : ℝ) : (fun ω => G τ v t a b ω ^ 2) = fun ω : Ω N =>
    Real.exp (2 * (p τ v a b - (q τ v t a b : ℝ)/2) +
      ∑ i, (2 * if τ (i.val+1) ≤ t then w a b (τ (i.val+1)) else 0) * ω i) := by
  funext ω
  simp only [G, L0175]
  rw [sq, ← Real.exp_add]
  congr 1
  have hterm : ∀ i : Fin N,
      (if τ (i.val+1) ≤ t then w a b (τ (i.val+1)) * ω i else 0) +
        (if τ (i.val+1) ≤ t then w a b (τ (i.val+1)) * ω i else 0) =
      (2 * if τ (i.val+1) ≤ t then w a b (τ (i.val+1)) else 0) * ω i := by
    intro i
    split_ifs <;> ring
  rw [← Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  ring

lemma futures_memLp (t a b : ℝ) : MemLp (G τ v t a b) 2 (Q v) := by
  rw [memLp_two_iff_integrable_sq
    ((CompoundedFuturesIdentificationProof.futures_measurable τ v t a b).mono
      ((filt τ).le t) le_rfl).aestronglyMeasurable, G_sq]
  exact BondOptionMeetingVariancesProof.integrable_exp_sum (v := v) _ _

lemma F_memLp (t a b : ℝ) : MemLp (F τ v t a b) 2 (Q v) := by
  rw [F_eq]
  exact ((futures_memLp τ v t a b).sub (memLp_const 1)).const_mul _

lemma F_integrable (t a b : ℝ) : Integrable (F τ v t a b) (Q v) :=
  (F_memLp τ v t a b).integrable one_le_two

lemma conditional : conditionalStatement := by
  intro N J τ v hτ0 hτ hJ u hu h0 hno
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have hexp := CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab
  have hcomp : ∀ ω, (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0202 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) :=
    fun ω => PreWindowVarianceAggregatesProof.compound_eq τ v u hu hno ω
  have hR : (fun ω => R0202 τ v u ω) = (u (Fin.last J) - u 0)⁻¹ •
      ((fun ω => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) - fun _ => (1 : ℝ)) := by
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, R0202, hcomp]
    rw [div_eq_inv_mul]
  have hcond : ∀ t, (Q v)[fun ω => R0202 τ v u ω | filt τ t] =ᵐ[Q v]
      F τ v t (u 0) (u (Fin.last J)) := by
    intro t
    rw [hR, F_eq]
    have h1 := condExp_smul (μ := Q v) (m := filt τ t) (u (Fin.last J) - u 0)⁻¹
      ((fun ω => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) - fun _ => (1 : ℝ))
    have h2 := condExp_sub (μ := Q v) hexp (integrable_const (1 : ℝ)) (filt τ t)
    have h3 := CompoundedFuturesIdentificationProof.futures_condExp τ v hτ0 hτ _ _ h0 hab t
    have h4 := condExp_const (μ := Q v) ((filt τ).le t) (1 : ℝ)
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    rw [h1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 ⊢
    rw [h2, h4, h3]
  refine ⟨hcomp, fun ω => CompoundedFuturesIdentificationProof.accrual_integral τ v hτ0 hτ _ _
    h0 hab ω, hcond, fun t => ?_, fun t t' h => ?_, fun t => F_memLp τ v t _ _,
    fun t s hts => ?_, fun ω => ?_, fun t => ?_⟩
  · rw [F_eq]
    exact ((CompoundedFuturesIdentificationProof.futures_measurable τ v t _ _).sub_const 1).const_mul _
  · funext ω
    simp only [F, G, L0175, q, h]
  · calc (Q v)[F τ v s (u 0) (u (Fin.last J)) | filt τ t]
        =ᵐ[Q v] (Q v)[(Q v)[fun ω => R0202 τ v u ω | filt τ s] | filt τ t] :=
          condExp_congr_ae (hcond s).symm
      _ =ᵐ[Q v] (Q v)[fun ω => R0202 τ v u ω | filt τ t] :=
          condExp_condExp_of_le ((filt τ).mono hts) ((filt τ).le s)
      _ =ᵐ[Q v] F τ v t (u 0) (u (Fin.last J)) := hcond t
  · rw [F, CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ]
  · have hexp0 : (∫ ω, Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) ∂Q v) =
        Real.exp (p τ v (u 0) (u (Fin.last J))) := by
      rw [← integral_condExp ((filt τ).le 0), integral_congr_ae
        (CompoundedFuturesIdentificationProof.futures_condExp τ v hτ0 hτ _ _ h0 hab 0)]
      simp [CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ]
    have hR' : (fun ω => R0202 τ v u ω) = fun ω =>
        (u (Fin.last J) - u 0)⁻¹ * (Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) - 1) := by
      funext ω
      simp only [R0202, hcomp]
      rw [div_eq_inv_mul]
    rw [← integral_congr_ae (hcond t), integral_condExp ((filt τ).le t), hR', integral_const_mul,
      integral_sub hexp (integrable_const _), hexp0]
    simp [div_eq_inv_mul]

/-! ### (c) the European value as the Gaussian call integral -/

lemma Q0148_zero : Standalone.BondOptionMeetingVariances.Q0148 v 0 = Q v := by
  unfold Standalone.BondOptionMeetingVariances.Q0148
  have : (fun ω : Ω N => ENNReal.ofReal (Standalone.BondOptionMeetingVariances.D0148 v 0 ω)) =
      1 := by
    funext ω
    simp [Standalone.BondOptionMeetingVariances.D0148]
  rw [this, withDensity_one]
  rfl

lemma law_L0175 (S a b : ℝ) :
    HasLaw (L0175 τ v S a b)
      (gaussianReal (Real.log (Real.exp (p τ v a b)) - (q τ v S a b : ℝ)/2) (q τ v S a b))
      (Q v) := by
  classical
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v) 0
    (fun i => if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0)
    (p τ v a b - (q τ v S a b : ℝ)/2)
  rw [Q0148_zero] at h
  have hf : Standalone.BondOptionMeetingVariances.L0149 (p τ v a b - (q τ v S a b : ℝ)/2)
      (fun i => if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0) = L0175 τ v S a b := by
    funext ω
    simp only [Standalone.BondOptionMeetingVariances.L0149, L0175, ite_mul, zero_mul]
  have hm : (p τ v a b - (q τ v S a b : ℝ)/2 +
      ∑ i, (if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0) * (v i : ℝ) *
        (0 : Fin N → ℝ) i) = Real.log (Real.exp (p τ v a b)) - (q τ v S a b : ℝ)/2 := by
    simp [Real.log_exp]
  have hv : (∑ i, v i * (((if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0)) ^ 2).toNNReal)
      = q τ v S a b := by
    simp only [Standalone.CompoundedFuturesIdentification.q]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hf, hm, hv] at h
  exact h

lemma payoff_eq (S a b K : ℝ) (hab : a < b) (ω : Ω N) :
    max (F τ v S a b ω - K) 0 =
      max (Real.exp (L0175 τ v S a b ω) - (1 + (b-a)*K)) 0 / (b-a) := by
  have hδ : 0 < b - a := sub_pos.mpr hab
  rw [← max_div_div_right hδ.le, zero_div]
  congr 1
  simp only [F, G]
  field_simp
  ring

lemma european_value (a b S K : ℝ) (hab : a < b) :
    (∫ ω, max (F τ v S a b ω - K) 0 ∂Q v) =
      C0177 (Real.exp (p τ v a b)) (q τ v S a b) (1 + (b-a)*K) / (b-a) := by
  simp_rw [payoff_eq τ v S a b K hab]
  rw [integral_div]
  congr 1
  have := (law_L0175 τ v S a b).integral_comp
    (f := fun x => max (Real.exp x - (1 + (b-a)*K)) 0)
    ((Real.measurable_exp.sub_const _).max measurable_const).aestronglyMeasurable
  simpa [C0177, Function.comp_def] using this

lemma payoff_integrable (S a b K : ℝ) :
    Integrable (fun ω => max (F τ v S a b ω - K) 0) (Q v) :=
  ((F_integrable τ v S a b).sub (integrable_const K)).pos_part

lemma european : europeanStatement := by
  intro N τ v hτ0 hτ a b S hab hS
  refine ⟨fun K => european_value τ v a b S K hab, fun K K' hK => ?_⟩
  refine integral_mono (payoff_integrable τ v S a b K') (payoff_integrable τ v S a b K)
    fun ω => ?_
  exact max_le_max (sub_le_sub_left hK _) le_rfl

/-! ### (d) the aggregate dependence -/

lemma h_past (a b T : ℝ) (hT : T ≤ a) (hab : a ≤ b) :
    h a b T = (b-a)*((a+b)/2 - T) + (b-a)^2/2 := by
  simp only [Standalone.CompoundedFuturesIdentification.h,
    Standalone.CompoundedFuturesIdentification.d, Standalone.CompoundedFuturesIdentification.w,
    max_eq_left (sub_nonneg.mpr (hT.trans hab)), max_eq_left (sub_nonneg.mpr hT)]
  ring

lemma p_split (A a b : ℝ) (hpast : ∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a)
    (hab : a ≤ b) :
    p τ v a b = (b-a)*(((a+b)/2)*Vk τ v A - Hk τ v A) + (b-a)^2/2*Vk τ v A +
      ∑ i, (if τ (i.val+1) ≤ A then 0 else h a b (τ (i.val+1)) * (v i : ℝ)) := by
  classical
  have hsplit : p τ v a b = ∑ i, (if τ (i.val+1) ≤ A then h a b (τ (i.val+1)) * (v i : ℝ) else 0) +
      ∑ i, (if τ (i.val+1) ≤ A then 0 else h a b (τ (i.val+1)) * (v i : ℝ)) := by
    rw [Standalone.CompoundedFuturesIdentification.p, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  congr 1
  rw [← Finset.sum_filter]
  have hV : (b-a)*(((a+b)/2)*Vk τ v A - Hk τ v A) + (b-a)^2/2*Vk τ v A =
      ∑ i ∈ past τ A, ((b-a)*((a+b)/2 - τ (i.val+1)) + (b-a)^2/2) * (v i : ℝ) := by
    simp only [Vk, Hk, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hV]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : τ (i.val+1) ≤ A := by simpa [past] using hi
  rw [h_past a b _ (hpast i hi') hab]

lemma q_split (A a b S : ℝ) (hpast : ∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a)
    (hab : a ≤ b) (hAS : A ≤ S) :
    (q τ v S a b : ℝ) = (b-a)^2*Vk τ v A +
      ∑ i, (if τ (i.val+1) ≤ A then 0 else
        if τ (i.val+1) ≤ S then (w a b (τ (i.val+1)))^2 * (v i : ℝ) else 0) := by
  classical
  rw [CompoundedFuturesIdentificationProof.q_sum]
  have hsplit : (∑ i, Standalone.CompoundedFuturesIdentification.k S a b (τ (i.val+1)) * (v i : ℝ)) =
      ∑ i, (if τ (i.val+1) ≤ A then (b-a)^2 * (v i : ℝ) else 0) +
      ∑ i, (if τ (i.val+1) ≤ A then 0 else
        if τ (i.val+1) ≤ S then (w a b (τ (i.val+1)))^2 * (v i : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Standalone.CompoundedFuturesIdentification.k]
    by_cases hA : τ (i.val+1) ≤ A
    · have hS : τ (i.val+1) ≤ S := hA.trans hAS
      rw [if_pos hS, if_pos hA, if_pos hA,
        CompoundedFuturesIdentificationProof.w_after (hpast i hA) hab]
      ring
    · rw [if_neg hA, if_neg hA]
      split_ifs <;> ring
  rw [hsplit]
  congr 1
  rw [← Finset.sum_filter, Vk, Finset.mul_sum]
  rfl

lemma aggregate : aggregateStatement := by
  intro N τ v v' hτ0 hτ A a b h0 hab hpast hlater hV hH
  have hp : p τ v a b = p τ v' a b := by
    rw [p_split τ v A a b hpast hab.le, p_split τ v' A a b hpast hab.le, hV, hH]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [hlater i (not_le.mp hi)]
  have hq : ∀ S, A ≤ S → q τ v S a b = q τ v' S a b := by
    intro S hAS
    apply NNReal.coe_injective
    rw [q_split τ v A a b S hpast hab.le hAS, q_split τ v' A a b S hpast hab.le hAS, hV]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [hlater i (not_le.mp hi)]
    · rfl
  refine ⟨hp, hq, fun ω => ?_, fun S K hAS hS => ?_⟩
  · simp only [F, CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ,
      CompoundedFuturesIdentificationProof.futures_initial τ v' hτ0 hτ, hp]
  · rw [european_value τ v a b S K hab, european_value τ v' a b S K hab, hp, hq S hAS]

/-! ### (b) no early-exercise value -/

section NoEarlyExercise

/-- The number of meetings at or before `t`. -/
noncomputable def cnt (t : ℝ) : ℕ := (Finset.univ.filter fun i : Fin N => τ (i.val+1) ≤ t).card

lemma cnt_le (t : ℝ) : cnt (N := N) τ t ≤ N := by
  unfold cnt
  exact (Finset.card_le_univ _).trans (by simp)

lemma cnt_mono {t t' : ℝ} (h : t ≤ t') : cnt (N := N) τ t ≤ cnt (N := N) τ t' := by
  unfold cnt
  exact Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans h⟩

/-- The revealed set is an initial segment of the meeting indices. -/
lemma mem_iff_lt_cnt (hτ : StrictMonoOn τ (Iic N)) (t : ℝ) (i : Fin N) :
    τ (i.val+1) ≤ t ↔ i.val < cnt (N := N) τ t := by
  classical
  set s := Finset.univ.filter fun i : Fin N => τ (i.val+1) ≤ t with hs
  have hdown : ∀ i j : Fin N, j ≤ i → i ∈ s → j ∈ s := by
    intro i j hji hi
    have hiN := i.isLt
    have hjN := j.isLt
    have hji' := Fin.le_iff_val_le_val.mp hji
    rw [hs, Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, le_trans ?_ hi.2⟩
    exact hτ.monotoneOn (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega)) (by omega)
  constructor
  · intro hi
    have hmem : i ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
    have hsub : Finset.Iic i ⊆ s := fun j hj => hdown i j (Finset.mem_Iic.mp hj) hmem
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    show i.val < s.card
    omega
  · intro hlt
    by_contra hcon
    have hnot : i ∉ s := by rw [hs, Finset.mem_filter]; exact fun h => hcon h.2
    have hsub : s ⊆ Finset.Iio i := fun j hj => by
      rw [Finset.mem_Iio]
      by_contra hle
      exact hnot (hdown j i (not_lt.mp hle) hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    change i.val < s.card at hlt
    omega

/-- The conditional futures rate at `t` is its value at the last meeting at or before `t`. -/
lemma F_cnt (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (a b t : ℝ) :
    F τ v t a b = F τ v (τ (cnt (N := N) τ t)) a b := by
  have h : ∀ i : Fin N, τ (i.val+1) ≤ t ↔ τ (i.val+1) ≤ τ (cnt (N := N) τ t) := by
    intro i
    have hiN := i.isLt
    rw [mem_iff_lt_cnt τ hτ t i]
    have hc := cnt_le (N := N) τ t
    rw [hτ.le_iff_le (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega))]
    omega
  funext ω
  simp only [F, G, L0175, q, h]

/-- The martingale property of the conditional futures rate. -/
lemma F_martingale (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b) {t s : ℝ} (hts : t ≤ s) :
    (Q v)[F τ v s a b | filt τ t] =ᵐ[Q v] F τ v t a b := by
  have hexp := CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ a b ha hab
  have hcond : ∀ t, (Q v)[fun ω => (b - a)⁻¹ * (Real.exp (∫ u in a..b, r τ v u ω) - 1) | filt τ t]
      =ᵐ[Q v] F τ v t a b := by
    intro t
    rw [F_eq]
    have h1 := condExp_smul (μ := Q v) (m := filt τ t) (b - a)⁻¹
      ((fun ω => Real.exp (∫ u in a..b, r τ v u ω)) - fun _ => (1 : ℝ))
    have h2 := condExp_sub (μ := Q v) hexp (integrable_const (1 : ℝ)) (filt τ t)
    have h3 := CompoundedFuturesIdentificationProof.futures_condExp τ v hτ0 hτ a b ha hab t
    have h4 := condExp_const (μ := Q v) ((filt τ).le t) (1 : ℝ)
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    rw [show (fun ω => (b - a)⁻¹ * (Real.exp (∫ u in a..b, r τ v u ω) - 1)) =
      (b - a)⁻¹ • ((fun ω => Real.exp (∫ u in a..b, r τ v u ω)) - fun _ => (1 : ℝ)) from rfl, h1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 ⊢
    rw [h2, h4, h3]
  calc (Q v)[F τ v s a b | filt τ t]
      =ᵐ[Q v] (Q v)[(Q v)[fun ω => (b - a)⁻¹ * (Real.exp (∫ u in a..b, r τ v u ω) - 1) | filt τ s]
        | filt τ t] := condExp_congr_ae (hcond s).symm
    _ =ᵐ[Q v] (Q v)[fun ω => (b - a)⁻¹ * (Real.exp (∫ u in a..b, r τ v u ω) - 1) | filt τ t] :=
        condExp_condExp_of_le ((filt τ).mono hts) ((filt τ).le s)
    _ =ᵐ[Q v] F τ v t a b := hcond t

lemma F_filt_measurable (t a b : ℝ) : Measurable[filt τ t] (F τ v t a b) := by
  rw [F_eq]
  exact ((CompoundedFuturesIdentificationProof.futures_measurable τ v t a b).sub_const 1).const_mul _

/-- The martingale set identity on the completed space. -/
lemma F_setIntegral_completed (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) {t s : ℝ} (hts : t ≤ s) (E : Set (Ωc v))
    (hE : MeasurableSet[completedFilt τ v t] E) :
    (∫ ω in E, F τ v s a b ω ∂Qc v) = ∫ ω in E, F τ v t a b ω ∂Qc v := by
  obtain ⟨E₀, hE₀, hEE₀⟩ := hE
  have hEE₀' : E =ᵐ[Qc v] E₀ := hEE₀
  have hE₀pi : MeasurableSet[MeasurableSpace.pi] (E₀ : Set (Ω N)) := (filt τ).le t _ hE₀
  calc (∫ ω in E, F τ v s a b ω ∂Qc v)
      = ∫ ω in E₀, F τ v s a b ω ∂Qc v :=
        setIntegral_congr_set (f := fun ω : Ωc v => F τ v s a b ω) hEE₀'
    _ = ∫ ω in E₀, F τ v s a b ω ∂Q v :=
        CompoundedFuturesIdentificationProof.completion_setIntegral v _ (F_integrable τ v s a b)
          E₀ hE₀pi
    _ = ∫ ω in E₀, F τ v t a b ω ∂Q v := by
        rw [← setIntegral_condExp ((filt τ).le t) (F_integrable τ v s a b) hE₀]
        exact setIntegral_congr_ae₀ hE₀pi.nullMeasurableSet
          ((F_martingale τ v hτ0 hτ a b ha hab hts).mono fun ω h _ => h)
    _ = ∫ ω in E₀, F τ v t a b ω ∂Qc v :=
        (CompoundedFuturesIdentificationProof.completion_setIntegral v _ (F_integrable τ v t a b)
          E₀ hE₀pi).symm
    _ = ∫ ω in E, F τ v t a b ω ∂Qc v :=
        (setIntegral_congr_set (f := fun ω : Ωc v => F τ v t a b ω) hEE₀').symm

lemma payoff_completed_integrable (t a b K : ℝ) :
    Integrable (fun ω : Ωc v => max (F τ v t a b ω - K) 0) (Qc v) := by
  have hF : Integrable (fun ω : Ωc v => F τ v t a b ω) (Qc v) :=
    (CompoundedFuturesIdentificationProof.completion_law v).integrable_comp (F_integrable τ v t a b)
  refine (hF.abs.add (integrable_const |K|)).mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((CrossMeetingAmericanProof.completed_measurable v _
      ((F_filt_measurable τ v t a b).mono ((filt τ).le t) le_rfl)).sub_const K).max
      measurable_const |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h2 := neg_abs_le K
    have h3 := le_abs_self (F τ v t a b ω)
    show max (F τ v t a b ω - K) 0 ≤ |F τ v t a b ω| + |K|
    exact max_le (by linarith) (by positivity)

/-- The submartingale set inequality for the payoff `(F − K)^+`. -/
lemma payoff_setIntegral_le (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (a b K : ℝ)
    (ha : 0 ≤ a) (hab : a < b) {t s : ℝ} (hts : t ≤ s) (D : Set (Ωc v))
    (hD : MeasurableSet[completedFilt τ v t] D) :
    (∫ ω in D, max (F τ v t a b ω - K) 0 ∂Qc v) ≤ ∫ ω in D, max (F τ v s a b ω - K) 0 ∂Qc v := by
  have hDm : MeasurableSet D := (completedFilt τ v).le t _ hD
  have hFt : Measurable[completedFilt τ v t] (fun ω : Ωc v => F τ v t a b ω) := fun B hB =>
    PreWindowVarianceAggregatesProof.filt_le_completed τ v t _ (F_filt_measurable τ v t a b hB)
  set E : Set (Ωc v) := D ∩ {ω | K < F τ v t a b ω} with hEdef
  have hE : MeasurableSet[completedFilt τ v t] E :=
    hD.inter (hFt measurableSet_Ioi)
  have hEm : MeasurableSet E := (completedFilt τ v).le t _ hE
  have hFint : ∀ u, Integrable (fun ω : Ωc v => F τ v u a b ω) (Qc v) := fun u =>
    (CompoundedFuturesIdentificationProof.completion_law v).integrable_comp (F_integrable τ v u a b)
  -- the payoff at `t` on `D` is `F t − K` on `E`
  have h1 : (∫ ω in D, max (F τ v t a b ω - K) 0 ∂Qc v) = ∫ ω in E, (F τ v t a b ω - K) ∂Qc v := by
    rw [← integral_indicator hDm, ← integral_indicator hEm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hωD : ω ∈ D
    · by_cases hωK : K < F τ v t a b ω
      · rw [Set.indicator_of_mem hωD, Set.indicator_of_mem (show ω ∈ E from ⟨hωD, hωK⟩),
          max_eq_left (by linarith)]
      · rw [Set.indicator_of_mem hωD, Set.indicator_of_notMem (show ω ∉ E from fun h => hωK h.2),
          max_eq_right (by linarith [not_lt.mp hωK])]
    · rw [Set.indicator_of_notMem hωD, Set.indicator_of_notMem (show ω ∉ E from fun h => hωD h.1)]
  -- the payoff at `s` on `D` dominates `F s − K` on `E`
  have h2 : (∫ ω in E, (F τ v s a b ω - K) ∂Qc v) ≤ ∫ ω in D, max (F τ v s a b ω - K) 0 ∂Qc v := by
    rw [← integral_indicator hDm, ← integral_indicator hEm]
    refine integral_mono (((hFint s).sub (integrable_const K)).indicator hEm)
      ((payoff_completed_integrable τ v s a b K).indicator hDm) fun ω => ?_
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE, Set.indicator_of_mem hωE.1]
      exact le_max_left _ _
    · rw [Set.indicator_of_notMem hωE]
      by_cases hωD : ω ∈ D
      · rw [Set.indicator_of_mem hωD]; exact le_max_right _ _
      · rw [Set.indicator_of_notMem hωD]
  -- the martingale identity on `E`
  have h3 : (∫ ω in E, (F τ v t a b ω - K) ∂Qc v) = ∫ ω in E, (F τ v s a b ω - K) ∂Qc v := by
    rw [integral_sub ((hFint t).integrableOn) (integrable_const K).integrableOn,
      integral_sub ((hFint s).integrableOn) (integrable_const K).integrableOn,
      F_setIntegral_completed τ v hτ0 hτ a b ha hab hts E hE]
  rw [h1, h3]
  exact h2

/-- The meeting count of an admissible exercise time is a stopping time of the discrete
filtration `completedFilt (τ n)`. -/
lemma cnt_stopping (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (σ : Ωc v → ℝ)
    (hσ : σ ∈ T0183 τ v A S) (n : ℕ) (hn : n < N) :
    MeasurableSet[completedFilt τ v (τ n)] {ω : Ωc v | cnt (N := N) τ (σ ω) ≤ n} := by
  have hset : {ω : Ωc v | cnt (N := N) τ (σ ω) ≤ n} =
      ⋃ q : {q : ℚ // (q : ℝ) < τ (n+1)}, {ω : Ωc v | (σ ω : WithTop ℝ) ≤ ((q.1 : ℝ) : WithTop ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop, WithTop.coe_le_coe]
    have hiff := mem_iff_lt_cnt τ hτ (σ ω) ⟨n, hn⟩
    simp only at hiff
    constructor
    · intro h
      have hlt : σ ω < τ (n+1) := by
        by_contra hge
        have := hiff.mp (not_lt.mp hge)
        omega
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact ⟨q, hq2, hq1.le⟩
    · rintro ⟨q, hq, hσq⟩
      by_contra hcon
      have := hiff.mpr (by omega)
      linarith
  rw [hset]
  refine MeasurableSet.iUnion fun q => ?_
  have hq := hσ.2 (q.1 : ℝ)
  -- `completedFilt q ≤ completedFilt (τ n)` since no meeting lies in `(τ n, q]`
  have hle : (filt τ (q.1 : ℝ) : MeasurableSpace (Ω N)) ≤ filt τ (τ n) := by
    refine iSup_mono fun i => iSup_mono' fun hi => ⟨?_, le_rfl⟩
    have hlt : τ (i.val+1) < τ (n+1) := hi.trans_lt q.2
    have hi' : i.val + 1 < n + 1 :=
      (hτ.lt_iff_lt (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega))).mp hlt
    exact hτ.monotoneOn (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega)) (by omega)
  obtain ⟨B, hB, hBq⟩ := hq
  exact ⟨B, hle B hB, hBq⟩

/-- Telescoping of a discretely stopped sequence. -/
lemma telescope (f : ℕ → ℝ) (ν m : ℕ) (hνm : ν ≤ m) :
    f m - f ν = ∑ n ∈ Finset.range m, (f (n+1) - f n) * (if ν ≤ n then 1 else 0) := by
  induction m, hνm using Nat.le_induction with
  | base =>
    rw [sub_self]
    symm
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [if_neg (by omega), mul_zero]
  | succ m hνm ih =>
    rw [Finset.sum_range_succ, ← ih, if_pos hνm]
    ring

lemma noEarlyExercise_bound (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S a b K : ℝ)
    (h0 : 0 ≤ A) (hAS : A ≤ S) (ha : 0 ≤ a) (hab : a < b) (σ : Ωc v → ℝ)
    (hσ : σ ∈ T0183 τ v A S) :
    (∫ ω : Ωc v, max (F τ v (σ ω) a b ω - K) 0 ∂Qc v) ≤
      ∫ ω : Ωc v, max (F τ v S a b ω - K) 0 ∂Qc v := by
  classical
  set X : ℕ → Ωc v → ℝ := fun n ω => max (F τ v (τ n) a b ω - K) 0 with hX
  set ν : Ωc v → ℕ := fun ω => cnt (N := N) τ (σ ω) with hν
  set nS : ℕ := cnt (N := N) τ S with hnS
  have hνS : ∀ ω, ν ω ≤ nS := fun ω => cnt_mono τ (hσ.1 ω).2
  have hXint : ∀ n, Integrable (X n) (Qc v) := fun n => payoff_completed_integrable τ v _ a b K
  -- the payoff at the exercise time and at `S` as values of the discrete sequence
  have hσX : (fun ω : Ωc v => max (F τ v (σ ω) a b ω - K) 0) = fun ω => X (ν ω) ω := by
    funext ω
    simp only [hX, hν]
    rw [F_cnt τ v hτ0 hτ a b (σ ω)]
  have hSX : (fun ω : Ωc v => max (F τ v S a b ω - K) 0) = X nS := by
    funext ω
    simp only [hX, hnS]
    rw [F_cnt τ v hτ0 hτ a b S]
  rw [hσX, hSX]
  -- telescoping
  have htel : (fun ω => X nS ω - X (ν ω) ω) = fun ω =>
      ∑ n ∈ Finset.range nS, (X (n+1) ω - X n ω) * (if ν ω ≤ n then 1 else 0) :=
    funext fun ω => telescope (fun n => X n ω) (ν ω) nS (hνS ω)
  have hnonneg : 0 ≤ ∫ ω, (X nS ω - X (ν ω) ω) ∂Qc v := by
    rw [htel]
    have hsets : ∀ n, n < nS → MeasurableSet[completedFilt τ v (τ n)] {ω : Ωc v | ν ω ≤ n} :=
      fun n hn => cnt_stopping τ v hτ0 hτ A S σ hσ n (lt_of_lt_of_le hn (cnt_le τ S))
    have hterm : ∀ n ∈ Finset.range nS, Integrable
        (fun ω => (X (n+1) ω - X n ω) * (if ν ω ≤ n then 1 else 0)) (Qc v) := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hm : MeasurableSet {ω : Ωc v | ν ω ≤ n} := (completedFilt τ v).le _ _ (hsets n hn)
      have : (fun ω => (X (n+1) ω - X n ω) * (if ν ω ≤ n then 1 else 0)) =
          {ω : Ωc v | ν ω ≤ n}.indicator (fun ω => X (n+1) ω - X n ω) := by
        funext ω
        by_cases h : ν ω ≤ n
        · rw [if_pos h, mul_one, Set.indicator_of_mem (show ω ∈ {ω | ν ω ≤ n} from h)]
        · rw [if_neg h, mul_zero, Set.indicator_of_notMem (show ω ∉ {ω | ν ω ≤ n} from h)]
      rw [this]
      exact ((hXint (n+1)).sub (hXint n)).indicator hm
    rw [integral_finset_sum _ hterm]
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hm : MeasurableSet {ω : Ωc v | ν ω ≤ n} := (completedFilt τ v).le _ _ (hsets n hn)
    have : (fun ω => (X (n+1) ω - X n ω) * (if ν ω ≤ n then 1 else 0)) =
        {ω : Ωc v | ν ω ≤ n}.indicator (fun ω => X (n+1) ω - X n ω) := by
      funext ω
      by_cases h : ν ω ≤ n
      · rw [if_pos h, mul_one, Set.indicator_of_mem (show ω ∈ {ω | ν ω ≤ n} from h)]
      · rw [if_neg h, mul_zero, Set.indicator_of_notMem (show ω ∉ {ω | ν ω ≤ n} from h)]
    rw [this, integral_indicator hm, integral_sub ((hXint (n+1)).integrableOn)
      ((hXint n).integrableOn), sub_nonneg]
    have hnN : n < N := lt_of_lt_of_le hn (cnt_le (N := N) τ S)
    have hτle : τ n ≤ τ (n+1) :=
      hτ.monotoneOn (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega)) (by omega)
    exact payoff_setIntegral_le τ v hτ0 hτ a b K ha hab hτle _ (hsets n hn)
  have hνint : Integrable (fun ω => X (ν ω) ω) (Qc v) := by
    have : (fun ω => X (ν ω) ω) = fun ω => X nS ω - (X nS ω - X (ν ω) ω) := by
      funext ω; ring
    rw [this]
    refine (hXint nS).sub ?_
    rw [htel]
    refine integrable_finset_sum _ fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hm : MeasurableSet {ω : Ωc v | ν ω ≤ n} := (completedFilt τ v).le _ _
      (cnt_stopping τ v hτ0 hτ A S σ hσ n (lt_of_lt_of_le hn (cnt_le τ S)))
    have : (fun ω => (X (n+1) ω - X n ω) * (if ν ω ≤ n then 1 else 0)) =
        {ω : Ωc v | ν ω ≤ n}.indicator (fun ω => X (n+1) ω - X n ω) := by
      funext ω
      by_cases h : ν ω ≤ n
      · rw [if_pos h, mul_one, Set.indicator_of_mem (show ω ∈ {ω | ν ω ≤ n} from h)]
      · rw [if_neg h, mul_zero, Set.indicator_of_notMem (show ω ∉ {ω | ν ω ≤ n} from h)]
    rw [this]
    exact ((hXint (n+1)).sub (hXint n)).indicator hm
  rw [integral_sub (hXint nS) hνint] at hnonneg
  linarith

lemma european_completed (a b S K : ℝ) :
    (∫ ω : Ωc v, max (F τ v S a b ω - K) 0 ∂Qc v) = ∫ ω, max (F τ v S a b ω - K) 0 ∂Q v :=
  (CompoundedFuturesIdentificationProof.completion_law v).integral_comp
    (((F_filt_measurable τ v S a b).mono ((filt τ).le S) le_rfl).sub_const K |>.max
      measurable_const).aestronglyMeasurable

lemma noEarlyExercise : noEarlyExerciseStatement := by
  intro N τ v hτ0 hτ A S a b K h0 hAS ha hab
  have hbound : ∀ σ ∈ T0183 τ v A S, (∫ ω : Ωc v, max (F τ v (σ ω) a b ω - K) 0 ∂Qc v) ≤
      ∫ ω, max (F τ v S a b ω - K) 0 ∂Q v := fun σ hσ =>
    (noEarlyExercise_bound τ v hτ0 hτ A S a b K h0 hAS ha hab σ hσ).trans
      (european_completed τ v a b S K).le
  refine ⟨hbound, le_antisymm ?_ ?_⟩
  · refine csSup_le ⟨_, ⟨fun _ => S, ⟨fun _ => ⟨hAS, le_rfl⟩, isStoppingTime_const _ _⟩, rfl⟩⟩ ?_
    rintro x ⟨σ, hσ, rfl⟩
    exact hbound σ hσ
  · refine le_csSup ⟨∫ ω, max (F τ v S a b ω - K) 0 ∂Q v, ?_⟩
      ⟨fun _ => S, ⟨fun _ => ⟨hAS, le_rfl⟩, isStoppingTime_const _ _⟩, ?_⟩
    · rintro x ⟨σ, hσ, rfl⟩
      exact hbound σ hσ
    · exact european_completed τ v a b S K

end NoEarlyExercise

/-! ### (c) the closed form (21.6) -/

section ClosedForm
open Standalone.CompoundedFuturesIdentification (Φ)

/-- The Gaussian call at a nonpositive strike is the forward minus the strike. -/
lemma C0177_nonpos {M K : ℝ} (hM : 0 < M) (hK : K ≤ 0) (R : NNReal) : C0177 M R K = M - K := by
  have hi : Integrable Real.exp (gaussianReal (Real.log M - (R : ℝ)/2) R) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := Real.log M - (R : ℝ)/2) (v := R) 1)
  have he : (fun x => max (Real.exp x - K) 0) = fun x => Real.exp x - K := by
    funext x
    exact max_eq_left (by linarith [Real.exp_pos x])
  unfold C0177
  rw [he, integral_sub hi (integrable_const K), CompoundedFuturesIdentificationProof.C0177_mean hM,
    integral_const, probReal_univ, one_smul]

/-- The Gaussian call is `1`-Lipschitz in the strike. -/
lemma C0177_lipschitz (M : ℝ) (R : NNReal) : LipschitzWith 1 (fun K => C0177 M R K) := by
  refine LipschitzWith.of_dist_le_mul fun K K' => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  unfold C0177
  rw [← integral_sub (CompoundedFuturesIdentificationProof.gaussian_call_integrable _ _ _)
    (CompoundedFuturesIdentificationProof.gaussian_call_integrable _ _ _)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ x, |max (Real.exp x - K) 0 - max (Real.exp x - K') 0|
        ∂gaussianReal (Real.log M - (R : ℝ)/2) R)
      ≤ ∫ _, |K - K'| ∂gaussianReal (Real.log M - (R : ℝ)/2) R := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun x => ?_)
        have h := abs_max_sub_max_le_abs (Real.exp x - K) (Real.exp x - K') 0
        calc |max (Real.exp x - K) 0 - max (Real.exp x - K') 0|
            ≤ |Real.exp x - K - (Real.exp x - K')| := h
          _ = |K - K'| := by rw [show Real.exp x - K - (Real.exp x - K') = K' - K by ring, abs_sub_comm]
    _ = |K - K'| := by rw [integral_const, probReal_univ, one_smul]

lemma closedForm : closedFormStatement := by
  intro N τ v hτ0 hτ A S a b h0 hAS ha hab
  intro G σ2
  have hδ : 0 < b - a := sub_pos.2 hab
  have hS : 0 ≤ S := h0.trans hAS
  have hU : ∀ K, Ufut τ v A S a b K =
      C0177 (Real.exp (p τ v a b)) (q τ v S a b) (1 + (b-a)*K) / (b-a) := fun K => by
    rw [(noEarlyExercise N τ v hτ0 hτ A S a b K h0 hAS ha hab).2,
      (european N τ v hτ0 hτ a b S hab hS).1 K]
  have hG : 0 < G := Real.exp_pos _
  refine ⟨fun K hσ hK => ?_, fun K hK => ?_, fun K hσ => ?_, ?_, ?_⟩
  · rw [hU K, CompoundedFuturesIdentificationProof.C0177_pos hG hK _
      (by exact_mod_cast hσ : (0 : NNReal) < q τ v S a b)]
  · rw [hU K, C0177_nonpos hG hK]
  · have hσ' : (q τ v S a b : ℝ) = 0 := hσ
    have hq : q τ v S a b = 0 := by exact_mod_cast hσ'
    rw [hU K, hq, CompoundedFuturesIdentificationProof.C0177_zero hG]
  · have : (fun K => Ufut τ v A S a b K) = fun K =>
        C0177 (Real.exp (p τ v a b)) (q τ v S a b) (1 + (b-a)*K) / (b-a) := funext hU
    rw [this]
    exact ((C0177_lipschitz _ _).continuous.comp (continuous_const.add
      (continuous_const.mul continuous_id))).div_const _
  · intro K K' hKK'
    show Ufut τ v A S a b K' ≤ Ufut τ v A S a b K
    rw [hU K, hU K', ← (european N τ v hτ0 hτ a b S hab hS).1 K,
      ← (european N τ v hτ0 hτ a b S hab hS).1 K']
    exact (european N τ v hτ0 hτ a b S hab hS).2 hKK'

end ClosedForm

/-! ### (d) the identification converse and (e) the equal pair -/

section Identification
open Standalone.CompoundedFuturesIdentification (q0178)

lemma Ufut_eq_C0177 (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S a b K : ℝ) (h0 : 0 ≤ A)
    (hAS : A ≤ S) (ha : 0 ≤ a) (hab : a < b) :
    Ufut τ v A S a b K = C0177 (Real.exp (p τ v a b)) (q τ v S a b) (1 + (b-a)*K) / (b-a) := by
  rw [(noEarlyExercise N τ v hτ0 hτ A S a b K h0 hAS ha hab).2,
    (european N τ v hτ0 hτ a b S hab (h0.trans hAS)).1 K]

lemma w_zero_of_le (a b T : ℝ) (hab : a ≤ b) (hbT : b ≤ T) : w a b T = 0 := by
  unfold w
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma h_zero_of_le (a b T : ℝ) (hab : a ≤ b) (hbT : b ≤ T) : h a b T = 0 := by
  unfold h d
  rw [w_zero_of_le a b T hab hbT, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- The difference of `σ_S²` across a gap holding exactly one meeting. -/
lemma q_gap (a b S₁ S₂ : ℝ) (n : Fin N) (hS : S₁ ≤ S₂)
    (hone : ∀ i : Fin N, S₁ < τ (i.val+1) → τ (i.val+1) ≤ S₂ → i = n)
    (h1 : S₁ < τ (n.val+1)) (h2 : τ (n.val+1) ≤ S₂) :
    (q τ v S₂ a b : ℝ) - q τ v S₁ a b = (w a b (τ (n.val+1)))^2 * v n := by
  classical
  simp only [q, NNReal.coe_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single n]
  · simp only [h2, h1.not_ge, if_true, if_false, NNReal.coe_zero, sub_zero, NNReal.coe_mul,
      Real.coe_toNNReal _ (sq_nonneg _)]
    ring
  · intro i _ hin
    by_cases hi2 : τ (i.val+1) ≤ S₂
    · have hi1 : τ (i.val+1) ≤ S₁ := by
        by_contra hcon
        exact hin (hone i (not_le.mp hcon) hi2)
      simp [hi1, hi2]
    · have hi1 : ¬ τ (i.val+1) ≤ S₁ := fun h => hi2 (h.trans hS)
      simp [hi1, hi2]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

lemma identification : identificationStatement := by
  intro N τ v v' hτ0 hτ A a b h0 ha hab
  refine ⟨fun hpast hlater hV hH S K hAS => ?_, fun S hAS hp hU => ?_,
    fun S₁ S₂ n hS hone h1 h2 => q_gap τ v a b S₁ S₂ n hS hone h1 h2,
    fun S₁ S₂ n hS hone h1 h2 haT hTb hq1 hq2 => ?_, fun n hbn hv => ?_⟩
  · rw [(noEarlyExercise N τ v hτ0 hτ A S a b K h0 hAS ha hab).2,
      (noEarlyExercise N τ v' hτ0 hτ A S a b K h0 hAS ha hab).2]
    exact (aggregate N τ v v' hτ0 hτ A a b ha hab hpast hlater hV hH).2.2.2 S K hAS (h0.trans hAS)
  · -- the at-the-money price recovers `σ_S²` through `q0178`
    have hδ : 0 < b - a := sub_pos.2 hab
    set G := Real.exp (p τ v a b) with hG
    have hGpos : 0 < G := Real.exp_pos _
    set K := (G - 1) / (b - a) with hK
    have hK' : 1 + (b - a) * K = G := by rw [hK]; field_simp; ring
    have h := hU K
    rw [Ufut_eq_C0177 τ v hτ0 hτ A S a b K h0 hAS ha hab,
      Ufut_eq_C0177 τ v' hτ0 hτ A S a b K h0 hAS ha hab, ← hp, ← hG, hK'] at h
    have h' : C0177 G (q τ v S a b) G = C0177 G (q τ v' S a b) G := by
      have := congrArg (fun x => x * (b - a)) h
      simpa [div_mul_cancel₀ _ hδ.ne'] using this
    have hr := CompoundedFuturesIdentificationProof.C0177_recover_q hGpos (q τ v S a b)
    have hr' := CompoundedFuturesIdentificationProof.C0177_recover_q hGpos (q τ v' S a b)
    rw [h'] at hr
    exact NNReal.coe_injective (hr.symm.trans hr')
  · have hw : w a b (τ (n.val+1)) = b - τ (n.val+1) := by
      unfold w
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    have hpos : 0 < (w a b (τ (n.val+1)))^2 := by rw [hw]; positivity
    have e1 := q_gap τ v a b S₁ S₂ n hS hone h1 h2
    have e2 := q_gap τ v' a b S₁ S₂ n hS hone h1 h2
    rw [hq1, hq2] at e1
    have : (w a b (τ (n.val+1)))^2 * (v n : ℝ) = (w a b (τ (n.val+1)))^2 * v' n := by linarith
    exact NNReal.coe_injective (mul_left_cancel₀ hpos.ne' this)
  · constructor
    · unfold p
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i = n
      · subst hi
        rw [h_zero_of_le a b _ hab.le hbn]
        ring
      · rw [hv i hi]
    · intro S
      unfold q
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i = n
      · subst hi
        rw [w_zero_of_le a b _ hab.le hbn]
        simp
      · rw [hv i hi]

lemma τ5_zero : τ5 0 = 0 := by simp [τ5]

lemma τ5_strictMono : StrictMonoOn τ5 (Iic 5) := fun m _ n _ hmn => by
  simp only [τ5]
  exact_mod_cast hmn

lemma pair : pairStatement := by
  intro ε w4 w5 A a b h3 h4 hAa hab
  have hpast : ∀ i : Fin 5, τ5 (i.val+1) ≤ A → τ5 (i.val+1) ≤ a := fun i hi => hi.trans hAa
  have hlater : ∀ i : Fin 5, A < τ5 (i.val+1) → v021 ε w4 w5 i = v021' ε w4 w5 i := by
    intro i hi
    simp only [τ5] at hi
    fin_cases i
    · exfalso; norm_num at hi; linarith
    · exfalso; norm_num at hi; linarith
    · exfalso; norm_num at hi; linarith
    · rfl
    · rfl
  have hpastSet : past τ5 A = ({0, 1, 2} : Finset (Fin 5)) := by
    ext i
    simp only [past, Finset.mem_filter, Finset.mem_univ, true_and, τ5, Finset.mem_insert,
      Finset.mem_singleton]
    fin_cases i <;> simp
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  have hV : Vk τ5 (v021 ε w4 w5) A = Vk τ5 (v021' ε w4 w5) A := by
    simp only [Vk, hpastSet, v021, v021']
    simp [Finset.sum_insert, NNReal.coe_mul]
    ring
  have hH : Hk τ5 (v021 ε w4 w5) A = Hk τ5 (v021' ε w4 w5) A := by
    simp only [Hk, hpastSet, v021, v021', τ5]
    simp [Finset.sum_insert, NNReal.coe_mul]
    ring
  have ha : 0 ≤ a := by linarith
  have h0 : 0 ≤ A := by linarith
  refine ⟨(aggregate 5 τ5 _ _ τ5_zero τ5_strictMono A a b ha hab hpast hlater hV hH).2.2.1,
    fun S K hAS => ?_⟩
  exact (identification 5 τ5 _ _ τ5_zero τ5_strictMono A a b h0 ha hab).1 hpast hlater hV hH S K
    hAS

end Identification

/-! ### (e) the separated pair -/

section Separation
open Standalone.CompoundedFuturesIdentification (Φ)
open Standalone.BondOptionMeetingVariances in
open scoped MeasureTheory

lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  have h := BondOptionMeetingVariancesProof.Φ_lt_one (-x)
  rw [BondOptionMeetingVariancesProof.Φ_neg] at h
  change 0 < Standalone.BondOptionMeetingVariances.Φ x
  linarith

/-- The Gaussian call is strictly increasing in the forward at positive strike and variance. -/
lemma C0177_strictMono_forward (K : ℝ) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    StrictMonoOn (fun M => C0177 M R K) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact fun M hM => (CompoundedFuturesIdentificationProof.C0177_deriv_mean hM hK R hR)
      |>.continuousAt.continuousWithinAt
  · intro M hM
    rw [interior_Ioi] at hM
    rw [(CompoundedFuturesIdentificationProof.C0177_deriv_mean hM hK R hR).deriv]
    exact Φ_pos _

/-- The Gaussian call is nondecreasing in the variance: the larger variance is the smaller one
convolved with an independent centred lognormal factor of mean one, and the positive part is
convex (Jensen). -/
lemma C0177_mono_var {M : ℝ} (hM : 0 < M) (K : ℝ) {R R' : NNReal} (hRR' : R ≤ R') :
    C0177 M R K ≤ C0177 M R' K := by
  set v₂ : NNReal := R' - R with hv₂
  have hR' : R' = R + v₂ := by rw [hv₂, add_tsub_cancel_of_le hRR']
  have hconv : gaussianReal (Real.log M - (R' : ℝ)/2) R' =
      gaussianReal (Real.log M - (R : ℝ)/2) R ∗ gaussianReal (-(v₂ : ℝ)/2) v₂ := by
    rw [gaussianReal_conv_gaussianReal, hR']
    congr 1
    push_cast
    ring
  have hfint : Integrable (fun x => max (Real.exp x - K) 0)
      (gaussianReal (Real.log M - (R : ℝ)/2) R ∗ gaussianReal (-(v₂ : ℝ)/2) v₂) := by
    rw [← hconv]
    exact CompoundedFuturesIdentificationProof.gaussian_call_integrable _ _ _
  unfold C0177
  rw [hconv, integral_conv hfint]
  -- integrability of the inner integral
  have hinner : Integrable (fun x => ∫ y, max (Real.exp (x + y) - K) 0 ∂gaussianReal (-(v₂ : ℝ)/2) v₂)
      (gaussianReal (Real.log M - (R : ℝ)/2) R) := by
    have h := ((integrable_conv_iff hfint.1).1 hfint).2
    refine h.congr (Eventually.of_forall fun x => ?_)
    show (∫ y, ‖max (Real.exp (x + y) - K) 0‖ ∂gaussianReal (-(v₂ : ℝ)/2) v₂) =
      ∫ y, max (Real.exp (x + y) - K) 0 ∂gaussianReal (-(v₂ : ℝ)/2) v₂
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ‖max (Real.exp (x + y) - K) 0‖ = max (Real.exp (x + y) - K) 0
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine integral_mono (CompoundedFuturesIdentificationProof.gaussian_call_integrable _ _ _) hinner
    fun x => ?_
  -- Jensen in the second variable
  have hexp : Integrable (fun y => Real.exp (x + y)) (gaussianReal (-(v₂ : ℝ)/2) v₂) := by
    have := integrable_exp_mul_gaussianReal (μ := -(v₂ : ℝ)/2) (v := v₂) 1
    simp only [one_mul] at this
    have h2 := this.const_mul (Real.exp x)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    simp [Real.exp_add]
  have hmean : (∫ y, Real.exp (x + y) ∂gaussianReal (-(v₂ : ℝ)/2) v₂) = Real.exp x := by
    have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := -(v₂ : ℝ)/2) (v := v₂)) 1
    simp only [mgf, one_mul] at hmgf
    simp only [Real.exp_add]
    rw [integral_const_mul, hmgf]
    have : -(v₂ : ℝ) / 2 * 1 + (v₂ : ℝ) * 1 ^ 2 / 2 = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  have hg : ConvexOn ℝ (univ : Set ℝ) (fun t => max (t - K) 0) := by
    have h1 : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => t - K) :=
      (convexOn_id convex_univ).sub (concaveOn_const K convex_univ)
    exact h1.sup (convexOn_const 0 convex_univ)
  have hgi : Integrable ((fun t => max (t - K) 0) ∘ fun y => Real.exp (x + y))
      (gaussianReal (-(v₂ : ℝ)/2) v₂) := by
    refine (hexp.add (integrable_const |K|)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (((measurable_const.add measurable_id).exp.sub_const K).max
        measurable_const).aestronglyMeasurable
    · simp only [Function.comp, Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have := neg_abs_le K
      have := le_abs_self (Real.exp (x + y))
      exact max_le (by linarith) (by positivity)
  have hgc : ContinuousOn (fun t : ℝ => max (t - K) 0) univ :=
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  have hJ := hg.map_integral_le hgc isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
    hexp hgi
  rw [hmean] at hJ
  exact hJ

lemma w_four (a b : ℝ) (ha : a < 4) (hb : 4 < b) : w a b 4 = b - 4 := by
  unfold w
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

lemma h_four (a b : ℝ) (ha : a < 4) (hb : 4 < b) : h a b 4 = (b - 4)^2 := by
  unfold h d
  rw [w_four a b ha hb, max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

lemma separation : separationStatement := by
  intro ε a b S hε ha ha4 hb4 hS4 hS5
  have hab : a < b := by linarith
  have hδ : 0 < b - a := by linarith
  have h1 : (1 : ℝ) ≤ S := by linarith
  have h2 : (2 : ℝ) ≤ S := by linarith
  have h3 : (3 : ℝ) ≤ S := by linarith
  have h5 : ¬ (5 : ℝ) ≤ S := by linarith
  have hw4 := w_four a b ha4 hb4
  have hh4 := h_four a b ha4 hb4
  have hq : (q τ5 (v021 ε (3*ε) (2*ε)) S a b : ℝ) - q τ5 (v021 ε ε (2*ε)) S a b =
      (b - 4)^2 * (2 * ε) := by
    simp only [q, NNReal.coe_sum, Fin.sum_univ_five, v021, τ5]
    simp [h1, h2, h3, hS4, h5, hw4]
    simp only [max_eq_left (sq_nonneg (b - 4))]
    ring
  have hp : p τ5 (v021 ε (3*ε) (2*ε)) a b - p τ5 (v021 ε ε (2*ε)) a b = (b - 4)^2 * (2 * ε) := by
    simp only [p, Fin.sum_univ_five, v021, τ5]
    simp [hh4]
    ring
  have hpos : (0 : ℝ) < (b - 4)^2 * (2 * ε) := by
    have : (0 : ℝ) < ε := hε
    positivity
  have hplt : p τ5 (v021 ε ε (2*ε)) a b < p τ5 (v021 ε (3*ε) (2*ε)) a b := by linarith
  have hqle : q τ5 (v021 ε ε (2*ε)) S a b ≤ q τ5 (v021 ε (3*ε) (2*ε)) S a b := by
    have : (q τ5 (v021 ε ε (2*ε)) S a b : ℝ) ≤ q τ5 (v021 ε (3*ε) (2*ε)) S a b := by linarith
    exact_mod_cast this
  have hq2 : 0 < q τ5 (v021 ε ε (2*ε)) S a b := by
    have hterm : (0 : NNReal) < (if τ5 ((3 : Fin 5).val + 1) ≤ S then
        v021 ε ε (2*ε) 3 * ((w a b (τ5 ((3 : Fin 5).val + 1)))^2).toNNReal else 0) := by
      simp only [τ5, v021]
      simp [hS4, hw4]
      exact ⟨hε, pow_pos (by linarith) 2⟩
    unfold q
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun i : Fin 5 => if τ5 (i.val+1) ≤ S then
        v021 ε ε (2*ε) i * ((w a b (τ5 (i.val+1)))^2).toNNReal else 0)
        (fun i _ => bot_le) (Finset.mem_univ (3 : Fin 5)))
  refine ⟨hq, hp, fun ω => ?_, fun A K h0 hAS => ?_⟩
  · rw [F_eq, F_eq]
    simp only
    rw [CompoundedFuturesIdentificationProof.futures_initial τ5 _ τ5_zero τ5_strictMono,
      CompoundedFuturesIdentificationProof.futures_initial τ5 _ τ5_zero τ5_strictMono]
    have : Real.exp (p τ5 (v021 ε ε (2*ε)) a b) < Real.exp (p τ5 (v021 ε (3*ε) (2*ε)) a b) :=
      Real.exp_lt_exp.2 hplt
    have hinv : 0 < (b - a)⁻¹ := inv_pos.2 hδ
    nlinarith
  · rw [Ufut_eq_C0177 τ5 _ τ5_zero τ5_strictMono A S a b K h0 hAS ha hab,
      Ufut_eq_C0177 τ5 _ τ5_zero τ5_strictMono A S a b K h0 hAS ha hab]
    refine div_lt_div_of_pos_right ?_ hδ
    have hG : Real.exp (p τ5 (v021 ε ε (2*ε)) a b) < Real.exp (p τ5 (v021 ε (3*ε) (2*ε)) a b) :=
      Real.exp_lt_exp.2 hplt
    have hG2 : 0 < Real.exp (p τ5 (v021 ε ε (2*ε)) a b) := Real.exp_pos _
    have hG1 : 0 < Real.exp (p τ5 (v021 ε (3*ε) (2*ε)) a b) := Real.exp_pos _
    by_cases hK : 0 < 1 + (b - a) * K
    · calc C0177 (Real.exp (p τ5 (v021 ε ε (2*ε)) a b)) (q τ5 (v021 ε ε (2*ε)) S a b)
            (1 + (b - a) * K)
          < C0177 (Real.exp (p τ5 (v021 ε (3*ε) (2*ε)) a b)) (q τ5 (v021 ε ε (2*ε)) S a b)
            (1 + (b - a) * K) :=
            C0177_strictMono_forward _ hK _ hq2 hG2 hG1 hG
        _ ≤ C0177 (Real.exp (p τ5 (v021 ε (3*ε) (2*ε)) a b)) (q τ5 (v021 ε (3*ε) (2*ε)) S a b)
            (1 + (b - a) * K) := C0177_mono_var hG1 _ hqle
    · rw [C0177_nonpos hG2 (not_lt.mp hK), C0177_nonpos hG1 (not_lt.mp hK)]
      linarith

end Separation

theorem futuresStyleExercise : Standalone.FuturesStyleExercise.statement :=
  ⟨conditional, european, aggregate, noEarlyExercise, closedForm, identification, pair,
    separation⟩

end Novel.FuturesStyleExerciseProof

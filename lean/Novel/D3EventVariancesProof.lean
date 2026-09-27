import Standalone.D3EventVariances
import Upstream.HJMScheduled
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation

/-! # Claim 011: the explicit finite Gaussian construction -/

open MeasureTheory ProbabilityTheory Set
open Standalone.D3EventVariances
open scoped Topology

namespace Novel.D3EventVariancesProof

variable {N : ℕ} {τ : ℕ → ℝ} {v : Fin N → NNReal}

instance : IsProbabilityMeasure (Q v) := by unfold Q; infer_instance

lemma law (i : Fin N) : HasLaw (fun ω : Ω N => ω i) (gaussianReal 0 (v i)) (Q v) :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

lemma indep : iIndepFun (fun (i : Fin N) (ω : Ω N) => ω i) (Q v) :=
  iIndepFun_infinitePi (X := fun (_ : Fin N) (x : ℝ) => x) fun _ => measurable_id

set_option warn.classDefReducibility false in
def coordAlg (A : Set (Fin N)) : MeasurableSpace (Ω N) :=
  ⨆ (i : Fin N) (_ : i ∈ A), MeasurableSpace.comap (fun ω : Ω N => ω i) inferInstance

lemma coordAlg_le (A : Set (Fin N)) : coordAlg A ≤ (MeasurableSpace.pi : MeasurableSpace (Ω N)) :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

lemma measurable_coord {A : Set (Fin N)} {i : Fin N} (hi : i ∈ A) :
    Measurable[coordAlg A] (fun ω : Ω N => ω i) :=
  measurable_iff_comap_le.2 (le_iSup₂_of_le i hi le_rfl)

lemma indep_algs {A B : Set (Fin N)} (h : Disjoint A B) :
    Indep (coordAlg A) (coordAlg B) (Q v) :=
  indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 indep) h

lemma filt_eq (t : ℝ) : filt (N := N) τ t = coordAlg {i | τ (i.val + 1) ≤ t} := rfl

lemma leftLimit_le (i : Fin N) :
    Upstream.leftLimit (filt τ) (τ (i.val + 1)) ≤ coordAlg {j | j ≠ i} := by
  refine iSup₂_le fun t ht => iSup₂_le fun j hj => ?_
  refine le_iSup₂_of_le j ?_ le_rfl
  intro hji
  subst j
  exact (not_le_of_gt ht) hj

lemma indep_left (i : Fin N) :
    Indep (coordAlg {i}) (Upstream.leftLimit (filt τ) (τ (i.val + 1))) (Q v) := by
  refine indep_of_indep_of_le_right (indep_algs ?_) (leftLimit_le i)
  exact Set.disjoint_left.2 fun j hj hj' => hj' (Set.mem_singleton_iff.1 hj)

lemma indep_before (i : Fin N) {t : ℝ} (ht : t < τ (i.val + 1)) :
    Indep (coordAlg {i}) (filt τ t) (Q v) := by
  rw [filt_eq]
  refine indep_algs (Set.disjoint_left.2 fun j hj hj' => ?_)
  subst j
  exact (not_le_of_gt ht) hj'

lemma integral_factor (T : ℝ) (i : Fin N) : ∫ ω, factor τ v T i ω ∂Q v = 1 := by
  have h := mgf_gaussianReal (law (v := v) i) (-(T - τ (i.val + 1)))
  unfold mgf at h
  have heq : factor τ v T i = fun ω =>
      Real.exp (-((v i : ℝ) * (T - τ (i.val + 1)) ^ 2 / 2)) *
        Real.exp (-(T - τ (i.val + 1)) * ω i) := by
    funext ω
    rw [factor, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, h, ← Real.exp_add]
  simp only [zero_mul, zero_add]
  rw [Real.exp_eq_one_iff]
  ring

lemma measurable_factor (T : ℝ) (i : Fin N) : Measurable (factor τ v T i) := by
  unfold factor
  fun_prop

lemma measurable_factor_alg (T : ℝ) {A : Set (Fin N)} {i : Fin N} (hi : i ∈ A) :
    Measurable[coordAlg A] (factor τ v T i) :=
  ((measurable_coord hi).const_mul _ |>.add measurable_const).neg.exp

lemma integral_ξ (i : Fin N) {T : ℝ} (hT : τ (i.val + 1) ≤ T) (ω : Ω N) :
    ∫ u in τ (i.val + 1)..T, ξ τ v i u ω =
      (T - τ (i.val + 1)) * ω i + (v i : ℝ) * (T - τ (i.val + 1)) ^ 2 / 2 := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hT (g := fun u =>
    ω i + (v i : ℝ) * (u - τ (i.val + 1))) (fun u hu => by simp [ξ, hu.1.le])]
  have hi : IntervalIntegrable (fun u : ℝ => (v i : ℝ) * (u - τ (i.val + 1)))
      volume (τ (i.val + 1)) T := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const) hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (f := fun u : ℝ => u)
      (continuous_id.intervalIntegrable _ _) (intervalIntegrable_const),
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma jump_martingale (i : Fin N) {T : ℝ} (hT : τ (i.val + 1) ≤ T) :
    (Q v)[fun ω => Real.exp (-(∫ u in τ (i.val + 1)..T, ξ τ v i u ω)) |
      Upstream.leftLimit (filt τ) (τ (i.val + 1))] =ᵐ[Q v] 1 := by
  simp_rw [integral_ξ i hT]
  have h := condExp_indep_eq (μ := Q v) (f := factor τ v T i) (coordAlg_le {i})
    (Upstream.leftLimit_le (filt τ) (τ (i.val + 1)))
    (measurable_factor_alg T (Set.mem_singleton i)).stronglyMeasurable (indep_left i)
  rw [integral_factor] at h
  exact h

lemma variance_coord (i : Fin N) : Var[fun ω : Ω N => ω i; Q v] = (v i : ℝ) := by
  rw [(law i).variance_eq, variance_id_gaussianReal]

lemma condVar_coord (i : Fin N) {t : ℝ} (ht : t < τ (i.val + 1)) :
    Var[fun ω : Ω N => ω i; Q v | filt τ t] =ᵐ[Q v] fun _ => (v i : ℝ) := by
  have hmean : (Q v)[fun ω : Ω N => ω i | filt τ t] =ᵐ[Q v]
      fun _ => ∫ ω : Ω N, ω i ∂Q v :=
    condExp_indep_eq (coordAlg_le {i}) ((filt τ).le t)
      (measurable_coord (Set.mem_singleton i)).stronglyMeasurable (indep_before i ht)
  have hsq := condExp_indep_eq (μ := Q v)
    (f := fun ω => (ω i - ∫ ω : Ω N, ω i ∂Q v) ^ 2) (coordAlg_le {i}) ((filt τ).le t)
    (((measurable_coord (Set.mem_singleton i)).sub measurable_const).pow_const 2).stronglyMeasurable
    (indep_before i ht)
  have heq : Var[fun ω : Ω N => ω i; Q v | filt τ t] =ᵐ[Q v]
      (Q v)[fun ω => (ω i - ∫ ω : Ω N, ω i ∂Q v) ^ 2 | filt τ t] := by
    apply condExp_congr_ae
    filter_upwards [hmean] with ω hω
    simp only [Pi.pow_apply, Pi.sub_apply]
    rw [hω]
  refine heq.trans (hsq.trans ?_)
  have hv := variance_eq_integral (law (v := v) i).aemeasurable
  rw [variance_coord] at hv
  exact Filter.Eventually.of_forall fun _ => hv.symm

lemma variance_range :
    Set.range (fun w : Fin N → NNReal => fun i => Var[fun ω : Ω N => ω i; Q w]) =
      {w : Fin N → ℝ | ∀ i, 0 ≤ w i} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩ i
    change 0 ≤ Var[fun ω : Ω N => ω i; Q v]
    rw [variance_coord]
    exact (v i).coe_nonneg
  · intro hw
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    funext i
    exact variance_coord i

lemma integral_prod (T : ℝ) (A : Finset (Fin N)) :
    ∫ ω, ∏ i ∈ A, factor τ v T i ω ∂Q v = 1 := by
  have hi : iIndepFun (factor τ v T) (Q v) :=
    indep.comp (fun i x => Real.exp (-((T - τ (i.val + 1)) * x +
      (v i : ℝ) * (T - τ (i.val + 1)) ^ 2 / 2))) (by intro i; fun_prop)
  have h := (hi.precomp (Subtype.val_injective : Function.Injective
    (fun i : A => (i : Fin N)))).integral_fun_prod_eq_prod_integral
      (fun i => (measurable_factor (τ := τ) (v := v) T (i : Fin N)).aestronglyMeasurable)
  simp only [integral_factor, Finset.prod_const_one] at h
  have heq : (fun ω => ∏ i : A, factor τ v T (i : Fin N) ω) =
      fun ω => ∏ i ∈ A, factor τ v T i ω := by
    funext ω
    exact Finset.prod_coe_sort A (fun i => factor τ v T i ω)
  rwa [heq] at h

lemma integrable_prod (T : ℝ) (A : Finset (Fin N)) :
    Integrable (fun ω => ∏ i ∈ A, factor τ v T i ω) (Q v) := by
  by_contra h
  have heq := integral_prod (τ := τ) (v := v) T A
  rw [integral_undef h] at heq
  exact zero_ne_one heq

lemma measurable_prod_alg (T : ℝ) (A : Finset (Fin N)) :
    Measurable[coordAlg (↑A)] (fun ω => ∏ i ∈ A, factor τ v T i ω) :=
  Finset.measurable_prod _ fun _ hi => measurable_factor_alg T hi

lemma past_mono {s t : ℝ} (hst : s ≤ t) : past (N := N) τ s ⊆ past τ t := by
  intro i hi
  simp only [past, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hst

lemma measurable_discounted (T t : ℝ) : Measurable[filt τ t] (discounted τ v T t) := by
  have h : coordAlg (↑(past (N := N) τ t) : Set (Fin N)) = filt τ t := by
    rw [filt_eq]
    congr 1
    ext i
    simp [past]
  change Measurable[filt τ t] (fun ω => ∏ i ∈ past τ t, factor τ v T i ω)
  rw [← h]
  exact measurable_prod_alg T _

lemma condExp_prod (T t : ℝ) (A : Finset (Fin N))
    (hi : Indep (coordAlg (↑A)) (filt τ t) (Q v)) :
    (Q v)[fun ω => ∏ i ∈ A, factor τ v T i ω | filt τ t] =ᵐ[Q v] 1 := by
  calc
    (Q v)[fun ω => ∏ i ∈ A, factor τ v T i ω | filt τ t] =ᵐ[Q v]
        fun _ => ∫ ω, ∏ i ∈ A, factor τ v T i ω ∂Q v := by
      apply condExp_indep_eq (m₁ := coordAlg (↑A))
      · exact coordAlg_le (N := N) (↑A)
      · exact (measurable_prod_alg (τ := τ) (v := v) T A).stronglyMeasurable
      · exact hi
    _ =ᵐ[Q v] 1 := by simp only [integral_prod]; rfl

lemma martingale_discounted (T : ℝ) : Martingale (discounted τ v T) (filt τ) (Q v) := by
  refine ⟨fun t => (measurable_discounted T t).stronglyMeasurable, ?_⟩
  intro s t hst
  let A := past (N := N) τ t \ past τ s
  let g : Ω N → ℝ := fun ω => ∏ i ∈ A, factor τ v T i ω
  have heq : discounted τ v T t = discounted τ v T s * g := by
    funext ω
    exact (mul_comm _ _).trans (Finset.prod_sdiff (past_mono hst)) |>.symm
  have hi : Indep (coordAlg (↑A)) (filt τ s) (Q v) := by
    rw [filt_eq]
    refine indep_algs (Set.disjoint_left.2 fun i hi hj => ?_)
    exact (Finset.mem_sdiff.1 hi).2 (by simpa only [past, Finset.mem_filter,
      Finset.mem_univ, true_and] using (show τ (i.val + 1) ≤ s from hj))
  have hg : (Q v)[g | filt τ s] =ᵐ[Q v] 1 := condExp_prod T s A hi
  rw [heq]
  have hfg : Integrable (discounted τ v T s * g) (Q v) := by
    rw [← heq]
    exact integrable_prod (τ := τ) (v := v) T (past τ t)
  have hp := condExp_mul_of_stronglyMeasurable_left
    (μ := Q v) (f := discounted τ v T s) (g := g)
    (measurable_discounted (τ := τ) (v := v) T s).stronglyMeasurable
    hfg (integrable_prod (τ := τ) (v := v) T A)
  refine hp.trans ?_
  filter_upwards [hg] with ω hω
  simp [Pi.mul_apply, hω]

lemma forward_equation {t T : ℝ} (htT : t ≤ T) (ω : Ω N) :
    f τ v t T ω = ∑ i ∈ past τ t, ξ τ v i T ω := by
  unfold f curve X
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : τ (i.val + 1) ≤ t := (Finset.mem_filter.1 hi).2
  simp [ξ, hi'.trans htT]

lemma curve_injective (t T : ℝ) : Function.Injective (fun x : ℝ => curve τ v t x T) := by
  intro x y hxy
  exact add_right_cancel hxy

lemma integral_forward (t T : ℝ) (ω : Ω N) :
    ∫ u in t..T, f τ v t u ω = (T - t) * X τ t ω +
      ∑ i ∈ past τ t, (v i : ℝ) * ((T - τ (i.val + 1)) ^ 2 - (t - τ (i.val + 1)) ^ 2) / 2 := by
  unfold f curve
  have hi (i : Fin N) : IntervalIntegrable (fun u : ℝ => (v i : ℝ) * (u - τ (i.val + 1)))
      volume t T := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun u => ∑ i ∈ past τ t,
      (v i : ℝ) * (u - τ (i.val + 1))) volume t T := by
    exact (by fun_prop : Continuous (fun u => ∑ i ∈ past τ t,
      (v i : ℝ) * (u - τ (i.val + 1)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hs, intervalIntegral.integral_const,
    intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp only [smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (f := fun u : ℝ => u)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma bond_discounted (t T : ℝ) (ω : Ω N) :
    bond τ v t T ω / Real.exp (logB τ v t ω) = discounted τ v T t ω := by
  rw [bond, ← Real.exp_sub, integral_forward]
  unfold discounted factor
  rw [← Real.exp_sum]
  congr 1
  unfold logB X
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma ξ_integrable (i : Fin N) (T : ℝ) (ω : Ω N) :
    ∫⁻ u in Icc 0 T, ENNReal.ofReal |ξ τ v i u ω| < ⊤ := by
  have hbd : ∀ u ∈ Icc 0 T, |ξ τ v i u ω| ≤
      |ω i| + (v i : ℝ) * (T + |τ (i.val + 1)|) := by
    intro u hu
    have hT : 0 ≤ T := hu.1.trans hu.2
    unfold ξ
    split_ifs
    · refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
      rw [abs_mul, NNReal.abs_eq]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (v i).coe_nonneg
      rw [abs_of_nonneg hu.1]
      exact add_le_add_left hu.2 _
    · simp only [abs_zero]
      positivity
  exact (Upstream.HJMScheduled.setLIntegral_Icc_le hbd).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

lemma measurable_ξ (i : Fin N) :
    Measurable[MeasurableSpace.prod inferInstance (filt τ (τ (i.val + 1)))]
      (fun p : ℝ × Ω N => ξ τ v i p.1 p.2) := by
  have hi : Measurable[filt τ (τ (i.val + 1))] (fun ω : Ω N => ω i) :=
    measurable_iff_comap_le.2 (le_iSup₂_of_le i le_rfl le_rfl)
  apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
    ((hi.comp measurable_snd).add (measurable_const.mul (measurable_fst.sub measurable_const)))
    measurable_const

/-- All standing fields and both axioms hold for the actual zero-diffusion coefficients. -/
noncomputable def instance011 (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) : Upstream.HJMScheduled (Ω N) where
  μ := Q v
  ℱ := filt τ
  d := 1
  N := N
  τ := τ
  τ_zero := hτ0
  τ_strictMono := hτ
  f₀ := fun _ => 0
  α := fun _ _ _ => 0
  σ := fun _ _ _ => 0
  ξ := ξNat τ v
  f₀_measurable := measurable_const
  f₀_locallyIntegrable := fun _ _ => integrableOn_zero
  α_progMeasurable := fun _ => stronglyMeasurable_const
  α_zero_of_lt := fun _ _ _ _ => rfl
  α_integrable := fun _ _ => Filter.Eventually.of_forall fun _ => by simp
  σ_progMeasurable := fun _ => stronglyMeasurable_const
  σ_zero_of_lt := fun _ _ _ _ => rfl
  σ_integrable := fun _ _ => Filter.Eventually.of_forall fun _ => by simp
  ξ_measurable := fun n hn hnN => by
    simp only [ξNat, hn, hnN, and_self, ↓reduceDIte]
    convert measurable_ξ (τ := τ) (v := v) ⟨n - 1, by omega⟩ using 1
    simp [Nat.sub_add_cancel hn]
  ξ_zero_of_lt := fun n hn hnN u ω hu => by
    simp [ξNat, hn, hnN, ξ, Nat.sub_add_cancel hn, not_le_of_gt hu]
  ξ_integrable := fun n hn hnN T _ => Filter.Eventually.of_forall fun ω => by
    simp only [ξNat, hn, hnN, and_self, ↓reduceDIte]
    exact ξ_integrable _ T ω
  drift_integrated := fun _ _ => Filter.Eventually.of_forall fun _ => by simp
  jump_martingale := fun n hn hnN T hT => by
    simp only [ξNat, hn, hnN, and_self, ↓reduceDIte]
    convert jump_martingale (τ := τ) (v := v) ⟨n - 1, by omega⟩
      (T := T) (by simpa [Nat.sub_add_cancel hn] using hT) using 1
    simp [Nat.sub_add_cancel hn]

lemma intervalIntegrable_ξ (i : Fin N) (a b : ℝ) (ω : Ω N) :
    IntervalIntegrable (fun u => ξ τ v i u ω) volume a b := by
  have h : Continuous (fun u : ℝ => ω i + (v i : ℝ) * (u - τ (i.val + 1))) := by fun_prop
  have heq : (fun u => ξ τ v i u ω) = (Ici (τ (i.val + 1))).indicator
      (fun u : ℝ => ω i + (v i : ℝ) * (u - τ (i.val + 1))) := by
    funext u
    simp [ξ, Set.indicator_apply]
  rw [heq]
  exact ⟨(h.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici,
    (h.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici⟩

lemma integral_ξ_zero_to (i : Fin N) (ha : 0 ≤ τ (i.val + 1)) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω N) : ∫ u in (0 : ℝ)..t, ξ τ v i u ω =
      if τ (i.val + 1) ≤ t then
        (t - τ (i.val + 1)) * ω i + (v i : ℝ) * (t - τ (i.val + 1)) ^ 2 / 2 else 0 := by
  have hz {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ τ (i.val + 1)) :
      ∫ u in (0 : ℝ)..b, ξ τ v i u ω = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hb (g := fun _ => 0)
      (fun u hu => by simp [ξ, not_le_of_gt (hu.2.trans_le hb')])]
    simp
  split_ifs with hat
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_ξ i 0 (τ (i.val + 1)) ω)
      (intervalIntegrable_ξ i (τ (i.val + 1)) t ω), hz ha le_rfl, zero_add,
      integral_ξ i hat]
  · exact hz ht (not_le.1 hat).le

lemma short_rate (t : ℝ) (ω : Ω N) : f τ v t t ω = ∑ i, ξ τ v i t ω := by
  rw [forward_equation le_rfl]
  unfold past
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · simp [ξ, hi]

lemma bank_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    {t : ℝ} (ht : 0 ≤ t) (ω : Ω N) : ∫ s in (0 : ℝ)..t, f τ v s s ω = logB τ v t ω := by
  simp_rw [short_rate]
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalIntegrable_ξ i 0 t ω)]
  unfold logB past
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => integral_ξ_zero_to i ?_ ht ω
  rw [← hτ0]
  exact hτ.monotoneOn (by simp) (by simp) (by omega)

lemma state_increment {s t : ℝ} (hst : s ≤ t) (ω : Ω N) :
    X τ t ω = X τ s ω + ∑ i ∈ past τ t \ past τ s, ω i := by
  exact ((add_comm _ _).trans (Finset.sum_sdiff (past_mono hst))).symm

/-- All unrevealed coordinates are independent of the entire current filtration. -/
lemma future_independent (s : ℝ) :
    Indep (coordAlg {i : Fin N | s < τ (i.val + 1)}) (filt τ s) (Q v) := by
  rw [filt_eq]
  refine indep_algs (Set.disjoint_left.2 fun i hi hj => ?_)
  exact (not_le_of_gt (show s < τ (i.val + 1) from hi)) hj

/-- Fixing the first variance leaves all later variance parameters unrestricted. -/
lemma future_variance_range (a : NNReal) :
    Set.range (fun w : Fin N → NNReal => fun i : Fin N =>
      Var[fun ω : Ω (N + 1) => ω i.succ; Q (Fin.cons a w)]) =
        {w : Fin N → ℝ | ∀ i, 0 ≤ w i} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩ i
    change 0 ≤ Var[fun ω : Ω (N + 1) => ω i.succ; Q (Fin.cons a v)]
    rw [variance_coord]
    exact (v i).coe_nonneg
  · intro hw
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    funext i
    change Var[fun ω : Ω (N + 1) => ω i.succ;
      Q (Fin.cons a (fun j => (⟨w j, hw j⟩ : NNReal)))] = w i
    rw [variance_coord]
    rfl

lemma curve_affine (t x T : ℝ) : curve τ v t x T =
    x + (∑ i ∈ past τ t, (v i : ℝ)) * T -
      ∑ i ∈ past τ t, (v i : ℝ) * τ (i.val + 1) := by
  simp [curve, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, add_sub_assoc]

lemma initial_curve (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (T : ℝ) (ω : Ω N) :
    f τ v 0 T ω = 0 := by
  have hp : past (N := N) τ 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hi
    have hpos := hτ (show 0 ∈ Iic N by simp) (show i.val + 1 ∈ Iic N by simp)
      (show 0 < i.val + 1 by omega)
    rw [hτ0] at hpos
    exact (not_le_of_gt hpos) (Finset.mem_filter.1 hi).2
  simp [f, curve, X, hp]

lemma variance_state_first (hN : 2 ≤ N) (hτ : StrictMonoOn τ (Iic N))
    {t : ℝ} (ht1 : τ 1 ≤ t) (ht2 : t < τ 2) :
    Var[X τ t; Q v] = (v ⟨0, by omega⟩ : ℝ) := by
  have hp : past (N := N) τ t = {⟨0, by omega⟩} := by
    ext i
    simp only [past, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      change i.val = 0
      by_contra h
      have h2 : 2 ≤ i.val + 1 := by omega
      have hd := hτ.monotoneOn (show 2 ∈ Iic N from hN)
        (show i.val + 1 ∈ Iic N by simp) h2
      exact (not_le_of_gt ht2) (hd.trans hi)
    · rintro rfl
      exact ht1
  have hx : X τ t = fun ω : Ω N => ω ⟨0, by omega⟩ := by
    funext ω
    simp [X, hp]
  rw [hx]
  exact variance_coord _

lemma ξ_tendsto_left (a : ℝ) (j : Fin N) (ω : Ω N) :
    Filter.Tendsto (fun t => ξ τ v j t ω) (𝓝[<] a)
      (𝓝 (if τ (j.val + 1) < a then ω j + (v j : ℝ) * (a - τ (j.val + 1)) else 0)) := by
  split_ifs with hja
  · have hc : Continuous (fun t : ℝ => ω j + (v j : ℝ) * (t - τ (j.val + 1))) := by fun_prop
    refine (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [(eventually_gt_nhds hja).filter_mono nhdsWithin_le_nhds] with t ht
    simp [ξ, ht.le]
  · refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] a) (𝓝 0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < τ (j.val + 1) := lt_of_lt_of_le ht (not_lt.1 hja)
    simp [ξ, not_le_of_gt ht']

lemma event_jump (hτ : StrictMonoOn τ (Iic N)) (i : Fin N) (ω : Ω N) : Δr τ v i ω = ω i := by
  have hlim : Function.leftLim (fun t => f τ v t t ω) (τ (i.val + 1)) =
      ∑ j : Fin N, if τ (j.val + 1) < τ (i.val + 1) then
        ω j + (v j : ℝ) * (τ (i.val + 1) - τ (j.val + 1)) else 0 := by
    apply leftLim_eq_of_tendsto
    simp_rw [short_rate]
    exact tendsto_finsetSum _ fun j _ => ξ_tendsto_left _ j ω
  rw [Δr, hlim, short_rate, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [ξ]
  · intro j _ hji
    have hne : τ (j.val + 1) ≠ τ (i.val + 1) := by
      intro h
      have hv := hτ.injOn (show j.val + 1 ∈ Iic N by simp)
        (show i.val + 1 ∈ Iic N by simp) h
      exact hji (Fin.ext (by omega))
    by_cases hj : τ (j.val + 1) < τ (i.val + 1)
    · simp [ξ, hj, hj.le]
    · simp [ξ, hj, not_le.2 (lt_of_le_of_ne (not_lt.1 hj) hne.symm)]
  · simp

theorem d3EventVariances : Standalone.D3EventVariances.statement := by
  intro N τ v hτ0 hτ
  refine ⟨fun i T hT => jump_martingale i hT, martingale_discounted,
    fun _ ω ht => bank_integral hτ0 hτ ht ω,
    bond_discounted, fun _ _ ω h => forward_equation h ω, curve_injective,
    fun _ _ ω hst => state_increment hst ω,
    event_jump hτ, fun i _ ht => ?_, variance_range⟩
  have heq : Δr τ v i = fun ω => ω i := funext (event_jump hτ i)
  rw [heq]
  exact condVar_coord i ht

end Novel.D3EventVariancesProof

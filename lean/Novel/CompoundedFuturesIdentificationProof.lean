import Standalone.CompoundedFuturesIdentification
import Novel.BondOptionMeetingVariancesProof
import Novel.BondOptionPriceIntervalsProof
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology
open Standalone.CompoundedFuturesIdentification
namespace Novel.CompoundedFuturesIdentificationProof
set_option maxHeartbeats 800000
variable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)

lemma short_rate_eq (t : ℝ) (ω : Ω N) : r τ v t ω = Standalone.D3EventVariances.f τ v t t ω := by
  rw [D3EventVariancesProof.short_rate]
  rfl
lemma rate_integrable (a b : ℝ) (ω : Ω N) : IntervalIntegrable (fun u => r τ v u ω) volume a b := by
  have he : (fun u => r τ v u ω) = ∑ i, fun u => Standalone.D3EventVariances.ξ τ v i u ω := by
    funext u
    simp [r, Standalone.D3EventVariances.ξ]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ (fun i _ => D3EventVariancesProof.intervalIntegrable_ξ (τ := τ) (v := v) i a b ω)
lemma bank_eq (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (t : ℝ) (ht : 0 ≤ t) (ω : Ω N) :
    logB τ v t ω = Standalone.D3EventVariances.logB τ v t ω := by
  simp only [logB, short_rate_eq]
  exact D3EventVariancesProof.bank_integral hτ0 hτ ht ω
lemma bank_positive_parts (t : ℝ) (ω : Ω N) :
    Standalone.D3EventVariances.logB τ v t ω =
      ∑ i, (max (t-τ (i.val+1)) 0 * ω i + (v i : ℝ)*(max (t-τ (i.val+1)) 0)^2/2) := by
  simp only [Standalone.D3EventVariances.logB, Standalone.D3EventVariances.past, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : τ (i.val+1) ≤ t
  · simp [ht]
  · simp [ht, max_eq_right (sub_nonpos.2 (not_le.1 ht).le)]
lemma accrual_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (ω : Ω N) :
    (∫ u in a..b, r τ v u ω) =
      ∑ i, (w a b (τ (i.val+1))*ω i + d a b (τ (i.val+1))*(v i : ℝ)) := by
  have he := intervalIntegral.integral_add_adjacent_intervals (rate_integrable τ v 0 a ω)
    (rate_integrable τ v a b ω)
  change logB τ v a ω + (∫ u in a..b, r τ v u ω) = logB τ v b ω at he
  rw [bank_eq τ v hτ0 hτ a ha, bank_eq τ v hτ0 hτ b (ha.trans hab.le),
    bank_positive_parts, bank_positive_parts] at he
  rw [eq_sub_iff_add_eq.mpr (by linarith : (∫ u in a..b, r τ v u ω) +
    (∑ i, (max (a-τ (i.val+1)) 0 * ω i + (v i : ℝ)*(max (a-τ (i.val+1)) 0)^2/2)) =
    ∑ i, (max (b-τ (i.val+1)) 0 * ω i + (v i : ℝ)*(max (b-τ (i.val+1)) 0)^2/2)),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [w, d]
  ring

instance : IsProbabilityMeasure (Q v) := by unfold Q; infer_instance

noncomputable def D0175 (a : Fin N → ℝ) (I : Finset (Fin N)) (ω : Ω N) : ℝ :=
  Real.exp (∑ i ∈ I, (a i * ω i - (v i : ℝ) * a i ^ 2 / 2))
lemma D0175_eq (a : Fin N → ℝ) (I : Finset (Fin N)) :
    D0175 v a I = Standalone.BondOptionMeetingVariances.D0148 v (fun i => if i ∈ I then a i else 0) := by
  classical
  ext ω
  simp [D0175, Standalone.BondOptionMeetingVariances.D0148, ite_mul, ite_pow, ite_div]
lemma integral_D0175 (a : Fin N → ℝ) (I : Finset (Fin N)) : ∫ ω, D0175 v a I ω ∂Q v = 1 := by
  rw [D0175_eq]
  exact BondOptionMeetingVariancesProof.integral_D0148 _
lemma integrable_D0175 (a : Fin N → ℝ) (I : Finset (Fin N)) : Integrable (D0175 v a I) (Q v) := by
  rw [D0175_eq]
  exact BondOptionMeetingVariancesProof.integrable_D0148 _
lemma measurable_D0175 (a : Fin N → ℝ) (I : Finset (Fin N)) :
    Measurable[D3EventVariancesProof.coordAlg (↑I)] (D0175 v a I) := by
  apply Measurable.exp
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_const.mul (D3EventVariancesProof.measurable_coord hi)).sub measurable_const
lemma D0175_split (a : Fin N → ℝ) (I : Finset (Fin N)) :
    D0175 v a Finset.univ = D0175 v a I * D0175 v a (Finset.univ \ I) := by
  ext ω
  simp only [Pi.mul_apply, D0175, ← Real.exp_add]
  congr 1
  exact (Finset.sum_add_sum_compl I (fun i => a i * ω i - (v i : ℝ) * a i ^ 2 / 2)).symm
lemma q_sum (S a b : ℝ) : (q τ v S a b : ℝ) = ∑ i, k S a b (τ (i.val+1)) * v i := by
  simp only [q, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [k, *, Real.coe_toNNReal _ (sq_nonneg _), mul_comm]
lemma G_D0175 (t a b : ℝ) :
    G τ v t a b = fun ω => Real.exp (p τ v a b) *
      D0175 v (fun i => w a b (τ (i.val+1))) (Standalone.D3EventVariances.past τ t) ω := by
  ext ω
  simp only [G, L0175, D0175, ← Real.exp_add, Standalone.D3EventVariances.past,
    Finset.sum_filter, q_sum, k]
  congr 1
  have he : (∑ i, if τ (i.val+1) ≤ t then
      w a b (τ (i.val+1))*ω i - (v i : ℝ)*(w a b (τ (i.val+1)))^2/2 else 0) =
      (∑ i, if τ (i.val+1) ≤ t then w a b (τ (i.val+1))*ω i else 0) -
      (∑ i, (if τ (i.val+1) ≤ t then (w a b (τ (i.val+1)))^2 else 0)*(v i : ℝ))/2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he]
  abel

lemma terminal_D0175 (a b : ℝ) (ω : Ω N) :
    Real.exp (∑ i, (w a b (τ (i.val+1))*ω i + d a b (τ (i.val+1))*(v i : ℝ))) =
      Real.exp (p τ v a b) * D0175 v (fun i => w a b (τ (i.val+1))) Finset.univ ω := by
  simp only [D0175, p, h, ← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma condExp_D0175 (a : Fin N → ℝ) (t : ℝ) :
    (Q v)[D0175 v a Finset.univ | filt τ t] =ᵐ[Q v]
      D0175 v a (Standalone.D3EventVariances.past τ t) := by
  let I := Standalone.D3EventVariances.past (N := N) τ t
  have hI : D3EventVariancesProof.coordAlg (↑I : Set (Fin N)) = filt τ t := by
    change D3EventVariancesProof.coordAlg (↑I : Set (Fin N)) = Standalone.D3EventVariances.filt τ t
    rw [D3EventVariancesProof.filt_eq]
    congr 1
    ext i
    simp [I, Standalone.D3EventVariances.past]
  have hmeas : Measurable[filt τ t] (D0175 v a I) := hI ▸ measurable_D0175 v a I
  have hi : Indep (D3EventVariancesProof.coordAlg (↑(Finset.univ \ I))) (filt τ t) (Q v) := by
    rw [← hI]
    exact D3EventVariancesProof.indep_algs (by
      simp only [Finset.coe_sdiff, Finset.coe_univ]
      exact disjoint_sdiff_left)
  have hr : (Q v)[D0175 v a (Finset.univ \ I) | filt τ t] =ᵐ[Q v] 1 := by
    calc
      (Q v)[D0175 v a (Finset.univ \ I) | filt τ t] =ᵐ[Q v]
          fun _ => ∫ ω, D0175 v a (Finset.univ \ I) ω ∂Q v := by
        apply condExp_indep_eq (m₁ := D3EventVariancesProof.coordAlg (↑(Finset.univ \ I)))
        · exact D3EventVariancesProof.coordAlg_le _
        · exact (measurable_D0175 v a _).stronglyMeasurable
        · exact hi
      _ =ᵐ[Q v] 1 := by simp only [integral_D0175]; rfl
  rw [D0175_split v a I]
  have hp := condExp_mul_of_stronglyMeasurable_left (μ := Q v)
    hmeas.stronglyMeasurable
    (D0175_split v a I ▸ integrable_D0175 v a Finset.univ)
    (integrable_D0175 v a (Finset.univ \ I))
  refine hp.trans ?_
  filter_upwards [hr] with ω hω
  simp [Pi.mul_apply, hω, I]

lemma futures_condExp (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (t : ℝ) :
    (Q v)[fun ω => Real.exp (∫ u in a..b, r τ v u ω) | filt τ t] =ᵐ[Q v] G τ v t a b := by
  simp_rw [accrual_integral τ v hτ0 hτ a b ha hab, terminal_D0175 τ v a b]
  have he := condExp_smul (μ := Q v) (m := filt τ t) (Real.exp (p τ v a b))
    (D0175 v (fun i => w a b (τ (i.val+1))) Finset.univ)
  rw [G_D0175]
  have hc := condExp_D0175 τ v (fun i => w a b (τ (i.val+1))) t
  filter_upwards [he, hc] with ω he hc
  simpa only [Pi.smul_def, smul_eq_mul, hc] using he

lemma filt_coord (t : ℝ) :
    D3EventVariancesProof.coordAlg (↑(Standalone.D3EventVariances.past (N := N) τ t) : Set (Fin N)) = filt τ t := by
  change _ = Standalone.D3EventVariances.filt τ t
  rw [D3EventVariancesProof.filt_eq]
  congr 1
  ext i
  simp [Standalone.D3EventVariances.past]

lemma futures_measurable (t a b : ℝ) : Measurable[filt τ t] (G τ v t a b) := by
  rw [G_D0175]
  exact measurable_const.mul (filt_coord τ t ▸ measurable_D0175 v _ _)

lemma futures_integrable (t a b : ℝ) : Integrable (G τ v t a b) (Q v) := by
  rw [G_D0175]
  exact (integrable_D0175 v _ _).const_mul _

lemma accrual_exp_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω => Real.exp (∫ u in a..b, r τ v u ω)) (Q v) := by
  simp_rw [accrual_integral τ v hτ0 hτ a b ha hab, terminal_D0175 τ v a b]
  exact (integrable_D0175 v _ _).const_mul _

lemma futures_martingale (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Martingale (fun t => G τ v t a b) (filt τ) (Q v) := by
  exact (martingale_condExp (fun ω => Real.exp (∫ u in a..b, r τ v u ω)) (filt τ) (Q v)).congr
    (fun t => (futures_measurable τ v t a b).stronglyMeasurable)
    (futures_condExp τ v hτ0 hτ a b ha hab)

lemma futures_initial (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (a b : ℝ) (ω : Ω N) :
    G τ v 0 a b ω = Real.exp (p τ v a b) := by
  have hp : Standalone.D3EventVariances.past (N := N) τ 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hi
    have ht : 0 < τ (i.val+1) := by
      rw [← hτ0]
      exact hτ (by simp) (by simp) (by omega)
    simp only [Standalone.D3EventVariances.past, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    linarith
  rw [G_D0175, hp]
  simp [D0175]

lemma QS_eq (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S : ℝ) (hS : 0 ≤ S) :
    QS τ v S = Standalone.BondOptionMeetingVariances.Q0148 v (BondOptionMeetingVariancesProof.a0148 τ S) := by
  have he : QS τ v S = Standalone.BondOptionMeetingVariances.QS τ v S := by
    unfold QS Standalone.BondOptionMeetingVariances.QS
    congr 1
    funext ω
    rw [bank_eq τ v hτ0 hτ S hS]
  rw [he, BondOptionMeetingVariancesProof.QS_eq]

lemma mean_eq (S a b : ℝ) :
    (p τ v a b - (q τ v S a b : ℝ)/2) +
      ∑ i, (if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0) * (v i : ℝ) *
        BondOptionMeetingVariancesProof.a0148 τ S i =
      Real.log (m τ v S a b) - (q τ v S a b : ℝ)/2 := by
  have he : (∑ i, (if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0) * (v i : ℝ) *
        BondOptionMeetingVariancesProof.a0148 τ S i) = -z τ v S a b := by
    rw [z, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [BondOptionMeetingVariancesProof.a0148, Standalone.D3EventVariances.past,
      Finset.mem_filter, Finset.mem_univ, true_and, j]
    split_ifs <;> ring
  rw [he, m, Real.log_exp]
  ring

lemma variance_eq (S a b : ℝ) :
    (∑ i, v i * ((if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0)^2).toNNReal) = q τ v S a b := by
  unfold q
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma law_logG (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S a b : ℝ) (hS : 0 ≤ S) :
    HasLaw (fun ω => Real.log (G τ v S a b ω))
      (gaussianReal (Real.log (m τ v S a b) - (q τ v S a b : ℝ)/2) (q τ v S a b)) (QS τ v S) := by
  rw [QS_eq τ v hτ0 hτ S hS]
  have he := BondOptionMeetingVariancesProof.law_L0149 (v := v)
    (BondOptionMeetingVariancesProof.a0148 τ S)
    (fun i => if τ (i.val+1) ≤ S then w a b (τ (i.val+1)) else 0)
    (p τ v a b - (q τ v S a b : ℝ)/2)
  rw [mean_eq, variance_eq] at he
  convert he using 1
  funext ω
  simp only [G, Real.log_exp, L0175, Standalone.BondOptionMeetingVariances.L0149]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma price_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S a b K : ℝ) (hS : 0 ≤ S) :
    C τ v S a b K = ∫ x, max (Real.exp x-K) 0
      ∂gaussianReal (Real.log (m τ v S a b) - (q τ v S a b : ℝ)/2) (q τ v S a b) := by
  have he := (law_logG τ v hτ0 hτ S a b hS).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (Real.exp x-K) 0) _)
  rw [QS_eq τ v hτ0 hτ S hS, BondOptionMeetingVariancesProof.integral_Q0148] at he
  convert he using 1
  unfold C
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [BondOptionMeetingVariancesProof.density_eq, bank_eq τ v hτ0 hτ S hS,
    Function.comp_apply, Real.exp_log (show 0 < G τ v S a b ω from Real.exp_pos _)]

lemma C0177_scale {M : ℝ} (hM : 0 < M) (R : NNReal) (K : ℝ) :
    C0177 M R K = M * ∫ x, max (Real.exp x-K/M) 0 ∂gaussianReal (-(R : ℝ)/2) R := by
  have hlaw : HasLaw (fun x : ℝ => Real.log M+x)
      (gaussianReal (Real.log M-(R : ℝ)/2) R) (gaussianReal (-(R : ℝ)/2) R) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [sub_eq_add_neg, add_comm, neg_div] using
      (gaussianReal_map_const_add (μ := -(R : ℝ)/2) (v := R) (Real.log M))
  rw [C0177, ← hlaw.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (Real.exp x-K) 0) _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, Real.exp_add, Real.exp_log hM]
  rw [mul_max_of_nonneg _ _ hM.le]
  congr 1 <;> field_simp <;> ring

lemma C0177_zero {M : ℝ} (hM : 0 < M) (K : ℝ) : C0177 M 0 K = max (M-K) 0 := by
  simp [C0177, gaussianReal_zero_var, Real.exp_log hM]

lemma C0177_pos {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    C0177 M R K = M * Φ ((Real.log (M/K)+(R : ℝ)/2)/Real.sqrt R) -
      K * Φ (((Real.log (M/K)+(R : ℝ)/2)/Real.sqrt R)-Real.sqrt R) := by
  have hs : Real.sqrt (R : ℝ) ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have he : (-(R : ℝ)/2-Real.log (K/M))/Real.sqrt R =
      ((Real.log (M/K)+(R : ℝ)/2)/Real.sqrt R)-Real.sqrt R := by
    rw [Real.log_div hK.ne' hM.ne', Real.log_div hM.ne' hK.ne']
    apply (div_eq_iff hs).2
    field_simp
    nlinarith [Real.sq_sqrt R.coe_nonneg]
  rw [C0177_scale hM, BondOptionMeetingVariancesProof.integral_call_gaussian R (div_pos hK hM) hR, he]
  have he' : (R : ℝ)/2-Real.log (K/M) = Real.log (M/K)+(R : ℝ)/2 := by
    rw [Real.log_div hK.ne' hM.ne', Real.log_div hM.ne' hK.ne']; ring
  rw [he']
  change M * (Φ _ - K/M*Φ _) = _
  field_simp

lemma C0177_at_mean {M : ℝ} (hM : 0 < M) (R : NNReal) :
    C0177 M R M / M = 2 * Φ (Real.sqrt R/2)-1 := by
  by_cases hR : R = 0
  · subst R
    rw [C0177_zero hM]
    change max (M-M) 0 / M = 2 * Standalone.BondOptionMeetingVariances.Φ (Real.sqrt (0 : NNReal)/2)-1
    simp [BondOptionMeetingVariancesProof.Φ_zero]
  · have hr := pos_iff_ne_zero.2 hR
    have hs : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 hr
    have he : (R : ℝ)/2/Real.sqrt R = Real.sqrt R/2 := by
      apply (div_eq_iff hs.ne').2
      nlinarith [Real.sq_sqrt R.coe_nonneg]
    rw [C0177_pos hM hM R hr]
    simp only [div_self hM.ne', Real.log_one, zero_add, he]
    have he' : Real.sqrt (R : ℝ)/2-Real.sqrt R = -(Real.sqrt R/2) := by ring
    rw [he']
    change (M * Φ _ - M * Standalone.BondOptionMeetingVariances.Φ (-_))/M = _
    rw [BondOptionMeetingVariancesProof.Φ_neg]
    change (M * Φ _ - M * (1-Φ _))/M = _
    field_simp
    ring

lemma C0177_recover_q {M : ℝ} (hM : 0 < M) (R : NNReal) : q0178 M (C0177 M R M) = (R : ℝ) := by
  rw [q0178, C0177_at_mean hM]
  have he (x : ℝ) : (1+(2*x-1))/2 = x := by ring
  rw [he, Function.leftInverse_invFun (show Function.Injective Φ from BondOptionMeetingVariancesProof.Φ_strictMono.injective)]
  nlinarith [Real.sq_sqrt R.coe_nonneg]

lemma gaussian_call_integrable (μ : ℝ) (R : NNReal) (K : ℝ) :
    Integrable (fun x => max (Real.exp x-K) 0) (gaussianReal μ R) := by
  have he : Integrable Real.exp (gaussianReal μ R) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := μ) (v := R) 1)
  refine (he.add (integrable_const |K|)).mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  change max (Real.exp x-K) 0 ≤ Real.exp x+|K|
  exact max_le (by linarith [neg_le_abs K]) (by positivity)

lemma C0177_mean {M : ℝ} (hM : 0 < M) (R : NNReal) :
    ∫ x, Real.exp x ∂gaussianReal (Real.log M-(R : ℝ)/2) R = M := by
  have he := congrFun (mgf_fun_id_gaussianReal (μ := Real.log M-(R : ℝ)/2) (v := R)) 1
  simpa [mgf, Real.exp_log hM] using he

lemma C0177_bounds {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K) (R : NNReal) :
    M-K ≤ C0177 M R K ∧ C0177 M R K ≤ M := by
  have hi : Integrable Real.exp (gaussianReal (Real.log M-(R : ℝ)/2) R) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := Real.log M-(R : ℝ)/2) (v := R) 1)
  have hc := gaussian_call_integrable (Real.log M-(R : ℝ)/2) R K
  constructor
  · calc M-K = ∫ x, (Real.exp x-K) ∂gaussianReal (Real.log M-(R : ℝ)/2) R := by
          rw [integral_sub hi (integrable_const K), C0177_mean hM, integral_const]; simp
         _ ≤ C0177 M R K := integral_mono (hi.sub (integrable_const K)) hc (fun x => le_max_left _ _)
  · calc C0177 M R K ≤ ∫ x, Real.exp x ∂gaussianReal (Real.log M-(R : ℝ)/2) R :=
          integral_mono hc hi (fun x => max_le (by linarith) (Real.exp_pos x).le)
         _ = M := C0177_mean hM R

lemma C0177_limit {M : ℝ} (hM : 0 < M) (R : NNReal) :
    Tendsto (C0177 M R) (𝓝[>] 0) (𝓝 M) := by
  have hlow : Tendsto (fun K : ℝ => M-K) (𝓝[>] 0) (𝓝 M) := by
    have hk : Tendsto (fun K : ℝ => K) (𝓝[>] 0) (𝓝 (0 : ℝ)) := nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub hk
  exact hlow.squeeze' tendsto_const_nhds
    ((show ∀ᶠ K : ℝ in 𝓝[>] 0, 0 < K from self_mem_nhdsWithin).mono fun K hK => (C0177_bounds hM hK.le R).1)
    ((show ∀ᶠ K : ℝ in 𝓝[>] 0, 0 < K from self_mem_nhdsWithin).mono fun K hK => (C0177_bounds hM hK.le R).2)

lemma C0177_surface {M M' : ℝ} (hM : 0 < M) (hM' : 0 < M') (R R' : NNReal) :
    (∀ K, 0 < K → C0177 M R K = C0177 M' R' K) ↔ M = M' ∧ R = R' := by
  constructor
  · intro he
    have hm : M = M' := tendsto_nhds_unique (C0177_limit hM R)
      ((C0177_limit hM' R').congr' ((show ∀ᶠ K : ℝ in 𝓝[>] 0, 0 < K from self_mem_nhdsWithin).mono fun K hK => (he K hK).symm))
    subst M'
    refine ⟨rfl, NNReal.coe_injective ?_⟩
    rw [← C0177_recover_q hM R, ← C0177_recover_q hM R', he M hM]
  · rintro ⟨rfl, rfl⟩ K _; rfl

lemma price_eq_C0177 (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S a b K : ℝ) (hS : 0 ≤ S) :
    C τ v S a b K = C0177 (m τ v S a b) (q τ v S a b) K := price_integral τ v hτ0 hτ S a b K hS

lemma integrable_price (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S a b K : ℝ) (hS : 0 ≤ S) :
    Integrable (fun ω => Real.exp (-logB τ v S ω) * max (G τ v S a b ω-K) 0) (Q v) := by
  have he := (law_logG τ v hτ0 hτ S a b hS).integrable_comp
    (gaussian_call_integrable (Real.log (m τ v S a b)-(q τ v S a b : ℝ)/2) (q τ v S a b) K)
  have hg : (fun x => max (Real.exp x-K) 0) ∘ (fun ω => Real.log (G τ v S a b ω)) =
      fun ω => max (G τ v S a b ω-K) 0 := by
    funext ω
    simp only [Function.comp_apply, G, Real.log_exp]
  rw [hg, QS] at he
  have hd : Measurable (fun ω => ENNReal.ofReal (Real.exp (-logB τ v S ω))) := by
    simp_rw [bank_eq τ v hτ0 hτ S hS]
    unfold Standalone.D3EventVariances.logB
    fun_prop
  have hi := (integrable_withDensity_iff_integrable_smul' hd (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 he
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using hi

lemma surface_iff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (v' : Fin N → NNReal) (S a b : ℝ) (hS : 0 ≤ S) :
    (∀ K, 0 < K → C τ v S a b K = C τ v' S a b K) ↔
      m τ v S a b = m τ v' S a b ∧ q τ v S a b = q τ v' S a b := by
  simp_rw [price_eq_C0177 τ _ hτ0 hτ S a b _ hS]
  exact C0177_surface (Real.exp_pos _) (Real.exp_pos _) _ _

lemma observations_iff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (v' : Fin N → NNReal) (S a b : ℝ) (hS : 0 ≤ S) (ω : Ω N) :
    (G τ v 0 a b ω = G τ v' 0 a b ω ∧ ∀ K, 0 < K → C τ v S a b K = C τ v' S a b K) ↔
      p τ v a b = p τ v' a b ∧ z τ v S a b = z τ v' S a b ∧ q τ v S a b = q τ v' S a b := by
  rw [futures_initial τ v hτ0 hτ, futures_initial τ v' hτ0 hτ, Real.exp_eq_exp,
    surface_iff τ v hτ0 hτ v' S a b hS]
  simp only [m, Real.exp_eq_exp]
  constructor
  · rintro ⟨hp, hm, hq⟩
    exact ⟨hp, by linarith, hq⟩
  · rintro ⟨hp, hz, hq⟩
    exact ⟨hp, by rw [hp, hz], hq⟩

lemma w_nonneg {a b T : ℝ} (hab : a ≤ b) : 0 ≤ w a b T :=
  sub_nonneg.2 (max_le_max (sub_le_sub_right hab T) le_rfl)

lemma h_eq (a b T : ℝ) : h a b T = w a b T * max (b-T) 0 := by
  dsimp [h, d, w]
  ring

lemma h_sub_j_nonneg {S a b T : ℝ} (hab : a ≤ b) (hSb : S ≤ b) :
    0 ≤ h a b T - j S a b T := by
  rw [h_eq]
  by_cases hT : T ≤ S
  · rw [j, ite_eq_left hT, max_eq_left (sub_nonneg.2 (hT.trans hSb)), ← mul_sub]
    exact mul_nonneg (w_nonneg hab) (by linarith)
  · rw [j, ite_eq_right hT, sub_zero]
    exact mul_nonneg (w_nonneg hab) (le_max_right _ _)

lemma mean_ge_one {S a b : ℝ} (hab : a ≤ b) (hSb : S ≤ b) : 1 ≤ m τ v S a b := by
  rw [m, Real.one_le_exp_iff, p, z, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [← sub_mul]
  exact mul_nonneg (h_sub_j_nonneg hab hSb) (v i).coe_nonneg

lemma futures_formula (t a b : ℝ) (ω : Ω N) :
    G τ v t a b ω = Real.exp
      ((∑ i, if τ (i.val+1) ≤ t then w a b (τ (i.val+1))*ω i else 0) +
        (∑ i, d a b (τ (i.val+1))*(v i : ℝ)) +
        (∑ i, if τ (i.val+1) ≤ t then 0 else (w a b (τ (i.val+1)))^2*(v i : ℝ))/2) := by
  simp only [G, L0175, p, q_sum, k]
  congr 1
  simp only [h, add_mul, Finset.sum_add_distrib, Finset.sum_div]
  have he : (∑ i, (w a b (τ (i.val+1)))^2/2*(v i : ℝ)) -
      (∑ i, (if τ (i.val+1) ≤ t then (w a b (τ (i.val+1)))^2 else 0)*(v i : ℝ)/2) =
      (∑ i, (if τ (i.val+1) ≤ t then 0 else (w a b (τ (i.val+1)))^2*(v i : ℝ))/2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  linarith

lemma matrix_rows {L : ℕ} (S a b : Fin L → ℝ) (l : Fin L) :
    (M0179 τ S a b *ᵥ (fun i => (v i : ℝ))) (l, 0) = p τ v (a l) (b l) ∧
    (M0179 τ S a b *ᵥ (fun i => (v i : ℝ))) (l, 1) = z τ v (S l) (a l) (b l) ∧
    (M0179 τ S a b *ᵥ (fun i => (v i : ℝ))) (l, 2) = (q τ v (S l) (a l) (b l) : ℝ) := by
  simp [M0179, Matrix.mulVec, dotProduct, p, z, q_sum]

lemma panel_iff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) {L : ℕ}
    (S a b : Fin L → ℝ) (hS : ∀ l, 0 ≤ S l) (v' : Fin N → NNReal) (ω : Ω N) :
    (∀ l, G τ v 0 (a l) (b l) ω = G τ v' 0 (a l) (b l) ω ∧
      ∀ K, 0 < K → C τ v (S l) (a l) (b l) K = C τ v' (S l) (a l) (b l) K) ↔
    M0179 τ S a b *ᵥ (fun i => (v i : ℝ)) = M0179 τ S a b *ᵥ (fun i => (v' i : ℝ)) := by
  simp_rw [observations_iff τ v hτ0 hτ v' _ _ _ (hS _) ω]
  constructor
  · intro he
    ext ⟨l, k⟩
    have hv := matrix_rows τ v S a b l
    have hv' := matrix_rows τ v' S a b l
    fin_cases k
    · exact hv.1.trans ((he l).1.trans hv'.1.symm)
    · exact hv.2.1.trans ((he l).2.1.trans hv'.2.1.symm)
    · exact hv.2.2.trans ((congrArg NNReal.toReal (he l).2.2).trans hv'.2.2.symm)
  · intro he l
    have hv := matrix_rows τ v S a b l
    have hv' := matrix_rows τ v' S a b l
    exact ⟨by rw [← hv.1, ← hv'.1, he], by rw [← hv.2.1, ← hv'.2.1, he],
      NNReal.coe_injective (by rw [← hv.2.2, ← hv'.2.2, he])⟩

lemma matrix_rank_injective {J : Type*} [Fintype J] (A : Matrix J (Fin N) ℝ) :
    A.rank = N ↔ Function.Injective A.mulVecLin := by
  have hr := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  simp only [Module.finrank_pi, Fintype.card_fin] at hr
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  change Module.finrank ℝ (LinearMap.range A.mulVecLin) = N ↔ _
  omega

lemma matrix_injective_nonneg {J : Type*} [Fintype J] (A : Matrix J (Fin N) ℝ) :
    Function.Injective (fun x : Fin N → NNReal => A *ᵥ (fun i => (x i : ℝ))) ↔ A.rank = N := by
  rw [matrix_rank_injective]
  constructor
  · intro hi
    apply LinearMap.ker_eq_bot.1
    apply (Submodule.eq_bot_iff _).2
    intro x hx
    have hzero : A *ᵥ x = 0 := hx
    let xp : Fin N → NNReal := fun i => (x i).toNNReal
    let xn : Fin N → NNReal := fun i => (-x i).toNNReal
    have he : (fun i => (xp i : ℝ)) - (fun i => (xn i : ℝ)) = x := by
      ext i
      simp only [Pi.sub_apply, xp, xn, Real.coe_toNNReal']
      rcases le_total 0 (x i) with hp | hn <;>
        simp [max_eq_left, max_eq_right, *, neg_nonpos, neg_nonneg]
    have hae : A *ᵥ (fun i => (xp i : ℝ)) = A *ᵥ (fun i => (xn i : ℝ)) := by
      rw [← sub_eq_zero, ← Matrix.mulVec_sub, he, hzero]
    have hh := hi hae
    rw [← he, hh, sub_self]
  · intro hi x y hxy
    have he := hi hxy
    funext i
    exact NNReal.coe_injective (congrFun he i)

lemma matrix_positive_perturbation {J : Type*} [Fintype J] (A : Matrix J (Fin N) ℝ)
    (hr : A.rank ≠ N) (x : Fin N → NNReal) (hx : ∀ i, 0 < x i) :
    ∃ y : Fin N → NNReal, (∀ i, 0 < y i) ∧ y ≠ x ∧
      A *ᵥ (fun i => (y i : ℝ)) = A *ᵥ (fun i => (x i : ℝ)) := by
  have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro he
    exact hr ((matrix_rank_injective A).2 (LinearMap.ker_eq_bot.1 he))
  obtain ⟨u, hu, hun⟩ := (Submodule.ne_bot_iff _).1 hk
  have hAu : A *ᵥ u = 0 := hu
  have hev : ∀ᶠ e : ℝ in 𝓝 0, ∀ i, 0 < (x i : ℝ)+e*u i := by
    rw [Filter.eventually_all]
    intro i
    have ht : Tendsto (fun e : ℝ => (x i : ℝ)+e*u i) (𝓝 0) (𝓝 (x i : ℝ)) := by
      have hc : Continuous (fun e : ℝ => (x i : ℝ)+e*u i) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact ht.eventually (Ioi_mem_nhds (hx i))
  have hev' : ∀ᶠ e : ℝ in 𝓝[>] 0, (∀ i, 0 < (x i : ℝ)+e*u i) ∧ 0 < e :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨e, he, hepos⟩ := hev'.exists
  let y : Fin N → NNReal := fun i => ⟨(x i : ℝ)+e*u i, (he i).le⟩
  refine ⟨y, he, ?_, ?_⟩
  · intro hy
    apply hun
    ext i
    have heq := congrArg (fun f : Fin N → NNReal => (f i : ℝ)) hy
    change (x i : ℝ)+e*u i = x i at heq
    have hh : e*u i = 0 := by linarith
    exact (mul_eq_zero.1 hh).resolve_left hepos.ne'
  · change A *ᵥ ((fun i => (x i : ℝ)) + e • u) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAu, smul_zero, add_zero]

noncomputable def D01713 (M : ℝ) (R : NNReal) (K : ℝ) : ℝ :=
  (Real.log M-Real.log K-(R : ℝ)/2)/Real.sqrt R

lemma C0177_pos' {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    C0177 M R K = M * Φ (D01713 M R K+Real.sqrt R)-K*Φ (D01713 M R K) := by
  rw [C0177_pos hM hK R hR, Real.log_div hM.ne' hK.ne']
  have hs : Real.sqrt (R : ℝ) ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have he : (Real.log M-Real.log K+(R : ℝ)/2)/Real.sqrt R = D01713 M R K+Real.sqrt R := by
    dsimp [D01713]
    apply (div_eq_iff hs).2
    field_simp
    nlinarith [Real.sq_sqrt R.coe_nonneg]
  rw [he, add_sub_cancel_right]

lemma density_identity {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    M * Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K+Real.sqrt R) =
      K * Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K) := by
  have hs : Real.sqrt (R : ℝ) ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have he : Real.log M-(D01713 M R K+Real.sqrt R)^2/2 = Real.log K-(D01713 M R K)^2/2 := by
    dsimp [D01713]
    field_simp
    nlinarith [Real.sq_sqrt R.coe_nonneg]
  have he' := congrArg Real.exp he
  simp only [sub_eq_add_neg, Real.exp_add, Real.exp_log hM, Real.exp_log hK] at he'
  simp only [Standalone.BondOptionPriceIntervals.φ0167]
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  simpa [neg_div] using he'

lemma C0177_deriv {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    HasDerivAt (C0177 M R) (-Φ (D01713 M R K)) K := by
  have hd : HasDerivAt (D01713 M R) (-K⁻¹/Real.sqrt R) K :=
    (((Real.hasDerivAt_log hK.ne').const_sub (Real.log M)).sub_const ((R : ℝ)/2)).div_const _
  have h1 := ((BondOptionPriceIntervalsProof.Φ_deriv (D01713 M R K+Real.sqrt R)).comp K
    (hd.add_const (Real.sqrt R))).const_mul M
  have h2 := (hasDerivAt_id K).mul ((BondOptionPriceIntervalsProof.Φ_deriv (D01713 M R K)).comp K hd)
  have hder := h1.sub h2
  have he : M*(Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K+Real.sqrt R)*(-K⁻¹/Real.sqrt R)) -
      (1*Φ (D01713 M R K)+K*(Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K)*(-K⁻¹/Real.sqrt R))) =
      -Φ (D01713 M R K) := by
    rw [← mul_assoc M, density_identity hM hK R hR]
    ring
  change HasDerivAt (fun x => M*Φ (D01713 M R x+Real.sqrt R)-x*Φ (D01713 M R x)) _ K at hder
  have hder' : HasDerivAt (fun x => M*Φ (D01713 M R x+Real.sqrt R)-x*Φ (D01713 M R x)) (-Φ (D01713 M R K)) K := by
    convert hder using 1
    exact he.symm
  apply hder'.congr_of_eventuallyEq
  exact (show ∀ᶠ x : ℝ in 𝓝 K, 0 < x from Ioi_mem_nhds hK).mono fun x hx => C0177_pos' hM hx R hR

lemma C0177_nonneg (M K : ℝ) (R : NNReal) : 0 ≤ C0177 M R K :=
  integral_nonneg (fun x => le_max_right _ _)

lemma C0177_strictAnti {M : ℝ} (hM : 0 < M) (R : NNReal) (hR : 0 < R) :
    StrictAntiOn (C0177 M R) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun K hK => (C0177_deriv hM hK R hR).continuousAt.continuousWithinAt
  · intro K hK
    rw [interior_Ioi] at hK
    rw [(C0177_deriv hM hK R hR).deriv]
    exact neg_neg_of_pos (BondOptionPriceIntervalsProof.Φ_pos _)

lemma C0177_positive {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    0 < C0177 M R K := by
  have ht : C0177 M R (K+1) < C0177 M R K :=
    C0177_strictAnti hM R hR hK (show 0 < K+1 by linarith) (show K < K+1 by linarith)
  exact lt_of_le_of_lt (C0177_nonneg M (K+1) R) ht

lemma C0177_tail_bound {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) :
    C0177 M R K ≤ Real.exp (2*Real.log M+(R : ℝ))/K := by
  have hi := (integrable_exp_mul_gaussianReal (μ := Real.log M-(R : ℝ)/2) (v := R) 2).div_const K
  have he : (∫ x, Real.exp (2*x) ∂gaussianReal (Real.log M-(R : ℝ)/2) R) = Real.exp (2*Real.log M+(R : ℝ)) := by
    have hh := congrFun (mgf_fun_id_gaussianReal (μ := Real.log M-(R : ℝ)/2) (v := R)) 2
    change (∫ x, Real.exp (2*x) ∂gaussianReal (Real.log M-(R : ℝ)/2) R) = _ at hh
    rw [hh]
    congr 1
    ring
  calc C0177 M R K ≤ ∫ x, Real.exp (2*x)/K ∂gaussianReal (Real.log M-(R : ℝ)/2) R := by
        apply integral_mono (gaussian_call_integrable _ _ _) hi
        intro x
        dsimp only
        apply (le_div_iff₀ hK).2
        rw [show 2*x = x+x by ring, Real.exp_add]
        by_cases h : K ≤ Real.exp x
        · rw [max_eq_left (sub_nonneg.2 h)]
          nlinarith [sq_nonneg (Real.exp x-K), Real.exp_pos x]
        · rw [max_eq_right (sub_nonpos.2 (not_le.1 h).le), zero_mul]
          positivity
       _ = Real.exp (2*Real.log M+(R : ℝ))/K := by rw [integral_div, he]

lemma C0177_tail {M : ℝ} (hM : 0 < M) (R : NNReal) :
    Tendsto (C0177 M R) atTop (𝓝 0) := by
  exact tendsto_const_nhds.squeeze' (tendsto_id.const_div_atTop _)
    (Filter.Eventually.of_forall fun K => C0177_nonneg M K R)
    ((eventually_gt_atTop (0 : ℝ)).mono fun K hK => C0177_tail_bound hM hK R)

lemma C0177_deriv_mean {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    HasDerivAt (fun M => C0177 M R K) (Φ (D01713 M R K+Real.sqrt R)) M := by
  have hd : HasDerivAt (fun M => D01713 M R K) (M⁻¹/Real.sqrt R) M :=
    (((Real.hasDerivAt_log hM.ne').sub_const (Real.log K)).sub_const ((R : ℝ)/2)).div_const _
  have h1 := (hasDerivAt_id M).mul ((BondOptionPriceIntervalsProof.Φ_deriv (D01713 M R K+Real.sqrt R)).comp M
    (hd.add_const (Real.sqrt R)))
  have h2 := ((BondOptionPriceIntervalsProof.Φ_deriv (D01713 M R K)).comp M hd).const_mul K
  have hder := h1.sub h2
  have he : 1*Φ (D01713 M R K+Real.sqrt R) +
      M*(Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K+Real.sqrt R)*(M⁻¹/Real.sqrt R)) -
      K*(Standalone.BondOptionPriceIntervals.φ0167 (D01713 M R K)*(M⁻¹/Real.sqrt R)) =
      Φ (D01713 M R K+Real.sqrt R) := by
    rw [← mul_assoc M, density_identity hM hK R hR]
    ring
  change HasDerivAt (fun M => M*Φ (D01713 M R K+Real.sqrt R)-K*Φ (D01713 M R K)) _ M at hder
  have hder' : HasDerivAt (fun M => M*Φ (D01713 M R K+Real.sqrt R)-K*Φ (D01713 M R K))
      (Φ (D01713 M R K+Real.sqrt R)) M := by
    convert hder using 1
    exact he.symm
  apply hder'.congr_of_eventuallyEq
  exact (show ∀ᶠ x : ℝ in 𝓝 M, 0 < x from Ioi_mem_nhds hM).mono fun x hx => C0177_pos' hx hK R hR

lemma C0177_strictMono_mean {K : ℝ} (hK : 0 < K) (R : NNReal) (hR : 0 < R) :
    StrictMonoOn (fun M => C0177 M R K) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun M hM => (C0177_deriv_mean hM hK R hR).continuousAt.continuousWithinAt
  · intro M hM
    rw [interior_Ioi] at hM
    rw [(C0177_deriv_mean hM hK R hR).deriv]
    exact BondOptionPriceIntervalsProof.Φ_pos _

lemma D01713_shift (M K U : ℝ) (R : NNReal) :
    D01713 M R K = D01713 M R U - (Real.log K-Real.log U)/Real.sqrt R := by
  dsimp [D01713]
  ring

lemma two_strikes_ne_of_variance_lt {M M' K₁ K₂ : ℝ} (hM : 0 < M) (hM' : 0 < M')
    (hK₁ : 0 < K₁) (hK : K₁ < K₂) (R R' : NNReal) (hR : 0 < R) (hRR' : R < R')
    (he₁ : C0177 M R K₁ = C0177 M' R' K₁) : C0177 M R K₂ ≠ C0177 M' R' K₂ := by
  intro he₂
  have hR' := hR.trans hRR'
  let f : ℝ → ℝ := fun K => C0177 M R K-C0177 M' R' K
  let f' : ℝ → ℝ := fun K => -Φ (D01713 M R K)+Φ (D01713 M' R' K)
  have hd (K : ℝ) (hK : 0 < K) : HasDerivAt f (f' K) K := by
    convert (C0177_deriv hM hK R hR).sub (C0177_deriv hM' hK R' hR') using 1
    simp [f', sub_eq_add_neg]
  obtain ⟨U, hU, hUd⟩ := exists_hasDerivAt_eq_zero hK
    (fun K hK => (hd K (hK₁.trans_le hK.1)).continuousAt.continuousWithinAt)
    (show f K₁ = f K₂ by simp [f, he₁, he₂])
    (fun K hK => hd K (hK₁.trans hK.1))
  have hUpos : 0 < U := hK₁.trans hU.1
  have heD : D01713 M R U = D01713 M' R' U := by
    apply (show Function.Injective Φ from BondOptionMeetingVariancesProof.Φ_strictMono.injective)
    change -Φ _+Φ _=0 at hUd
    linarith
  have hU₂ : U < K₂ := hU.2
  have hs : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 hR
  have hss : Real.sqrt (R : ℝ) < Real.sqrt (R' : ℝ) := Real.sqrt_lt_sqrt R.coe_nonneg hRR'
  have hfmono : StrictMonoOn f (Ioi U) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi U)
    · exact fun K hK => (hd K (hUpos.trans hK)).continuousAt.continuousWithinAt
    · intro K hK
      rw [interior_Ioi] at hK
      rw [(hd K (hUpos.trans hK)).deriv]
      have hlog : 0 < Real.log K-Real.log U := sub_pos.2 (Real.strictMonoOn_log hUpos (hUpos.trans hK) hK)
      have hD : D01713 M R K < D01713 M' R' K := by
        rw [D01713_shift M K U R, D01713_shift M' K U R', heD]
        exact sub_lt_sub_left (div_lt_div_of_pos_left hlog hs hss) _
      have hh : Φ (D01713 M R K) < Φ (D01713 M' R' K) := BondOptionMeetingVariancesProof.Φ_strictMono hD
      change -Φ _+Φ _ > 0
      linarith
  have htail : Tendsto f atTop (𝓝 0) := by
    simpa [f] using (C0177_tail hM R).sub (C0177_tail hM' R')
  have hgt : 0 < f (K₂+1) := by
    have hh := hfmono hU.2 (show U < K₂+1 by linarith) (show K₂ < K₂+1 by linarith)
    simpa [f, he₂] using hh
  have hle : f (K₂+1) ≤ 0 := ge_of_tendsto htail
    ((eventually_ge_atTop (K₂+1)).mono fun K hK =>
      hfmono.monotoneOn (show U < K₂+1 by linarith) (show U < K by linarith) hK)
  linarith

lemma two_strikes_ne_zero {M M' K : ℝ} (hM : 1 ≤ M) (hM' : 0 < M') (hK : 1 < K)
    (R : NNReal) (hR : 0 < R) (he₁ : C0177 M 0 1 = C0177 M' R 1) :
    C0177 M 0 K ≠ C0177 M' R K := by
  have hmpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hm : C0177 M' R 1 = M-1 := by
    rw [← he₁, C0177_zero hmpos, max_eq_left (sub_nonneg.2 hM)]
  have hmono : StrictMonoOn (fun K => C0177 M' R K+K) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun K hK => ((C0177_deriv hM' hK R hR).add (hasDerivAt_id K)).continuousAt.continuousWithinAt
    · intro K hK
      rw [interior_Ioi] at hK
      have hd : HasDerivAt (fun K => C0177 M' R K+K) (-Φ (D01713 M' R K)+1) K := by
        simpa only [Pi.add_def, id_eq] using (C0177_deriv hM' hK R hR).add (hasDerivAt_id K)
      rw [hd.deriv]
      have hh : Φ (D01713 M' R K) < 1 := BondOptionMeetingVariancesProof.Φ_lt_one _
      change -Φ _+1 > 0
      linarith
  have ht := hmono (show (0:ℝ) < 1 by norm_num) (show 0 < K by linarith) hK
  dsimp only at ht
  rw [hm] at ht
  have hp := C0177_positive hM' (show 0 < K by linarith) R hR
  rw [C0177_zero hmpos]
  exact ne_of_lt (max_lt (by linarith) hp)

lemma C0177_two_strikes {M M' K : ℝ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hK : 1 < K)
    (R R' : NNReal) :
    (C0177 M R 1 = C0177 M' R' 1 ∧ C0177 M R K = C0177 M' R' K) ↔ M = M' ∧ R = R' := by
  have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hm' : 0 < M' := lt_of_lt_of_le zero_lt_one hM'
  constructor
  · rintro ⟨he₁, he₂⟩
    by_cases hR : R = 0
    · subst R
      by_cases hR' : R' = 0
      · subst R'
        rw [C0177_zero hm, C0177_zero hm', max_eq_left (sub_nonneg.2 hM),
          max_eq_left (sub_nonneg.2 hM')] at he₁
        exact ⟨by linarith, rfl⟩
      · exact False.elim (two_strikes_ne_zero hM hm' hK R' (pos_iff_ne_zero.2 hR') he₁ he₂)
    · have hr := pos_iff_ne_zero.2 hR
      by_cases hR' : R' = 0
      · subst R'
        exact False.elim (two_strikes_ne_zero hM' hm hK R hr he₁.symm he₂.symm)
      · have hr' := pos_iff_ne_zero.2 hR'
        have heR : R = R' := by
          rcases lt_trichotomy R R' with hlt | he | hgt
          · exact False.elim (two_strikes_ne_of_variance_lt hm hm' (by norm_num) hK R R' hr hlt he₁ he₂)
          · exact he
          · exact False.elim (two_strikes_ne_of_variance_lt hm' hm (by norm_num) hK R' R hr' hgt he₁.symm he₂.symm)
        subst R'
        exact ⟨(C0177_strictMono_mean (by norm_num) R hr).injOn hm hm' he₁, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

lemma two_strikes_iff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (v' : Fin N → NNReal) (S a b K : ℝ) (hS : 0 ≤ S) (hab : a ≤ b) (hSb : S ≤ b) (hK : 1 < K) :
    (C τ v S a b 1 = C τ v' S a b 1 ∧ C τ v S a b K = C τ v' S a b K) ↔
      m τ v S a b = m τ v' S a b ∧ q τ v S a b = q τ v' S a b := by
  simp_rw [price_eq_C0177 τ _ hτ0 hτ S a b _ hS]
  exact C0177_two_strikes (mean_ge_one τ v hab hSb) (mean_ge_one τ v' hab hSb) hK _ _

lemma two_strikes_panel_iff (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) {L : ℕ}
    (S a b K : Fin L → ℝ) (hS : ∀ l, 0 ≤ S l) (hab : ∀ l, a l ≤ b l)
    (hSb : ∀ l, S l ≤ b l) (hK : ∀ l, 1 < K l) (v' : Fin N → NNReal) (ω : Ω N) :
    (∀ l, G τ v 0 (a l) (b l) ω = G τ v' 0 (a l) (b l) ω ∧
      C τ v (S l) (a l) (b l) 1 = C τ v' (S l) (a l) (b l) 1 ∧
      C τ v (S l) (a l) (b l) (K l) = C τ v' (S l) (a l) (b l) (K l)) ↔
    M0179 τ S a b *ᵥ (fun i => (v i : ℝ)) = M0179 τ S a b *ᵥ (fun i => (v' i : ℝ)) := by
  rw [← panel_iff τ v hτ0 hτ S a b hS v' ω]
  apply forall_congr'
  intro l
  rw [two_strikes_iff τ v hτ0 hτ v' (S l) (a l) (b l) (K l) (hS l) (hab l) (hSb l) (hK l),
    surface_iff τ v hτ0 hτ v' (S l) (a l) (b l) (hS l)]

lemma w_after {a b T : ℝ} (hT : T ≤ a) (hab : a ≤ b) : w a b T = b-a := by
  rw [w, max_eq_left (sub_nonneg.2 (hT.trans hab)), max_eq_left (sub_nonneg.2 hT)]
  ring

lemma q_prefix (hτ : StrictMonoOn τ (Iic N)) (S : Fin N → ℝ)
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (a b : ℝ) (ha : τ N ≤ a) (hab : a < b) (i : Fin N) :
    (q τ v (S i) a b : ℝ) = (b-a)^2 * ∑ j ∈ Standalone.D3EventVariances.past τ (S i), (v j : ℝ) := by
  rw [q_sum, Finset.mul_sum]
  simp only [Standalone.D3EventVariances.past, Finset.sum_filter, k]
  apply Finset.sum_congr rfl
  intro j _
  have hj : τ (j.val+1) ≤ a := (hτ.monotoneOn (by simp) (by simp) (by omega)).trans ha
  rw [w_after hj hab.le]
  split_ifs <;> ring

lemma separating_recovery (hτ : StrictMonoOn τ (Iic N)) (S : Fin N → ℝ)
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (a b : ℝ) (ha : τ N ≤ a) (hab : a < b) (i : Fin N) :
    v0179 (b-a) (fun j => (q τ v (S j) a b : ℝ)) i = (v i : ℝ) := by
  classical
  have hn : (b-a)^2 ≠ 0 := pow_ne_zero _ (sub_pos.2 hab).ne'
  unfold v0179
  dsimp only
  rw [q_prefix τ v hτ S hS a b ha hab]
  split_ifs with hi
  · have hp : Standalone.D3EventVariances.past τ (S i) = {i} := by
      ext j
      rw [BondOptionMeetingVariancesProof.past_separating τ S hτ hS, Finset.mem_singleton]
      constructor
      · intro hj; apply Fin.ext; omega
      · intro hj; subst j; exact le_rfl
    simp [hp, hn]
  · let j : Fin N := ⟨i.val-1, by omega⟩
    have hp : Standalone.D3EventVariances.past τ (S j) = (Standalone.D3EventVariances.past τ (S i)).erase i := by
      ext k
      rw [BondOptionMeetingVariancesProof.past_separating τ S hτ hS, Finset.mem_erase,
        BondOptionMeetingVariancesProof.past_separating τ S hτ hS]
      constructor
      · intro hk
        constructor
        · intro he; subst k; simp only [Fin.le_iff_val_le_val, j] at hk; omega
        · simp only [Fin.le_iff_val_le_val, j] at *; omega
      · intro hk
        have hne : k.val ≠ i.val := fun he => hk.1 (Fin.ext he)
        simp only [Fin.le_iff_val_le_val, j] at *
        omega
    rw [q_prefix τ v hτ S hS a b ha hab (j), hp, ← mul_sub, mul_div_cancel_left₀ _ hn]
    have hh := Finset.sum_erase_add (s := Standalone.D3EventVariances.past τ (S i)) (f := fun k => (v k : ℝ))
      ((BondOptionMeetingVariancesProof.past_separating τ S hτ hS i i).2 le_rfl)
    linarith

lemma futures_rate_initial (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (hab : a < b) (ω : Ω N) :
    Real.log (1+(b-a)*F τ v 0 a b ω) = p τ v a b := by
  rw [F, futures_initial τ v hτ0 hτ]
  have he : 1+(b-a)*((Real.exp (p τ v a b)-1)/(b-a)) = Real.exp (p τ v a b) := by
    field_simp [(sub_pos.2 hab).ne']
    <;> ring
  rw [he, Real.log_exp]

lemma futures_coefficient (hτ : StrictMonoOn τ (Iic N)) (b : Fin N → ℝ)
    (hb : ∀ i, τ (i.val+1) < b i ∧ (i.val+1 < N → b i < τ (i.val+2))) (i j : Fin N) :
    H0179 τ b i j = if j ≤ i then (b i-τ (i.val+1))*(b i-τ (j.val+1)) else 0 := by
  rw [H0179, h_eq]
  by_cases hji : j ≤ i
  · have ht : τ (j.val+1) ≤ τ (i.val+1) := hτ.monotoneOn (by simp) (by simp) (by omega)
    rw [ite_eq_left hji, w_after ht (hb i).1.le, max_eq_left (sub_nonneg.2 (ht.trans (hb i).1.le))]
  · have ht : b i < τ (j.val+1) := ((hb i).2 (by omega)).trans_le
      (hτ.monotoneOn (by simp; omega) (by simp) (by omega))
    rw [ite_eq_right hji, max_eq_right (sub_nonpos.2 ht.le), mul_zero]

lemma futures_matrix_injective (hτ : StrictMonoOn τ (Iic N)) (b : Fin N → ℝ)
    (hb : ∀ i, τ (i.val+1) < b i ∧ (i.val+1 < N → b i < τ (i.val+2))) :
    Function.Injective (H0179 τ b).mulVecLin := by
  have hl : (H0179 (N := N) τ b).IsLowerTriangular := by
    intro i j hij
    have hj : i < j := hij
    rw [futures_coefficient τ hτ b hb, ite_eq_right (not_le.2 hj)]
  have hdet : (H0179 (N := N) τ b).det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular _ hl]
    apply Finset.prod_ne_zero_iff.2
    intro i _
    rw [futures_coefficient τ hτ b hb, ite_eq_left le_rfl]
    exact mul_ne_zero (sub_pos.2 (hb i).1).ne' (sub_pos.2 (hb i).1).ne'
  exact Matrix.mulVec_injective_of_det_ne_zero hdet

lemma futures_recovery (hτ : StrictMonoOn τ (Iic N)) (b : Fin N → ℝ)
    (hb : ∀ i, τ (i.val+1) < b i ∧ (i.val+1 < N → b i < τ (i.val+2))) (i : Fin N) :
    (v i : ℝ) = (p τ v (τ (i.val+1)) (b i) -
      (b i-τ (i.val+1)) * ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i),
        (b i-τ (j.val+1))*(v j : ℝ)) / (b i-τ (i.val+1))^2 := by
  classical
  have hp : p τ v (τ (i.val+1)) (b i) =
      (b i-τ (i.val+1))^2*(v i : ℝ) +
      (b i-τ (i.val+1)) * ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i),
        (b i-τ (j.val+1))*(v j : ℝ) := by
    rw [p, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
    have hd : h (τ (i.val+1)) (b i) (τ (i.val+1)) = (b i-τ (i.val+1))^2 := by
      change H0179 τ b i i = _
      rw [futures_coefficient τ hτ b hb, ite_eq_left le_rfl, pow_two]
    rw [hd]
    congr 1
    rw [Finset.mul_sum]
    trans ∑ j ∈ Finset.univ.erase i, if j < i then (b i-τ (i.val+1))*((b i-τ (j.val+1))*(v j : ℝ)) else 0
    · apply Finset.sum_congr rfl
      intro j hj
      have hne : j ≠ i := (Finset.mem_erase.1 hj).1
      change H0179 τ b i j * (v j : ℝ) = _
      rw [futures_coefficient τ hτ b hb]
      by_cases hji : j < i
      · simp [hji, hji.le, mul_assoc]
      · have hnl : ¬ j ≤ i := fun h => hji (lt_of_le_of_ne h hne)
        simp [hji, hnl]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      exact and_iff_right_of_imp (fun hj : j < i => hj.ne)
  rw [hp, add_sub_cancel_right]
  field_simp [(sub_pos.2 (hb i).1).ne']

lemma futures_only_injective (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (b : Fin N → ℝ)
    (hb : ∀ i, τ (i.val+1) < b i ∧ (i.val+1 < N → b i < τ (i.val+2)))
    (v' : Fin N → NNReal) (ω : Ω N)
    (he : ∀ i, F τ v 0 (τ (i.val+1)) (b i) ω = F τ v' 0 (τ (i.val+1)) (b i) ω) : v = v' := by
  have hp : (H0179 τ b).mulVecLin (fun i => (v i : ℝ)) = (H0179 τ b).mulVecLin (fun i => (v' i : ℝ)) := by
    ext i
    change p τ v (τ (i.val+1)) (b i) = p τ v' (τ (i.val+1)) (b i)
    rw [← futures_rate_initial τ v hτ0 hτ _ _ (hb i).1 ω,
      ← futures_rate_initial τ v' hτ0 hτ _ _ (hb i).1 ω, he i]
  have hh := futures_matrix_injective τ hτ b hb hp
  funext i
  exact NNReal.coe_injective (congrFun hh i)

lemma separating_injective (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S : Fin N → ℝ)
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (a b : ℝ) (ha : τ N ≤ a) (hab : a < b) (v' : Fin N → NNReal)
    (he : ∀ i K, 0 < K → C τ v (S i) a b K = C τ v' (S i) a b K) : v = v' := by
  have hq : (fun i => (q τ v (S i) a b : ℝ)) = fun i => (q τ v' (S i) a b : ℝ) := by
    funext i
    have hSi : 0 ≤ S i := by
      rw [← hτ0]
      exact (hτ.monotoneOn (by simp) (by simp) (by omega)).trans (hS i).1
    exact congrArg NNReal.toReal ((surface_iff τ v hτ0 hτ v' (S i) a b hSi).1 (he i)).2
  funext i
  apply NNReal.coe_injective
  rw [← separating_recovery τ v hτ S hS a b ha hab i,
    ← separating_recovery τ v' hτ S hS a b ha hab i, hq]

lemma p_after (a b : ℝ) (hT : ∀ i : Fin N, τ (i.val+1) ≤ a) (hab : a ≤ b) :
    p τ v a b = (b-a)*(b*(∑ i, (v i : ℝ)) - ∑ i, τ (i.val+1)*(v i : ℝ)) := by
  unfold p
  simp_rw [h_eq, w_after (hT _) hab, max_eq_left (sub_nonneg.2 ((hT _).trans hab))]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma z_after (S a b : ℝ) (hT : ∀ i : Fin N, τ (i.val+1) ≤ S) (hSa : S ≤ a) (hab : a ≤ b) :
    z τ v S a b = (b-a)*(S*(∑ i, (v i : ℝ)) - ∑ i, τ (i.val+1)*(v i : ℝ)) := by
  unfold z
  simp_rw [j, ite_eq_left (hT _), w_after ((hT _).trans hSa) hab]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma q_after (S a b : ℝ) (hT : ∀ i : Fin N, τ (i.val+1) ≤ S) (hSa : S ≤ a) (hab : a ≤ b) :
    (q τ v S a b : ℝ) = (b-a)^2 * ∑ i, (v i : ℝ) := by
  rw [q_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [k, ite_eq_left (hT i), w_after ((hT i).trans hSa) hab]

lemma initial_bonds (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (U : ℝ) (ω : Ω N) :
    P τ v 0 U ω = 1 := by
  have hf : f τ v 0 = fun _ _ => 0 := by
    funext u ω
    unfold f
    apply Finset.sum_eq_zero
    intro i _
    have ht : 0 < τ (i.val+1) := by
      rw [← hτ0]
      exact hτ (by simp) (by simp) (by omega)
    rw [ite_eq_right (not_le.2 ht)]
  simp [P, hf]

lemma example_moments (ε : NNReal) :
    ((∑ i, (v01710 ε i : ℝ)) = 7*ε ∧ (∑ i : Fin 3, ((i.val+1 : ℕ) : ℝ)*(v01710 ε i : ℝ)) = 14*ε) ∧
    ((∑ i, (v01710' ε i : ℝ)) = 7*ε ∧ (∑ i : Fin 3, ((i.val+1 : ℕ) : ℝ)*(v01710' ε i : ℝ)) = 14*ε) := by
  norm_num [v01710, v01710', Fin.sum_univ_succ]
  <;> ring_nf <;> simp

lemma example_distinct (ε : NNReal) (hε : 0 < ε) : v01710 ε ≠ v01710' ε := by
  intro he
  have hh := congrArg (fun v : Fin 3 → NNReal => (v 0 : ℝ)) he
  simp [v01710, v01710'] at hh
  exact hε.ne' hh

lemma example_equal_futures (ε : NNReal) (a b : ℝ) (ha : 3 ≤ a) (hab : a < b) (ω : Ω 3) :
    F (fun n : ℕ => (n : ℝ)) (v01710 ε) 0 a b ω = F (fun n : ℕ => (n : ℝ)) (v01710' ε) 0 a b ω := by
  have hτ : StrictMonoOn (fun n : ℕ => (n : ℝ)) (Iic 3) := by intro i _ j _ hij; change (i : ℝ) < (j : ℝ); exact_mod_cast hij
  have hT (i : Fin 3) : ((i.val+1 : ℕ) : ℝ) ≤ a := by
    have hi : ((i.val+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact hi.trans ha
  rw [F, F, futures_initial _ _ (by norm_num) hτ, futures_initial _ _ (by norm_num) hτ,
    p_after _ _ a b hT hab.le, p_after _ _ a b hT hab.le,
    (example_moments ε).1.1, (example_moments ε).1.2, (example_moments ε).2.1, (example_moments ε).2.2]

lemma example_equal_calls (ε : NNReal) (S a b K : ℝ) (hS : 3 ≤ S) (hSa : S ≤ a) (hab : a < b) :
    C (fun n : ℕ => (n : ℝ)) (v01710 ε) S a b K = C (fun n : ℕ => (n : ℝ)) (v01710' ε) S a b K := by
  have hτ : StrictMonoOn (fun n : ℕ => (n : ℝ)) (Iic 3) := by intro i _ j _ hij; change (i : ℝ) < (j : ℝ); exact_mod_cast hij
  have hT (i : Fin 3) : ((i.val+1 : ℕ) : ℝ) ≤ S := by
    have hi : ((i.val+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact hi.trans hS
  have hS0 : 0 ≤ S := by linarith
  rw [price_eq_C0177 _ _ (by norm_num) hτ S a b K hS0,
    price_eq_C0177 _ _ (by norm_num) hτ S a b K hS0]
  have hm : m (fun n : ℕ => (n : ℝ)) (v01710 ε) S a b = m (fun n : ℕ => (n : ℝ)) (v01710' ε) S a b := by
    rw [m, m, p_after _ _ a b (fun i => (hT i).trans hSa) hab.le,
      p_after _ _ a b (fun i => (hT i).trans hSa) hab.le,
      z_after _ _ S a b hT hSa hab.le, z_after _ _ S a b hT hSa hab.le,
      (example_moments ε).1.1, (example_moments ε).1.2, (example_moments ε).2.1, (example_moments ε).2.2]
  have hq : q (fun n : ℕ => (n : ℝ)) (v01710 ε) S a b = q (fun n : ℕ => (n : ℝ)) (v01710' ε) S a b := by
    apply NNReal.coe_injective
    rw [q_after _ _ S a b hT hSa hab.le, q_after _ _ S a b hT hSa hab.le,
      (example_moments ε).1.1, (example_moments ε).2.1]
  rw [hm, hq]

instance : IsProbabilityMeasure (Qc v) := ⟨by change (Q v) univ = 1; exact measure_univ⟩

lemma completion_law : HasLaw (Ω := Ωc v) (𝓧 := Ω N) (m𝓧 := MeasurableSpace.pi) (fun ω : Ωc v => (ω : Ω N)) (Q v) (Qc v) := by
  have hm : @Measurable (Ωc v) (Ω N) inferInstance MeasurableSpace.pi (fun ω => ω) := by
    intro s hs
    exact ⟨s, hs, Filter.EventuallyEq.refl _ _⟩
  refine ⟨hm.aemeasurable, ?_⟩
  apply @Measure.ext (Ω N) MeasurableSpace.pi
  intro s hs
  rw [Measure.map_apply hm hs]
  rfl

lemma completion_setIntegral (u : Ω N → ℝ) (hu : Integrable u (Q v)) (s : Set (Ω N)) (hs : MeasurableSet s) :
    ∫ ω in s, u ω ∂Qc v = ∫ ω in s, u ω ∂Q v := by
  have hm : @MeasurePreserving (Ωc v) (Ω N) inferInstance MeasurableSpace.pi (fun ω => ω) (Qc v) (Q v) :=
    ⟨(by intro s hs; exact ⟨s, hs, Filter.EventuallyEq.refl _ _⟩), (completion_law v).map_eq⟩
  have hr := hm.restrict_preimage hs
  have hl : HasLaw (Ω := Ωc v) (𝓧 := Ω N) (m𝓧 := MeasurableSpace.pi) (fun ω : Ωc v => (ω : Ω N)) ((Q v).restrict s) ((Qc v).restrict s) :=
    ⟨hr.measurable.aemeasurable, hr.map_eq⟩
  exact hl.integral_comp hu.aestronglyMeasurable.restrict

lemma futures_completed_measurable (t a b : ℝ) :
    Measurable[completedFilt τ v t] (fun ω : Ωc v => G τ v t a b ω) := by
  intro s hs
  exact ⟨_, (futures_measurable τ v t a b) hs, Filter.EventuallyEq.refl _ _⟩

lemma futures_completed_condExp (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (t : ℝ) :
    (Qc v)[fun ω => Real.exp (∫ u in a..b, r τ v u ω) | completedFilt τ v t] =ᵐ[Qc v] G τ v t a b := by
  have hf := accrual_exp_integrable τ v hτ0 hτ a b ha hab
  have hg := futures_integrable τ v t a b
  have hfc : Integrable (fun ω : Ωc v => Real.exp (∫ u in a..b, r τ v u ω)) (Qc v) :=
    (completion_law v).integrable_comp hf
  have hgc : Integrable (fun ω : Ωc v => G τ v t a b ω) (Qc v) :=
    (completion_law v).integrable_comp hg
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((completedFilt τ v).le t) hfc
    (fun s _ _ => hgc.integrableOn) ?_
    (futures_completed_measurable τ v t a b).stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨s', hs', hae⟩ := hs
  have hae' : s =ᵐ[Qc v] s' := hae
  rw [Measure.restrict_congr_set hae',
    completion_setIntegral v _ hg s' ((filt τ).le t s' hs'),
    completion_setIntegral v _ hf s' ((filt τ).le t s' hs'),
    ← setIntegral_condExp ((filt τ).le t) hf hs']
  apply setIntegral_congr_ae ((filt τ).le t s' hs')
  filter_upwards [futures_condExp τ v hτ0 hτ a b ha hab t] with ω hω _
  exact hω.symm

lemma futures_completed_martingale (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Martingale (fun t (ω : Ωc v) => G τ v t a b ω) (completedFilt τ v) (Qc v) := by
  letI : IsProbabilityMeasure (Qc v) := ⟨by change (Q v) univ = 1; exact measure_univ⟩
  exact (martingale_condExp (fun ω : Ωc v => Real.exp (∫ u in a..b, r τ v u ω)) (completedFilt τ v) (Qc v)).congr
    (fun t => (futures_completed_measurable τ v t a b).stronglyMeasurable)
    (futures_completed_condExp τ v hτ0 hτ a b ha hab)

lemma price_completed (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (S a b K : ℝ) (hS : 0 ≤ S) :
    (∫ ω, Real.exp (-logB τ v S ω)*max (G τ v S a b ω-K) 0 ∂Qc v) = C τ v S a b K := by
  exact (completion_law v).integral_comp (integrable_price τ v hτ0 hτ S a b K hS).aestronglyMeasurable

lemma C0177_inverse_domain {M : ℝ} (hM : 0 < M) (R : NNReal) :
    (1+C0177 M R M/M)/2 ∈ Ico (1/2 : ℝ) 1 := by
  rw [C0177_at_mean hM]
  have he (x : ℝ) : (1+(2*x-1))/2 = x := by ring
  rw [he]
  have h0 : (1/2 : ℝ) ≤ Φ (Real.sqrt R/2) := by
    change (1/2 : ℝ) ≤ Standalone.BondOptionMeetingVariances.Φ (Real.sqrt R/2)
    rw [← BondOptionMeetingVariancesProof.Φ_zero]
    exact BondOptionMeetingVariancesProof.Φ_strictMono.monotone (by positivity)
  exact ⟨h0, BondOptionMeetingVariancesProof.Φ_lt_one _⟩

lemma rate_payoff (S a b K : ℝ) (hab : a < b) (ω : Ω N) :
    max (F τ v S a b ω-(K-1)/(b-a)) 0 = max (G τ v S a b ω-K) 0/(b-a) := by
  rw [F, ← sub_div, show G τ v S a b ω-1-(K-1) = G τ v S a b ω-K by ring]
  simpa using max_div_div_right (sub_pos.2 hab).le (G τ v S a b ω-K) 0

lemma rate_call (S a b K : ℝ) (hab : a < b) :
    (∫ ω, Real.exp (-logB τ v S ω)*max (F τ v S a b ω-(K-1)/(b-a)) 0 ∂Q v) = C τ v S a b K/(b-a) := by
  simp_rw [rate_payoff τ v S a b K hab, ← mul_div_assoc]
  rw [integral_div]
  rfl

lemma q_prefix' (hτ : StrictMonoOn τ (Iic N)) (S : Fin N → ℝ)
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (a b : ℝ) (ha : τ N ≤ a) (hab : a < b) (i : Fin N) :
    (q τ v (S i) a b : ℝ) = (b-a)^2 * ∑ j, if j ≤ i then (v j : ℝ) else 0 := by
  rw [q_prefix τ v hτ S hS a b ha hab]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext j
  rw [BondOptionMeetingVariancesProof.past_separating τ S hτ hS]
  simp

lemma event_jump (hτ : StrictMonoOn τ (Iic N)) (i : Fin N) (ω : Ω N) : Δr τ v i ω = ω i := by
  simp only [Δr, short_rate_eq]
  exact D3EventVariancesProof.event_jump hτ i ω

theorem compoundedFuturesIdentification : Standalone.CompoundedFuturesIdentification.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N τ v hτ0 hτ a b ha hab
    refine ⟨accrual_integral τ v hτ0 hτ a b ha hab,
      accrual_exp_integrable τ v hτ0 hτ a b ha hab,
      futures_condExp τ v hτ0 hτ a b ha hab,
      futures_martingale τ v hτ0 hτ a b ha hab,
      fun t ω => futures_formula τ v t a b ω,
      futures_initial τ v hτ0 hτ a b, ?_⟩
    intro S hS
    refine ⟨?_, law_logG τ v hτ0 hτ S a b hS,
      fun K => integrable_price τ v hτ0 hτ S a b K hS,
      fun K => price_eq_C0177 τ v hτ0 hτ S a b K hS,
      fun hSb => mean_ge_one τ v hab.le hSb,
      fun v' => surface_iff τ v hτ0 hτ v' S a b hS⟩
    rw [QS_eq τ v hτ0 hτ S hS]
    exact measure_univ
  · intro M hM
    exact ⟨C0177_zero hM, fun R K hR hK => C0177_pos hM hK R hR,
      C0177_at_mean hM, C0177_limit hM, C0177_recover_q hM,
      fun M' R R' hM' => C0177_surface hM hM' R R'⟩
  · exact ⟨fun N L τ S a b hτ0 hτ hS v v' ω => panel_iff τ v hτ0 hτ S a b hS v' ω,
      fun N J _ A => ⟨matrix_injective_nonneg A, fun hr x hx => matrix_positive_perturbation A hr x hx⟩⟩
  · intro N τ v hτ0 hτ
    refine ⟨fun a b hab ω => futures_rate_initial τ v hτ0 hτ a b hab ω, ?_, ?_⟩
    · intro S hS a b ha hab
      exact ⟨q_prefix' τ v hτ S hS a b ha hab, separating_recovery τ v hτ S hS a b ha hab,
        fun v' he => separating_injective τ v hτ0 hτ S hS a b ha hab v' he⟩
    · intro b hb
      exact ⟨futures_coefficient τ hτ b hb, futures_recovery τ v hτ b hb,
        fun v' ω he => futures_only_injective τ v hτ0 hτ b hb v' ω he⟩
  · intro ε hε
    refine ⟨?_, example_distinct ε hε, ?_, example_equal_futures ε, example_equal_calls ε⟩
    · intro i
      fin_cases i <;> simp [v01710, v01710', hε]
    · intro v U ω
      exact initial_bonds _ v (by norm_num)
        (by intro i _ j _ hij; change (i : ℝ) < (j : ℝ); exact_mod_cast hij) U ω
  · exact ⟨fun M M' K R R' hM hM' hK => C0177_two_strikes hM hM' hK R R',
      fun N L τ S a b K hτ0 hτ hS hab hSb hK v v' ω =>
        two_strikes_panel_iff τ v hτ0 hτ S a b K hS hab hSb hK v' ω⟩
  · intro N τ v hτ0 hτ a b ha hab
    exact ⟨futures_completed_condExp τ v hτ0 hτ a b ha hab,
      futures_completed_martingale τ v hτ0 hτ a b ha hab,
      fun S K hS => price_completed τ v hτ0 hτ S a b K hS⟩
  · exact ⟨fun M R hM => C0177_inverse_domain hM R,
      fun N τ v S a b K hab => ⟨rate_payoff τ v S a b K hab, rate_call τ v S a b K hab⟩⟩
  · intro N τ v hτ
    refine ⟨event_jump τ v hτ, ?_, ?_, fun i => D3EventVariancesProof.law i, D3EventVariancesProof.indep⟩
    · intro i
      have he : Δr τ v i = fun ω => ω i := funext (event_jump τ v hτ i)
      rw [he]
      exact D3EventVariancesProof.variance_coord i
    · intro i t ht
      have he : Δr τ v i = fun ω => ω i := funext (event_jump τ v hτ i)
      rw [he]
      exact D3EventVariancesProof.condVar_coord i ht
end Novel.CompoundedFuturesIdentificationProof

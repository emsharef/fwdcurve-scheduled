import Standalone.PreWindowVarianceAggregates
import Novel.CrossMeetingAmericanProof
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open Standalone.PreWindowVarianceAggregates
namespace Novel.PreWindowVarianceAggregatesProof

variable {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)

instance : IsProbabilityMeasure (Q v) := by unfold Q; infer_instance

/-! ### (a) the curve after `A` -/

lemma curve_split (A t U : ℝ) (hAt : A ≤ t) (ω : Ω N) :
    f τ v t U ω = r τ v A ω + Vk τ v A * (U - A) +
      ∑ i ∈ Finset.univ.filter (fun i => A < τ (i.val+1) ∧ τ (i.val+1) ≤ t),
        (ω i + (v i : ℝ) * (U - τ (i.val+1))) := by
  classical
  have hf : f τ v t U ω = ∑ i ∈ Finset.univ.filter (fun i => τ (i.val+1) ≤ t),
      (ω i + (v i : ℝ) * (U - τ (i.val+1))) := by
    simp only [f, Finset.sum_filter]
  have hr : r τ v A ω = ∑ i ∈ past τ A, (ω i + (v i : ℝ) * (A - τ (i.val+1))) := by
    simp only [r, past, Finset.sum_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun i : Fin N => τ (i.val+1) ≤ t) (fun i => τ (i.val+1) ≤ A)
    (fun i => ω i + (v i : ℝ) * (U - τ (i.val+1)))
  rw [hf, hr, ← hsplit]
  have h1 : (Finset.univ.filter fun i : Fin N => τ (i.val+1) ≤ t).filter
      (fun i => τ (i.val+1) ≤ A) = past τ A := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, past]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hAt, h⟩⟩
  have h2 : (Finset.univ.filter fun i : Fin N => τ (i.val+1) ≤ t).filter
      (fun i => ¬ τ (i.val+1) ≤ A) =
      Finset.univ.filter (fun i => A < τ (i.val+1) ∧ τ (i.val+1) ≤ t) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [h1, h2, Vk, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma curve : curveStatement := by
  intro N τ v hτ A t U hAt htU ω
  refine ⟨curve_split τ v A t U hAt ω, curve_split τ v A t t hAt ω, fun i => ?_⟩
  exact CompoundedFuturesIdentificationProof.event_jump τ v hτ i ω

/-! ### (b) the discount density and the change of measure -/

lemma past_nonneg_dates (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (i : Fin N) :
    0 ≤ τ (i.val+1) := by
  rw [← hτ0]
  exact hτ.monotoneOn (by simp) (by simp only [mem_Iic]; omega) (Nat.zero_le _)

lemma bank_past_sum (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (ω : Ω N) : logB τ v A ω =
      ∑ i ∈ past τ A, ((A-τ (i.val+1))*ω i + (v i : ℝ)*(A-τ (i.val+1))^2/2) := by
  classical
  change Standalone.CompoundedFuturesIdentification.logB τ v A ω = _
  rw [CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ A h0,
    CompoundedFuturesIdentificationProof.bank_positive_parts]
  rw [past, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    simp

lemma bank_filt_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    Measurable[filt τ A] (logB τ v A) := by
  have he : logB τ v A = fun ω => ∑ i ∈ past τ A,
      ((A-τ (i.val+1))*ω i + (v i : ℝ)*(A-τ (i.val+1))^2/2) :=
    funext (bank_past_sum τ v hτ0 hτ A h0)
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  have hiA : τ (i.val+1) ≤ A := by simpa [past] using hi
  have hc : Measurable[filt τ A] (fun ω : Ω N => ω i) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le i (le_iSup_of_le hiA le_rfl))
  exact (measurable_const.mul hc).add measurable_const

lemma rate_filt_measurable (A : ℝ) : Measurable[filt τ A] (r τ v A) :=
  CrossMeetingAmericanProof.model_rate_measurable τ v A

lemma rate_past_sum (A : ℝ) (ω : Ω N) :
    r τ v A ω = ∑ i ∈ past τ A, (ω i + (v i : ℝ)*(A-τ (i.val+1))) := by
  simp only [r, past, Finset.sum_filter]

lemma density_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    (∫ ω, Real.exp (-logB τ v A ω) ∂Q v) = 1 := by
  have h := BondOptionMeetingVariancesProof.integral_D0148 (v := v)
    (BondOptionMeetingVariancesProof.a0148 τ A)
  refine Eq.trans ?_ h
  apply integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hd := BondOptionMeetingVariancesProof.density_eq (v := v) τ A ω
  change Real.exp (-Standalone.CompoundedFuturesIdentification.logB τ v A ω) = _
  rw [CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ A h0]
  exact hd.symm

lemma discounted_law (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    HasLaw (r τ v A) (gaussianReal 0 (∑ i ∈ past τ A, v i)) (Qtilde τ v A) := by
  classical
  change HasLaw _ _ (Standalone.CompoundedFuturesIdentification.QS τ v A)
  rw [CompoundedFuturesIdentificationProof.QS_eq τ v hτ0 hτ A h0]
  let c : Fin N → ℝ := fun i => if τ (i.val+1) ≤ A then 1 else 0
  let b : ℝ := ∑ i ∈ past τ A, (v i : ℝ)*(A-τ (i.val+1))
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v)
    (BondOptionMeetingVariancesProof.a0148 τ A) c b
  have hm : b + ∑ i, c i*(v i : ℝ)*BondOptionMeetingVariancesProof.a0148 τ A i = 0 := by
    simp only [b, c, BondOptionMeetingVariancesProof.a0148, Standalone.D3EventVariances.past,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [past, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> ring
  have hv : (∑ i, v i * (c i^2).toNNReal) = ∑ i ∈ past τ A, v i := by
    rw [past, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c]
    split_ifs <;> simp
  rw [hm, hv] at h
  apply h.congr
  apply Eventually.of_forall
  intro ω
  rw [rate_past_sum]
  simp only [Standalone.BondOptionMeetingVariances.L0149, b, c, ite_mul, one_mul, zero_mul,
    past, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- Freezing an independent block: the general form of `CrossMeetingAmericanProof.freeze`
with a vector-valued independent variable. -/
lemma freezeGen {Ω' : Type} {γ : Type} [mγ : MeasurableSpace γ]
    (m₁ m₂ : MeasurableSpace Ω') [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω') [IsFiniteMeasure P]
    (hm₁ : m₁ ≤ mΩ') (hm₂ : m₂ ≤ mΩ') (hind : Indep m₁ m₂ P)
    (X Ψ : Ω' → ℝ) (Z : Ω' → γ) (hX : Measurable[m₁] X) (hΨ : Measurable[m₁] Ψ)
    (hZ : Measurable[m₂] Z) (g : ℝ × γ → ℝ) (hg : Measurable g)
    (hint : Integrable (fun ω => Ψ ω * g (X ω, Z ω)) P) :
    Integrable (fun ω => Ψ ω * ∫ z, g (X ω, z) ∂(P.map Z)) P ∧
    ∫ ω, Ψ ω * g (X ω, Z ω) ∂P = ∫ ω, Ψ ω * ∫ z, g (X ω, z) ∂(P.map Z) ∂P := by
  have hXΨ₁ : Measurable[m₁] (fun ω => (X ω, Ψ ω)) := hX.prodMk hΨ
  have hXΨ : Measurable[mΩ'] (fun ω => (X ω, Ψ ω)) := hXΨ₁.mono hm₁ le_rfl
  have hZ' : Measurable[mΩ'] Z := hZ.mono hm₂ le_rfl
  have hindf : IndepFun (fun ω => (X ω, Ψ ω)) Z P :=
    indep_of_indep_of_le_left (indep_of_indep_of_le_right hind (measurable_iff_comap_le.1 hZ))
      (measurable_iff_comap_le.1 hXΨ₁)
  have hmap := hindf.map_prod_eq_prod_map_map hXΨ.aemeasurable hZ'.aemeasurable
  let φ : (ℝ × ℝ) × γ → ℝ := fun p => p.1.2 * g (p.1.1, p.2)
  have hφ : Measurable φ := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × γ => g (p.1.1, p.2)) :=
      hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (measurable_snd.comp measurable_fst).mul h1
  have hpair : Measurable[mΩ'] (fun ω => ((X ω, Ψ ω), Z ω)) := hXΨ.prodMk hZ'
  have hφint : Integrable φ ((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hφ.aestronglyMeasurable hpair.aemeasurable).2 hint
  have hG : Measurable (fun x : ℝ => ∫ z, g (x, z) ∂(P.map Z)) :=
    hg.stronglyMeasurable.integral_prod_right'.measurable
  have hΨG : Measurable (fun p : ℝ × ℝ => p.2 * ∫ z, g (p.1, z) ∂(P.map Z)) :=
    measurable_snd.mul (hG.comp measurable_fst)
  have h1 : ∫ ω, Ψ ω * g (X ω, Z ω) ∂P =
      ∫ p, φ p ∂((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) := by
    rw [← hmap]
    exact (integral_map hpair.aemeasurable hφ.aestronglyMeasurable).symm
  have h2 : ∫ p, φ p ∂((P.map (fun ω => (X ω, Ψ ω))).prod (P.map Z)) =
      ∫ x, x.2 * ∫ z, g (x.1, z) ∂(P.map Z) ∂(P.map (fun ω => (X ω, Ψ ω))) := by
    rw [integral_prod φ hφint]
    congr 1
    funext x
    exact integral_const_mul x.2 (fun z => g (x.1, z))
  have h3 : ∫ x, x.2 * ∫ z, g (x.1, z) ∂(P.map Z) ∂(P.map (fun ω => (X ω, Ψ ω))) =
      ∫ ω, Ψ ω * ∫ z, g (X ω, z) ∂(P.map Z) ∂P :=
    integral_map hXΨ.aemeasurable hΨG.aestronglyMeasurable
  refine ⟨?_, h1.trans (h2.trans h3)⟩
  have hi := hφint.integral_prod_left
  have hi' : Integrable (fun x : ℝ × ℝ => x.2 * ∫ z, g (x.1, z) ∂(P.map Z))
      (P.map (fun ω => (X ω, Ψ ω))) :=
    hi.congr (Eventually.of_forall fun x => integral_const_mul x.2 (fun z => g (x.1, z)))
  exact (integrable_map_measure hΨG.aestronglyMeasurable hXΨ.aemeasurable).1 hi'

instance (A : ℝ) : IsProbabilityMeasure (Qlater τ v A) := by unfold Qlater; infer_instance

lemma later_law (A : ℝ) :
    (Q v).map (later N τ A).domRestrict = Qlater τ v A := by
  change (Measure.infinitePi fun i => gaussianReal 0 (v i)).map (later N τ A).domRestrict = _
  exact Measure.infinitePi_map_restrict' _

lemma later_measurable (A : ℝ) :
    Measurable[D3EventVariancesProof.coordAlg (later N τ A)] (later N τ A).domRestrict := by
  refine (@measurable_pi_iff (Ω N) (later N τ A) (fun _ => ℝ)
    (D3EventVariancesProof.coordAlg (later N τ A)) _ _).mpr fun i => ?_
  exact D3EventVariancesProof.measurable_coord i.2

lemma indep_blocks (A : ℝ) :
    Indep (filt τ A) (D3EventVariancesProof.coordAlg (later N τ A)) (Q v) := by
  have hdisj : Disjoint {i : Fin N | τ (i.val+1) ≤ A} (later N τ A) := by
    rw [Set.disjoint_left]
    intro i hi hi'
    simp only [Set.mem_setOf_eq] at hi
    exact absurd hi (not_le.mpr hi')
  exact D3EventVariancesProof.indep_algs (v := v) hdisj

lemma discounted_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (G : ℝ → ℝ) (hG : AEStronglyMeasurable G (gaussianReal 0 (∑ i ∈ past τ A, v i))) :
    (∫ ω, Real.exp (-logB τ v A ω)*G (r τ v A ω) ∂Q v) =
      ∫ x, G x ∂gaussianReal 0 (∑ i ∈ past τ A, v i) := by
  have h := (discounted_law τ v hτ0 hτ A h0).integral_comp hG
  have hb : Measurable (logB τ v A) := LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0
  rw [Qtilde, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, Function.comp_apply] using h

lemma change_of_measure (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (later N τ A → ℝ) → ℝ) (hΦ : Measurable Φ)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) *
      Φ (r τ v A ω, (later N τ A).domRestrict ω)) (Q v)) :
    (∫ ω, Real.exp (-logB τ v A ω) * Φ (r τ v A ω, (later N τ A).domRestrict ω) ∂Q v) =
      ∫ y, ∫ z, Φ (y, z) ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i) := by
  have hΨ : Measurable[filt τ A] (fun ω => Real.exp (-logB τ v A ω)) := by
    have := bank_filt_measurable τ v hτ0 hτ A h0
    fun_prop
  have h := freezeGen (filt τ A) _ (Q v) ((filt τ).le A) (D3EventVariancesProof.coordAlg_le _)
    (indep_blocks τ v A) (r τ v A) _ _ (rate_filt_measurable τ v A) hΨ
    (later_measurable τ A) Φ hΦ hint
  rw [later_law] at h
  rw [h.2]
  have hG : Measurable (fun y : ℝ => ∫ z, Φ (y, z) ∂Qlater τ v A) :=
    hΦ.stronglyMeasurable.integral_prod_right'.measurable
  exact discounted_integral τ v hτ0 hτ A h0 _ hG.aestronglyMeasurable

lemma discount : discountStatement := by
  intro N τ v hτ0 hτ A h0
  have hl := discounted_law τ v hτ0 hτ A h0
  exact ⟨density_integral τ v hτ0 hτ A h0, hl.isProbabilityMeasure, hl,
    fun Φ hΦ hint => change_of_measure τ v hτ0 hτ A h0 Φ hΦ hint⟩

/-! ### (e) exact compounding with meetings at partition points, and the initial quote -/

lemma bond_inv (a b : ℝ) (hab : a ≤ b)
    (hno : ∀ i : Fin N, ¬ (a < τ (i.val+1) ∧ τ (i.val+1) < b)) (ω : Ω N) :
    (P τ v a b ω)⁻¹ = Real.exp (∫ s in a..b, r τ v s ω) := by
  have hb : ∀ᵐ x : ℝ, x ∉ ({b} : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton b)
  have he : (∫ s in a..b, f τ v a s ω) = ∫ s in a..b, r τ v s ω := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hb] with s hs hsI
    rw [uIoc_of_le hab] at hsI
    have hsb : s < b := lt_of_le_of_ne hsI.2 (fun h => hs (by simp [h]))
    simp only [f, r]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : τ (i.val+1) ≤ a ↔ τ (i.val+1) ≤ s := by
      constructor
      · exact fun h => h.trans hsI.1.le
      · intro h
        by_contra hna
        exact hno i ⟨lt_of_not_ge hna, h.trans_lt hsb⟩
    simp only [hiff]
  simp [P, he, ← Real.exp_neg]

lemma factor_eq {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (hno : ∀ (j : Fin J) (i : Fin N), ¬ (u j.castSucc < τ (i.val+1) ∧ τ (i.val+1) < u j.succ))
    (j : Fin J) (ω : Ω N) :
    1+(u j.succ-u j.castSucc)*L0202 τ v u j ω =
      Real.exp (∫ s in u j.castSucc..u j.succ, r τ v s ω) := by
  have hj : u j.castSucc < u j.succ := hu (by simp)
  rw [← bond_inv τ v _ _ hj.le (hno j) ω]
  unfold L0202
  field_simp [(sub_pos.mpr hj).ne']
  ring

lemma compound_eq {J : ℕ} (u : Fin (J+1) → ℝ) (hu : StrictMono u)
    (hno : ∀ (j : Fin J) (i : Fin N), ¬ (u j.castSucc < τ (i.val+1) ∧ τ (i.val+1) < u j.succ))
    (ω : Ω N) :
    (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0202 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω) := by
  simp_rw [factor_eq τ v u hu hno]
  rw [← Real.exp_sum]
  congr 1
  have he (j : Fin J) : (∫ s in u j.castSucc..u j.succ, r τ v s ω) =
      logB τ v (u j.succ) ω-logB τ v (u j.castSucc) ω := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (CompoundedFuturesIdentificationProof.rate_integrable τ v 0 (u j.castSucc) ω)
      (CompoundedFuturesIdentificationProof.rate_integrable τ v (u j.castSucc) (u j.succ) ω)
    change logB τ v (u j.castSucc) ω+(∫ s in u j.castSucc..u j.succ, r τ v s ω) =
      logB τ v (u j.succ) ω at h
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

lemma exponent_cases (a b T : ℝ) (hab : a ≤ b) (x : ℝ) :
    Standalone.CompoundedFuturesIdentification.h a b T * x =
      if T ≤ a then (b-a)*x*(b-T) else if T ≤ b then x*(b-T)^2 else 0 := by
  simp only [Standalone.CompoundedFuturesIdentification.h,
    Standalone.CompoundedFuturesIdentification.d, Standalone.CompoundedFuturesIdentification.w]
  split_ifs with h1 h2
  · rw [max_eq_left (sub_nonneg.mpr (h1.trans hab)), max_eq_left (sub_nonneg.mpr h1)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h2), max_eq_right (sub_nonpos.mpr (le_of_not_ge h1))]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h2)),
      max_eq_right (sub_nonpos.mpr (le_of_not_ge h1))]
    ring

lemma accrual_exp_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (∫ ω, Real.exp (∫ s in a..b, r τ v s ω) ∂Q v) =
      Real.exp (Standalone.CompoundedFuturesIdentification.p τ v a b) := by
  have hg := integral_congr_ae
    (CompoundedFuturesIdentificationProof.futures_condExp τ v hτ0 hτ a b ha hab 0)
  rw [integral_condExp ((Standalone.CompoundedFuturesIdentification.filt τ).le 0)] at hg
  simp_rw [CompoundedFuturesIdentificationProof.futures_initial τ v hτ0 hτ] at hg
  simp only [integral_const, probReal_univ, one_smul] at hg
  exact hg

lemma futures : futuresStatement := by
  intro N J τ v hτ0 hτ hJ u hu h0 hno
  have hab : u 0 < u (Fin.last J) := hu (by change (0 : ℕ) < J; exact hJ)
  have he : R0202 τ v u = fun ω =>
      (Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)-1)/(u (Fin.last J)-u 0) := by
    funext ω
    rw [R0202, compound_eq τ v u hu hno]
  have hexp : Integrable (fun ω : Ω N => Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) (Q v) :=
    CompoundedFuturesIdentificationProof.accrual_exp_integrable τ v hτ0 hτ _ _ h0 hab
  refine ⟨compound_eq τ v u hu hno, ?_, ?_⟩
  · rw [he]
    exact (hexp.sub (integrable_const 1)).div_const _
  · rw [he, integral_div, integral_sub hexp (integrable_const 1)]
    simp only [integral_const, probReal_univ, one_smul]
    rw [accrual_exp_integral τ v hτ0 hτ _ _ h0 hab]
    congr 3
    simp only [Standalone.CompoundedFuturesIdentification.p]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact exponent_cases _ _ _ hab.le _

/-! ### (c) prices of contracts settled after `A` -/

lemma extLater_domRestrict (A : ℝ) (ω : Ω N) (i : Fin N) (hi : A < τ (i.val+1)) :
    extLater τ A ((later N τ A).domRestrict ω) i = ω i := by
  simp only [extLater, dif_pos hi, Set.domRestrict]

lemma bank_ratio (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (hAS : A ≤ S) (ω : Ω N) :
    logB τ v S ω - logB τ v A ω =
      accrualAfter τ v A S (r τ v A ω) ((later N τ A).domRestrict ω) := by
  classical
  rcases hAS.eq_or_lt with rfl | hlt
  · simp only [sub_self, accrualAfter, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
      add_zero, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with h
    · exact absurd (h.1.trans_le h.2) (lt_irrefl _)
    · rfl
  · have hint : logB τ v S ω - logB τ v A ω = ∫ s in A..S, r τ v s ω := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (CompoundedFuturesIdentificationProof.rate_integrable τ v 0 A ω)
        (CompoundedFuturesIdentificationProof.rate_integrable τ v A S ω)
      change logB τ v A ω + (∫ s in A..S, r τ v s ω) = logB τ v S ω at h
      linarith
    have hacc : (∫ s in A..S, r τ v s ω) = ∑ i,
        (Standalone.CompoundedFuturesIdentification.w A S (τ (i.val+1))*ω i +
          Standalone.CompoundedFuturesIdentification.d A S (τ (i.val+1))*(v i : ℝ)) :=
      CompoundedFuturesIdentificationProof.accrual_integral τ v hτ0 hτ A S h0 hlt ω
    rw [hint, hacc, rate_past_sum, accrualAfter, Vk, past, Finset.sum_filter, Finset.sum_filter]
    simp only [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Standalone.CompoundedFuturesIdentification.w,
      Standalone.CompoundedFuturesIdentification.d]
    by_cases hA : τ (i.val+1) ≤ A
    · have hS : τ (i.val+1) ≤ S := hA.trans hlt.le
      have hnot : ¬ (A < τ (i.val+1) ∧ τ (i.val+1) ≤ S) := fun h => absurd hA (not_le.mpr h.1)
      rw [if_pos hA, if_pos hA, if_neg hnot, max_eq_left (sub_nonneg.mpr hS),
        max_eq_left (sub_nonneg.mpr hA)]
      ring
    · rw [if_neg hA, if_neg hA, max_eq_right (sub_nonpos.mpr (le_of_not_ge hA))]
      by_cases hS : τ (i.val+1) ≤ S
      · rw [if_pos ⟨lt_of_not_ge hA, hS⟩, max_eq_left (sub_nonneg.mpr hS),
          extLater_domRestrict τ A ω i (lt_of_not_ge hA)]
        ring
      · rw [if_neg (fun h => hS h.2), max_eq_right (sub_nonpos.mpr (le_of_not_ge hS))]
        ring

lemma accrualAfter_measurable (A S : ℝ) :
    Measurable (fun p : ℝ × (later N τ A → ℝ) => accrualAfter τ v A S p.1 p.2) := by
  classical
  unfold accrualAfter
  refine (Measurable.add (by fun_prop) ?_)
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : A < τ (i.val+1) ∧ τ (i.val+1) ≤ S
  · simp only [if_pos h, extLater, dif_pos h.1]
    fun_prop
  · simp only [if_neg h]
    exact measurable_const

lemma price (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A) (hAS : A ≤ S)
    (Ψ : ℝ × (later N τ A → ℝ) → ℝ) (hΨ : Measurable Ψ)
    (hint : Integrable (fun ω => Real.exp (-logB τ v S ω) *
      Ψ (r τ v A ω, (later N τ A).domRestrict ω)) (Q v)) :
    (∫ ω, Real.exp (-logB τ v S ω) * Ψ (r τ v A ω, (later N τ A).domRestrict ω) ∂Q v) =
      ∫ y, ∫ z, Real.exp (-accrualAfter τ v A S y z) * Ψ (y, z)
        ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i) := by
  have hΦ : Measurable (fun p : ℝ × (later N τ A → ℝ) =>
      Real.exp (-accrualAfter τ v A S p.1 p.2) * Ψ p) :=
    (Real.measurable_exp.comp (accrualAfter_measurable τ v A S).neg).mul hΨ
  have he : ∀ ω, Real.exp (-logB τ v S ω) * Ψ (r τ v A ω, (later N τ A).domRestrict ω) =
      Real.exp (-logB τ v A ω) * (Real.exp (-accrualAfter τ v A S (r τ v A ω)
        ((later N τ A).domRestrict ω)) * Ψ (r τ v A ω, (later N τ A).domRestrict ω)) := by
    intro ω
    rw [← bank_ratio τ v hτ0 hτ A S h0 hAS ω, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hint' : Integrable (fun ω => Real.exp (-logB τ v A ω) *
      (fun p : ℝ × (later N τ A → ℝ) => Real.exp (-accrualAfter τ v A S p.1 p.2) * Ψ p)
        (r τ v A ω, (later N τ A).domRestrict ω)) (Q v) :=
    hint.congr (Eventually.of_forall he)
  rw [integral_congr_ae (Eventually.of_forall he)]
  exact change_of_measure τ v hτ0 hτ A h0 _ hΦ hint'

lemma priceProp : priceStatement := by
  intro N τ v hτ0 hτ A S h0 hAS
  exact ⟨bank_ratio τ v hτ0 hτ A S h0 hAS, fun Ψ hΨ hint => price τ v hτ0 hτ A S h0 hAS Ψ hΨ hint⟩

/-! ### (f) identification of the aggregates from the quote exponents -/

lemma exponent_split (v : Fin N → NNReal) (A a b : ℝ)
    (hpast : ∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a) :
    quoteExponent τ v a b = (b-a)*(b*Vk τ v A - Hk τ v A) +
      ∑ i, (if τ (i.val+1) ≤ A then 0 else
        if τ (i.val+1) ≤ a then (b-a)*(v i : ℝ)*(b-τ (i.val+1))
        else if τ (i.val+1) ≤ b then (v i : ℝ)*(b-τ (i.val+1))^2 else 0) := by
  classical
  have hV : (b-a)*(b*Vk τ v A - Hk τ v A) =
      ∑ i, (if τ (i.val+1) ≤ A then (b-a)*(v i : ℝ)*(b-τ (i.val+1)) else 0) := by
    simp only [Vk, Hk, past, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hV, ← Finset.sum_add_distrib, quoteExponent]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hA : τ (i.val+1) ≤ A
  · rw [if_pos hA, if_pos hA, if_pos (hpast i hA), add_zero]
  · rw [if_neg hA, if_neg hA, zero_add]

lemma identification : identificationStatement := by
  intro N τ v v' A hlater
  refine ⟨?_, ?_, ?_⟩
  · intro hV hH a b hpast
    rw [exponent_split τ v A a b hpast, exponent_split τ v' A a b hpast, hV, hH]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hA : τ (i.val+1) ≤ A
    · rw [if_pos hA, if_pos hA]
    · rw [if_neg hA, if_neg hA, hlater i (lt_of_not_ge hA)]
  · intro a b hab
    constructor
    · intro h
      have hδ : (b-a) ≠ 0 := (sub_pos.mpr hab).ne'
      have := (div_left_inj' hδ).mp h
      exact Real.exp_injective (by linarith)
    · intro h
      rw [h]
  · intro a b a' b' hab hab' hbb' hpast hpast' h1 h2
    have hlaterSum : ∀ (c e : ℝ) (hp : ∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ c),
        (∑ i, (if τ (i.val+1) ≤ A then 0 else
          if τ (i.val+1) ≤ c then (e-c)*(v i : ℝ)*(e-τ (i.val+1))
          else if τ (i.val+1) ≤ e then (v i : ℝ)*(e-τ (i.val+1))^2 else 0)) =
        ∑ i, (if τ (i.val+1) ≤ A then 0 else
          if τ (i.val+1) ≤ c then (e-c)*(v' i : ℝ)*(e-τ (i.val+1))
          else if τ (i.val+1) ≤ e then (v' i : ℝ)*(e-τ (i.val+1))^2 else 0) := by
      intro c e _
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hA : τ (i.val+1) ≤ A
      · rw [if_pos hA, if_pos hA]
      · rw [if_neg hA, if_neg hA, hlater i (lt_of_not_ge hA)]
    rw [exponent_split τ v A a b hpast, exponent_split τ v' A a b hpast, hlaterSum a b hpast] at h1
    rw [exponent_split τ v A a' b' hpast', exponent_split τ v' A a' b' hpast',
      hlaterSum a' b' hpast'] at h2
    have e1 : (b-a)*(b*(Vk τ v A - Vk τ v' A) - (Hk τ v A - Hk τ v' A)) = 0 := by linarith
    have e2 : (b'-a')*(b'*(Vk τ v A - Vk τ v' A) - (Hk τ v A - Hk τ v' A)) = 0 := by linarith
    have f1 : b*(Vk τ v A - Vk τ v' A) - (Hk τ v A - Hk τ v' A) = 0 :=
      (mul_eq_zero.mp e1).resolve_left (sub_pos.mpr hab).ne'
    have f2 : b'*(Vk τ v A - Vk τ v' A) - (Hk τ v A - Hk τ v' A) = 0 :=
      (mul_eq_zero.mp e2).resolve_left (sub_pos.mpr hab').ne'
    have g : (b-b')*(Vk τ v A - Vk τ v' A) = 0 := by linarith
    have hV : Vk τ v A - Vk τ v' A = 0 := (mul_eq_zero.mp g).resolve_left (sub_ne_zero.mpr hbb')
    constructor
    · linarith
    · rw [hV] at f1
      linarith

/-! ### (f) the polytope bounds for three revealed meetings -/

lemma bounds : boundsStatement := by
  intro T1 T2 T3 V H h12 h23
  have h31 : 0 < T3 - T1 := by linarith
  have h21 : 0 < T2 - T1 := by linarith
  have h32 : 0 < T3 - T2 := by linarith
  -- the two coordinates determined by the middle one
  have hsolve : ∀ x : Fin 3 → ℝ, x 0 + x 1 + x 2 = V → T1*x 0 + T2*x 1 + T3*x 2 = H →
      x 0 * (T3 - T1) = T3*V - H - (T3-T2)*x 1 ∧
      x 2 * (T3 - T1) = H - T1*V - (T2-T1)*x 1 := by
    intro x hs hH
    constructor
    · linear_combination T3*hs - hH
    · linear_combination hH - T1*hs
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨x, hx, hs, hH⟩
      have e1 : H - T1*V = (T2-T1)*x 1 + (T3-T1)*x 2 := by linear_combination T1*hs - hH
      have e2 : T3*V - H = (T3-T1)*x 0 + (T3-T2)*x 1 := by linear_combination hH - T3*hs
      constructor
      · nlinarith [mul_nonneg h21.le (hx 1), mul_nonneg h31.le (hx 2)]
      · nlinarith [mul_nonneg h31.le (hx 0), mul_nonneg h32.le (hx 1)]
    · rintro ⟨hlo, hhi⟩
      refine ⟨![(T3*V - H)/(T3-T1), 0, (H - T1*V)/(T3-T1)], ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · exact div_nonneg (by linarith) h31.le
        · exact le_rfl
        · exact div_nonneg (by linarith) h31.le
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
  · intro hlo hhi
    have hs1 : 0 ≤ (H - T1*V)/(T2-T1) := div_nonneg (by linarith) h21.le
    have hs2 : 0 ≤ (T3*V - H)/(T3-T2) := div_nonneg (by linarith) h32.le
    have hsmin1 : sStar T1 T2 T3 V H ≤ (H - T1*V)/(T2-T1) := min_le_left _ _
    have hsmin2 : sStar T1 T2 T3 V H ≤ (T3*V - H)/(T3-T2) := min_le_right _ _
    have hsmin1' : (T2-T1)*sStar T1 T2 T3 V H ≤ H - T1*V := by
      have := mul_le_mul_of_nonneg_left hsmin1 h21.le
      rwa [mul_div_cancel₀ _ h21.ne'] at this
    have hsmin2' : (T3-T2)*sStar T1 T2 T3 V H ≤ T3*V - H := by
      have := mul_le_mul_of_nonneg_left hsmin2 h32.le
      rwa [mul_div_cancel₀ _ h32.ne'] at this
    refine ⟨le_min hs1 hs2, ?_, ?_, ?_⟩
    · intro x hx hs hH
      obtain ⟨hx0, hx2⟩ := hsolve x hs hH
      have hx0' : x 0 = (T3*V - H - (T3-T2)*x 1)/(T3-T1) := by
        rw [eq_div_iff h31.ne']; exact hx0
      have hx2' : x 2 = (H - T1*V - (T2-T1)*x 1)/(T3-T1) := by
        rw [eq_div_iff h31.ne']; exact hx2
      have hb1 : x 1 ≤ (H - T1*V)/(T2-T1) := by
        rw [le_div_iff₀ h21]
        nlinarith [hx 2]
      have hb2 : x 1 ≤ (T3*V - H)/(T3-T2) := by
        rw [le_div_iff₀ h32]
        nlinarith [hx 0]
      have hb : x 1 ≤ sStar T1 T2 T3 V H := le_min hb1 hb2
      refine ⟨hb, ?_, ?_, ?_, ?_⟩
      · rw [hx0', div_le_div_iff_of_pos_right h31]
        nlinarith
      · rw [hx0', div_le_div_iff_of_pos_right h31]
        nlinarith [hx 1]
      · rw [hx2', div_le_div_iff_of_pos_right h31]
        nlinarith
      · rw [hx2', div_le_div_iff_of_pos_right h31]
        nlinarith [hx 1]
    · refine ⟨![(T3*V - H)/(T3-T1), 0, (H - T1*V)/(T3-T1)], ?_, ?_, ?_, rfl, rfl, rfl⟩
      · intro i
        fin_cases i
        · exact div_nonneg (by linarith) h31.le
        · exact le_rfl
        · exact div_nonneg (by linarith) h31.le
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
    · refine ⟨![(T3*V - H - (T3-T2)*sStar T1 T2 T3 V H)/(T3-T1), sStar T1 T2 T3 V H,
        (H - T1*V - (T2-T1)*sStar T1 T2 T3 V H)/(T3-T1)], ?_, ?_, ?_, rfl, rfl, rfl⟩
      · intro i
        fin_cases i
        · exact div_nonneg (by linarith) h31.le
        · exact le_min hs1 hs2
        · exact div_nonneg (by linarith) h31.le
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring

lemma exampleBounds : exampleBoundsStatement := by
  intro ε hε
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp at this
    linarith
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp; ring
  · simp; ring
  · simp; ring
  · simp; ring
  · simp only [sStar]
    norm_num
    rw [show 14*ε - 7*ε = 7*ε by ring, show 3*(7*ε) - 14*ε = 7*ε by ring, min_self]

/-! ### (f) pair equality for the prices of (c) -/

lemma pairPrice : pairPriceStatement := by
  intro N τ v v' hτ0 hτ A S h0 hAS hlater hV Ψ hΨ hint hint'
  rw [price τ v hτ0 hτ A S h0 hAS Ψ hΨ hint, price τ v' hτ0 hτ A S h0 hAS Ψ hΨ hint']
  have hQ : Qlater τ v A = Qlater τ v' A := by
    unfold Qlater
    congr 1
    funext i
    rw [hlater i.1 i.2]
  have hsum : (∑ i ∈ past τ A, v i) = ∑ i ∈ past τ A, v' i := by
    apply NNReal.coe_injective
    simpa [NNReal.coe_sum, Vk] using hV
  have hacc : ∀ y z, accrualAfter τ v A S y z = accrualAfter τ v' A S y z := by
    intro y z
    unfold accrualAfter
    rw [hV]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [hlater i h.1]
    · rfl
  rw [hQ, hsum]
  simp only [hacc]

/-! ### (f) the general polytope -/

lemma polytope : polytopeStatement := by
  intro m T V H hT hV
  have hlast : T 0 ≤ T (Fin.last m) := hT (Fin.zero_le _)
  have hex : T 0 * V ≤ H → H ≤ T (Fin.last m) * V →
      ∃ x : Fin (m+1) → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = V ∧ ∑ i, T i * x i = H ∧
        ∀ i, i ≠ 0 → i ≠ Fin.last m → x i = 0 := by
    intro h1 h2
    classical
    rcases eq_or_lt_of_le hlast with heq | hlt
    · rw [← heq] at h2
      have hH : H = T 0 * V := le_antisymm h2 h1
      refine ⟨fun i => if i = 0 then V else 0, fun i => ?_, ?_, ?_, fun i hi _ => if_neg hi⟩
      · show 0 ≤ if i = 0 then V else 0
        split_ifs
        · exact hV
        · exact le_rfl
      · simp
      · rw [hH]
        simp
    · set a := (T (Fin.last m) * V - H) / (T (Fin.last m) - T 0) with ha
      set b := (H - T 0 * V) / (T (Fin.last m) - T 0) with hb
      have hd : 0 < T (Fin.last m) - T 0 := sub_pos.mpr hlt
      have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr h2) hd.le
      have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr h1) hd.le
      have h0l : (0 : Fin (m+1)) ≠ Fin.last m := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      let x : Fin (m+1) → ℝ := fun i => if i = 0 then a else if i = Fin.last m then b else 0
      have hx0 : x 0 = a := by simp [x]
      have hxl : x (Fin.last m) = b := by simp [x, h0l.symm]
      have hxo : ∀ i, i ≠ 0 → i ≠ Fin.last m → x i = 0 := fun i hi hi' => by simp [x, hi, hi']
      have hsum : ∀ g : Fin (m+1) → ℝ, ∑ i, g i * x i = g 0 * a + g (Fin.last m) * b := by
        intro g
        rw [Finset.sum_eq_add_of_mem 0 (Fin.last m) (Finset.mem_univ _) (Finset.mem_univ _) h0l
          (fun c _ hc => by rw [hxo c hc.1 hc.2, mul_zero]), hx0, hxl]
      refine ⟨x, fun i => ?_, ?_, ?_, hxo⟩
      · by_cases hi : i = 0
        · rw [hi, hx0]; exact ha0
        · by_cases hi' : i = Fin.last m
          · rw [hi', hxl]; exact hb0
          · rw [hxo i hi hi']
      · have := hsum (fun _ => 1)
        simp only [one_mul] at this
        rw [this, ha, hb]
        field_simp
        ring
      · rw [hsum, ha, hb]
        field_simp
        ring
  refine ⟨⟨fun ⟨x, hx0, hxV, hxH⟩ => ⟨?_, ?_⟩, fun h => ?_⟩, hex⟩
  · calc T 0 * V = ∑ i, T 0 * x i := by rw [← Finset.mul_sum, hxV]
      _ ≤ ∑ i, T i * x i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hT (Fin.zero_le i)) (hx0 i)
      _ = H := hxH
  · calc H = ∑ i, T i * x i := hxH.symm
      _ ≤ ∑ i, T (Fin.last m) * x i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hT (Fin.le_last i)) (hx0 i)
      _ = T (Fin.last m) * V := by rw [← Finset.mul_sum, hxV]
  · obtain ⟨x, hx0, hxV, hxH, -⟩ := hex h.1 h.2
    exact ⟨x, hx0, hxV, hxH⟩

/-! ### (b) the residuals -/

section Residuals
open Standalone.BondOptionMeetingVariances

variable (a : Fin N → ℝ)

/-- The coordinate vector `e_i`. -/
def ei (i : Fin N) : Fin N → ℝ := fun p => if p = i then 1 else 0

instance : IsProbabilityMeasure (Q0148 v a) :=
  (BondOptionMeetingVariancesProof.law_L0149 (v := v) a 0 0).hasGaussianLaw.isProbabilityMeasure

lemma coord_law (i : Fin N) :
    HasLaw (fun ω : Ω N => ω i) (gaussianReal ((v i : ℝ) * a i) (v i)) (Q0148 v a) := by
  classical
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v) a (ei i) 0
  have hf : L0149 0 (ei i) = fun ω : Ω N => ω i := by
    funext ω
    simp [L0149, ei, ite_mul]
  have hm : (0 + ∑ j, ei i j * (v j : ℝ) * a j) = (v i : ℝ) * a i := by
    simp [ei, ite_mul]
  have hv : (∑ j, v j * ((ei i j) ^ 2).toNNReal) = v i := by
    rw [Finset.sum_eq_single i]
    · simp [ei]
    · intro j _ hj
      simp [ei, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hf, hm, hv] at h
  exact h

lemma coord_gaussian (i : Fin N) : HasGaussianLaw (fun ω : Ω N => ω i) (Q0148 v a) :=
  (coord_law v a i).hasGaussianLaw

lemma coord_memLp (i : Fin N) : MemLp (fun ω : Ω N => ω i) 2 (Q0148 v a) :=
  (coord_gaussian v a i).memLp_two

lemma coord_var (i : Fin N) : Var[fun ω : Ω N => ω i; Q0148 v a] = v i := by
  rw [(coord_law v a i).variance_eq, variance_id_gaussianReal]

lemma coord_cov (i j : Fin N) (hij : i ≠ j) :
    cov[fun ω : Ω N => ω i, fun ω : Ω N => ω j; Q0148 v a] = 0 := by
  classical
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v) a (fun p => ei i p + ei j p) 0
  have hf : L0149 0 (fun p => ei i p + ei j p) = (fun ω : Ω N => ω i) + (fun ω : Ω N => ω j) := by
    funext ω
    simp [L0149, ei, add_mul, Finset.sum_add_distrib, ite_mul]
  have hv : (∑ p, v p * ((ei i p + ei j p) ^ 2).toNNReal) = v i + v j := by
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
    · simp [ei, hij, hij.symm]
    · intro p _ hp
      simp [ei, hp.1, hp.2]
  rw [hf, hv] at h
  have hvar := h.variance_eq
  rw [variance_id_gaussianReal, variance_add (coord_memLp v a i) (coord_memLp v a j),
    coord_var, coord_var] at hvar
  push_cast at hvar
  linarith

lemma cov_coord_mul (p q : Fin N) (cp dq : ℝ) :
    cov[fun ω : Ω N => cp * ω p, fun ω : Ω N => dq * ω q; Q0148 v a] =
      if p = q then cp * dq * (v p : ℝ) else 0 := by
  rw [covariance_const_mul_left, covariance_const_mul_right]
  split_ifs with h
  · subst h
    rw [covariance_self (measurable_pi_apply p).aemeasurable, coord_var]
    ring
  · rw [coord_cov v a p q h, mul_zero, mul_zero]

lemma L0149_zero_eq (c : Fin N → ℝ) : L0149 0 c = fun ω : Ω N => ∑ p, c p * ω p := by
  funext ω
  simp [L0149]

lemma cov_sum_sum (c d : Fin N → ℝ) :
    cov[L0149 0 c, L0149 0 d; Q0148 v a] = ∑ p, c p * d p * (v p : ℝ) := by
  classical
  have h := covariance_fun_sum_fun_sum (μ := Q0148 v a) (X := fun p (ω : Ω N) => c p * ω p)
    (Y := fun p (ω : Ω N) => d p * ω p) (fun p => (coord_memLp v a p).const_mul (c p))
    (fun p => (coord_memLp v a p).const_mul (d p))
  rw [L0149_zero_eq, L0149_zero_eq, h]
  simp only [cov_coord_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The covariance of two affine functionals under the discounted measure. -/
lemma cov_linear (b b' : ℝ) (c d : Fin N → ℝ) :
    cov[L0149 b c, L0149 b' d; Q0148 v a] = ∑ p, c p * d p * (v p : ℝ) := by
  have hsum : MemLp (L0149 0 c) 2 (Q0148 v a) :=
    (BondOptionMeetingVariancesProof.law_L0149 (v := v) a c 0).hasGaussianLaw.memLp_two
  have hsum' : MemLp (L0149 0 d) 2 (Q0148 v a) :=
    (BondOptionMeetingVariancesProof.law_L0149 (v := v) a d 0).hasGaussianLaw.memLp_two
  have he : L0149 b c = fun ω : Ω N => L0149 0 c ω + b := by
    funext ω
    simp [L0149, add_comm]
  have he' : L0149 b' d = fun ω : Ω N => L0149 0 d ω + b' := by
    funext ω
    simp [L0149, add_comm]
  rw [he, he', covariance_add_const_left (hsum.integrable one_le_two),
    covariance_add_const_right (hsum'.integrable one_le_two), cov_sum_sum]

/-- Every affine image of the discounted measure is Gaussian. -/
lemma isGaussian_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (M : (Fin N → ℝ) →L[ℝ] F) (b0 : F) :
    IsGaussian ((Q0148 v a).map (fun ω : Ω N => M ω + b0)) := by
  classical
  constructor
  intro L
  have hmeas : Measurable (fun ω : Ω N => M ω + b0) := M.continuous.measurable.add_const _
  rw [Measure.map_map L.continuous.measurable hmeas]
  set c : Fin N → ℝ := fun i => L (M (Pi.single i 1)) with hc
  have hf : (fun ω : Ω N => L (M ω + b0)) = L0149 (L b0) c := by
    funext ω
    have hω : M ω = ∑ i, ω i • M (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' ω]
      simp only [map_sum, map_smul]
    simp only [L0149, map_add, hω, map_sum, map_smul, smul_eq_mul, hc]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h := BondOptionMeetingVariancesProof.law_L0149 (v := v) a c (L b0)
  have hcomp : (L ∘ fun ω : Ω N => M ω + b0) = L0149 (L b0) c := hf
  rw [hcomp, h.map_eq, integral_map hmeas.aemeasurable L.continuous.measurable.aestronglyMeasurable,
    variance_map L.continuous.measurable.aemeasurable hmeas.aemeasurable]
  have h2 : (fun ω : Ω N => L (M ω + b0)) = L0149 (L b0) c := hf
  rw [h2, hcomp, h.integral_eq, h.variance_eq, integral_id_gaussianReal, variance_id_gaussianReal,
    Real.toNNReal_coe]

end Residuals

section ResidualAssembly

lemma Qtilde_eq (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    Qtilde τ v A = Standalone.BondOptionMeetingVariances.Q0148 v
      (BondOptionMeetingVariancesProof.a0148 τ A) := by
  change Standalone.CompoundedFuturesIdentification.QS τ v A = _
  exact CompoundedFuturesIdentificationProof.QS_eq τ v hτ0 hτ A h0

/-- The indicator of the revealed meetings. -/
noncomputable def pastInd (A : ℝ) (p : Fin N) : ℝ := if τ (p.val+1) ≤ A then 1 else 0

lemma pastInd_sq (A : ℝ) (p : Fin N) : pastInd τ A p * pastInd τ A p = pastInd τ A p := by
  unfold pastInd
  split_ifs <;> simp

lemma sum_pastInd_mul (A : ℝ) (f : Fin N → ℝ) :
    (∑ p, pastInd τ A p * f p) = ∑ p ∈ past τ A, f p := by
  classical
  rw [past, Finset.sum_filter]
  simp only [pastInd, ite_mul, one_mul, zero_mul]

lemma rate_eq_L0149 (A : ℝ) :
    r τ v A = Standalone.BondOptionMeetingVariances.L0149
      (∑ p ∈ past τ A, (v p : ℝ) * (A - τ (p.val+1))) (pastInd τ A) := by
  classical
  funext ω
  rw [rate_past_sum, Standalone.BondOptionMeetingVariances.L0149, Finset.sum_add_distrib,
    ← sum_pastInd_mul τ A (fun p => ω p)]
  ring

lemma resid_eq_L0149 (A : ℝ) (i : earlier N τ A) :
    resid τ v A i = Standalone.BondOptionMeetingVariances.L0149
      ((v i.1 : ℝ) * (A - τ (i.1.val+1)) -
        ((v i.1 : ℝ) / Vk τ v A) * ∑ p ∈ past τ A, (v p : ℝ) * (A - τ (p.val+1)))
      (fun p => ei i.1 p - ((v i.1 : ℝ) / Vk τ v A) * pastInd τ A p) := by
  classical
  funext ω
  rw [resid, rate_eq_L0149]
  simp only [Standalone.BondOptionMeetingVariances.L0149, ei, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc,
    ← Finset.mul_sum]
  ring

lemma coord_eq_L0149 (j : Fin N) :
    (fun ω : Ω N => ω j) = Standalone.BondOptionMeetingVariances.L0149 0 (ei j) := by
  classical
  funext ω
  simp [Standalone.BondOptionMeetingVariances.L0149, ei, ite_mul]

lemma residual (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (hV : 0 < Vk τ v A) :
    HasGaussianLaw (fun ω (i : earlier N τ A) => resid τ v A i ω) (Qtilde τ v A) ∧
    IndepFun (fun ω (i : earlier N τ A) => resid τ v A i ω)
      (fun ω => (r τ v A ω, (later N τ A).domRestrict ω)) (Qtilde τ v A) ∧
    ∀ (i : earlier N τ A) (ω : Ω N), ω i.1 + (v i.1 : ℝ) * (A - τ (i.1.val+1)) =
      resid τ v A i ω + ((v i.1 : ℝ) / Vk τ v A) * r τ v A ω := by
  classical
  rw [Qtilde_eq τ v hτ0 hτ A h0]
  set a := BondOptionMeetingVariancesProof.a0148 τ A with ha
  let Y : Option (later N τ A) → Ω N → ℝ := fun j => Option.elim j (r τ v A) (fun j ω => ω j.1)
  let Mlin : (Fin N → ℝ) →ₗ[ℝ] (earlier N τ A → ℝ) × (Option (later N τ A) → ℝ) :=
    LinearMap.prod
      (LinearMap.pi fun i : earlier N τ A =>
        LinearMap.proj i.1 - ((v i.1 : ℝ) / Vk τ v A) • ∑ p ∈ past τ A, LinearMap.proj p)
      (LinearMap.pi fun j : Option (later N τ A) =>
        Option.elim j (∑ p ∈ past τ A, LinearMap.proj p) (fun j => LinearMap.proj j.1))
  let M : (Fin N → ℝ) →L[ℝ] (earlier N τ A → ℝ) × (Option (later N τ A) → ℝ) :=
    LinearMap.toContinuousLinearMap Mlin
  let b0 : (earlier N τ A → ℝ) × (Option (later N τ A) → ℝ) :=
    (fun i => (v i.1 : ℝ) * (A - τ (i.1.val+1)) -
        ((v i.1 : ℝ) / Vk τ v A) * ∑ p ∈ past τ A, (v p : ℝ) * (A - τ (p.val+1)),
      fun j => Option.elim j (∑ p ∈ past τ A, (v p : ℝ) * (A - τ (p.val+1))) (fun _ => 0))
  have hM : ∀ ω : Ω N, M ω =
      ((LinearMap.pi fun i : earlier N τ A =>
        (LinearMap.proj i.1 : (Fin N → ℝ) →ₗ[ℝ] ℝ) - ((v i.1 : ℝ) / Vk τ v A) •
          ∑ p ∈ past τ A, (LinearMap.proj p : (Fin N → ℝ) →ₗ[ℝ] ℝ)) ω,
       (LinearMap.pi fun j : Option (later N τ A) =>
        Option.elim j (∑ p ∈ past τ A, (LinearMap.proj p : (Fin N → ℝ) →ₗ[ℝ] ℝ))
          (fun j => (LinearMap.proj j.1 : (Fin N → ℝ) →ₗ[ℝ] ℝ))) ω) :=
    fun ω => rfl
  have hpair : (fun ω => (fun i : earlier N τ A => resid τ v A i ω, fun j => Y j ω)) =
      fun ω : Ω N => M ω + b0 := by
    funext ω
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [hM, b0, Prod.fst_add, Pi.add_apply, LinearMap.pi_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul, resid,
        rate_past_sum, Finset.sum_add_distrib, mul_add]
      ring
    · rcases j with _ | j
      · simp only [hM, b0, Y, Prod.snd_add, Pi.add_apply, LinearMap.pi_apply, Option.elim_none,
          LinearMap.sum_apply, LinearMap.proj_apply, rate_past_sum, Finset.sum_add_distrib]
      · simp only [hM, b0, Y, Prod.snd_add, Pi.add_apply, LinearMap.pi_apply, Option.elim_some,
          LinearMap.proj_apply, add_zero]
  have hG : HasGaussianLaw (fun ω => (fun i : earlier N τ A => resid τ v A i ω, fun j => Y j ω))
      (Standalone.BondOptionMeetingVariances.Q0148 v a) := by
    rw [hpair]
    haveI := isGaussian_affine v a M b0
    exact IsGaussian.hasGaussianLaw (M.continuous.measurable.add_const _).aemeasurable
  refine ⟨hG.fst, ?_, fun i ω => by simp [resid]⟩
  have hVk : Vk τ v A = ∑ p ∈ past τ A, (v p : ℝ) := rfl
  have hcov : ∀ (i : earlier N τ A) (j : Option (later N τ A)),
      cov[fun ω => resid τ v A i ω, Y j; Standalone.BondOptionMeetingVariances.Q0148 v a] = 0 := by
    intro i j
    have hi : τ (i.1.val+1) ≤ A := i.2
    have hIi : pastInd τ A i.1 = 1 := by simp [pastInd, hi]
    rcases j with _ | j
    · change cov[resid τ v A i, r τ v A; _] = 0
      rw [resid_eq_L0149, rate_eq_L0149, cov_linear]
      have hterm : ∀ p, (ei i.1 p - (v i.1 : ℝ) / Vk τ v A * pastInd τ A p) * pastInd τ A p *
          (v p : ℝ) = (if p = i.1 then pastInd τ A p * (v p : ℝ) else 0) -
            (v i.1 : ℝ) / Vk τ v A * (pastInd τ A p * (v p : ℝ)) := by
        intro p
        unfold ei
        split_ifs
        · linear_combination (-((v i.1 : ℝ) / Vk τ v A) * (v p : ℝ)) * pastInd_sq τ A p
        · linear_combination (-((v i.1 : ℝ) / Vk τ v A) * (v p : ℝ)) * pastInd_sq τ A p
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        ← Finset.mul_sum]
      rw [sum_pastInd_mul τ A (fun p => (v p : ℝ)), ← hVk, hIi, one_mul,
        div_mul_cancel₀ _ hV.ne', sub_self]
    · change cov[resid τ v A i, fun ω => ω j.1; _] = 0
      rw [resid_eq_L0149, coord_eq_L0149, cov_linear]
      have hj : ¬ τ (j.1.val+1) ≤ A := not_le.mpr j.2
      have hij : j.1 ≠ i.1 := fun h => hj (h ▸ hi)
      rw [Finset.sum_eq_single j.1]
      · simp [ei, pastInd, hij, hj]
      · intro p _ hp
        simp [ei, hp]
      · intro h
        exact absurd (Finset.mem_univ _) h
  have hind := HasGaussianLaw.indepFun_of_covariance_eval hG hcov
  have hg : Measurable (fun f : Option (later N τ A) → ℝ => (f none, fun j => f (some j))) :=
    (measurable_pi_apply none).prodMk (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
  exact hind.comp measurable_id hg

lemma residualProp : residualStatement := by
  intro N τ v hτ0 hτ A h0 hV
  exact residual τ v hτ0 hτ A h0 hV

end ResidualAssembly

/-! ### (a) the σ-algebra identity (20.4) -/

section SigmaAlgebra

lemma rate_eq_curve (A : ℝ) : r τ v A = f τ v A A := rfl

/-- A revealed shock is a difference of two curve values. -/
lemma jump_from_curve (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (i : Fin N)
    (hi : A < τ (i.val+1)) (U : ℝ) (ω : Ω N) :
    f τ v (τ (i.val+1)) U ω - f τ v (max A (τ i.val)) U ω =
      ω i + (v i : ℝ) * (U - τ (i.val+1)) := by
  classical
  have hiN : i.val + 1 ∈ Iic N := Set.mem_Iic.mpr i.isLt
  have hi0 : i.val ∈ Iic N := Set.mem_Iic.mpr i.isLt.le
  have hprev : τ i.val < τ (i.val+1) := hτ hi0 hiN (Nat.lt_succ_self _)
  have hmax : max A (τ i.val) < τ (i.val+1) := max_lt hi hprev
  simp only [f]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [le_refl, ite_true, not_le.mpr hmax, ite_false, sub_zero]
  · intro j _ hji
    have hjN : j.val + 1 ∈ Iic N := Set.mem_Iic.mpr j.isLt
    rcases lt_or_gt_of_ne hji with h | h
    · have h1 : τ (j.val+1) ≤ τ i.val :=
        hτ.monotoneOn hjN hi0 (Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp h))
      have h2 : τ (j.val+1) ≤ τ (i.val+1) := h1.trans hprev.le
      have h3 : τ (j.val+1) ≤ max A (τ i.val) := h1.trans (le_max_right _ _)
      simp only [h2, h3, ite_true, sub_self]
    · have h1 : τ (i.val+1) < τ (j.val+1) :=
        hτ hiN hjN (Nat.succ_lt_succ (Fin.lt_iff_val_lt_val.mp h))
      have h2 : ¬ τ (j.val+1) ≤ τ (i.val+1) := not_le.mpr h1
      have h3 : ¬ τ (j.val+1) ≤ max A (τ i.val) := not_le.mpr (hmax.trans h1)
      simp only [h2, h3, ite_false, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A vector of revealed coordinates extended by zero to all meetings. -/
noncomputable def extRev (A t : ℝ) (z : revealedIn N τ A t → ℝ) (i : Fin N) : ℝ :=
  if h : A < τ (i.val+1) ∧ τ (i.val+1) ≤ t then z ⟨i, h⟩ else 0

lemma extRev_domRestrict (A t : ℝ) (ω : Ω N) (i : Fin N) (hi : A < τ (i.val+1) ∧ τ (i.val+1) ≤ t) :
    extRev τ A t ((revealedIn N τ A t).domRestrict ω) i = ω i := by
  simp [extRev, hi, Set.domRestrict]

/-- The curve at `(s, U)` as a function of the post-window state. -/
noncomputable def curveOf (A t s U : ℝ) (p : ℝ × (revealedIn N τ A t → ℝ)) : ℝ :=
  p.1 + Vk τ v A * (U - A) +
    ∑ i, (if A < τ (i.val+1) ∧ τ (i.val+1) ≤ s then
      extRev τ A t p.2 i + (v i : ℝ) * (U - τ (i.val+1)) else 0)

lemma curveOf_measurable (A t s U : ℝ) : Measurable (curveOf τ v A t s U) := by
  classical
  unfold curveOf
  refine (Measurable.add (by fun_prop) ?_)
  refine Finset.measurable_sum _ fun i _ => ?_
  have hext : Measurable (fun p : ℝ × (revealedIn N τ A t → ℝ) => extRev τ A t p.2 i) := by
    unfold extRev
    by_cases h' : A < τ (i.val+1) ∧ τ (i.val+1) ≤ t
    · simp only [dif_pos h']
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [dif_neg h']
      exact measurable_const
  by_cases h : A < τ (i.val+1) ∧ τ (i.val+1) ≤ s
  · simp only [h, and_self, ite_true]
    exact hext.add measurable_const
  · simp only [h, ite_false]
    exact measurable_const

lemma curve_eq_curveOf (A t s U : ℝ) (hAs : A ≤ s) (hst : s ≤ t) (ω : Ω N) :
    f τ v s U ω = curveOf τ v A t s U (r τ v A ω, (revealedIn N τ A t).domRestrict ω) := by
  classical
  rw [curve_split τ v A s U hAs ω, curveOf, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [extRev_domRestrict τ A t ω i ⟨h.1, h.2.trans hst⟩]
  · rfl

lemma sigmaAlgebra (hτ : StrictMonoOn τ (Iic N)) (A t : ℝ) (hAt : A ≤ t) :
    curveAlg τ v A t = stateAlg τ v A t := by
  classical
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => iSup_le fun U => ?_
    refine (measurable_iff_comap_le (m₁ := stateAlg τ v A t)).mp ?_
    have hfun : f τ v s U = fun ω =>
        curveOf τ v A t s U (r τ v A ω, (revealedIn N τ A t).domRestrict ω) :=
      funext fun ω => curve_eq_curveOf τ v A t s U hs.1 hs.2 ω
    rw [hfun]
    exact (curveOf_measurable τ v A t s U).comp (comap_measurable _)
  · refine (measurable_iff_comap_le (m₁ := curveAlg τ v A t)).mp ?_
    have hf : ∀ s ∈ Icc A t, ∀ U, Measurable[curveAlg τ v A t] (f τ v s U) := fun s hs U =>
      (measurable_iff_comap_le (m₁ := curveAlg τ v A t)).mpr
        (le_iSup₂_of_le s hs (le_iSup (fun U => MeasurableSpace.comap (f τ v s U) inferInstance) U))
    have hr : Measurable[curveAlg τ v A t] (r τ v A) := by
      rw [rate_eq_curve]
      exact hf A ⟨le_rfl, hAt⟩ A
    have hz : Measurable[curveAlg τ v A t] (revealedIn N τ A t).domRestrict := by
      refine (@measurable_pi_iff (Ω N) (revealedIn N τ A t) (fun _ => ℝ)
        (curveAlg τ v A t) _ _).mpr fun i => ?_
      have hi := i.2
      have hprev : τ i.1.val < τ (i.1.val+1) :=
        hτ (Set.mem_Iic.mpr i.1.isLt.le) (Set.mem_Iic.mpr i.1.isLt) (Nat.lt_succ_self _)
      have hmax : max A (τ i.1.val) < τ (i.1.val+1) := max_lt hi.1 hprev
      have heq : (fun ω : Ω N => ω i.1) = fun ω =>
          f τ v (τ (i.1.val+1)) (τ (i.1.val+1)) ω - f τ v (max A (τ i.1.val)) (τ (i.1.val+1)) ω := by
        funext ω
        rw [jump_from_curve τ v hτ A i.1 hi.1 _ ω, sub_self, mul_zero, add_zero]
      show Measurable[curveAlg τ v A t] (fun ω : Ω N => ω i.1)
      rw [heq]
      exact (hf _ ⟨hi.1.le, hi.2⟩ _).sub
        (hf _ ⟨le_max_left _ _, hmax.le.trans hi.2⟩ _)
    exact hr.prodMk hz

lemma sigmaAlgebraProp : sigmaAlgebraStatement := by
  intro N τ v hτ A t hAt
  exact sigmaAlgebra τ v hτ A t hAt

end SigmaAlgebra

/-! ### (b) the degenerate case `V_k = 0` -/

section Degenerate

lemma degenerate (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (hV : Vk τ v A = 0) :
    (∀ i : earlier N τ A, ∀ᵐ ω ∂Qtilde τ v A, ω i.1 = 0) ∧
    (∀ᵐ ω ∂Qtilde τ v A, r τ v A ω = 0) := by
  classical
  have hv : ∀ i ∈ past τ A, v i = 0 := by
    intro i hi
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => NNReal.coe_nonneg (v i)).mp hV i hi
    exact_mod_cast this
  have hcoord : ∀ i ∈ past τ A, ∀ᵐ ω ∂Qtilde τ v A, ω i = 0 := by
    intro i hi
    rw [Qtilde_eq τ v hτ0 hτ A h0]
    have h := coord_law v (BondOptionMeetingVariancesProof.a0148 τ A) i
    rw [hv i hi, NNReal.coe_zero, zero_mul, gaussianReal_zero_var] at h
    have := (ae_map_iff h.aemeasurable (measurableSet_singleton (0 : ℝ))).mp
      (by rw [h.map_eq]; exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).mpr rfl)
    exact this
  refine ⟨fun i => hcoord i.1 ?_, ?_⟩
  · have hi : τ (i.1.val+1) ≤ A := i.2
    simp only [past, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have hall : ∀ᵐ ω ∂Qtilde τ v A, ∀ i : Fin N, i ∈ past τ A → ω i = 0 := by
    refine ae_all_iff.2 fun i => ?_
    by_cases hi : i ∈ past τ A
    · filter_upwards [hcoord i hi] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall fun ω h => absurd h hi
  filter_upwards [hall] with ω hω
  rw [rate_past_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hω i hi, hv i hi]
  simp

lemma degenerateProp : degenerateStatement := by
  intro N τ v hτ0 hτ A h0 hV
  exact degenerate τ v hτ0 hτ A h0 hV

end Degenerate

/-! ### (b) the σ-algebra form of the residual statement -/

section ResidualAlgebra
open scoped Classical

lemma rate_eq_sum_earlier (A : ℝ) (ω : Ω N) :
    r τ v A ω = ∑ i : earlier N τ A, (ω i.1 + (v i.1 : ℝ) * (A - τ (i.1.val+1))) := by
  rw [rate_past_sum]
  exact Finset.sum_subtype (p := (· ∈ earlier N τ A)) (past τ A)
    (fun i => by simp [past, earlier]) _

/-- `(y, ξ)` as a function of the revealed shocks. -/
noncomputable def residOf (A : ℝ) (z : earlier N τ A → ℝ) : ℝ × (earlier N τ A → ℝ) :=
  (∑ i, (z i + (v i.1 : ℝ) * (A - τ (i.1.val+1))),
    fun i => z i + (v i.1 : ℝ) * (A - τ (i.1.val+1)) -
      ((v i.1 : ℝ) / Vk τ v A) * ∑ j, (z j + (v j.1 : ℝ) * (A - τ (j.1.val+1))))

/-- The revealed shocks as a function of `(y, ξ)`. -/
noncomputable def shocksOf (A : ℝ) (p : ℝ × (earlier N τ A → ℝ)) : earlier N τ A → ℝ :=
  fun i => p.2 i + ((v i.1 : ℝ) / Vk τ v A) * p.1 - (v i.1 : ℝ) * (A - τ (i.1.val+1))

lemma residOf_measurable (A : ℝ) : Measurable (residOf τ v A) := by
  unfold residOf
  refine Measurable.prodMk ?_ ?_
  · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).add_const _
  · refine measurable_pi_iff.mpr fun i => ?_
    refine ((measurable_pi_apply i).add_const _).sub (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).add_const _

lemma shocksOf_measurable (A : ℝ) : Measurable (shocksOf τ v A) := by
  unfold shocksOf
  fun_prop

lemma pair_eq_residOf (A : ℝ) (ω : Ω N) :
    (r τ v A ω, fun i : earlier N τ A => resid τ v A i ω) =
      residOf τ v A ((earlier N τ A).domRestrict ω) := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · exact rate_eq_sum_earlier τ v A ω
  · simp only [residOf, resid, Set.domRestrict]
    rw [rate_eq_sum_earlier]

lemma shocks_eq_shocksOf (A : ℝ) (hV : 0 < Vk τ v A) (ω : Ω N) :
    (earlier N τ A).domRestrict ω =
      shocksOf τ v A (r τ v A ω, fun i : earlier N τ A => resid τ v A i ω) := by
  funext i
  simp only [shocksOf, resid, Set.domRestrict]
  ring

lemma residualAlgebra (A : ℝ) (hV : 0 < Vk τ v A) : revealedAlg τ A = residAlg τ v A := by
  apply le_antisymm
  · refine (measurable_iff_comap_le (m₁ := residAlg τ v A)).mp ?_
    have hfun : (earlier N τ A).domRestrict = fun ω =>
        shocksOf τ v A (r τ v A ω, fun i : earlier N τ A => resid τ v A i ω) :=
      funext fun ω => shocks_eq_shocksOf τ v A hV ω
    rw [hfun]
    exact (shocksOf_measurable τ v A).comp (comap_measurable _)
  · refine (measurable_iff_comap_le (m₁ := revealedAlg τ A)).mp ?_
    have hfun : (fun ω => (r τ v A ω, fun i : earlier N τ A => resid τ v A i ω)) =
        fun ω => residOf τ v A ((earlier N τ A).domRestrict ω) :=
      funext fun ω => pair_eq_residOf τ v A ω
    rw [hfun]
    exact (residOf_measurable τ v A).comp (comap_measurable _)

lemma residualAlgebraProp : residualAlgebraStatement := by
  intro N τ v A hV
  exact residualAlgebra τ v A hV

end ResidualAlgebra

/-! ### (f) extremes of a coordinate over the general polytope -/

section Extremes
open scoped Classical
variable {n : ℕ}

/-- The support of a vector. -/
noncomputable def supp (x : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter fun j => x j ≠ 0

lemma mem_supp {x : Fin n → ℝ} {j : Fin n} : j ∈ supp x ↔ x j ≠ 0 := by simp [supp]

lemma exists_neg_of_sum_zero (δ : Fin n → ℝ) (hs : ∑ j, δ j = 0) (hne : δ ≠ 0) :
    ∃ j, δ j < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply hne
  funext j
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h j).mp hs j (Finset.mem_univ _)

/-- Moving along a null direction of the two constraints until a coordinate hits zero. -/
lemma line_move (T x δ : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hδs : ∑ j, δ j = 0)
    (hδT : ∑ j, T j * δ j = 0) (hneg : ∃ j, δ j < 0) :
    ∃ x' : Fin n → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (∀ j, 0 ≤ δ j → x j ≤ x' j) ∧
      (∀ j, δ j ≤ 0 → x' j ≤ x j) ∧ (∀ j, δ j = 0 → x' j = x j) ∧ ∃ j, δ j < 0 ∧ x' j = 0 := by
  obtain ⟨j0, hj0, hmin⟩ := Set.exists_min_image {j | δ j < 0} (fun j => x j / (-δ j))
    (Set.toFinite _) hneg
  simp only [Set.mem_setOf_eq] at hj0 hmin
  set l := x j0 / (-δ j0) with hl
  have hl0 : 0 ≤ l := div_nonneg (hx j0) (by linarith)
  refine ⟨fun j => x j + l * δ j, fun j => ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, ⟨j0, hj0, ?_⟩⟩
  · rcases le_or_gt 0 (δ j) with h | h
    · have := mul_nonneg hl0 h
      linarith [hx j]
    · have h1 := hmin j h
      have h2 : l * (-δ j) ≤ x j := (le_div_iff₀ (by linarith)).mp h1
      linarith
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hδs, mul_zero, add_zero]
  · simp only [mul_add, Finset.sum_add_distrib]
    have : (∑ j, T j * (l * δ j)) = l * ∑ j, T j * δ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hδT, mul_zero, add_zero]
  · have := mul_nonneg hl0 hj
    linarith
  · have := mul_nonneg hl0 (neg_nonneg.mpr hj)
    linarith
  · simp [hj]
  · have hne : δ j0 ≠ 0 := hj0.ne
    rw [hl]
    field_simp
    ring

lemma sum_mul_single (T : Fin n → ℝ) (p : Fin n) (a : ℝ) :
    ∑ j, T j * (Pi.single p a : Fin n → ℝ) j = T p * a := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A nonzero null direction of the two constraints supported on three given coordinates. -/
lemma direction (T : Fin n → ℝ) (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ δ : Fin n → ℝ, ∑ j, δ j = 0 ∧ ∑ j, T j * δ j = 0 ∧ δ ≠ 0 ∧
      ∀ j, j ≠ p → j ≠ q → j ≠ r → δ j = 0 := by
  by_cases hT : T p = T q ∧ T q = T r
  · refine ⟨Pi.single p 1 + Pi.single q (-1), ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, Fintype.sum_pi_single']
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_single]
      rw [hT.1]
      ring
    · intro h
      have := congrFun h p
      simp [Pi.single_eq_of_ne hpq] at this
    · intro j hjp hjq _
      simp [Pi.single_eq_of_ne hjp, Pi.single_eq_of_ne hjq]
  · refine ⟨Pi.single p (T q - T r) + Pi.single q (T r - T p) + Pi.single r (T p - T q),
      ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, Fintype.sum_pi_single']
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_single]
      ring
    · intro h
      have hp := congrFun h p
      have hq := congrFun h q
      simp [Pi.single_eq_of_ne hpq, Pi.single_eq_of_ne hpr, Pi.single_eq_of_ne hpq.symm,
        Pi.single_eq_of_ne hqr] at hp hq
      exact hT ⟨by linarith, by linarith⟩
    · intro j hjp hjq hjr
      simp [Pi.single_eq_of_ne hjp, Pi.single_eq_of_ne hjq, Pi.single_eq_of_ne hjr]

/-- One reduction step: three positive coordinates can be cut to two without moving the
constraints, raising (resp. lowering) any chosen coordinate. -/
lemma reduce (T x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i p q r : Fin n)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hp : 0 < x p) (hq : 0 < x q) (hr : 0 < x r) :
    (∃ x' : Fin n → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (supp x').card < (supp x).card ∧ x i ≤ x' i) ∧
    (∃ x' : Fin n → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (supp x').card < (supp x).card ∧ x' i ≤ x i) := by
  obtain ⟨δ, hs, hT, hne, hoff⟩ := direction T p q r hpq hpr hqr
  have key : ∀ δ' : Fin n → ℝ, (∑ j, δ' j = 0) → (∑ j, T j * δ' j = 0) → δ' ≠ 0 →
      (∀ j, j ≠ p → j ≠ q → j ≠ r → δ' j = 0) →
      ∃ x' : Fin n → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
        ∑ j, T j * x' j = ∑ j, T j * x j ∧ (supp x').card < (supp x).card ∧
        (0 ≤ δ' i → x i ≤ x' i) ∧ (δ' i ≤ 0 → x' i ≤ x i) := by
    intro δ' hs hT hne hoff
    obtain ⟨x', h0, h1, h2, hup, hdown, hfix, j0, hj0, hj0z⟩ :=
      line_move T x δ' hx hs hT (exists_neg_of_sum_zero δ' hs hne)
    have hsub : supp x' ⊆ supp x := by
      intro j hj
      rw [mem_supp] at hj ⊢
      intro hz
      apply hj
      have hδ : δ' j = 0 := by
        refine hoff j ?_ ?_ ?_
        · rintro rfl; exact hp.ne' hz
        · rintro rfl; exact hq.ne' hz
        · rintro rfl; exact hr.ne' hz
      rw [hfix j hδ, hz]
    have hj0in : j0 ∈ supp x := by
      rw [mem_supp]
      intro hz
      have hδ : δ' j0 = 0 := by
        refine hoff j0 ?_ ?_ ?_
        · rintro rfl; exact hp.ne' hz
        · rintro rfl; exact hq.ne' hz
        · rintro rfl; exact hr.ne' hz
      exact absurd hδ hj0.ne
    have hj0out : j0 ∉ supp x' := by
      rw [mem_supp]
      simp [hj0z]
    refine ⟨x', h0, h1, h2, Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
      ⟨j0, hj0in, hj0out⟩), hup i, hdown i⟩
  have hs' : ∑ j, (-δ) j = 0 := by simp [hs]
  have hT' : ∑ j, T j * (-δ) j = 0 := by simp [hT]
  have hoff' : ∀ j, j ≠ p → j ≠ q → j ≠ r → (-δ) j = 0 := fun j h1 h2 h3 => by
    simp [hoff j h1 h2 h3]
  constructor
  · rcases le_or_gt 0 (δ i) with hi | hi
    · obtain ⟨x', h0, h1, h2, hc, hup, -⟩ := key δ hs hT hne hoff
      exact ⟨x', h0, h1, h2, hc, hup hi⟩
    · obtain ⟨x', h0, h1, h2, hc, hup, -⟩ := key (-δ) hs' hT' (neg_ne_zero.mpr hne) hoff'
      exact ⟨x', h0, h1, h2, hc, hup (by simp; linarith)⟩
  · rcases le_or_gt (δ i) 0 with hi | hi
    · obtain ⟨x', h0, h1, h2, hc, -, hdown⟩ := key δ hs hT hne hoff
      exact ⟨x', h0, h1, h2, hc, hdown hi⟩
    · obtain ⟨x', h0, h1, h2, hc, -, hdown⟩ := key (-δ) hs' hT' (neg_ne_zero.mpr hne) hoff'
      exact ⟨x', h0, h1, h2, hc, hdown (by simp; linarith)⟩

lemma extreme_aux {m : ℕ} (T : Fin (m+1) → ℝ) (i : Fin (m+1)) :
    ∀ (k : ℕ) (x : Fin (m+1) → ℝ), (supp x).card = k → (∀ j, 0 ≤ x j) →
    (∃ x' : Fin (m+1) → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (∃ a b, ∀ j, j ≠ a → j ≠ b → x' j = 0) ∧ x i ≤ x' i) ∧
    (∃ x' : Fin (m+1) → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (∃ a b, ∀ j, j ≠ a → j ≠ b → x' j = 0) ∧ x' i ≤ x i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hcard hx
    rcases Nat.lt_or_ge k 3 with hk | hk
    · have hsub : ∃ a b : Fin (m+1), supp x ⊆ {a, b} := by
        interval_cases k
        · exact ⟨0, 0, by rw [Finset.card_eq_zero.mp hcard]; exact Finset.empty_subset _⟩
        · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
          exact ⟨a, a, by rw [ha]; simp⟩
        · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp hcard
          exact ⟨a, b, by rw [hab]⟩
      obtain ⟨a, b, hab⟩ := hsub
      have hoff : ∀ j, j ≠ a → j ≠ b → x j = 0 := fun j hja hjb => by
        by_contra h
        have := hab (mem_supp.mpr h)
        simp [hja, hjb] at this
      exact ⟨⟨x, hx, rfl, rfl, ⟨a, b, hoff⟩, le_rfl⟩, ⟨x, hx, rfl, rfl, ⟨a, b, hoff⟩, le_rfl⟩⟩
    · obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < (supp x).card)
      rw [mem_supp] at hp hq hr
      have hp' : 0 < x p := lt_of_le_of_ne (hx p) (Ne.symm hp)
      have hq' : 0 < x q := lt_of_le_of_ne (hx q) (Ne.symm hq)
      have hr' : 0 < x r := lt_of_le_of_ne (hx r) (Ne.symm hr)
      obtain ⟨⟨xu, hu0, hu1, hu2, hucard, hui⟩, ⟨xd, hd0, hd1, hd2, hdcard, hdi⟩⟩ :=
        reduce T x hx i p q r hpq hpr hqr hp' hq' hr'
      obtain ⟨⟨xu', hu0', hu1', hu2', hab, hui'⟩, -⟩ :=
        ih _ (by rw [← hcard]; exact hucard) xu rfl hu0
      obtain ⟨-, ⟨xd', hd0', hd1', hd2', hab', hdi'⟩⟩ :=
        ih _ (by rw [← hcard]; exact hdcard) xd rfl hd0
      exact ⟨⟨xu', hu0', hu1'.trans hu1, hu2'.trans hu2, hab, hui.trans hui'⟩,
        ⟨xd', hd0', hd1'.trans hd1, hd2'.trans hd2, hab', hdi'.trans hdi⟩⟩

lemma extreme : extremeStatement := by
  intro m T x hx i
  exact extreme_aux T i _ x rfl hx

end Extremes

/-! ### (d) the state-rule half of the American value -/

section American
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)

lemma stateMap_measurable (A : ℝ) : Measurable (stateMap τ v A) := by
  refine Measurable.prodMk ((rate_filt_measurable τ v A).mono ((filt τ).le A) le_rfl) ?_
  exact measurable_pi_iff.mpr fun i => measurable_pi_apply _

lemma filt_le_completed (t : ℝ) : (filt τ t : MeasurableSpace (Ω N)) ≤
    (completedFilt τ v t : MeasurableSpace (Ωc v)) :=
  fun s hs => ⟨s, hs, Filter.EventuallyEq.refl _ _⟩

lemma accrualAfter_joint_measurable (A : ℝ) :
    Measurable (fun q : ℝ × (ℝ × (later N τ A → ℝ)) => accrualAfter τ v A q.1 q.2.1 q.2.2) := by
  classical
  unfold accrualAfter
  refine Measurable.add (by fun_prop) ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  have hs : MeasurableSet {q : ℝ × (ℝ × (later N τ A → ℝ)) |
      A < τ (i.val+1) ∧ τ (i.val+1) ≤ q.1} :=
    (MeasurableSet.const _).inter (measurableSet_le measurable_const measurable_fst)
  refine Measurable.ite hs ?_ measurable_const
  have hext : Measurable (fun q : ℝ × (ℝ × (later N τ A → ℝ)) => extLater τ A q.2.2 i) := by
    unfold extLater
    by_cases h : A < τ (i.val+1)
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · simp only [dif_neg h]
      exact measurable_const
  exact (hext.mul (measurable_fst.sub_const _)).add (by fun_prop)

/-- The bank account along an exercise time is measurable on the completed space. -/
lemma bank_along_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (σ : Ωc v → ℝ) (hσ : Measurable σ) (hσA : ∀ ω, A ≤ σ ω) :
    Measurable (fun ω : Ωc v => logB τ v (σ ω) ω) := by
  have he : (fun ω : Ωc v => logB τ v (σ ω) ω) = fun ω : Ωc v =>
      ∑ i, (max (σ ω - τ (i.val+1)) 0 * (ω : Ω N) i +
        (v i : ℝ) * (max (σ ω - τ (i.val+1)) 0)^2/2) := by
    funext ω
    exact (CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ _ (h0.trans (hσA ω))
      (ω : Ω N)).trans (CompoundedFuturesIdentificationProof.bank_positive_parts τ v _ (ω : Ω N))
  rw [he]
  have hcoord : ∀ i : Fin N, Measurable (fun ω : Ωc v => (ω : Ω N) i) := fun i =>
    CrossMeetingAmericanProof.completed_measurable v _ (measurable_pi_apply i)
  exact Finset.measurable_sum _ fun i _ =>
    (((hσ.sub_const _).max measurable_const).mul (hcoord i)).add
      ((((hσ.sub_const _).max measurable_const).pow_const 2).const_mul _ |>.div_const _)

lemma pay020_eq (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (σ : Ωc v → ℝ) (ω : Ωc v) (hσA : A ≤ σ ω) :
    pay020 τ v A Φ σ ω = Real.exp (-logB τ v A ω) *
      (Real.exp (-accrualAfter τ v A (σ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ ω, stateMap τ v A ω)) := by
  unfold pay020
  have h : logB τ v (σ ω) ω = logB τ v A ω +
      accrualAfter τ v A (σ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2 := by
    have := bank_ratio τ v hτ0 hτ A (σ ω) h0 hσA ω
    show logB τ v (σ ω) ω = logB τ v A ω +
      accrualAfter τ v A (σ ω) (r τ v A ω) ((later N τ A).domRestrict ω)
    rw [← this, add_sub_cancel]
  rw [h, neg_add, Real.exp_add, mul_assoc]

lemma pay020_bound (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (σ : Ωc v → ℝ) (hσ : ∀ ω, σ ω ∈ Icc A S) (ω : Ωc v) :
    |pay020 τ v A Φ σ ω| ≤ Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) := by
  rw [pay020_eq τ v hτ0 hτ A h0 Φ σ ω (hσ ω).1, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hD _ (hσ ω) (stateMap τ v A ω)) (Real.exp_pos _).le

lemma bound_completed_integrable (A : ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v)) :
    Integrable (fun ω : Ωc v => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Qc v) :=
  (LateAmericanExerciseProof.completion_law v).integrable_comp hint

lemma bound_completed_integral (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ)
    (h0 : 0 ≤ A) (D : ℝ × (later N τ A → ℝ) → ℝ) (hDm : Measurable D) :
    (∫ ω : Ωc v, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Qc v) =
      ∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v := by
  have hm : Measurable (fun ω : Ω N => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) :=
    (Real.measurable_exp.comp (LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0).neg).mul
      (hDm.comp (stateMap_measurable τ v A))
  exact (LateAmericanExerciseProof.completion_law v).integral_comp hm.aestronglyMeasurable

lemma pay020_measurable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (hΦ : Measurable Φ) (σ : Ωc v → ℝ) (hσ : Measurable σ)
    (hσA : ∀ ω, A ≤ σ ω) : Measurable (pay020 τ v A Φ σ) := by
  unfold pay020
  have hr : Measurable (fun ω : Ωc v => r τ v A ω) :=
    CrossMeetingAmericanProof.completed_measurable v _
      ((rate_filt_measurable τ v A).mono ((filt τ).le A) le_rfl)
  have hz : Measurable (fun ω : Ωc v => (later N τ A).domRestrict ω) :=
    measurable_pi_iff.mpr fun i =>
      CrossMeetingAmericanProof.completed_measurable v _ (measurable_pi_apply _)
  have hstate : Measurable (fun ω : Ωc v => stateMap τ v A ω) := hr.prodMk hz
  exact (Real.measurable_exp.comp (bank_along_measurable τ v hτ0 hτ A h0 σ hσ hσA).neg).mul
    (hΦ.comp (hσ.prodMk hstate))

lemma admissible_pay (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hDm : Measurable D)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v))
    (σ : Ωc v → ℝ) (hσ : σ ∈ T0183 τ v A S) :
    Integrable (pay020 τ v A Φ σ) (Qc v) ∧
    |∫ ω, pay020 τ v A Φ σ ω ∂Qc v| ≤
      ∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v := by
  have hσm : Measurable σ := LateAmericanExerciseProof.admissible_measurable τ v A S σ hσ
  have hg := bound_completed_integrable τ v A D hint
  have hb : ∀ ω, ‖pay020 τ v A Φ σ ω‖ ≤ Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) :=
    fun ω => by
      rw [Real.norm_eq_abs]
      exact pay020_bound τ v hτ0 hτ A S h0 Φ D hD σ hσ.1 ω
  have hi : Integrable (pay020 τ v A Φ σ) (Qc v) :=
    hg.mono' (pay020_measurable τ v hτ0 hτ A h0 Φ hΦ σ hσm fun ω => (hσ.1 ω).1).aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  rw [← Real.norm_eq_abs, ← bound_completed_integral τ v hτ0 hτ A h0 D hDm]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono hi.norm hg hb

lemma stateRule_stopping (A S : ℝ) (ρ : ℝ × (later N τ A → ℝ) → ℝ) (hρ : ρ ∈ stateRules N τ A S) :
    IsStoppingTime (completedFilt τ v) (fun ω : Ωc v => ((ρ (stateMap τ v A ω) : ℝ) : WithTop ℝ)) := by
  intro t
  by_cases ht : A ≤ t
  · have hmeas : @Measurable (Ωc v) _ (completedFilt τ v t) (stateFilt N τ A t)
        (fun ω : Ωc v => stateMap τ v A ω) := by
      refine measurable_iff_comap_le.mpr ?_
      change MeasurableSpace.comap _ (⨆ (i : Option (later N τ A)) (_ : revealedBy N τ A i t),
        MeasurableSpace.comap (stateProj N τ A i) inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun hi => ?_
      rw [MeasurableSpace.comap_comp]
      refine (measurable_iff_comap_le.mp ?_)
      cases i with
      | none =>
        show @Measurable (Ωc v) ℝ (completedFilt τ v t) _ (fun ω : Ωc v => r τ v A ω)
        have h1 : Measurable[filt τ t] (r τ v A) :=
          (rate_filt_measurable τ v A).mono ((filt τ).mono ht) le_rfl
        exact fun s hs => filt_le_completed τ v t _ (h1 hs)
      | some i =>
        show @Measurable (Ωc v) ℝ (completedFilt τ v t) _ (fun ω : Ωc v => (ω : Ω N) i.1)
        have hi' : τ (i.1.val+1) ≤ t := hi
        have h1 : Measurable[filt τ t] (fun ω : Ω N => ω i.1) :=
          measurable_iff_comap_le.2 (le_iSup₂_of_le i.1 hi' le_rfl)
        exact fun s hs => filt_le_completed τ v t _ (h1 hs)
    exact hmeas (hρ.2.2.measurableSet_le t)
  · have he : {ω : Ωc v | ((ρ (stateMap τ v A ω) : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, WithTop.coe_le_coe]
      exact not_le.2 ((not_le.1 ht).trans_le (hρ.2.1 _).1)
    rw [he]
    exact @MeasurableSet.empty _ (completedFilt τ v t)

lemma stateRule_admissible (A S : ℝ) (ρ : ℝ × (later N τ A → ℝ) → ℝ)
    (hρ : ρ ∈ stateRules N τ A S) :
    (fun ω : Ωc v => ρ (stateMap τ v A ω)) ∈ T0183 τ v A S :=
  ⟨fun ω => hρ.2.1 _, stateRule_stopping τ v A S ρ hρ⟩

lemma stateRule_value (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hΦ : Measurable Φ)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v))
    (ρ : ℝ × (later N τ A → ℝ) → ℝ) (hρ : ρ ∈ stateRules N τ A S) :
    (∫ ω, pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω ∂Qc v) =
      ∫ y, ∫ z, Real.exp (-accrualAfter τ v A (ρ (y, z)) y z) * Φ (ρ (y, z), (y, z))
        ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i) := by
  set Ψ : ℝ × (later N τ A → ℝ) → ℝ := fun p =>
    Real.exp (-accrualAfter τ v A (ρ p) p.1 p.2) * Φ (ρ p, p) with hΨ
  have hΨm : Measurable Ψ :=
    (Real.measurable_exp.comp ((accrualAfter_joint_measurable τ v A).comp
      (hρ.1.prodMk measurable_id)).neg).mul (hΦ.comp (hρ.1.prodMk measurable_id))
  have hpt : (fun ω : Ωc v => pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω) =
      fun ω : Ωc v => Real.exp (-logB τ v A ω) * Ψ (stateMap τ v A ω) := by
    funext ω
    rw [pay020_eq τ v hτ0 hτ A h0 Φ _ ω (hρ.2.1 _).1]
  have hm : Measurable (fun ω : Ω N => Real.exp (-logB τ v A ω) * Ψ (stateMap τ v A ω)) :=
    (Real.measurable_exp.comp (LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0).neg).mul
      (hΨm.comp (stateMap_measurable τ v A))
  have hΨint : Integrable (fun ω => Real.exp (-logB τ v A ω) * Ψ (stateMap τ v A ω)) (Q v) := by
    refine hint.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hD _ (hρ.2.1 _) _) (Real.exp_pos _).le
  have hc : (∫ ω : Ωc v, Real.exp (-logB τ v A ω) * Ψ (stateMap τ v A ω) ∂Qc v) =
      ∫ ω, Real.exp (-logB τ v A ω) * Ψ (stateMap τ v A ω) ∂Q v :=
    (LateAmericanExerciseProof.completion_law v).integral_comp hm.aestronglyMeasurable
  rw [hpt, hc]
  exact change_of_measure τ v hτ0 hτ A h0 Ψ hΨm hΨint

lemma americanState : americanStateStatement := by
  intro N τ v hτ0 hτ A S h0 hAS Φ D hΦ hDm hD hint
  refine ⟨fun σ hσ => admissible_pay τ v hτ0 hτ A S h0 Φ D hΦ hDm hD hint σ hσ,
    fun ρ hρ => ⟨stateRule_admissible τ v A S ρ hρ,
      stateRule_value τ v hτ0 hτ A S h0 Φ D hΦ hD hint ρ hρ⟩, ?_⟩
  refine csSup_le_csSup ?_ ?_ ?_
  · refine ⟨∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v, ?_⟩
    rintro x ⟨σ, hσ, rfl⟩
    exact (le_abs_self _).trans (admissible_pay τ v hτ0 hτ A S h0 Φ D hΦ hDm hD hint σ hσ).2
  · refine ⟨_, ⟨fun _ => S, ⟨measurable_const, fun _ => ⟨hAS, le_rfl⟩,
      isStoppingTime_const _ _⟩, rfl⟩⟩
  · rintro x ⟨ρ, hρ, rfl⟩
    exact ⟨_, stateRule_admissible τ v A S ρ hρ, rfl⟩

lemma accrualAfter_congr (v v' : Fin N → NNReal) (A : ℝ)
    (hlater : ∀ i : Fin N, A < τ (i.val+1) → v i = v' i) (hV : Vk τ v A = Vk τ v' A)
    (S y : ℝ) (z : later N τ A → ℝ) : accrualAfter τ v A S y z = accrualAfter τ v' A S y z := by
  classical
  unfold accrualAfter
  rw [hV]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [hlater i h.1]
  · rfl

lemma americanAggregate : americanAggregateStatement := by
  intro N τ v v' hτ0 hτ A S h0 hAS hlater hV Φ D hΦ hDm hD hint hint'
  have hD' : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v' A t p.1 p.2) * Φ (t, p)| ≤ D p := by
    intro t ht p
    rw [← accrualAfter_congr τ v v' A hlater hV]
    exact hD t ht p
  have hQ : Qlater τ v A = Qlater τ v' A := by
    unfold Qlater
    congr 1
    funext i
    rw [hlater i.1 i.2]
  have hsum : (∑ i ∈ past τ A, v i) = ∑ i ∈ past τ A, v' i := by
    apply NNReal.coe_injective
    simpa [NNReal.coe_sum, Vk] using hV
  unfold Ustate020
  congr 1
  refine Set.image_congr fun ρ hρ => ?_
  rw [stateRule_value τ v hτ0 hτ A S h0 Φ D hΦ hD hint ρ hρ,
    stateRule_value τ v' hτ0 hτ A S h0 Φ D hΦ hD' hint' ρ hρ, hQ, hsum]
  simp only [accrualAfter_congr τ v v' A hlater hV]

end American

/-! ### (d) the product realization of the discounted measure -/

section Realization
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)

lemma residMap_measurable (A : ℝ) : Measurable (residMap τ v A) := by
  refine measurable_pi_iff.mpr fun i => ?_
  show Measurable fun ω : Ω N => ω i.1 + (v i.1 : ℝ) * (A - τ (i.1.val+1)) -
    ((v i.1 : ℝ) / Vk τ v A) * r τ v A ω
  have hr : Measurable (r τ v A) := (rate_filt_measurable τ v A).mono ((filt τ).le A) le_rfl
  fun_prop

lemma realize_measurable (A : ℝ) : Measurable (realize τ v A) :=
  (residMap_measurable τ v A).prodMk (stateMap_measurable τ v A)

lemma unrealize_measurable (A : ℝ) : Measurable (unrealize τ v A) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold unrealize
  by_cases h : τ (i.val+1) ≤ A
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h]
    by_cases h' : A < τ (i.val+1)
    · simp only [dif_pos h']
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · simp only [dif_neg h']
      exact measurable_const

lemma unrealize_realize (A : ℝ) (hV : 0 < Vk τ v A) (ω : Ω N) :
    unrealize τ v A (realize τ v A ω) = ω := by
  funext i
  unfold unrealize realize residMap stateMap
  by_cases h : τ (i.val+1) ≤ A
  · simp only [dif_pos h, resid]
    ring
  · simp only [dif_neg h, dif_pos (not_le.mp h)]
    rfl

lemma density_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    Integrable (fun ω => Real.exp (-logB τ v A ω)) (Q v) := by
  have he : (fun ω => Real.exp (-logB τ v A ω)) =
      Standalone.BondOptionMeetingVariances.D0148 v (BondOptionMeetingVariancesProof.a0148 τ A) := by
    funext ω
    have hd := BondOptionMeetingVariancesProof.density_eq (v := v) τ A ω
    change Real.exp (-Standalone.CompoundedFuturesIdentification.logB τ v A ω) = _
    rw [CompoundedFuturesIdentificationProof.bank_eq τ v hτ0 hτ A h0]
    exact hd.symm
  rw [he]
  exact BondOptionMeetingVariancesProof.integrable_D0148 (v := v) _

lemma state_law (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A) :
    (Qtilde τ v A).map (stateMap τ v A) =
      (gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A) := by
  have hprob : IsProbabilityMeasure (Qtilde τ v A) :=
    (discount N τ v hτ0 hτ A h0).2.1
  have hsm := stateMap_measurable τ v A
  have : IsProbabilityMeasure ((Qtilde τ v A).map (stateMap τ v A)) :=
    ⟨by rw [Measure.map_apply hsm MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  refine Measure.ext fun s hs => ?_
  have hsec : ∀ y, MeasurableSet (Prod.mk y ⁻¹' s) := fun y => measurable_prodMk_left hs
  have hb : Measurable (logB τ v A) := LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0
  -- the left side as a real integral
  have hL : ((Qtilde τ v A).map (stateMap τ v A) s).toReal =
      ∫ ω, Real.exp (-logB τ v A ω) *
        s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (stateMap τ v A ω) ∂Q v := by
    rw [Measure.map_apply hsm hs, ← measureReal_def, ← integral_indicator_one (hsm hs), Qtilde,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    congr 1
  -- change of measure for the indicator
  have hΦ : Measurable (s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ)) := measurable_one.indicator hs
  have hint : Integrable (fun ω => Real.exp (-logB τ v A ω) *
      s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (stateMap τ v A ω)) (Q v) := by
    refine (density_integrable τ v hτ0 hτ A h0).mono'
      ((Real.measurable_exp.comp hb.neg).mul (hΦ.comp hsm)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
    by_cases hω : stateMap τ v A ω ∈ s
    · rw [Set.indicator_of_mem hω]; simp
    · rw [Set.indicator_of_notMem hω]; simp
  have hcm : (∫ ω, Real.exp (-logB τ v A ω) *
      s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (stateMap τ v A ω) ∂Q v) =
      ∫ y, ∫ z, s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (y, z) ∂Qlater τ v A
        ∂gaussianReal 0 (∑ i ∈ past τ A, v i) :=
    change_of_measure τ v hτ0 hτ A h0 _ hΦ hint
  -- the inner integral is the section measure
  have hinner : ∀ y, (∫ z, s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (y, z) ∂Qlater τ v A) =
      ((Qlater τ v A) (Prod.mk y ⁻¹' s)).toReal := by
    intro y
    rw [← measureReal_def, ← integral_indicator_one (hsec y)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show s.indicator (1 : ℝ × (later N τ A → ℝ) → ℝ) (y, z) =
      (Prod.mk y ⁻¹' s).indicator (1 : (later N τ A → ℝ) → ℝ) z
    by_cases hz : (y, z) ∈ s
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Prod.mk y ⁻¹' s from hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show z ∉ Prod.mk y ⁻¹' s from hz)]
  -- the right side
  have hR : (((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) s).toReal =
      ∫ y, ((Qlater τ v A) (Prod.mk y ⁻¹' s)).toReal ∂gaussianReal 0 (∑ i ∈ past τ A, v i) := by
    rw [Measure.prod_apply hs, integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top _ _)]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ?_
  rw [hL, hcm, hR]
  exact integral_congr_ae (Eventually.of_forall fun y => hinner y)

lemma realize_law (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (hV : 0 < Vk τ v A) :
    (Qtilde τ v A).map (realize τ v A) = ((Qtilde τ v A).map (residMap τ v A)).prod
      ((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) := by
  have hprob : IsProbabilityMeasure (Qtilde τ v A) := (discount N τ v hτ0 hτ A h0).2.1
  have hind : IndepFun (residMap τ v A) (stateMap τ v A) (Qtilde τ v A) :=
    (residual τ v hτ0 hτ A h0 hV).2.1
  have h := (indepFun_iff_map_prod_eq_prod_map_map (residMap_measurable τ v A).aemeasurable
    (stateMap_measurable τ v A).aemeasurable).mp hind
  rw [← state_law τ v hτ0 hτ A h0]
  exact h

lemma realization : realizationStatement := by
  intro N τ v hτ0 hτ A h0 hV
  exact ⟨unrealize_realize τ v A hV, realize_measurable τ v A, unrealize_measurable τ v A,
    state_law τ v hτ0 hτ A h0, realize_law τ v hτ0 hτ A h0 hV⟩

end Realization

/-! ### (d) the sectioning argument -/

section Sectioning
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)

/-- The rational times in `[A, S]`. -/
def ratTimes (A S : ℝ) : Set ℚ := {q | A ≤ (q : ℝ) ∧ (q : ℝ) ≤ S}

/-- The candidate set of the raw exercise time at `ω`: the rational times whose event
contains `ω`, together with `S`. -/
def rawSet (A S : ℝ) (C : ℚ → Set (Ω N)) (ω : Ω N) : Set ℝ :=
  ((fun q : ℚ => (q : ℝ)) '' {q | q ∈ ratTimes A S ∧ ω ∈ C q}) ∪ {S}

/-- The raw exercise time built from events `C q` at rational times. -/
noncomputable def rawTime (A S : ℝ) (C : ℚ → Set (Ω N)) (ω : Ω N) : ℝ := sInf (rawSet A S C ω)

lemma rawSet_nonempty (A S : ℝ) (C : ℚ → Set (Ω N)) (ω : Ω N) : (rawSet A S C ω).Nonempty :=
  ⟨S, Or.inr rfl⟩

lemma rawSet_lower (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N)) (ω : Ω N) :
    ∀ x ∈ rawSet A S C ω, A ≤ x := by
  rintro x (⟨q, ⟨hq, -⟩, rfl⟩ | rfl)
  · exact hq.1
  · exact hAS

lemma rawSet_bddBelow (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N)) (ω : Ω N) :
    BddBelow (rawSet A S C ω) :=
  ⟨A, fun x hx => rawSet_lower A S hAS C ω x hx⟩

lemma rawTime_mem (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N)) (ω : Ω N) :
    rawTime A S C ω ∈ Icc A S :=
  ⟨le_csInf (rawSet_nonempty A S C ω) (rawSet_lower A S hAS C ω),
    csInf_le (rawSet_bddBelow A S hAS C ω) (Or.inr rfl)⟩

/-- Where the events are exactly `{x ≤ q}` for a value `x ∈ [A, S]`, the raw time is `x`. -/
lemma rawTime_eq (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N)) (ω : Ω N) (x : ℝ)
    (hx : x ∈ Icc A S) (h : ∀ q ∈ ratTimes A S, ω ∈ C q ↔ x ≤ q) : rawTime A S C ω = x := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt_rat_imp_le fun q hq => ?_
    by_cases hqS : S ≤ (q : ℝ)
    · exact (csInf_le (rawSet_bddBelow A S hAS C ω) (Or.inr rfl)).trans hqS
    · have hq' : q ∈ ratTimes A S := ⟨hx.1.trans hq.le, (not_le.mp hqS).le⟩
      exact csInf_le (rawSet_bddBelow A S hAS C ω) (Or.inl ⟨q, ⟨hq', (h q hq').mpr hq.le⟩, rfl⟩)
  · refine le_csInf (rawSet_nonempty A S C ω) ?_
    rintro y (⟨q, ⟨hq, hωq⟩, rfl⟩ | rfl)
    · exact (h q hq).mp hωq
    · exact hx.2

/-- The level sets of the raw time at times in `[A, S)`. -/
lemma rawTime_le_iff (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N)) (ω : Ω N) (t : ℝ)
    (htA : A ≤ t) (htS : t < S) :
    rawTime A S C ω ≤ t ↔
      ∀ q' ∈ ratTimes A S, t < q' → ∃ q ∈ ratTimes A S, (q : ℝ) ≤ q' ∧ ω ∈ C q := by
  constructor
  · intro hle q' hq' htq'
    have hlt : sInf (rawSet A S C ω) < q' := hle.trans_lt htq'
    obtain ⟨z, hz, hzq⟩ := exists_lt_of_csInf_lt (rawSet_nonempty A S C ω) hlt
    rcases hz with ⟨q, ⟨hq, hωq⟩, rfl⟩ | rfl
    · exact ⟨q, hq, hzq.le, hωq⟩
    · exact absurd hzq (not_lt.mpr hq'.2)
  · intro h
    refine le_of_forall_lt_rat_imp_le fun q' hq' => ?_
    by_cases hqS : S ≤ (q' : ℝ)
    · exact (csInf_le (rawSet_bddBelow A S hAS C ω) (Or.inr rfl)).trans hqS
    · have hq'' : q' ∈ ratTimes A S := ⟨htA.trans hq'.le, (not_le.mp hqS).le⟩
      obtain ⟨q, hq, hqq', hωq⟩ := h q' hq'' hq'
      exact (csInf_le (rawSet_bddBelow A S hAS C ω) (Or.inl ⟨q, ⟨hq, hωq⟩, rfl⟩)).trans hqq'

/-- The reveal filtration does not grow between `t` and a later `q` without a meeting. -/
lemma filt_le_of_no_meeting (t q : ℝ) (hno : ∀ i : Fin N, τ (i.val+1) ≤ q → τ (i.val+1) ≤ t) :
    (filt τ q : MeasurableSpace (Ω N)) ≤ filt τ t :=
  iSup_mono fun i => iSup_mono' fun h => ⟨hno i h, le_rfl⟩

/-- A rational time just after `t` before the next meeting. -/
lemma exists_rat_no_meeting (S t : ℝ) (htS : t < S) :
    ∃ q₀ : ℚ, t < q₀ ∧ (q₀ : ℝ) < S ∧ ∀ i : Fin N, τ (i.val+1) ≤ q₀ → τ (i.val+1) ≤ t := by
  classical
  by_cases hne : ({i : Fin N | t < τ (i.val+1)} : Set (Fin N)).Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := Set.exists_min_image {i : Fin N | t < τ (i.val+1)}
      (fun i => τ (i.val+1)) (Set.toFinite _) hne
    have hi₀' : t < τ (i₀.val+1) := hi₀
    obtain ⟨q₀, hq₀, hq₀'⟩ := exists_rat_btwn (lt_min htS hi₀' : t < min S (τ (i₀.val+1)))
    refine ⟨q₀, hq₀, hq₀'.trans_le (min_le_left _ _), fun i hi => ?_⟩
    by_contra hcon
    have hiF : i ∈ {i : Fin N | t < τ (i.val+1)} := not_le.mp hcon
    have h1 : τ (i₀.val+1) ≤ τ (i.val+1) := hmin i hiF
    have h2 : (q₀ : ℝ) < τ (i₀.val+1) := hq₀'.trans_le (min_le_right _ _)
    linarith
  · obtain ⟨q₀, hq₀, hq₀'⟩ := exists_rat_btwn htS
    refine ⟨q₀, hq₀, hq₀', fun i hi => ?_⟩
    by_contra hcon
    exact hne ⟨i, not_le.mp hcon⟩

/-- The raw time is a stopping time of the raw reveal filtration. -/
lemma rawTime_stopping (A S : ℝ) (hAS : A ≤ S) (C : ℚ → Set (Ω N))
    (hC : ∀ q : ℚ, MeasurableSet[filt τ q] (C q)) :
    IsStoppingTime (filt τ) (fun ω => (rawTime A S C ω : WithTop ℝ)) := by
  intro t
  have hset : {ω : Ω N | (rawTime A S C ω : WithTop ℝ) ≤ (t : WithTop ℝ)} =
      {ω | rawTime A S C ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
  show MeasurableSet[filt τ t] {ω : Ω N | (rawTime A S C ω : WithTop ℝ) ≤ (t : WithTop ℝ)}
  rw [hset]
  by_cases htA : A ≤ t
  · by_cases htS : t < S
    · obtain ⟨q₀, hq₀t, hq₀S, hno⟩ := exists_rat_no_meeting τ S t htS
      have hq₀ : q₀ ∈ ratTimes A S := ⟨htA.trans hq₀t.le, hq₀S.le⟩
      have he : {ω : Ω N | rawTime A S C ω ≤ t} =
          ⋂ q' : {q' : ℚ // q' ∈ ratTimes A S ∧ t < (q' : ℝ) ∧ (q' : ℝ) ≤ q₀},
            ⋃ q : {q : ℚ // q ∈ ratTimes A S ∧ (q : ℝ) ≤ q'.1}, C q.1 := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Subtype.exists,
          exists_prop, Subtype.forall]
        rw [rawTime_le_iff A S hAS C ω t htA htS]
        constructor
        · rintro h q' ⟨hq', htq', -⟩
          obtain ⟨q, hq, hqq', hωq⟩ := h q' hq' htq'
          exact ⟨q, ⟨hq, hqq'⟩, hωq⟩
        · intro h q' hq' htq'
          by_cases hle : (q' : ℝ) ≤ q₀
          · obtain ⟨q, ⟨hq, hqq'⟩, hωq⟩ := h q' ⟨hq', htq', hle⟩
            exact ⟨q, hq, hqq', hωq⟩
          · obtain ⟨q, ⟨hq, hqq'⟩, hωq⟩ := h q₀ ⟨hq₀, hq₀t, le_rfl⟩
            exact ⟨q, hq, hqq'.trans (not_le.mp hle).le, hωq⟩
      rw [he]
      refine MeasurableSet.iInter fun q' => ?_
      refine (filt_le_of_no_meeting τ t q₀ hno) _ ?_
      refine MeasurableSet.iUnion fun q => ?_
      exact (filt τ).mono (q.2.2.trans q'.2.2.2) _ (hC q.1)
    · have he : {ω : Ω N | rawTime A S C ω ≤ t} = Set.univ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (rawTime_mem A S hAS C ω).2.trans (not_lt.mp htS)
      rw [he]
      exact @MeasurableSet.univ _ (filt τ t)
  · have he : {ω : Ω N | rawTime A S C ω ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact (not_le.mp htA).trans_le (rawTime_mem A S hAS C ω).1
    rw [he]
    exact @MeasurableSet.empty _ (filt τ t)

/-- A stopping time of the raw filtration bounded by `S` is measurable. -/
lemma raw_measurable (S : ℝ) (σ₀ : Ω N → ℝ) (hS : ∀ ω, σ₀ ω ≤ S)
    (hst : IsStoppingTime (filt τ) (fun ω => (σ₀ ω : WithTop ℝ))) : Measurable σ₀ := by
  have h := hst.measurable_of_le (fun ω =>
    show (σ₀ ω : WithTop ℝ) ≤ S from WithTop.coe_le_coe.mpr (hS ω))
  have h' := h.untopA.mono ((filt τ).le S) le_rfl
  simpa using h'

/-- Every admissible exercise time agrees almost surely with a stopping time of the raw reveal
filtration with values in `[A, S]`. -/
lemma exists_raw (A S : ℝ) (hAS : A ≤ S) (σ : Ωc v → ℝ) (hσ : σ ∈ T0183 τ v A S) :
    ∃ σ₀ : Ω N → ℝ, (∀ ω, σ₀ ω ∈ Icc A S) ∧
      IsStoppingTime (filt τ) (fun ω => (σ₀ ω : WithTop ℝ)) ∧ ∀ᵐ ω ∂Q v, σ₀ ω = σ ω := by
  have hC : ∀ q : ℚ, ∃ C : Set (Ω N), MeasurableSet[filt τ q] C ∧
      ∀ᵐ ω ∂Q v, ω ∈ C ↔ σ ω ≤ q := by
    intro q
    obtain ⟨C, hCm, hCe⟩ := hσ.2 (q : ℝ)
    refine ⟨C, hCm, ?_⟩
    have hCe' : ∀ᵐ ω ∂Q v, ((σ ω : WithTop ℝ) ≤ ((q : ℝ) : WithTop ℝ)) = (ω ∈ C) := hCe
    filter_upwards [hCe'] with ω hω
    rw [← WithTop.coe_le_coe, hω]
    exact Iff.rfl
  choose C hCm hCe using hC
  refine ⟨rawTime A S C, rawTime_mem A S hAS C, rawTime_stopping τ A S hAS C hCm, ?_⟩
  have hall : ∀ᵐ ω ∂Q v, ∀ q : ℚ, ω ∈ C q ↔ σ ω ≤ q := ae_all_iff.2 hCe
  filter_upwards [hall] with ω hω
  exact rawTime_eq A S hAS C ω (σ ω) (hσ.1 ω) fun q _ => hω q

/-- The coordinates of the inverse realization at a fixed residual are measurable for the
state filtration once revealed. -/
lemma unrealize_coord_measurable (A t : ℝ) (ξ : earlier N τ A → ℝ) (i : Fin N)
    (hi : τ (i.val+1) ≤ t) :
    @Measurable (ℝ × (later N τ A → ℝ)) ℝ (stateFilt N τ A t) _
      (fun p => unrealize τ v A (ξ, p) i) := by
  unfold unrealize
  by_cases h : τ (i.val+1) ≤ A
  · simp only [dif_pos h]
    have hfst : @Measurable (ℝ × (later N τ A → ℝ)) ℝ (stateFilt N τ A t) _ (fun p => p.1) :=
      measurable_iff_comap_le.2 (le_iSup₂_of_le (none : Option (later N τ A)) trivial le_rfl)
    exact ((measurable_const.add (hfst.const_mul _)).sub measurable_const)
  · simp only [dif_neg h]
    have h' : A < τ (i.val+1) := not_le.mp h
    simp only [dif_pos h']
    exact measurable_iff_comap_le.2 (le_iSup₂_of_le (some ⟨i, h'⟩) hi le_rfl)

/-- The section of a raw stopping time at a fixed residual is a state rule. -/
lemma section_rule (A S : ℝ) (σ₀ : Ω N → ℝ) (hσm : Measurable σ₀) (h01 : ∀ ω, σ₀ ω ∈ Icc A S)
    (hst : IsStoppingTime (filt τ) (fun ω => (σ₀ ω : WithTop ℝ))) (ξ : earlier N τ A → ℝ) :
    (fun p => σ₀ (unrealize τ v A (ξ, p))) ∈ stateRules N τ A S := by
  refine ⟨hσm.comp ((unrealize_measurable τ v A).comp (measurable_const.prodMk measurable_id)),
    fun p => h01 _, ?_⟩
  intro t
  by_cases htA : A ≤ t
  · have hmeas : @Measurable (ℝ × (later N τ A → ℝ)) (Ω N) (stateFilt N τ A t) (filt τ t)
        (fun p => unrealize τ v A (ξ, p)) := by
      refine measurable_iff_comap_le.mpr ?_
      change MeasurableSpace.comap _ (⨆ (i : Fin N) (_ : τ (i.val + 1) ≤ t),
        MeasurableSpace.comap (fun ω : Ω N => ω i) inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun hi => ?_
      rw [MeasurableSpace.comap_comp]
      exact measurable_iff_comap_le.mp (unrealize_coord_measurable τ v A t ξ i hi)
    exact hmeas (hst t)
  · have he : {p : ℝ × (later N τ A → ℝ) |
        ((σ₀ (unrealize τ v A (ξ, p)) : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, WithTop.coe_le_coe]
      exact not_le.2 ((not_le.1 htA).trans_le (h01 _).1)
    show MeasurableSet[stateFilt N τ A t] {p : ℝ × (later N τ A → ℝ) |
        ((σ₀ (unrealize τ v A (ξ, p)) : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}
    rw [he]
    exact @MeasurableSet.empty _ (stateFilt N τ A t)

/-- The sectioned integrand of the Fubini argument. -/
noncomputable def sectioned (A : ℝ) (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (σ₀ : Ω N → ℝ)
    (q : (earlier N τ A → ℝ) × (ℝ × (later N τ A → ℝ))) : ℝ :=
  Real.exp (-accrualAfter τ v A (σ₀ (unrealize τ v A q)) q.2.1 q.2.2) *
    Φ (σ₀ (unrealize τ v A q), q.2)

lemma sectioned_measurable (A : ℝ) (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (hΦ : Measurable Φ)
    (σ₀ : Ω N → ℝ) (hσm : Measurable σ₀) : Measurable (sectioned τ v A Φ σ₀) := by
  have hρm : Measurable (fun q : (earlier N τ A → ℝ) × (ℝ × (later N τ A → ℝ)) =>
      σ₀ (unrealize τ v A q)) := hσm.comp (unrealize_measurable τ v A)
  unfold sectioned
  exact (Real.measurable_exp.comp ((accrualAfter_joint_measurable τ v A).comp
    (hρm.prodMk measurable_snd)).neg).mul (hΦ.comp (hρm.prodMk measurable_snd))

lemma sectioned_realize (A : ℝ) (hV : 0 < Vk τ v A) (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ)
    (σ₀ : Ω N → ℝ) (ω : Ω N) :
    sectioned τ v A Φ σ₀ (realize τ v A ω) =
      Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω) := by
  unfold sectioned
  rw [unrealize_realize τ v A hV ω]
  rfl

/-- The value of a measurable exercise time as an integral under the discounted measure. -/
lemma raw_value (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (hΦ : Measurable Φ)
    (σ₀ : Ω N → ℝ) (hσm : Measurable σ₀) (h01 : ∀ ω, σ₀ ω ∈ Icc A S) :
    (∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v) =
      ∫ ω, Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω) ∂Qtilde τ v A := by
  have hb : Measurable (logB τ v A) := LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0
  have hGm : Measurable (fun ω : Ω N =>
      Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω)) :=
    (Real.measurable_exp.comp ((accrualAfter_joint_measurable τ v A).comp
      (hσm.prodMk (stateMap_measurable τ v A))).neg).mul
      (hΦ.comp (hσm.prodMk (stateMap_measurable τ v A)))
  have hpt : (fun ω : Ωc v => pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω) = fun ω : Ωc v =>
      Real.exp (-logB τ v A ω) *
        (Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
          Φ (σ₀ ω, stateMap τ v A ω)) := by
    funext ω
    rw [pay020_eq τ v hτ0 hτ A h0 Φ _ ω (h01 _).1]
  have hm : Measurable (fun ω : Ω N => Real.exp (-logB τ v A ω) *
      (Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω))) :=
    (Real.measurable_exp.comp hb.neg).mul hGm
  have hc : (∫ ω : Ωc v, Real.exp (-logB τ v A ω) *
      (Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω)) ∂Qc v) =
      ∫ ω, Real.exp (-logB τ v A ω) *
      (Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω)) ∂Q v :=
    (LateAmericanExerciseProof.completion_law v).integral_comp hm.aestronglyMeasurable
  rw [hpt, hc]
  unfold Qtilde
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- The bound `D` of the payoff is integrable under the discounted measure. -/
lemma bound_tilde_integrable (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v)) :
    Integrable (fun ω => D (stateMap τ v A ω)) (Qtilde τ v A) := by
  have hb : Measurable (logB τ v A) := LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0
  unfold Qtilde
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hint.congr (Eventually.of_forall fun ω => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- The Fubini bound: the value of a raw stopping time is at most the state-rule value. -/
lemma raw_value_le (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (hV : 0 < Vk τ v A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hDm : Measurable D)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v))
    (σ₀ : Ω N → ℝ) (hσm : Measurable σ₀) (h01 : ∀ ω, σ₀ ω ∈ Icc A S)
    (hst : IsStoppingTime (filt τ) (fun ω => (σ₀ ω : WithTop ℝ))) :
    (∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v) ≤ Ustate020 τ v A S Φ := by
  have hprob : IsProbabilityMeasure (Qtilde τ v A) := (discount N τ v hτ0 hτ A h0).2.1
  have hprobΞ : IsProbabilityMeasure ((Qtilde τ v A).map (residMap τ v A)) :=
    ⟨by rw [Measure.map_apply (residMap_measurable τ v A) MeasurableSet.univ, Set.preimage_univ,
      measure_univ]⟩
  have hGm := sectioned_measurable τ v A Φ hΦ σ₀ hσm
  have hGbound : ∀ q, |sectioned τ v A Φ σ₀ q| ≤ D q.2 := fun q => hD _ (h01 _) q.2
  -- the state-rule values are bounded
  have hbdd : BddAbove ((fun ρ => ∫ ω, pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω ∂Qc v) ''
      stateRules N τ A S) := by
    refine ⟨∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v, ?_⟩
    rintro x ⟨ρ, hρ, rfl⟩
    exact (le_abs_self _).trans (admissible_pay τ v hτ0 hτ A S h0 Φ D hΦ hDm hD hint _
      (stateRule_admissible τ v A S ρ hρ)).2
  -- the bound is integrable under the state law
  have hDE : Integrable D ((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) := by
    rw [← state_law τ v hτ0 hτ A h0, integrable_map_measure hDm.aestronglyMeasurable
      (stateMap_measurable τ v A).aemeasurable]
    exact bound_tilde_integrable τ v hτ0 hτ A h0 D hint
  -- every section is a state rule with value at most the state-rule value
  have hsec : ∀ ξ, (∫ p, sectioned τ v A Φ σ₀ (ξ, p)
      ∂(gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) ≤ Ustate020 τ v A S Φ := by
    intro ξ
    have hmem := section_rule τ v A S σ₀ hσm h01 hst ξ
    have hint_ξ : Integrable (fun p => sectioned τ v A Φ σ₀ (ξ, p))
        ((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) :=
      hDE.mono' (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hGbound (ξ, p))
    have hval : (∫ ω, pay020 τ v A Φ (fun ω => σ₀ (unrealize τ v A (ξ, stateMap τ v A ω))) ω
        ∂Qc v) = ∫ y, ∫ z, Real.exp (-accrualAfter τ v A (σ₀ (unrealize τ v A (ξ, (y, z)))) y z) *
          Φ (σ₀ (unrealize τ v A (ξ, (y, z))), (y, z)) ∂Qlater τ v A
          ∂gaussianReal 0 (∑ i ∈ past τ A, v i) :=
      stateRule_value τ v hτ0 hτ A S h0 Φ D hΦ hD hint _ hmem
    have h2 : (∫ p, sectioned τ v A Φ σ₀ (ξ, p)
        ∂(gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)) =
        ∫ ω, pay020 τ v A Φ (fun ω => σ₀ (unrealize τ v A (ξ, stateMap τ v A ω))) ω ∂Qc v := by
      rw [hval]
      exact integral_prod _ hint_ξ
    rw [h2]
    exact le_csSup hbdd ⟨_, hmem, rfl⟩
  -- the raw value through the realization
  rw [raw_value τ v hτ0 hτ A S h0 Φ hΦ σ₀ hσm h01]
  have hG : (fun ω : Ω N =>
      Real.exp (-accrualAfter τ v A (σ₀ ω) (stateMap τ v A ω).1 (stateMap τ v A ω).2) *
        Φ (σ₀ ω, stateMap τ v A ω)) = fun ω => sectioned τ v A Φ σ₀ (realize τ v A ω) := by
    funext ω
    rw [sectioned_realize τ v A hV Φ σ₀ ω]
  rw [hG]
  have hintG : Integrable (fun ω => sectioned τ v A Φ σ₀ (realize τ v A ω)) (Qtilde τ v A) := by
    refine (bound_tilde_integrable τ v hτ0 hτ A h0 D hint).mono'
      (hGm.comp (realize_measurable τ v A)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hGbound (realize τ v A ω)
  have hintP : Integrable (sectioned τ v A Φ σ₀) (((Qtilde τ v A).map (residMap τ v A)).prod
      ((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A))) := by
    rw [← realize_law τ v hτ0 hτ A h0 hV, integrable_map_measure hGm.aestronglyMeasurable
      (realize_measurable τ v A).aemeasurable]
    exact hintG
  have hsplit : (∫ ω, sectioned τ v A Φ σ₀ (realize τ v A ω) ∂Qtilde τ v A) =
      ∫ ξ, ∫ p, sectioned τ v A Φ σ₀ (ξ, p)
        ∂(gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)
        ∂(Qtilde τ v A).map (residMap τ v A) := by
    rw [← integral_map (realize_measurable τ v A).aemeasurable hGm.aestronglyMeasurable,
      realize_law τ v hτ0 hτ A h0 hV]
    exact integral_prod _ hintP
  rw [hsplit]
  calc (∫ ξ, ∫ p, sectioned τ v A Φ σ₀ (ξ, p)
        ∂(gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A)
        ∂(Qtilde τ v A).map (residMap τ v A))
      ≤ ∫ _, Ustate020 τ v A S Φ ∂(Qtilde τ v A).map (residMap τ v A) :=
        integral_mono hintP.integral_prod_left (integrable_const _) fun ξ => hsec ξ
    _ = Ustate020 τ v A S Φ := by rw [integral_const, probReal_univ, one_smul]

lemma sectioning : sectioningStatement := by
  intro N τ v hτ0 hτ A S h0 hAS hV Φ D hΦ hDm hD hint
  refine le_antisymm ?_ (americanState N τ v hτ0 hτ A S h0 hAS Φ D hΦ hDm hD hint).2.2
  refine csSup_le ⟨_, ⟨fun _ => S, stateRule_admissible τ v A S (fun _ => S)
    ⟨measurable_const, fun _ => ⟨hAS, le_rfl⟩, isStoppingTime_const _ _⟩, rfl⟩⟩ ?_
  rintro x ⟨σ, hσ, rfl⟩
  show (∫ ω, pay020 τ v A Φ σ ω ∂Qc v) ≤ Ustate020 τ v A S Φ
  obtain ⟨σ₀, h01, hst, hae⟩ := exists_raw τ v A S hAS σ hσ
  have hσm : Measurable σ₀ := raw_measurable τ S σ₀ (fun ω => (h01 ω).2) hst
  have heq : (∫ ω, pay020 τ v A Φ σ ω ∂Qc v) =
      ∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v := by
    refine integral_congr_ae ?_
    have hae' : ∀ᵐ ω ∂Qc v, σ₀ ω = σ ω := hae
    filter_upwards [hae'] with ω hω
    show Real.exp (-logB τ v (σ ω) ω) * Φ (σ ω, stateMap τ v A ω) =
      Real.exp (-logB τ v (σ₀ ω) ω) * Φ (σ₀ ω, stateMap τ v A ω)
    rw [hω]
  rw [heq]
  exact raw_value_le τ v hτ0 hτ A S h0 hV Φ D hΦ hDm hD hint σ₀ hσm h01 hst

/-- The state-rule values are bounded above by the discounted bound. -/
lemma stateValues_bddAbove (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ) (h0 : 0 ≤ A)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hDm : Measurable D)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v)) :
    BddAbove ((fun ρ => ∫ ω, pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω ∂Qc v) ''
      stateRules N τ A S) := by
  refine ⟨∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v, ?_⟩
  rintro x ⟨ρ, hρ, rfl⟩
  exact (le_abs_self _).trans (admissible_pay τ v hτ0 hτ A S h0 Φ D hΦ hDm hD hint _
    (stateRule_admissible τ v A S ρ hρ)).2

/-- For `V_k = 0` every revealed shock vanishes almost surely under `Q`. -/
lemma revealed_zero (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A : ℝ) (h0 : 0 ≤ A)
    (hV : Vk τ v A = 0) : ∀ᵐ ω ∂Q v, ∀ i : earlier N τ A, ω i.1 = 0 := by
  refine ae_all_iff.2 fun i => ?_
  have h := (degenerate τ v hτ0 hτ A h0 hV).1 i
  have hb : Measurable (logB τ v A) := LateAmericanExerciseProof.bank_measurable τ v hτ0 hτ A h0
  unfold Qtilde at h
  rw [ae_withDensity_iff' (by fun_prop)] at h
  filter_upwards [h] with ω hω
  exact hω (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-- For `V_k = 0` the inverse realization at the zero residual recovers the sample point
whenever its revealed shocks vanish. -/
lemma unrealize_zero_state (A : ℝ) (hV : Vk τ v A = 0) (ω : Ω N)
    (hω : ∀ i : earlier N τ A, ω i.1 = 0) :
    unrealize τ v A ((0 : earlier N τ A → ℝ), stateMap τ v A ω) = ω := by
  classical
  have hv : ∀ i : Fin N, τ (i.val+1) ≤ A → (v i : ℝ) = 0 := by
    intro i hi
    have hmem : i ∈ past τ A := by simp [past, hi]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => (v j).coe_nonneg).1 hV i hmem
    exact this
  funext i
  unfold unrealize
  by_cases h : τ (i.val+1) ≤ A
  · simp only [dif_pos h, Pi.zero_apply, hv i h, zero_div, zero_mul, zero_add, sub_zero]
    exact (hω ⟨i, h⟩).symm
  · simp only [dif_neg h, dif_pos (not_le.mp h)]
    rfl

/-- The degenerate case of the Fubini bound: for `V_k = 0` the raw time is almost surely the
section at the zero residual, a state rule. -/
lemma raw_value_le_degenerate (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (A S : ℝ)
    (h0 : 0 ≤ A) (hV : Vk τ v A = 0)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ)
    (hΦ : Measurable Φ) (hDm : Measurable D)
    (hD : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p)
    (hint : Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v))
    (σ₀ : Ω N → ℝ) (hσm : Measurable σ₀) (h01 : ∀ ω, σ₀ ω ∈ Icc A S)
    (hst : IsStoppingTime (filt τ) (fun ω => (σ₀ ω : WithTop ℝ))) :
    (∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v) ≤ Ustate020 τ v A S Φ := by
  have hmem := section_rule τ v A S σ₀ hσm h01 hst 0
  have heq : (∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v) =
      ∫ ω, pay020 τ v A Φ (fun ω => σ₀ (unrealize τ v A ((0 : earlier N τ A → ℝ),
        stateMap τ v A ω))) ω ∂Qc v := by
    refine integral_congr_ae ?_
    have hz : ∀ᵐ ω ∂Qc v, ∀ i : earlier N τ A, (ω : Ω N) i.1 = 0 :=
      revealed_zero τ v hτ0 hτ A h0 hV
    filter_upwards [hz] with ω hω
    show Real.exp (-logB τ v (σ₀ ω) ω) * Φ (σ₀ ω, stateMap τ v A ω) =
      Real.exp (-logB τ v (σ₀ (unrealize τ v A ((0 : earlier N τ A → ℝ), stateMap τ v A ω))) ω) *
        Φ (σ₀ (unrealize τ v A ((0 : earlier N τ A → ℝ), stateMap τ v A ω)), stateMap τ v A ω)
    rw [unrealize_zero_state τ v A hV ω hω]
  rw [heq]
  exact le_csSup (stateValues_bddAbove τ v hτ0 hτ A S h0 Φ D hΦ hDm hD hint) ⟨_, hmem, rfl⟩

lemma sectioningFull : sectioningFullStatement := by
  intro N τ v hτ0 hτ A S h0 hAS Φ D hΦ hDm hD hint
  have hV0 : 0 ≤ Vk τ v A := Finset.sum_nonneg fun j _ => (v j).coe_nonneg
  rcases hV0.eq_or_lt with hV | hV
  · refine le_antisymm ?_ (americanState N τ v hτ0 hτ A S h0 hAS Φ D hΦ hDm hD hint).2.2
    refine csSup_le ⟨_, ⟨fun _ => S, stateRule_admissible τ v A S (fun _ => S)
      ⟨measurable_const, fun _ => ⟨hAS, le_rfl⟩, isStoppingTime_const _ _⟩, rfl⟩⟩ ?_
    rintro x ⟨σ, hσ, rfl⟩
    show (∫ ω, pay020 τ v A Φ σ ω ∂Qc v) ≤ Ustate020 τ v A S Φ
    obtain ⟨σ₀, h01, hst, hae⟩ := exists_raw τ v A S hAS σ hσ
    have hσm : Measurable σ₀ := raw_measurable τ S σ₀ (fun ω => (h01 ω).2) hst
    have heq : (∫ ω, pay020 τ v A Φ σ ω ∂Qc v) =
        ∫ ω, pay020 τ v A Φ (fun ω : Ωc v => σ₀ ω) ω ∂Qc v := by
      refine integral_congr_ae ?_
      have hae' : ∀ᵐ ω ∂Qc v, σ₀ ω = σ ω := hae
      filter_upwards [hae'] with ω hω
      show Real.exp (-logB τ v (σ ω) ω) * Φ (σ ω, stateMap τ v A ω) =
        Real.exp (-logB τ v (σ₀ ω) ω) * Φ (σ₀ ω, stateMap τ v A ω)
      rw [hω]
    rw [heq]
    exact raw_value_le_degenerate τ v hτ0 hτ A S h0 hV.symm Φ D hΦ hDm hD hint σ₀ hσm h01 hst
  · exact sectioning N τ v hτ0 hτ A S h0 hAS hV Φ D hΦ hDm hD hint

lemma americanGeneral : americanGeneralStatement := by
  intro N τ v v' hτ0 hτ A S h0 hAS hlater hVeq Φ D hΦ hDm hD hint hint'
  have hD' : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v' A t p.1 p.2) * Φ (t, p)| ≤ D p := by
    intro t ht p
    rw [← accrualAfter_congr τ v v' A hlater hVeq]
    exact hD t ht p
  rw [sectioningFull N τ v hτ0 hτ A S h0 hAS Φ D hΦ hDm hD hint,
    sectioningFull N τ v' hτ0 hτ A S h0 hAS Φ D hΦ hDm hD' hint']
  exact americanAggregate N τ v v' hτ0 hτ A S h0 hAS hlater hVeq Φ D hΦ hDm hD hint hint'

lemma americanFull : americanFullStatement := by
  intro N τ v v' hτ0 hτ A S h0 hAS hlater hVeq hV Φ D hΦ hDm hD hint hint'
  have hD' : ∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v' A t p.1 p.2) * Φ (t, p)| ≤ D p := by
    intro t ht p
    rw [← accrualAfter_congr τ v v' A hlater hVeq]
    exact hD t ht p
  rw [sectioning N τ v hτ0 hτ A S h0 hAS hV Φ D hΦ hDm hD hint,
    sectioning N τ v' hτ0 hτ A S h0 hAS (hVeq ▸ hV) Φ D hΦ hDm hD' hint']
  exact americanAggregate N τ v v' hτ0 hτ A S h0 hAS hlater hVeq Φ D hΦ hDm hD hint hint'

end Sectioning

theorem preWindowVarianceAggregates : Standalone.PreWindowVarianceAggregates.statement :=
  ⟨curve, discount, futures, priceProp, identification, bounds, exampleBounds, pairPrice,
    polytope, residualProp, sigmaAlgebraProp, degenerateProp, residualAlgebraProp, extreme,
    americanState, americanAggregate, realization, sectioning, americanFull, sectioningFull,
    americanGeneral⟩

end Novel.PreWindowVarianceAggregatesProof

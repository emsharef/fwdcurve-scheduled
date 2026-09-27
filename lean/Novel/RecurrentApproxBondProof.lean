import Standalone.RecurrentApproxBond
import Novel.RecurrentApproxPriceBoundsProof
import Novel.RecurrenceNecessityCurveProof

open MeasureTheory ProbabilityTheory Set Filter Matrix NormedSpace Topology
open scoped NNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxMeanSquare Standalone.RecurrentApproxPriceBounds
  Standalone.RecurrentApproxBond Standalone.ZeroMeanReversionUpstreamBridge
open Novel.MaturityShapeIdentitiesProof (ii_of_bound)
open Novel.RecurrentApproxEstimatesProof
namespace Novel.RecurrentApproxBondProof

variable {r : ℕ}

/-! ### The split of `σ` -/

lemma count_add (Tm : Finset ℝ) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    count030 Tm s u = count030 Tm s t + count030 Tm t u := by
  classical
  unfold count030
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun τ _ h1 h2 => by linarith [h1.2, h2.1]),
    ← Finset.filter_or]
  congr 1
  refine Finset.filter_congr fun τ _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_or_gt τ t with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.trans htu⟩
    · exact ⟨hst.trans_lt h1, h2⟩

lemma shape_split (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s t u : ℝ) :
    shape030 c b A (u - s) = ∑ j, (c ᵥ* exp ((u - t) • A)) j * (exp ((t - s) • A) *ᵥ b) j :=
  (Novel.RecurrenceNecessityCurveProof.lam_split c A b u t s).symm

/-- `σ(s, u) = Σ_{n,j} g_{n,j}(u) h_{n,j}(s)` for `s ≤ t ≤ u`. -/
lemma sig_split (Tm : Finset ℝ) (a : ℕ → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    sig048 Tm a (shape030 c b A) s u =
      ∑ n ∈ Finset.range (Tm.card + 1), ∑ j, gq048 Tm a c A t n j u * hq048 Tm b A t n j s := by
  rw [Finset.sum_eq_single (count030 Tm s t)]
  · simp only [sig048, gq048, hq048, hst, true_and, ite_true, count_add Tm hst htu,
      shape_split c b A s t u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  · intro n _ hn
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hq048, Ne.symm hn]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (count_le Tm s t))) h

/-! ### Measurability, bounds and continuity -/

lemma countL_meas (Tm : Finset ℝ) (t : ℝ) : Measurable fun s => count030 Tm s t :=
  (count_meas Tm).comp (measurable_id.prodMk measurable_const)

lemma countR_meas (Tm : Finset ℝ) (t : ℝ) : Measurable fun u => count030 Tm t u :=
  (count_meas Tm).comp (measurable_const.prodMk measurable_id)

lemma E2_cont (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (j : Fin r) :
    Continuous fun s : ℝ => (exp ((t - s) • A) *ᵥ b) j :=
  (Novel.RecurrenceNecessityReductionProof.phi_cont A b j).comp (continuous_const.sub continuous_id)

lemma E1_cont (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (j : Fin r) :
    Continuous fun u : ℝ => (c ᵥ* exp ((u - t) • A)) j := by
  simp only [vecMul, dotProduct]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    ((Novel.RecurrenceNecessityReductionProof.exp_entry_cont A i j).comp
      (continuous_id.sub continuous_const))

lemma hq_meas (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (n : ℕ)
    (j : Fin r) : Measurable (hq048 Tm b A t n j) :=
  Measurable.ite ((measurableSet_le measurable_id measurable_const).inter
      (countL_meas Tm t (measurableSet_singleton n)))
    (E2_cont b A t j).measurable measurable_const

lemma hq_bdd (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (n : ℕ)
    (j : Fin r) : ∃ B, ∀ s : ℝ≥0, |hq048 Tm b A t n j s| ≤ B := by
  obtain ⟨B, hB⟩ := Novel.RecurrenceNecessityCurveProof.bdd_of_cont
    (fun s : ℝ≥0 => (exp (((t:ℝ) - s) • A) *ᵥ b) j)
    ((E2_cont b A t j).comp NNReal.continuous_coe) t
  refine ⟨B, fun s => ?_⟩
  unfold hq048
  split_ifs with h
  · exact hB s (by exact_mod_cast h.1)
  · simpa using (abs_nonneg _).trans (hB 0 zero_le)

lemma gq_meas (Tm : Finset ℝ) (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ)
    (n : ℕ) (j : Fin r) : Measurable (gq048 Tm a c A t n j) :=
  ((measurable_from_nat (f := a)).comp (measurable_const.add (countR_meas Tm t))).mul
    (E1_cont c A t j).measurable

lemma gq_bdd (Tm : Finset ℝ) (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t H : ℝ)
    (n : ℕ) (j : Fin r) : ∃ B, ∀ u ∈ Icc t H, |gq048 Tm a c A t n j u| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (E1_cont c A t j).continuousOn
    (s := Icc t H)
  refine ⟨(∑ i ∈ Finset.range (n + Tm.card + 1), |a i|) * B, fun u hu => ?_⟩
  rw [gq048, abs_mul]
  refine mul_le_mul ?_ (hB u hu) (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine Finset.single_le_sum (f := fun i => |a i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 ?_)
  have := count_le Tm t u
  omega

/-- `h_{n,j}` is continuous off the meetings and `t`. -/
lemma hq_contAt (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (n : ℕ)
    (j : Fin r) {x : ℝ} (hx : x ∉ Tm) (hxt : x ≠ t) : ContinuousAt (hq048 Tm b A t n j) x := by
  have hcount : ∀ᶠ y in 𝓝 x, count030 Tm y t = count030 Tm x t := by
    have : ∀ᶠ y in 𝓝 x, ∀ τ ∈ Tm, (y < τ ↔ x < τ) := by
      refine (eventually_all_finset Tm).2 fun τ hτ => ?_
      have hne : x ≠ τ := fun h => hx (h ▸ hτ)
      rcases hne.lt_or_gt with h | h
      · filter_upwards [eventually_lt_nhds h] with y hy using iff_of_true hy h
      · filter_upwards [eventually_gt_nhds h] with y hy using
          iff_of_false (not_lt.2 hy.le) (not_lt.2 h.le)
    filter_upwards [this] with y hy
    unfold count030
    congr 1
    exact Finset.filter_congr fun τ hτ => by rw [hy τ hτ]
  rcases hxt.lt_or_gt with h | h
  · have : hq048 Tm b A t n j =ᶠ[𝓝 x]
        fun y => if count030 Tm x t = n then (exp ((t - y) • A) *ᵥ b) j else 0 := by
      filter_upwards [hcount, eventually_lt_nhds h] with y hy hyt
      simp only [hq048, hyt.le, true_and, hy]
    refine ContinuousAt.congr ?_ this.symm
    split_ifs
    · exact (E2_cont b A t j).continuousAt
    · exact continuousAt_const
  · have : hq048 Tm b A t n j =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds h] with y hy
      simp [hq048, not_le.2 hy]
    exact ContinuousAt.congr continuousAt_const this.symm

/-! ### Two facts about deterministic integrands -/

section Ito
variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
open Novel.RecurrenceNecessityGaussianProof (det_U4 det_U5 isometry)

/-- Linearity over a finite family of bounded Borel integrands. -/
lemma I_sum {ι : Type*} (s : Finset ι) (G : ι → ℝ≥0 → ℝ) (hG : ∀ i, Measurable (G i))
    (hB : ∀ i, ∃ B, ∀ x, |G i x| ≤ B) (κ : ι → ℝ) (t : ℝ≥0) :
    (fun ω => ∑ i ∈ s, κ i * S.I k (fun x _ => G i x) t ω) =ᵐ[S.μ]
      S.I k (fun x _ => ∑ i ∈ s, κ i * G i x) t := by
  classical
  choose B hB using hB
  have hU : ∀ s : Finset ι, U4 S.ℱ S.μ (fun x (_ : Ω) => ∑ i ∈ s, κ i * G i x) := fun s =>
    det_U4 S _ (Finset.measurable_sum _ fun i _ => (hG i).const_mul _) (∑ i ∈ s, |κ i| * B i)
      fun x => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB i x) (abs_nonneg _))
  induction s using Finset.induction_on with
  | empty =>
    have h0 := S.int_linear k (fun _ _ => (0:ℝ)) (fun _ _ => 0) 0 0 (by simpa using hU ∅)
      (by simpa using hU ∅) t
    have e : ((0:ℝ) • (fun (_ : ℝ≥0) (_ : Ω) => (0:ℝ)) + (0:ℝ) • (fun (_ : ℝ≥0) (_ : Ω) => (0:ℝ)) :
        ℝ≥0 → Ω → ℝ) = fun x _ => ∑ i ∈ (∅ : Finset ι), κ i * G i x := by
      funext x ω; simp
    rw [e] at h0
    filter_upwards [h0] with ω hω
    rw [hω]; simp
  | insert i s hi ih =>
    have hGi := det_U4 S (G i) (hG i) (B i) (hB i)
    have h1 := S.int_linear k (fun x _ => G i x) (fun x _ => ∑ i ∈ s, κ i * G i x) (κ i) 1 hGi
      (hU s) t
    have e : ((κ i) • (fun (x : ℝ≥0) (_ : Ω) => G i x) +
        (1:ℝ) • (fun (x : ℝ≥0) (_ : Ω) => ∑ i ∈ s, κ i * G i x) : ℝ≥0 → Ω → ℝ) =
        fun x _ => ∑ j ∈ insert i s, κ j * G j x := by
      funext x ω; simp [Finset.sum_insert hi]
    rw [e] at h1
    filter_upwards [h1, ih] with ω hω hω'
    rw [hω, Finset.sum_insert hi]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, hω']

/-- `I(G)_t` depends only on `G` on `[0, t]`. -/
lemma I_local (hBr : IsPreBrownianReal (S.B k) S.μ) (G G' : ℝ≥0 → ℝ) (hG : Measurable G)
    (hG' : Measurable G') (C C' : ℝ) (hC : ∀ x, |G x| ≤ C) (hC' : ∀ x, |G' x| ≤ C') (t : ℝ≥0)
    (h : ∀ x : ℝ≥0, (x:ℝ) ≤ t → G x = G' x) :
    S.I k (fun x _ => G x) t =ᵐ[S.μ] S.I k (fun x _ => G' x) t := by
  set D : ℝ≥0 → ℝ := fun x => G x - G' x
  have mD : Measurable D := hG.sub hG'
  have hD : ∀ x, |D x| ≤ C + C' := fun x => (abs_sub _ _).trans (add_le_add (hC x) (hC' x))
  have hlin := S.int_linear k (fun x _ => G x) (fun x _ => G' x) 1 (-1) (det_U4 S G hG C hC)
    (det_U4 S G' hG' C' hC') t
  have e : ((1:ℝ) • (fun (x : ℝ≥0) (_ : Ω) => G x) + (-1:ℝ) • (fun (x : ℝ≥0) (_ : Ω) => G' x) :
      ℝ≥0 → Ω → ℝ) = fun x _ => D x := by
    funext x ω; simp [D, sub_eq_add_neg]
  rw [e] at hlin
  have hiso := isometry S k hBr D mD (C + C') hD t
  have hz : ∫ s in (0:ℝ)..t, D (Real.toNNReal s) ^ 2 = 0 := by
    have hEq : EqOn (fun s : ℝ => D (Real.toNNReal s) ^ 2) (fun _ => (0:ℝ)) (uIcc 0 (t:ℝ)) :=
      fun s hs => by
        rw [uIcc_of_le t.coe_nonneg] at hs
        have : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ t := by rw [Real.coe_toNNReal s hs.1]; exact hs.2
        simp [D, h _ this]
    rw [intervalIntegral.integral_congr hEq]; simp
  rw [hz] at hiso
  have hL2 : MemLp (S.I k (fun x _ => D x) t) 2 S.μ :=
    (S.int_martingale k _ t (det_U5 S D mD (C + C') hD t)).2 t le_rfl
  have hsq := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hL2.integrable_sq).1 hiso
  filter_upwards [hsq, hlin] with ω h1 h2
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at h1
  rw [h1] at h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul] at h2
  linarith

end Ito

/-! ### Combinations of the `h_{n,j}` -/

/-- `W_κ(x) = Σ_{n,j} κ_{n,j} h_{n,j}(x)`. -/
noncomputable def Wq (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ)
    (κ : ℕ → Fin r → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Tm.card + 1), ∑ j, κ n j * hq048 Tm b A t n j x

section W
variable (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0)
  (κ : ℕ → Fin r → ℝ)

lemma W_meas : Measurable (Wq Tm b A t κ) :=
  Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun j _ =>
    (hq_meas Tm b A t n j).const_mul _

lemma W_bdd : ∃ B, ∀ x : ℝ≥0, |Wq Tm b A t κ x| ≤ B := by
  choose B hB using fun (n : ℕ) (j : Fin r) => hq_bdd Tm b A t n j
  refine ⟨∑ n ∈ Finset.range (Tm.card + 1), ∑ j, |κ n j| * B n j, fun x => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB n j x) (abs_nonneg _)

lemma W_contAt {x : ℝ} (hx : x ∉ Tm) (hxt : x ≠ t) : ContinuousAt (Wq Tm b A t κ) x := by
  unfold Wq
  exact tendsto_finsetSum _ fun n _ => tendsto_finsetSum _ fun j _ =>
    continuousAt_const.mul (hq_contAt Tm b A t n j hx hxt)

variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
open Novel.RecurrenceNecessityGaussianProof (det_U4 I_measurable gaussian_scalar)

lemma hq_U4 (n : ℕ) (j : Fin r) : U4 S.ℱ S.μ (fun x (_ : Ω) => hq048 Tm b A t n j x) := by
  obtain ⟨B, hB⟩ := hq_bdd Tm b A t n j
  exact det_U4 S _ ((hq_meas Tm b A t n j).comp measurable_subtype_coe) B hB

lemma zeta_meas (n : ℕ) (j : Fin r) : Measurable (zeta048 S k Tm b A t n j) :=
  I_measurable S k _ (hq_U4 Tm b A t S n j) t

lemma sum_zeta : (fun ω => ∑ n ∈ Finset.range (Tm.card + 1), ∑ j, κ n j * zeta048 S k Tm b A t n j ω)
    =ᵐ[S.μ] S.I k (fun x _ => Wq Tm b A t κ x) t := by
  have := I_sum S k (Finset.range (Tm.card + 1) ×ˢ (Finset.univ : Finset (Fin r)))
    (fun p x => hq048 Tm b A t p.1 p.2 x)
    (fun p => (hq_meas Tm b A t p.1 p.2).comp measurable_subtype_coe)
    (fun p => hq_bdd Tm b A t p.1 p.2) (fun p => κ p.1 p.2) t
  simp only [Finset.sum_product] at this
  exact this

lemma law_W (hBr : IsPreBrownianReal (S.B k) S.μ) :
    HasLaw (S.I k (fun x _ => Wq Tm b A t κ x) t)
      (gaussianReal 0 (∫ s in (0:ℝ)..t, Wq Tm b A t κ s ^ 2).toNNReal) S.μ := by
  obtain ⟨B, hB⟩ := W_bdd Tm b A t κ
  have hm : Measurable fun x : ℝ≥0 => Wq Tm b A t κ x := (W_meas Tm b A t κ).comp measurable_subtype_coe
  have hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (t:ℝ) →
      ContinuousAt (fun x : ℝ≥0 => Wq Tm b A t κ x) (Real.toNNReal s) := by
    filter_upwards [((Tm.finite_toSet.insert (t:ℝ)).countable).ae_notMem volume] with s hs hs0 _
    simp only [mem_insert_iff, Finset.mem_coe, not_or] at hs
    refine ContinuousAt.comp (g := Wq Tm b A t κ) ?_ NNReal.continuous_coe.continuousAt
    rw [Real.coe_toNNReal s hs0.le]
    exact W_contAt Tm b A t κ hs.2 hs.1
  have hlaw := gaussian_scalar S k hBr _ hm B hB t hcont
  have e : ∫ s in (0:ℝ)..t, Wq Tm b A t κ (Real.toNNReal s : ℝ) ^ 2 =
      ∫ s in (0:ℝ)..t, Wq Tm b A t κ s ^ 2 := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [Real.coe_toNNReal s hs.1]
  rw [e] at hlaw
  exact ⟨(I_measurable S k _ (det_U4 S _ hm B hB) t).aemeasurable, hlaw⟩

end W

/-- `E X² = m² + v` for `X ~ N(m, v)`. -/
lemma second_moment_gauss (m : ℝ) (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal m v = m ^ 2 + v := by
  have h0 : (0:ℝ) ∈ interior (integrableExpSet id (gaussianReal m v)) := by simp
  have := iteratedDeriv_mgf_zero h0 2
  rw [mgf_id_gaussianReal] at this
  rw [show (∫ x, x ^ 2 ∂gaussianReal m v) = (gaussianReal m v)[id ^ 2] by rfl, ← this]
  set w : ℝ := (v : ℝ)
  have e1 : iteratedDeriv 1 (fun t => Real.exp (m * t + w * t ^ 2 / 2)) =
      fun t => (m + w * t) * Real.exp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_one]; funext t; exact (Novel.RecurrentApproxPriceBoundsProof.hd_E m w t).deriv
  have e2 : iteratedDeriv 2 (fun t => Real.exp (m * t + w * t ^ 2 / 2)) =
      fun t => (w + (m + w * t) ^ 2) * Real.exp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e1, Novel.RecurrentApproxPriceBoundsProof.deriv_PE m w
      (P := fun t => m + w * t) (P' := fun _ => w)]
    · funext t; ring
    · intro t; simpa using ((hasDerivAt_id t).const_mul w).const_add m
  rw [e2]; simp; ring

/-- The inner drift integral is bounded on `[t, H]`. -/
lemma inner_bound {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam : ℝ → ℝ} {H Λ ε Abar : ℝ}
    (h : Hyp048 Tm a a' lam H Λ ε Abar) (b₀ : ℕ → ℝ) (hb : b₀ = a ∨ b₀ = a') {t u : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc t H) :
    |∫ s in (0:ℝ)..t, alpha048 Tm b₀ lam s u| ≤ Abar * Λ * (Abar * Λ * H) * t := by
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (hu.1.trans hu.2)⟩)
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have := Novel.RecurrentApproxPriceBoundsProof.abs_int_le ht
    (f := fun s => alpha048 Tm b₀ lam s u) (C := Abar * Λ * (Abar * Λ * H)) fun s hs => by
      have h1 := sig_bound h (hs.2.trans hu.1) (by linarith [hs.1, hu.2])
      have h2 := S_bound h hs.1 (hs.2.trans hu.1) hu.2
      have e1 : |sig048 Tm b₀ lam s u| ≤ Abar * Λ := by
        rcases hb with rfl | rfl; exacts [h1.1, h1.2.1]
      have e2 : |S048 Tm b₀ lam s u| ≤ Abar * Λ * (u - s) := by
        rcases hb with rfl | rfl; exacts [h2.1, h2.2.1]
      rw [alpha048, abs_mul]
      refine mul_le_mul e1 (e2.trans ?_) (abs_nonneg _) (mul_nonneg hA0 hl0)
      exact mul_le_mul_of_nonneg_left (by linarith [hs.1, hu.2]) (mul_nonneg hA0 hl0)
  rwa [sub_zero] at this

/-! ### The version -/

section Main
variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m) {c b : Fin r → ℝ}
  {A : Matrix (Fin r) (Fin r) ℝ} {Tm : Finset ℝ} {a a' : ℕ → ℝ} {H Λ ε Abar : ℝ}
  (h : Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar) {f0 : ℝ → ℝ} {F0 : ℝ} (hf0 : Measurable f0)
  (hF0 : ∀ x ∈ Icc 0 H, |f0 x| ≤ F0) (t : ℝ≥0)
open Novel.RecurrenceNecessityGaussianProof (det_U4)
open Novel.RecurrentApproxMeanSquareProof (sigT_meas sigT_bound)

include h hf0 hF0 in
lemma version (hBr : IsPreBrownianReal (S.B k) S.μ) (a₀ : ℕ → ℝ) (ha₀ : a₀ = a ∨ a₀ = a') :
    Measurable (fun p : Ω × ℝ => V048 S k f0 Tm a₀ c b A t p.2 p.1) ∧
    (∀ ω, ∃ C, ∀ u ∈ Set.Icc (t:ℝ) H, |V048 S k f0 Tm a₀ c b A t u ω| ≤ C) ∧
    ∀ u ∈ Set.Icc (t:ℝ) H, (fun ω => V048 S k f0 Tm a₀ c b A t u ω) =ᵐ[S.μ]
      fwd048 S k f0 Tm a₀ (shape030 c b A) t u := by
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  refine ⟨?_, fun ω => ?_, fun u hu => ?_⟩
  · unfold V048
    exact ((hf0.comp measurable_snd).add
      ((Novel.RecurrentApproxPriceBoundsProof.inner_meas Tm a₀ h.1 t).comp measurable_snd)).add
      (Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun j _ =>
        ((gq_meas Tm a₀ c A t n j).comp measurable_snd).mul
          ((zeta_meas Tm b A t S k n j).comp measurable_fst))
  · choose B hB using fun (n : ℕ) (j : Fin r) => gq_bdd Tm a₀ c A t H n j
    refine ⟨F0 + Abar * Λ * (Abar * Λ * H) * t +
      ∑ n ∈ Finset.range (Tm.card + 1), ∑ j, B n j * |zeta048 S k Tm b A t n j ω|, fun u hu => ?_⟩
    unfold V048
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (hF0 u ⟨ht.trans hu.1, hu.2⟩) (inner_bound h a₀ ha₀ ht hu))) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB n j u hu) (abs_nonneg _)
  · have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (hu.1.trans hu.2)⟩)
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
    have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
    set κ : ℕ → Fin r → ℝ := fun n j => gq048 Tm a₀ c A t n j u
    have hsum := sum_zeta Tm b A t κ S k
    obtain ⟨BW, hBW⟩ := W_bdd Tm b A t κ
    have hsb := sigT_bound h hu.2 (mul_nonneg hA0 hl0) (mul_nonneg hε0 hl0)
    have hsig : ∀ x, |sigT Tm a₀ (shape030 c b A) u x| ≤ Abar * Λ := fun x => by
      rcases ha₀ with rfl | rfl; exacts [(hsb x).1, (hsb x).2.1]
    have hloc := I_local S k hBr (fun x => Wq Tm b A t κ x) (sigT Tm a₀ (shape030 c b A) u)
      ((W_meas Tm b A t κ).comp measurable_subtype_coe) (sigT_meas Tm a₀ h.1 u) BW _ hBW hsig t
      fun x hx => by
        simp only [sigT, show (x:ℝ) ≤ u from hx.trans hu.1, ite_true]
        exact (sig_split Tm a₀ c b A hx hu.1).symm
    filter_upwards [hsum, hloc] with ω h1 h2
    simp only [V048, fwd048]
    rw [h1, h2]

lemma ii_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {x y : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume x y) :
    IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume x y := by
  convert IntervalIntegrable.sum s hf using 1
  funext u; simp [Finset.sum_apply]

/-- The centered log-price `X = μ + Σ (∫_t^T g_{n,j}) ζ_{n,j}`. -/
noncomputable def Xq (Tm : Finset ℝ) (a₀ : ℕ → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (T : ℝ) (ω : Ω) : ℝ :=
  mu048 Tm a₀ (shape030 c b A) t T + ∑ n ∈ Finset.range (Tm.card + 1), ∑ j,
    (∫ u in (t:ℝ)..T, gq048 Tm a₀ c A t n j u) * zeta048 S k Tm b A t n j ω

include h hf0 hF0 in
/-- `∫_t^T V(t, u) du = ∫_t^T f_0 + X`. -/
lemma VX (a₀ : ℕ → ℝ) (ha₀ : a₀ = a ∨ a₀ = a') {T : ℝ} (htT : (t:ℝ) ≤ T) (hTH : T ≤ H) (ω : Ω) :
    ∫ u in (t:ℝ)..T, V048 S k f0 Tm a₀ c b A t u ω =
      (∫ u in (t:ℝ)..T, f0 u) + Xq S k t Tm a₀ c b A T ω := by
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have iF : IntervalIntegrable f0 volume t T :=
    ii_of_bound hf0 htT fun u hu => hF0 u ⟨ht.trans hu.1, hu.2.trans hTH⟩
  have iI : IntervalIntegrable (fun u => ∫ s in (0:ℝ)..t, alpha048 Tm a₀ (shape030 c b A) s u)
      volume t T :=
    ii_of_bound (Novel.RecurrentApproxPriceBoundsProof.inner_meas Tm a₀ h.1 t) htT
      fun u hu => inner_bound h a₀ ha₀ ht ⟨hu.1, hu.2.trans hTH⟩
  have ig : ∀ n j, IntervalIntegrable (gq048 Tm a₀ c A t n j) volume t T := fun n j => by
    obtain ⟨B, hB⟩ := gq_bdd Tm a₀ c A t H n j
    exact ii_of_bound (gq_meas Tm a₀ c A t n j) htT fun u hu => hB u ⟨hu.1, hu.2.trans hTH⟩
  have iS : ∀ n, IntervalIntegrable
      (fun u => ∑ j, gq048 Tm a₀ c A t n j u * zeta048 S k Tm b A t n j ω) volume t T :=
    fun n => ii_sum _ fun j _ => (ig n j).mul_const _
  have hsum : ∫ u in (t:ℝ)..T, ∑ n ∈ Finset.range (Tm.card + 1), ∑ j,
      gq048 Tm a₀ c A t n j u * zeta048 S k Tm b A t n j ω =
      ∑ n ∈ Finset.range (Tm.card + 1), ∑ j,
        (∫ u in (t:ℝ)..T, gq048 Tm a₀ c A t n j u) * zeta048 S k Tm b A t n j ω := by
    rw [intervalIntegral.integral_finsetSum fun n _ => iS n]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => (ig n j).mul_const _]
    exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_mul_const _ _
  unfold V048 Xq mu048
  rw [intervalIntegral.integral_add (iF.add iI) (ii_sum _ fun n _ => iS n),
    intervalIntegral.integral_add iF iI, hsum]
  ring

/-- `W_κ = U` on `[0, t]` for `κ_{n,j} = ∫_t^T g_{n,j}`. -/
lemma WU (a₀ : ℕ → ℝ) {T : ℝ} (htT : (t:ℝ) ≤ T) (hTH : T ≤ H) {x : ℝ}
    (hx : x ∈ Icc 0 (t:ℝ)) :
    Wq Tm b A t (fun n j => ∫ u in (t:ℝ)..T, gq048 Tm a₀ c A t n j u) x =
      U048 Tm a₀ (shape030 c b A) t T x := by
  have ig : ∀ n j, IntervalIntegrable (gq048 Tm a₀ c A t n j) volume t T := fun n j => by
    obtain ⟨B, hB⟩ := gq_bdd Tm a₀ c A t H n j
    exact ii_of_bound (gq_meas Tm a₀ c A t n j) htT fun u hu => hB u ⟨hu.1, hu.2.trans hTH⟩
  unfold Wq U048
  rw [intervalIntegral.integral_congr (g := fun u => ∑ n ∈ Finset.range (Tm.card + 1), ∑ j,
      gq048 Tm a₀ c A t n j u * hq048 Tm b A t n j x) fun u hu => by
    rw [uIcc_of_le htT] at hu
    exact sig_split Tm a₀ c b A hx.2 hu.1,
    intervalIntegral.integral_finsetSum fun n _ => ii_sum _ fun j _ => (ig n j).mul_const _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (ig n j).mul_const _]
  exact Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_mul_const _ _).symm

end Main

/-! ### (48.6) and (48.7) -/

theorem bondS : bondStatement := by
  intro Ω _ S k hBr r c b A Tm a a' H Λ ε Abar h f0 F0 hf0 hF0 t T htT hTH
  have := S.isProbabilityMeasure
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have hH : 0 ≤ H := ht.trans (htT.trans hTH)
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, hH⟩)
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hF00 : 0 ≤ F0 := (abs_nonneg _).trans (hF0 0 ⟨le_rfl, hH⟩)
  refine ⟨fun a₀ ha₀ => version S k h hf0 hF0 t hBr a₀ ha₀, ?_⟩
  set lam := shape030 c b A
  set B := Abar ^ 2 * Λ ^ 2 * H ^ 3 with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨-, hUa, hUa', hmu, hmu', -, -, hfin⟩ :=
    Novel.RecurrentApproxPriceBoundsProof.boundS Tm a a' lam H Λ ε Abar h t T ht htT hTH
  set κ : (ℕ → ℝ) → ℕ → Fin r → ℝ := fun a₀ n j => ∫ u in (t:ℝ)..T, gq048 Tm a₀ c A t n j u
  set X := Xq S k t Tm a c b A T
  set X' := Xq S k t Tm a' c b A T
  set F := ∫ u in (t:ℝ)..T, f0 u
  -- the laws
  have hXae : ∀ a₀ : ℕ → ℝ, Xq S k t Tm a₀ c b A T =ᵐ[S.μ]
      fun ω => mu048 Tm a₀ lam t T + S.I k (fun x _ => Wq Tm b A t (κ a₀) x) t ω := fun a₀ => by
    filter_upwards [sum_zeta Tm b A t (κ a₀) S k] with ω hω
    simp only [Xq]; rw [hω]
  have hvar : ∀ a₀ : ℕ → ℝ, ∫ s in (0:ℝ)..t, Wq Tm b A t (κ a₀) s ^ 2 =
      ∫ s in (0:ℝ)..t, U048 Tm a₀ lam t T s ^ 2 := fun a₀ =>
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht] at hs
      rw [show Wq Tm b A t (κ a₀) s = U048 Tm a₀ lam t T s from WU (c := c) t a₀ htT hTH hs]
  have lawX : ∀ a₀ : ℕ → ℝ, HasLaw (Xq S k t Tm a₀ c b A T)
      (gaussianReal (0 + mu048 Tm a₀ lam t T)
        (∫ s in (0:ℝ)..t, U048 Tm a₀ lam t T s ^ 2).toNNReal) S.μ := fun a₀ => by
    have := gaussianReal_const_add (law_W Tm b A t (κ a₀) S k hBr) (mu048 Tm a₀ lam t T)
    rw [hvar a₀] at this
    exact this.congr (hXae a₀)
  set κd : ℕ → Fin r → ℝ := fun n j => κ a n j - κ a' n j
  have hDae : (fun ω => X ω - X' ω) =ᵐ[S.μ] fun ω => (mu048 Tm a lam t T - mu048 Tm a' lam t T) +
      S.I k (fun x _ => Wq Tm b A t κd x) t ω := by
    filter_upwards [sum_zeta Tm b A t κd S k] with ω hω
    rw [← hω]
    simp only [X, X', Xq, κd, sub_mul, Finset.sum_sub_distrib]
    ring
  set w : ℝ := ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2
  have hw0 : 0 ≤ w := intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _
  have lawD : HasLaw (fun ω => X ω - X' ω)
      (gaussianReal (0 + (mu048 Tm a lam t T - mu048 Tm a' lam t T)) w.toNNReal) S.μ := by
    have := gaussianReal_const_add (law_W Tm b A t κd S k hBr)
      (mu048 Tm a lam t T - mu048 Tm a' lam t T)
    have e : ∫ s in (0:ℝ)..t, Wq Tm b A t κd s ^ 2 = w :=
      intervalIntegral.integral_congr fun s hs => by
        rw [uIcc_of_le ht] at hs
        have e1 : Wq Tm b A t κd s = Wq Tm b A t (κ a) s - Wq Tm b A t (κ a') s := by
          simp only [Wq, κd, sub_mul, Finset.sum_sub_distrib]
        rw [e1, show Wq Tm b A t (κ a) s = U048 Tm a lam t T s from WU (c := c) t a htT hTH hs,
          show Wq Tm b A t (κ a') s = U048 Tm a' lam t T s from WU (c := c) t a' htT hTH hs]
    rw [e] at this
    exact this.congr hDae
  set m := mu048 Tm a lam t T - mu048 Tm a' lam t T
  have hED : ∫ ω, (X ω - X' ω) ^ 2 ∂S.μ = m ^ 2 + w := by
    rw [show (∫ ω, (X ω - X' ω) ^ 2 ∂S.μ) = S.μ[(fun x : ℝ => x ^ 2) ∘ fun ω => X ω - X' ω] from rfl,
      lawD.integral_comp (by fun_prop), second_moment_gauss, Real.coe_toNNReal _ hw0, zero_add]
  have hmw : m ^ 2 + w ≤ ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4) := hfin
  -- the prices
  have hP : ∀ a₀ : ℕ → ℝ, (a₀ = a ∨ a₀ = a') → ∀ ω,
      P048 S k f0 Tm a₀ c b A t T ω = Real.exp (-F) * Real.exp (-Xq S k t Tm a₀ c b A T ω) :=
    fun a₀ ha₀ ω => by
      rw [P048, VX S k h hf0 hF0 t a₀ ha₀ htT hTH ω, ← Real.exp_add, neg_add]
  refine ⟨?_, ?_⟩
  · -- (48.6)
    have e : ∀ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) -
        Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2 = (X ω - X' ω) ^ 2 := fun ω => by
      rw [P048, P048, Real.log_exp, Real.log_exp, VX S k h hf0 hF0 t a (Or.inl rfl) htT hTH ω,
        VX S k h hf0 hF0 t a' (Or.inr rfl) htT hTH ω]
      ring
    simp only [e, hED]
    exact hmw
  · -- (48.7)
    have e : ∀ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 =
        Real.exp (-F) ^ 2 * (Real.exp (-X ω) - Real.exp (-X' ω)) ^ 2 := fun ω => by
      rw [hP a (Or.inl rfl), hP a' (Or.inr rfl)]; ring
    simp only [e]
    rw [integral_const_mul]
    have hXm : ∀ a₀ : ℕ → ℝ, Measurable (Xq S k t Tm a₀ c b A T) := fun a₀ =>
      measurable_const.add (Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun j _ =>
        (zeta_meas Tm b A t S k n j).const_mul _)
    have hv : ∀ a₀ : ℕ → ℝ, ∫ s in (0:ℝ)..t, U048 Tm a₀ lam t T s ^ 2 ≤ B →
        (((∫ s in (0:ℝ)..t, U048 Tm a₀ lam t T s ^ 2).toNNReal : ℝ≥0) : ℝ) ≤ B := fun a₀ hle => by
      rw [Real.coe_toNNReal']; exact max_le hle hB0
    have hpr := Novel.RecurrentApproxPriceBoundsProof.price_ineq (hXm a) (hXm a') (lawX a) (lawX a')
      lawD (by rw [zero_add]; exact hmu) (by rw [zero_add]; exact hmu') (hv a hUa) (hv a' hUa')
    rw [zero_add, Real.coe_toNNReal _ hw0] at hpr
    have hF : |F| ≤ F0 * H := by
      have := Novel.RecurrentApproxPriceBoundsProof.abs_int_le htT (f := f0) (C := F0)
        fun u hu => hF0 u ⟨ht.trans hu.1, hu.2.trans hTH⟩
      exact this.trans (mul_le_mul_of_nonneg_left (by linarith) hF00)
    have hexp : Real.exp (-F) ^ 2 ≤ Real.exp (2 * H * F0) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have := neg_abs_le F
      push_cast; nlinarith
    have hI0 : 0 ≤ ∫ ω, (Real.exp (-X ω) - Real.exp (-X' ω)) ^ 2 ∂S.μ :=
      integral_nonneg fun _ => sq_nonneg _
    calc Real.exp (-F) ^ 2 * ∫ ω, (Real.exp (-X ω) - Real.exp (-X' ω)) ^ 2 ∂S.μ
        ≤ Real.exp (2 * H * F0) * (2 * √3 * Real.exp (5 * B) * (m ^ 2 + w)) :=
          mul_le_mul hexp hpr hI0 (Real.exp_pos _).le
      _ ≤ Real.exp (2 * H * F0) * (2 * √3 * Real.exp (5 * B) *
            (ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4))) := by gcongr
      _ = _ := by
          rw [show 2 * H * F0 + 5 * Abar ^ 2 * Λ ^ 2 * H ^ 3 = 2 * H * F0 + 5 * B by rw [hBdef]; ring,
            Real.exp_add]
          ring

theorem recurrentApproxBond : Standalone.RecurrentApproxBond.statement := bondS

end Novel.RecurrentApproxBondProof

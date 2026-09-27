import Standalone.RecurrenceNecessityRank
import Novel.MeetingLoadingRankProof
import Novel.RecurrenceNecessityCurveProof
import Novel.RecurrenceNecessityGaussianProof
import Novel.RecurrenceNecessityReductionProof

open MeasureTheory ProbabilityTheory Filter Topology Matrix NormedSpace
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingCurve
open Standalone.RecurrenceNecessityCurve Standalone.RecurrenceNecessityReduction
open Standalone.RecurrenceNecessityAlgebra Standalone.RecurrenceNecessityRank
namespace Novel.RecurrenceNecessityRankProof

/-- Claim 029's rank step, for any matrix. -/
lemma rank_general : generalRankStatement := by
  intro Ω mΩ μ hμ R N H δ hδm hδ f c hf q Y Z Ψ hΨ hreal
  classical
  set L := H.mulVecLin
  set V := LinearMap.range L
  set ρ := H.rank
  have hρ : Module.finrank ℝ V = Module.finrank ℝ (Fin ρ → ℝ) := by
    rw [Module.finrank_fin_fun]; rfl
  let e : V ≃ₗ[ℝ] (Fin ρ → ℝ) := LinearEquiv.ofFinrankEq V (Fin ρ → ℝ) hρ
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (e : V →ₗ[ℝ] (Fin ρ → ℝ))
  have hπL : Function.Surjective (π.comp L) := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := hv
    refine ⟨x, ?_⟩
    have := congrArg (fun g => g ⟨L x, LinearMap.mem_range_self L x⟩) hπ
    simpa using this
  have hlaw := Novel.MeetingLoadingLawProof.affine N ρ (μ.map δ) (π.comp L) (π c) hδ hπL
  have hcontA : Continuous fun x : Fin N → ℝ => π c + (π.comp L) x :=
    continuous_const.add (π.comp L).continuous_of_finiteDimensional
  have hVm : AEMeasurable (fun ω => π c + (π.comp L) (δ ω)) μ :=
    hcontA.measurable.comp_aemeasurable hδm
  have hmapV : μ.map (fun ω => π c + (π.comp L) (δ ω)) =
      (μ.map δ).map (fun x => π c + (π.comp L) x) :=
    (AEMeasurable.map_map_of_aemeasurable hcontA.aemeasurable hδm).symm
  set Φ : (Fin q → ℝ) → Fin ρ → ℝ := fun y => π (Ψ y)
  have hΦ : ∀ j, LocallyLipschitzOn Z fun y => Φ y j := by
    intro j x hx
    obtain ⟨C, t, ht, hL⟩ := Novel.MeetingLoadingDimensionProof.locallyLipschitzOn_pi Ψ Z hΨ x hx
    have hπL' : LipschitzWith ‖π.toContinuousLinearMap‖₊ π := π.toContinuousLinearMap.lipschitzWith
    refine ⟨‖π.toContinuousLinearMap‖₊ * C, t, ht, fun u hu v hv => ?_⟩
    calc edist (Φ u j) (Φ v j) ≤ edist (Φ u) (Φ v) := edist_le_pi_edist _ _ j
      _ ≤ ‖π.toContinuousLinearMap‖₊ * edist (Ψ u) (Ψ v) := hπL' _ _
      _ ≤ ‖π.toContinuousLinearMap‖₊ * (C * edist u v) := by gcongr; exact hL hu hv
      _ = (‖π.toContinuousLinearMap‖₊ * C : ℝ≥0) * edist u v := by
          push_cast; ring
  refine Novel.MeetingLoadingDimensionProof.dimension Ω mΩ μ hμ q ρ
    (fun ω => π c + (π.comp L) (δ ω)) Y Φ Z hVm (hmapV ▸ hlaw) hΦ ?_
  filter_upwards [hf, hreal] with ω h1 h2
  refine ⟨h2.1, ?_⟩
  show _ = π (Ψ (Y ω))
  rw [← h2.2, h1, map_add]
  rfl

variable {r : ℕ}

/-- The quadratic form of `Γ_δ`. -/
lemma quad_gamma (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (δ : ℝ) (x : Fin r → ℝ) :
    x ⬝ᵥ (gamma032 C b δ *ᵥ x) = ∫ u in (0:ℝ)..δ, (x ⬝ᵥ (exp (u • C) *ᵥ b)) ^ 2 := by
  set φ : ℝ → Fin r → ℝ := fun u => exp (u • C) *ᵥ b with hφ
  have hφc : ∀ i, Continuous fun u => φ u i := Novel.RecurrenceNecessityReductionProof.phi_cont C b
  have hii : ∀ i j, IntervalIntegrable (fun u : ℝ => x i * x j * (φ u i * φ u j)) volume 0 δ :=
    fun i j => (continuous_const.mul ((hφc i).mul (hφc j))).intervalIntegrable _ _
  have e : (fun u => (x ⬝ᵥ φ u) ^ 2) = fun u => ∑ i, ∑ j, x i * x j * (φ u i * φ u j) := by
    funext u
    simp only [dotProduct]
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hii2 : ∀ i, IntervalIntegrable (fun u : ℝ => ∑ j, x i * x j * (φ u i * φ u j))
      volume 0 δ := fun i => by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hii i j) using 1
    funext u
    simp [Finset.sum_apply]
  have hG : ∀ i j, gamma032 C b δ i j = ∫ u in (0:ℝ)..δ, φ u i * φ u j := fun i j => rfl
  show _ = ∫ u in (0:ℝ)..δ, (x ⬝ᵥ φ u) ^ 2
  rw [e, intervalIntegral.integral_finsetSum fun i _ => hii2 i]
  simp only [dotProduct, mulVec, hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hii i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ### The pieces -/

lemma lower_coe (n : ℕ) (l : Fin (n+1)) : (lower029 n l : ℝ) = ((n - l : ℕ) : ℝ) := by
  unfold lower029; exact NNReal.coe_natCast _

lemma upper_coe (n : ℕ) (l : Fin (n+1)) :
    (upper029 n l : ℝ) = if (l:ℕ) = 0 then (n:ℝ) + 1/2 else ((n - l + 1 : ℕ) : ℝ) := by
  unfold upper029
  split_ifs
  · exact Novel.MeetingLoadingCurveProof.time_coe n
  · exact NNReal.coe_natCast _

lemma pieces_disjoint (n : ℕ) (l l' : Fin (n+1)) (s : ℝ)
    (h : (lower029 n l : ℝ) < s ∧ s ≤ upper029 n l)
    (h' : (lower029 n l' : ℝ) < s ∧ s ≤ upper029 n l') : l = l' := by
  by_contra hne
  have key : ∀ l l' : Fin (n+1), (l:ℕ) < l' → (upper029 n l' : ℝ) ≤ lower029 n l := by
    intro l l' hlt
    rw [upper_coe, lower_coe, if_neg (by omega)]
    exact_mod_cast (by omega : n - (l':ℕ) + 1 ≤ n - l)
  rcases lt_or_gt_of_ne (fun h : (l:ℕ) = l' => hne (Fin.ext h)) with hlt | hgt
  · linarith [key l l' hlt, h.1, h'.2]
  · linarith [key l' l hgt, h'.1, h.2]

lemma piece_len_pos (n : ℕ) (l : Fin (n+1)) : (lower029 n l : ℝ) < upper029 n l := by
  rw [upper_coe, lower_coe]
  split_ifs with h
  · rw [h]; simp
  · push_cast [show (l:ℕ) ≤ n from Nat.lt_succ_iff.1 l.isLt]; linarith

lemma upper_le_time (n : ℕ) (l : Fin (n+1)) : (upper029 n l : ℝ) ≤ time029 n := by
  exact_mod_cast Novel.MeetingLoadingCurveProof.upper_le n l

lemma ind_contAt (lo up p : ℝ≥0) (h1 : p ≠ lo) (h2 : p ≠ up) :
    ContinuousAt (fun s => Set.indicator (Set.Ioc lo up) (1 : ℝ≥0 → ℝ) s) p := by
  by_cases hin : p ∈ Set.Ioo lo up
  · refine (continuousAt_const (y := (1:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hin] with s hs
    rw [Set.indicator_of_mem (Set.Ioo_subset_Ioc_self hs)]; rfl
  · rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hin
    rcases hin with h | h
    · have hlt : p < lo := lt_of_le_of_ne h h1
      refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact Set.indicator_of_notMem (fun hm => absurd hm.1 (not_lt.2 (le_of_lt hs))) _
    · have hgt : up < p := lt_of_le_of_ne h (Ne.symm h2)
      refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact Set.indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hs)) _

/-- The integrand of `ξ_{l,j}` as a function of time. -/
noncomputable def xiF (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ)
    (lj : Fin (n+1) × Fin r) (s : ℝ≥0) : ℝ :=
  Set.indicator (Set.Ioc (lower029 n lj.1) (upper029 n lj.1)) 1 s *
    (exp (((upper029 n lj.1 : ℝ) - s) • C) *ᵥ b) lj.2

lemma xiF_bdd (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ lj s, |xiF C b n lj s| ≤ K := by
  choose B hB using fun lj => Novel.RecurrenceNecessityCurveProof.xi_bdd C b n lj (time029 n)
  refine ⟨∑ lj, |B lj|, fun lj s => ?_⟩
  have hle : |B lj| ≤ ∑ lj, |B lj| :=
    Finset.single_le_sum (f := fun lj => |B lj|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  by_cases hs : s ≤ time029 n
  · exact ((hB lj s hs).trans (le_abs_self _)).trans hle
  · have : s ∉ Set.Ioc (lower029 n lj.1) (upper029 n lj.1) := fun h =>
      hs (h.2.trans (Novel.MeetingLoadingCurveProof.upper_le n lj.1))
    rw [xiF, Set.indicator_of_notMem this, zero_mul, abs_zero]
    exact (abs_nonneg _).trans hle

lemma xiF_cont (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) :
    ∀ᵐ (s : ℝ) ∂volume, 0 < s → ∀ lj, ContinuousAt (xiF C b n lj) (Real.toNNReal s) := by
  set E : Finset ℝ := Finset.univ.image (fun l : Fin (n+1) => (lower029 n l : ℝ)) ∪
    Finset.univ.image (fun l : Fin (n+1) => (upper029 n l : ℝ))
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ (E : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Finset.finite_toSet _).measure_zero volume)
  filter_upwards [hnull] with s hs hpos lj
  have hne : ∀ p : ℝ≥0, (p : ℝ) ∈ (E : Set ℝ) → Real.toNNReal s ≠ p := by
    intro p hp h
    apply hs
    rw [← h, Real.coe_toNNReal s hpos.le] at hp
    exact hp
  refine (ind_contAt _ _ _ (hne _ ?_) (hne _ ?_)).mul
    (Novel.RecurrenceNecessityCurveProof.xi_cont C b _ lj.2).continuousAt
  · simp [E]
  · simp [E]

/-- On the piece `l`, only the coordinates of `ξ_l` are active. -/
lemma xiF_on_piece (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) (l0 : Fin (n+1))
    (lj : Fin (n+1) × Fin r) (s : ℝ) (hs : (lower029 n l0 : ℝ) < s ∧ s ≤ upper029 n l0) :
    xiF C b n lj (Real.toNNReal s) =
      if lj.1 = l0 then (exp (((upper029 n l0 : ℝ) - s) • C) *ᵥ b) lj.2 else 0 := by
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg _).trans hs.1.le
  unfold xiF
  split_ifs with h
  · subst h
    rw [Set.indicator_of_mem, Real.coe_toNNReal s hs0]
    · simp
    · rw [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal s hs0]
      exact hs
  · rw [Set.indicator_of_notMem, zero_mul]
    rw [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal s hs0]
    intro h'
    exact h (pieces_disjoint n lj.1 l0 s h' hs)

/-- The stacked integrand of `(ξ_0, ..., ξ_n)`, indexed by `Fin ((n+1) r)`. -/
noncomputable def Fv (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) (s : ℝ≥0)
    (j : Fin ((n+1) * r)) : ℝ :=
  xiF C b n (finProdFinEquiv.symm j) s

lemma Fv_meas (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) (j : Fin ((n+1) * r)) :
    Measurable fun s => Fv C b n s j :=
  Novel.RecurrenceNecessityCurveProof.xi_meas C b n _

open Standalone.RecurrenceNecessityGaussian in
/-- The covariance of `(ξ_0, ..., ξ_n)` is positive definite. -/
lemma gram_posDef (C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (hΓ : ∀ δ : ℝ, 0 < δ → (gamma032 C b δ).PosDef) (n : ℕ) :
    (gram032 (Fv C b n) (time029 n)).PosDef := by
  obtain ⟨K, hK⟩ := xiF_bdd C b n
  have hK' : ∀ s j, |Fv C b n s j| ≤ K := fun s j => hK _ s
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Novel.RecurrenceNecessityGaussianProof.gram_posSemidef _ (Fv_meas C b n) K hK'
    (time029 n)).1, fun x hx => ?_⟩
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hx
  set e := (finProdFinEquiv : Fin (n+1) × Fin r ≃ Fin ((n+1) * r))
  set l0 := (e.symm j0).1
  set y : Fin r → ℝ := fun m => x (e (l0, m))
  have hy : y ≠ 0 := by
    intro h
    apply hj0
    have := congrFun h (e.symm j0).2
    simpa [y, l0] using this
  rw [star_trivial, Novel.RecurrenceNecessityGaussianProof.quad_gram (Fv C b n) (Fv_meas C b n)
    K hK' (time029 n) x]
  set g : ℝ → ℝ := fun s => ∑ j, x j * Fv C b n (Real.toNNReal s) j
  have hgm : Measurable g := Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((Fv_meas C b n j).comp measurable_real_toNNReal)
  have hgb : ∀ s, |g s ^ 2| ≤ (∑ j, |x j| * K) ^ 2 := fun s => by
    have h1 : |g s| ≤ ∑ j, |x j| * K :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK' _ j) (abs_nonneg _))
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hlo : (0:ℝ) ≤ lower029 n l0 := NNReal.coe_nonneg _
  have hlu := piece_len_pos n l0
  have hut := upper_le_time n l0
  have hmono := intervalIntegral.integral_mono_interval (f := fun s => g s ^ 2) hlo hlu.le hut
    (Eventually.of_forall fun s => sq_nonneg _)
    (Novel.RecurrenceNecessityGaussianProof.ii_bounded _ (hgm.pow_const 2) _ hgb _ _)
  refine lt_of_lt_of_le ?_ hmono
  have heq : (∫ s in (lower029 n l0 : ℝ)..(upper029 n l0 : ℝ), g s ^ 2) =
      ∫ s in (lower029 n l0 : ℝ)..(upper029 n l0 : ℝ),
        (y ⬝ᵥ (exp (((upper029 n l0 : ℝ) - s) • C) *ᵥ b)) ^ 2 := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le hlu.le] at hs
    congr 1
    simp only [g, Fv]
    rw [← Fintype.sum_equiv e (fun lj => x (e lj) * xiF C b n lj (Real.toNNReal s))
      (fun j => x j * xiF C b n (e.symm j) (Real.toNNReal s)) (fun lj => by simp)]
    simp only [xiF_on_piece C b n l0 _ s hs, mul_ite, mul_zero, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single l0]
    · simp [dotProduct, y]
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [heq, intervalIntegral.integral_comp_sub_left
    (fun u => (y ⬝ᵥ (exp (u • C) *ᵥ b)) ^ 2), sub_self, ← quad_gamma]
  have hpd := hΓ _ (sub_pos.2 hlu)
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hpd
  simpa using hpd.2 hy

section Law
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

open Standalone.RecurrenceNecessityGaussian in
/-- The vector `(ξ_0, ..., ξ_n)` has an absolutely continuous law. -/
lemma xi_ac (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) (C : Matrix (Fin r) (Fin r) ℝ)
    (b : Fin r → ℝ) (hΓ : ∀ δ : ℝ, 0 < δ → (gamma032 C b δ).PosDef) (n : ℕ) :
    AEMeasurable (fun ω (j : Fin ((n+1) * r)) =>
      S.I k (xiInt032 C b n (finProdFinEquiv.symm j)) (time029 n) ω) S.μ ∧
    S.μ.map (fun ω (j : Fin ((n+1) * r)) =>
      S.I k (xiInt032 C b n (finProdFinEquiv.symm j)) (time029 n) ω) ≪ volume := by
  obtain ⟨K, hK⟩ := xiF_bdd C b n
  have hK' : ∀ s j, |Fv C b n s j| ≤ K := fun s j => hK _ s
  have hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (time029 n : ℝ) →
      ∀ j, ContinuousAt (fun s => Fv C b n s j) (Real.toNNReal s) := by
    filter_upwards [xiF_cont C b n] with s hs h0 _ j
    exact hs h0 _
  have hG := Novel.RecurrenceNecessityGaussianProof.gaussian_vector S k hB (Fv C b n)
    (Fv_meas C b n) K hK' (time029 n) hcont
  have hU : ∀ j, U4 S.ℱ S.μ (fun s (_ : Ω) => Fv C b n s j) := fun j =>
    Novel.RecurrenceNecessityGaussianProof.det_U4 S _ (Fv_meas C b n j) K (hK' · j)
  have hδm : Measurable (fun ω (j : Fin ((n+1) * r)) =>
      S.I k (fun s (_ : Ω) => Fv C b n s j) (time029 n) ω) :=
    measurable_pi_iff.2 fun j =>
      Novel.RecurrenceNecessityGaussianProof.I_measurable S k _ (hU j) (time029 n)
  refine ⟨hδm.aemeasurable, ?_⟩
  have hV : Measurable (fun ω => WithLp.toLp 2 fun j =>
      S.I k (fun s (_ : Ω) => Fv C b n s j) (time029 n) ω) :=
    (PiLp.continuous_toLp 2 _).measurable.comp hδm
  have hac := Novel.RecurrenceNecessityGaussianProof.multivariateGaussian_ac 0 _
    (gram_posDef C b hΓ n)
  rw [← hG] at hac
  have e : (fun ω (j : Fin ((n+1) * r)) =>
      S.I k (xiInt032 C b n (finProdFinEquiv.symm j)) (time029 n) ω) =
      WithLp.ofLp ∘ fun ω => WithLp.toLp 2 fun j =>
        S.I k (fun s (_ : Ω) => Fv C b n s j) (time029 n) ω := rfl
  rw [e, ← Measure.map_map (PiLp.continuous_ofLp 2 _).measurable hV,
    ← (PiLp.volume_preserving_ofLp (Fin ((n+1) * r))).map_eq]
  exact hac.map (PiLp.continuous_ofLp 2 _).measurable

end Law

/-! ### The Hankel section inside the coefficients of (32.4) -/

lemma exp_pow_mul (C : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) (x : ℝ) :
    exp C ^ k * exp (x • C) = exp (((k:ℝ) + x) • C) := by
  rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl C).smul_left _ |>.smul_right _), ← add_smul]

lemma rank_hankel_le (a : ℕ → ℝ) (c : Fin r → ℝ) (C : Matrix (Fin r) (Fin r) ℝ) (n R : ℕ) :
    (blockHankel032 a c (exp C) R n).rank ≤
      (Matrix.of fun (i : Fin (R+1)) (lj : Fin (n+1) × Fin r) => coef032 a c C n i lj).rank := by
  classical
  set Mp : Matrix (Fin (R+1)) (Fin (n+1) × Fin r) ℝ :=
    Matrix.of fun i lj => coef032 a c C n i lj
  let P : Matrix (Fin (n+1) × Fin r) (Fin n × Fin r) ℝ :=
    Matrix.of fun lj0 lj => if lj0 = (lj.1.succ, lj.2) then 1 else 0
  let D : ℝ → Matrix (Fin n × Fin r) (Fin n × Fin r) ℝ := fun x =>
    Matrix.of fun lj1 lj => if lj1.1 = lj.1 then exp (x • C) lj1.2 lj.2 else 0
  have hD : D (-(1/4)) * D (1/4) = 1 := by
    ext ⟨l1, j1⟩ ⟨l, j⟩
    have hE : exp ((-(1/4:ℝ)) • C) * exp ((1/4:ℝ) • C) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl C).smul_left _ |>.smul_right _),
        ← add_smul]
      norm_num
    simp only [mul_apply, D, of_apply, Fintype.sum_prod_type, one_apply, Prod.mk.injEq]
    by_cases hl : l1 = l
    · subst hl
      rw [Finset.sum_eq_single l1 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp only [ite_true, true_and]
      have := congrFun (congrFun hE j1) j
      rw [mul_apply, one_apply] at this
      exact this
    · simp only [ite_mul, zero_mul]
      rw [if_neg (by tauto)]
      refine Finset.sum_eq_zero fun l2 _ => Finset.sum_eq_zero fun j2 _ => ?_
      by_cases h1 : l1 = l2
      · subst h1; simp [hl]
      · simp [h1]
  have hdet : IsUnit (D (-(1/4))).det := isUnit_det_of_right_inverse hD
  have hMP : Mp * P = blockHankel032 a c (exp C) R n * D (-(1/4)) := by
    ext i ⟨l, j⟩
    simp only [mul_apply, P, D, Mp, of_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      Prod.mk.injEq]
    rw [Finset.sum_eq_single l.succ, Finset.sum_eq_single j]
    · simp only [and_self, if_true]
      rw [Finset.sum_eq_single l]
      · simp only [ite_true, blockHankel032, of_apply]
        simp only [coef032, Fin.val_succ, mul_assoc, ← Finset.mul_sum]
        rw [show (i:ℕ) + ((l:ℕ) + 1) = i + l + 1 by ring]
        congr 1
        rw [show (∑ x, (c ᵥ* exp C ^ ((i:ℕ) + l + 1)) x *
            (exp ((-(1/4:ℝ)) • C) : Matrix (Fin r) (Fin r) ℝ) x j) =
          ((c ᵥ* exp C ^ ((i:ℕ) + l + 1)) ᵥ* (exp ((-(1/4:ℝ)) • C) : Matrix (Fin r) (Fin r) ℝ)) j
          from rfl, vecMul_vecMul, exp_pow_mul]
        congr 3
        rw [Novel.RecurrenceNecessityRankProof.upper_coe, if_neg (by simp)]
        simp only [mat029, Fin.val_succ]
        push_cast [show (l:ℕ) + 1 ≤ n from l.isLt]
        ring
      · intro l' _ hl'; simp [hl']
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro j' _ hj'; simp [hj']
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro l' _ hl'; simp [hl']
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← rank_mul_eq_left_of_isUnit_det _ _ hdet, ← hMP]
  exact rank_mul_le_left _ _

lemma rank_bound : rankStatement := by
  intro Ω mΩ S k hB a r c b A f0 n R q hreal C b' c' hlam hΓ
  classical
  obtain ⟨Y, Z, Ψ, hΨ, hY⟩ := hreal
  have hsig : ∀ T, sigma032 (Ω := Ω) a c A b n R T = sigma032 a c' C b' n R T := fun T => by
    funext s ω; simp only [sigma032, hlam]
  have halpha : alpha032 a c A b n R = alpha032 a c' C b' n R := by
    funext s T; simp only [alpha032, hlam]
  obtain ⟨-, -, hcurve⟩ := Novel.RecurrenceNecessityCurveProof.curve Ω mΩ S k a r c' b' C n R
  set e := (finProdFinEquiv : Fin (n+1) × Fin r ≃ Fin ((n+1) * r))
  obtain ⟨hδm, hδ⟩ := xi_ac S k hB C b' hΓ n
  set δ : Ω → Fin ((n+1) * r) → ℝ := fun ω j =>
    S.I k (xiInt032 C b' n (e.symm j)) (time029 n) ω
  set Mp : Matrix (Fin (R+1)) (Fin (n+1) × Fin r) ℝ := Matrix.of fun i lj => coef032 a c' C n i lj
  set M : Matrix (Fin (R+1)) (Fin ((n+1) * r)) ℝ := Mp.submatrix id e.symm
  set c0 : Fin (R+1) → ℝ := fun i => f0 (mat029 n i) +
    ∫ s in (0:ℝ)..(time029 n : ℝ), alpha032 a c' C b' n R s (mat029 n i)
  set f : Ω → Fin (R+1) → ℝ := fun ω i => curve032 S k a c A b f0 n R i ω
  have hf : ∀ᵐ ω ∂S.μ, f ω = c0 + M *ᵥ δ ω := by
    filter_upwards [hcurve] with ω hω
    funext i
    simp only [f, curve032, hsig, halpha, Pi.add_apply, c0, hω i]
    congr 1
    simp only [mulVec, dotProduct, M, Mp, submatrix_apply, id, of_apply, δ]
    exact (Fintype.sum_equiv e.symm _ _ fun j => rfl).symm
  have hrank := rank_general Ω mΩ S.μ S.isProbabilityMeasure R _ M δ hδm hδ f c0 hf q Y Z Ψ hΨ
    (hY.mono fun ω h => ⟨h.1, funext h.2⟩)
  calc (blockHankel032 a c' (exp C) R n).rank ≤ Mp.rank := rank_hankel_le a c' C n R
    _ = M.rank := (rank_submatrix Mp (Equiv.refl _) e.symm).symm
    _ ≤ q := hrank

theorem recurrenceNecessityRank : Standalone.RecurrenceNecessityRank.statement := ⟨rank_general, rank_bound⟩

end Novel.RecurrenceNecessityRankProof

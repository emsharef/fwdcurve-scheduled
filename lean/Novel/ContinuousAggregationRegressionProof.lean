import Standalone.ContinuousAggregationRegression
import Novel.ContinuousAggregationAmericanLowerProof
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! # Claim 054 (54-R): regression and product representation (proof)

* Under `Q^A` (Claim 046's tilt) each combination `Σ β_i Z_i + I f` has a Gaussian law
  (`law_QS`). Every linear form of a pair of combinations is again a combination almost surely,
  so the pair is jointly Gaussian (`pair_gauss`). Its covariance under `Q^A` is the covariance
  form (`cov_QS`, from `variance_add`), so zero covariance gives independence (`indep_comb`).
* (C3) `resAlg_indep_y`: a linear combination of residuals is almost surely a combination
  uncorrelated with `ycomb` (`lin_indep`, `cov_resid`). Cramér–Wold over finite families and a
  directed supremum give `σ(r) ⊥ ycomb`. When `V = 0`, `ycomb` is almost surely constant under
  `Q^A` (`ycomb_const`).
* (C4) `resAlg_indep_pair`: `σ(r) ∨ σ(c₀ + ycomb) ≤ F_A`, and the representative `Ξ′` of `Ξ` is
  measurable for the future increments, which are independent of `F_A` under `Q^A`. With
  `indep_sup_right`, `σ(r)` is independent of `(c₀ + ycomb, Ξ′)`, which is `(y_A, Ξ)` almost surely.
  The rectangle formula follows with (c)'s law of `(y_A, Ξ)` under `Q^A`.
* (C6) `filt`: each generator of `natural_s` is almost surely a `σ(r) ∨ (y_A, Ξ)⁻¹ σ(y, ξ_{≤s})`
  function. A pre-`A` coordinate is `r + coef · (y_A − c₀)`; `Z_i` with `T_i > A` is a coordinate
  of `Ξ`; `Y_u − Y_A` with `u > A` is a limit of rational coordinates, by path continuity
  (`incr_G`). Conversely each residual is almost surely `natural_s`-measurable, and `(y_A, Ξ)` is
  `natural_s`-measurable into `σ(y, ξ_{≤s})` (`pair_natural`).

Reused, not reproved: Claim 046's `tilt`, `QS_eq`, `comb_add`, `comb_meas`, `var_add`,
`integrand_add`; Claim 054's earlier stages (`futureAlg_QS`, `yA_ae`, `yA'_meas`,
`indep_of_dual`, `indep_comap_congr`, `I_zero`, `Xi'_meas`, `Xi_ae`, `law_pair`, `comb_sum`,
`integrand_sum`, `Z_nat`, `Y_nat`, `yA_nat`, `pair_natural`); Mathlib's
`HasGaussianLaw.indepFun_of_covariance_eq_zero`, `isGaussian_of_map_eq_gaussianReal`,
`indep_iSup_of_directed_le`, `IndepSets.indep`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Novel.ContinuousAggregationRegressionProof
open Standalone.CompoundedFuturesIdentification (w)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw Integrand)
open Standalone.DiffusionMeetingPricing (QS Qacc)
open Novel.DiffusionMeetingGaussProof (comb comb_meas var var_nonneg Wf Wf_integrand)
open Novel.DiffusionMeetingPricingProof (comb_add integrand_add tilt QS_eq cov var_add prod_ii)
open Novel.ContinuousAggregationEuropeanProof (comb_sum integrand_sum QS_prob Xi' Xi'_meas Xi_ae
  law_pair)
open Novel.ContinuousAggregationLevelProof (indep_comap_congr indep_of_dual integrand_zero I_zero
  β1 c0 f1_integrand yA_ae yA'_meas futureAlg_QS futureAlg_le)
open Novel.ContinuousAggregationAmericanLowerProof (Z_nat Y_nat yA_nat pair_natural pair_aem_QS)
open Standalone.ContinuousAggregationRegression
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationEuropean (State Rat' Xi)
open Standalone.ContinuousAggregationAmericanLower (natural postFilt)

section Gauss
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {M : DiffModel Ω N} {H A : ℝ}

/-- The law of a combination under `Q^A`. -/
lemma law_QS (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {δ : Fin N → ℝ} {h : ℝ → ℝ}
    (hh : Integrand h 0 H) :
    HasLaw (comb M δ h) (gaussianReal (-1 * cov M H (fun n => w 0 A (M.T n)) (Wf 0 A) δ h)
      (var M H δ h).toNNReal) (QS M Q A) := by
  refine ⟨(comb_meas hG hh).aemeasurable, ?_⟩
  rw [QS_eq hG hA hAH]
  exact tilt hG (hA.trans hAH) _ _ (Wf_integrand (a := 0) hAH) hh (by norm_num)

omit [IsProbabilityMeasure Q] in
/-- `a U + b W` is, almost surely, the combination with the combined coefficients. -/
lemma lin2 (hG : GaussLaw M Q H) {γ δ : Fin N → ℝ} {g h : ℝ → ℝ} (hg : Integrand g 0 H)
    (hh : Integrand h 0 H) (a b : ℝ) :
    (fun ω => a * comb M γ g ω + b * comb M δ h ω) =ᵐ[Q]
      comb M (fun i => a * γ i + b * δ i) (fun s => a * g s + b * h s) := by
  have := comb_sum hG (Finset.univ : Finset (Fin 2)) ![(γ, g), (δ, h)]
    (fun k => by fin_cases k <;> simpa) ![a, b]
  simpa [Fin.sum_univ_two] using this

lemma lin2_integrand {g h : ℝ → ℝ} (hg : Integrand g 0 H) (hh : Integrand h 0 H) (a b : ℝ) :
    Integrand (fun s => a * g s + b * h s) 0 H := by
  have := integrand_sum (N := 0) H (Finset.univ : Finset (Fin 2)) ![((0 : Fin 0 → ℝ), g), (0, h)]
    (fun k => by fin_cases k <;> simpa) ![a, b]
  simpa [Fin.sum_univ_two] using this

/-- A pair of combinations is jointly Gaussian under `Q^A`. -/
lemma pair_gauss (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {γ δ : Fin N → ℝ}
    {g h : ℝ → ℝ} (hg : Integrand g 0 H) (hh : Integrand h 0 H) :
    HasGaussianLaw (fun ω => (comb M γ g ω, comb M δ h ω)) (QS M Q A) := by
  have := QS_prob hG hA hAH
  have hU := comb_meas (β := γ) hG hg
  have hW := comb_meas (β := δ) hG hh
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  refine ⟨(hU.prodMk hW).aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  have hL : ∀ u v : ℝ, L (u, v) = L (1, 0) * u + L (0, 1) * v := fun u v => by
    have e : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, L.map_add, L.map_smul, L.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have e1 : (L ∘ fun ω => (comb M γ g ω, comb M δ h ω)) =
      fun ω => L (1, 0) * comb M γ g ω + L (0, 1) * comb M δ h ω := funext fun ω => hL _ _
  have key := (law_QS (δ := fun i => L (1, 0) * γ i + L (0, 1) * δ i) hG hA hAH
    (lin2_integrand hg hh (L (1, 0)) (L (0, 1)))).map_eq
  rw [← Measure.map_congr (hac.ae_le (lin2 hG hg hh _ _)), ← e1,
    ← Measure.map_map L.continuous.measurable (hU.prodMk hW)] at key
  exact ⟨_, _, key⟩

/-- The covariance of two combinations under `Q^A` is the covariance form. -/
lemma cov_QS (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {γ δ : Fin N → ℝ}
    {g h : ℝ → ℝ} (hg : Integrand g 0 H) (hh : Integrand h 0 H) :
    cov[comb M γ g, comb M δ h; QS M Q A] = cov M H γ g δ h := by
  have := QS_prob hG hA hAH
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hA.trans hAH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  have hU := law_QS (δ := γ) hG hA hAH hg
  have hW := law_QS (δ := δ) hG hA hAH hh
  have hUW := law_QS (δ := fun i => γ i + 1 * δ i) hG hA hAH (integrand_add hg hh 1)
  have hmU : MemLp (comb M γ g) 2 (QS M Q A) := hU.memLp (memLp_id_gaussianReal 2)
  have hmW : MemLp (comb M δ h) 2 (QS M Q A) := hW.memLp (memLp_id_gaussianReal 2)
  have hv := variance_add hmU hmW
  have hsum : (comb M γ g + comb M δ h) =ᵐ[QS M Q A]
      comb M (fun i => γ i + 1 * δ i) (fun s => g s + 1 * h s) :=
    hac.ae_le (comb_add hG γ δ hg hh 1 |>.mono fun ω hω => by simpa using hω)
  rw [variance_congr hsum, hU.variance_eq, hW.variance_eq, hUW.variance_eq,
    variance_id_gaussianReal, variance_id_gaussianReal, variance_id_gaussianReal,
    Real.coe_toNNReal _ (var_nonneg hG hH _ _), Real.coe_toNNReal _ (var_nonneg hG hH _ _),
    Real.coe_toNNReal _ (var_nonneg hG hH _ _), var_add hσ hB γ δ hg hh 1] at hv
  linarith

/-- Two combinations with zero covariance form are independent under `Q^A`. -/
lemma indep_comb (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {γ δ : Fin N → ℝ}
    {g h : ℝ → ℝ} (hg : Integrand g 0 H) (hh : Integrand h 0 H) (hcov : cov M H γ g δ h = 0) :
    IndepFun (comb M γ g) (comb M δ h) (QS M Q A) := by
  have := QS_prob hG hA hAH
  exact (pair_gauss hG hA hAH hg hh).indepFun_of_covariance_eq_zero
    (by rw [cov_QS hG hA hAH hg hh, hcov])

end Gauss

/-! ### General facts -/

section General
variable {Ω : Type*}

/-- `𝒜 ⊥ ℬ` and `𝒜 ∨ ℬ ⊥ 𝒞` give `𝒜 ⊥ ℬ ∨ 𝒞`. -/
lemma indep_sup_right {𝒜 ℬ 𝒞 : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hA : 𝒜 ≤ m0) (hB : ℬ ≤ m0) (hC : 𝒞 ≤ m0) (h1 : Indep 𝒜 ℬ μ)
    (h2 : Indep (𝒜 ⊔ ℬ) 𝒞 μ) : Indep 𝒜 (ℬ ⊔ 𝒞) μ := by
  set p : Set (Set Ω) := {s | ∃ b c, MeasurableSet[ℬ] b ∧ MeasurableSet[𝒞] c ∧ s = b ∩ c}
  have hp : IsPiSystem p := by
    rintro _ ⟨b, c, hb, hc, rfl⟩ _ ⟨b', c', hb', hc', rfl⟩ -
    exact ⟨b ∩ b', c ∩ c', hb.inter hb', hc.inter hc', by ext; simp only [mem_inter_iff]; tauto⟩
  have hgen : ℬ ⊔ 𝒞 = MeasurableSpace.generateFrom p := by
    refine le_antisymm (sup_le (fun b hb => ?_) (fun c hc => ?_))
      (MeasurableSpace.generateFrom_le ?_)
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨b, univ, hb, MeasurableSet.univ, (inter_univ b).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨univ, c, MeasurableSet.univ, hc, (univ_inter c).symm⟩
    · rintro _ ⟨b, c, hb, hc, rfl⟩
      exact MeasurableSet.inter ((le_sup_left : ℬ ≤ ℬ ⊔ 𝒞) b hb)
        ((le_sup_right : 𝒞 ≤ ℬ ⊔ 𝒞) c hc)
  refine IndepSets.indep hA (sup_le hB hC) (@MeasurableSpace.isPiSystem_measurableSet Ω 𝒜) hp
    (@MeasurableSpace.generateFrom_measurableSet Ω 𝒜).symm hgen ?_
  rw [IndepSets_iff]
  rintro a _ ha ⟨b, c, hb, hc, rfl⟩
  have e1 := (Indep_iff _ _ _).1 h2 (a ∩ b) c
    (((le_sup_left : 𝒜 ≤ 𝒜 ⊔ ℬ) a ha).inter ((le_sup_right : ℬ ≤ 𝒜 ⊔ ℬ) b hb)) hc
  have e2 := (Indep_iff _ _ _).1 h2 b c ((le_sup_right : ℬ ≤ 𝒜 ⊔ ℬ) b hb) hc
  have e3 := (Indep_iff _ _ _).1 h1 a b ha hb
  rw [← inter_assoc, e1, e3, e2, mul_assoc]

lemma cov_congr [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y : Ω → ℝ} (h : X =ᵐ[μ] X') :
    cov[X, Y; μ] = cov[X', Y; μ] := by
  unfold covariance
  rw [integral_congr_ae h]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

/-- A function almost everywhere equal to an `m`-measurable one is measurable for `m ∨ 𝒩`. -/
lemma ae_meas {m : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hg : Measurable[m] g) (h : f =ᵐ[μ] g) :
    Measurable[eventuallyMeasurableSpace m (ae μ)] f := fun B hB =>
  ⟨g ⁻¹' B, hg hB, h.mono fun ω hω => by change (f ω ∈ B) = (g ω ∈ B); rw [hω]⟩

lemma evMeas_mono {m m' : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : m ≤ eventuallyMeasurableSpace m' (ae μ)) :
    eventuallyMeasurableSpace m (ae μ) ≤ eventuallyMeasurableSpace m' (ae μ) := by
  rintro B ⟨C, hC, hBC⟩
  obtain ⟨D, hD, hCD⟩ := h C hC
  exact ⟨D, hD, hBC.trans hCD⟩

end General

/-! ### The residuals -/

section Den
variable {Ω : Type} {N : ℕ}

/-- `V = bil(y, y)`, the denominator of `coef`. -/
noncomputable def den (M : DiffModel Ω N) (A H : ℝ) : ℝ :=
  bil M H (β1 M A) ((Icc 0 A).indicator 1) (β1 M A) ((Icc 0 A).indicator 1)

/-- The natural version of a pre-`A` coordinate: `Z_i`, or `Y_u`. -/
def preNat (M : DiffModel Ω N) (A : ℝ) : preIdx M A → Ω → ℝ
  | Sum.inl i => M.Z i.1
  | Sum.inr u => M.Y u.1

lemma coef_mul {M : DiffModel Ω N} {A H : ℝ} (hD : den M A H ≠ 0) (x : preIdx M A) :
    coef M A H x * den M A H =
      bil M H (preβ M A x) (pref M A x) (β1 M A) ((Icc 0 A).indicator 1) :=
  div_mul_cancel₀ _ hD

lemma var_eq_den {M : DiffModel Ω N} {A H : ℝ} :
    var M H (β1 M A) ((Icc 0 A).indicator 1) = den M A H := by
  unfold var den bil
  simp only [sq]

lemma pref_integrand {M : DiffModel Ω N} {A K : ℝ} (hAK : A ≤ K) (x : preIdx M A) :
    Integrand (pref M A x) 0 K := by
  rcases x with i | u
  · exact integrand_zero K
  · exact f1_integrand (u.2.2.trans hAK)

end Den

section Reg
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {M : DiffModel Ω N} {H A : ℝ}

omit [IsProbabilityMeasure Q] in
lemma preCoord_meas (hG : GaussLaw M Q H) (hAH : A ≤ H) (x : preIdx M A) :
    Measurable (preCoord M A x) :=
  comb_meas (β := preβ M A x) hG (pref_integrand hAH x)

omit [IsProbabilityMeasure Q] in
lemma ycomb_meas (hG : GaussLaw M Q H) (hAH : A ≤ H) : Measurable (ycomb M A) :=
  comb_meas (β := β1 M A) hG (f1_integrand hAH)

omit [IsProbabilityMeasure Q] in
lemma resid_meas (hG : GaussLaw M Q H) (hAH : A ≤ H) (x : preIdx M A) :
    Measurable (resid M A H x) :=
  (preCoord_meas hG hAH x).sub (measurable_const.mul (ycomb_meas hG hAH))

omit [IsProbabilityMeasure Q] in
lemma resAlg_le (hG : GaussLaw M Q H) (hAH : A ≤ H) : resAlg M A H ≤ m₀ :=
  iSup_le fun x => (resid_meas hG hAH x).comap_le

omit [IsProbabilityMeasure Q] in
lemma preCoord_F (hG : GaussLaw M Q H) (x : preIdx M A) :
    Measurable[M.F A] (preCoord M A x) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hZF, hIF, -⟩ := id hG
  show Measurable[M.F A] fun ω => ∑ j, preβ M A x j * M.Z j ω + M.I (pref M A x) ω
  refine Measurable.add (Finset.measurable_sum _ fun j _ => ?_) (hIF _ A (pref_integrand le_rfl x))
  rcases x with i | u
  · by_cases h : j = i.1
    · subst h
      simpa [preβ] using hZF _ A i.2
    · simp only [preβ, Pi.single_apply, h, ite_false, zero_mul]
      exact measurable_const
  · simp only [preβ, Pi.zero_apply, zero_mul]
    exact measurable_const

omit [IsProbabilityMeasure Q] in
lemma ycomb_F (hG : GaussLaw M Q H) : Measurable[M.F A] (ycomb M A) := by
  have h := (yA'_meas (A := A) hG).sub_const (c0 M A)
  simp only [add_sub_cancel_left] at h
  exact h

omit [IsProbabilityMeasure Q] in
lemma resid_F (hG : GaussLaw M Q H) (x : preIdx M A) : Measurable[M.F A] (resid M A H x) :=
  (preCoord_F hG x).sub (measurable_const.mul (ycomb_F hG))

/-- When `V = 0`, `ycomb` is almost surely constant under `Q^A`. -/
lemma ycomb_const (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) (hD : den M A H = 0) :
    ∃ c, ycomb M A =ᵐ[QS M Q A] fun _ => c := by
  have := QS_prob hG hA hAH
  obtain ⟨c, hc⟩ : ∃ c, c = -1 * cov M H (fun n => w 0 A (M.T n)) (Wf 0 A) (β1 M A)
    ((Icc 0 A).indicator 1) := ⟨_, rfl⟩
  have hl : HasLaw (ycomb M A) (gaussianReal c (var M H (β1 M A) ((Icc 0 A).indicator 1)).toNNReal)
      (QS M Q A) := hc ▸ law_QS (δ := β1 M A) hG hA hAH (f1_integrand hAH)
  rw [var_eq_den, hD, Real.toNNReal_zero, gaussianReal_zero_var] at hl
  have h : ∀ᵐ y ∂(QS M Q A).map (ycomb M A), y = c := by
    rw [hl.map_eq, ae_dirac_eq]
    exact eventually_pure.2 rfl
  refine ⟨c, ?_⟩
  filter_upwards [ae_of_ae_map hl.aemeasurable h] with ω hω using hω

lemma memLp_comb (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {δ : Fin N → ℝ} {h : ℝ → ℝ}
    (hh : Integrand h 0 H) : MemLp (comb M δ h) 2 (QS M Q A) := by
  have := QS_prob hG hA hAH
  exact (law_QS (δ := δ) hG hA hAH hh).memLp (memLp_id_gaussianReal 2)

lemma memLp_resid (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) (x : preIdx M A) :
    MemLp (resid M A H x) 2 (QS M Q A) :=
  (memLp_comb (δ := preβ M A x) hG hA hAH (pref_integrand hAH x)).sub
    ((memLp_comb (δ := β1 M A) hG hA hAH (f1_integrand hAH)).const_mul (coef M A H x))

/-- Each residual is uncorrelated with `ycomb` under `Q^A`. -/
lemma cov_resid (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) (hD : den M A H ≠ 0)
    (x : preIdx M A) : cov[resid M A H x, ycomb M A; QS M Q A] = 0 := by
  have hP : MemLp (preCoord M A x) 2 (QS M Q A) :=
    memLp_comb (δ := preβ M A x) hG hA hAH (pref_integrand hAH x)
  have hY : MemLp (ycomb M A) 2 (QS M Q A) :=
    memLp_comb (δ := β1 M A) hG hA hAH (f1_integrand hAH)
  have e1 : cov[preCoord M A x, ycomb M A; QS M Q A] =
      bil M H (preβ M A x) (pref M A x) (β1 M A) ((Icc 0 A).indicator 1) :=
    cov_QS (δ := β1 M A) hG hA hAH (pref_integrand hAH x) (f1_integrand hAH)
  have := QS_prob hG hA hAH
  have e2 : cov[ycomb M A, ycomb M A; QS M Q A] = den M A H :=
    cov_QS (γ := β1 M A) (δ := β1 M A) hG hA hAH (f1_integrand hAH) (f1_integrand hAH)
  show cov[fun ω => preCoord M A x ω - coef M A H x * ycomb M A ω, ycomb M A; QS M Q A] = 0
  rw [covariance_fun_sub_left hP (hY.const_mul _) hY, covariance_const_mul_left, e1, e2,
    coef_mul hD, sub_self]

/-- A linear combination of residuals is independent of `ycomb` under `Q^A`. -/
lemma lin_indep (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) (hD : den M A H ≠ 0)
    {ι : Type*} (s : Finset ι) (x : ι → preIdx M A) (a : ι → ℝ) :
    IndepFun (fun ω => ∑ k ∈ s, a k * resid M A H (x k) ω) (ycomb M A) (QS M Q A) := by
  have := QS_prob hG hA hAH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  have hf1 := f1_integrand (A := A) hAH
  set c := ∑ k ∈ s, a k * coef M A H (x k)
  have h1 := comb_sum hG s (fun k => (preβ M A (x k), pref M A (x k)))
    (fun k => pref_integrand hAH (x k)) a
  have hGi := integrand_sum H s (fun k => (preβ M A (x k), pref M A (x k)))
    (fun k => pref_integrand hAH (x k)) a
  have h2 := comb_add hG (fun i => ∑ k ∈ s, a k * preβ M A (x k) i) (β1 M A) hGi hf1 (-c)
  have hγ := integrand_add hGi hf1 (-c)
  have hX : (fun ω => ∑ k ∈ s, a k * resid M A H (x k) ω) =ᵐ[Q]
      comb M (fun i => ∑ k ∈ s, a k * preβ M A (x k) i + -c * β1 M A i)
        (fun u => ∑ k ∈ s, a k * pref M A (x k) u + -c * (Icc 0 A).indicator 1 u) := by
    filter_upwards [h1, h2] with ω e1 e2
    have e3 : ∑ k ∈ s, a k * resid M A H (x k) ω =
        (∑ k ∈ s, a k * comb M (preβ M A (x k)) (pref M A (x k)) ω) +
          -c * comb M (β1 M A) ((Icc 0 A).indicator 1) ω := by
      show ∑ k ∈ s, a k * (comb M (preβ M A (x k)) (pref M A (x k)) ω -
        coef M A H (x k) * comb M (β1 M A) ((Icc 0 A).indicator 1) ω) = _
      simp only [c, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, neg_mul, mul_assoc]
      ring
    rw [e3, e1]
    exact e2
  have hY : MemLp (ycomb M A) 2 (QS M Q A) := memLp_comb (δ := β1 M A) hG hA hAH hf1
  have hcov : cov M H (fun i => ∑ k ∈ s, a k * preβ M A (x k) i + -c * β1 M A i)
      (fun u => ∑ k ∈ s, a k * pref M A (x k) u + -c * (Icc 0 A).indicator 1 u)
      (β1 M A) ((Icc 0 A).indicator 1) = 0 := by
    have e : cov[comb M (fun i => ∑ k ∈ s, a k * preβ M A (x k) i + -c * β1 M A i)
        (fun u => ∑ k ∈ s, a k * pref M A (x k) u + -c * (Icc 0 A).indicator 1 u), ycomb M A;
        QS M Q A] = _ := cov_QS (δ := β1 M A) hG hA hAH hγ hf1
    rw [← e, ← cov_congr (hac.ae_le hX),
      covariance_fun_sum_left' (X := fun k ω => a k * resid M A H (x k) ω)
        (fun k _ => (memLp_resid hG hA hAH (x k)).const_mul _) hY]
    exact Finset.sum_eq_zero fun k _ => by
      rw [covariance_const_mul_left, cov_resid hG hA hAH hD, mul_zero]
  exact (indep_comb hG hA hAH hγ hf1 hcov).congr (EventuallyEq.symm (hac.ae_le hX))
    (EventuallyEq.refl _ _)

/-- (C3) `σ(r)` is independent of `ycomb` under `Q^A`. -/
theorem resAlg_indep_y (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) :
    Indep (resAlg M A H) (MeasurableSpace.comap (ycomb M A) inferInstance) (QS M Q A) := by
  classical
  have := QS_prob hG hA hAH
  by_cases hD : den M A H = 0
  · obtain ⟨c, hc⟩ := ycomb_const hG hA hAH hD
    refine (indep_comap_congr hc ?_).symm
    rw [MeasurableSpace.comap_const]
    exact indep_bot_left _
  have hy := ycomb_meas hG hAH
  set m : Finset (preIdx M A) → MeasurableSpace Ω := fun s =>
    MeasurableSpace.comap (fun ω (q : s) => resid M A H q.1 ω) inferInstance
  have hvec : ∀ s : Finset (preIdx M A), Measurable fun ω (q : s) => resid M A H q.1 ω :=
    fun s => measurable_pi_iff.2 fun q => resid_meas hG hAH q.1
  have hindep : ∀ s, Indep (m s) (MeasurableSpace.comap (ycomb M A) inferInstance)
      (QS M Q A) := fun s => by
    refine indep_of_dual (hvec s) hy.comap_le fun L => ?_
    have e : (fun ω => L (fun q : s => resid M A H q.1 ω)) =
        fun ω => ∑ q ∈ (Finset.univ : Finset s), L (Pi.single q 1) * resid M A H q.1 ω := by
      funext ω
      have hL := L.toLinearMap.pi_apply_eq_sum_univ (fun q : s => resid M A H q.1 ω)
      simp only [ContinuousLinearMap.coe_coe] at hL
      rw [hL]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [e]
    exact (IndepFun_iff_Indep _ _ _).1 (lin_indep hG hA hAH hD _ (fun q : s => q.1) _)
  have hle : ∀ s, m s ≤ m₀ := fun s => (hvec s).comap_le
  have hsub : ∀ s t : Finset (preIdx M A), s ⊆ t → m s ≤ m t := fun s t hst => by
    have hr : Measurable fun (v : ↥t → ℝ) (q : ↥s) => v ⟨q.1, hst q.2⟩ :=
      measurable_pi_iff.2 fun q => measurable_pi_apply _
    have e : (fun ω (q : ↥s) => resid M A H q.1 ω) =
        (fun (v : ↥t → ℝ) (q : ↥s) => v ⟨q.1, hst q.2⟩) ∘
          (fun ω (q : ↥t) => resid M A H q.1 ω) := rfl
    show MeasurableSpace.comap _ _ ≤ MeasurableSpace.comap _ _
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  have hdir : Directed (· ≤ ·) m := fun s t =>
    ⟨s ∪ t, hsub s _ Finset.subset_union_left, hsub t _ Finset.subset_union_right⟩
  have hsup := indep_iSup_of_directed_le hindep hle hy.comap_le hdir
  refine indep_of_indep_of_le_left hsup (iSup_le fun x => ?_)
  refine le_iSup_of_le {x} ?_
  have e : resid M A H x = (fun v : ↥({x} : Finset (preIdx M A)) → ℝ =>
      v ⟨x, Finset.mem_singleton_self _⟩) ∘ (fun ω (q : ↥({x} : Finset (preIdx M A))) =>
        resid M A H q.1 ω) := rfl
  show MeasurableSpace.comap (resid M A H x) _ ≤ MeasurableSpace.comap _ _
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- (C4) `σ(r)` is independent of the representative `(c₀ + ycomb, Ξ′)` of `(y_A, Ξ)`. -/
theorem resAlg_indep_pair (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) :
    Indep (resAlg M A H) (MeasurableSpace.comap
      (fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω)) inferInstance) (QS M Q A) := by
  have := QS_prob hG hA hAH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -⟩ := id hG
  have hy'F : Measurable[M.F A] fun ω => c0 M A + ycomb M A ω := yA'_meas hG
  have hX'F := Xi'_meas hG hA (A := A) (H := H)
  have h1 : Indep (resAlg M A H)
      (MeasurableSpace.comap (fun ω => c0 M A + ycomb M A ω) inferInstance) (QS M Q A) :=
    indep_of_indep_of_le_right (resAlg_indep_y hG hA hAH)
      (Measurable.comap_le (measurable_const.add (comap_measurable (ycomb M A))))
  have hRF : resAlg M A H ⊔ MeasurableSpace.comap (fun ω => c0 M A + ycomb M A ω) inferInstance ≤
      M.F A := sup_le (iSup_le fun x => (resid_F hG x).comap_le) hy'F.comap_le
  have h2 := indep_of_indep_of_le_left (indep_of_indep_of_le_right
    (futureAlg_QS hG hA hAH).1.symm hX'F.comap_le) hRF
  have h3 := indep_sup_right (resAlg_le hG hAH) (hy'F.comap_le.trans (hFle A))
    (hX'F.comap_le.trans (futureAlg_le hG A)) h1 h2
  rwa [← MeasurableSpace.comap_prodMk (mβ := (inferInstance : MeasurableSpace ℝ))
    (mγ := (inferInstance : MeasurableSpace (State N A H)))] at h3

end Reg

/-! ### The filtration identity -/

section Filt
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N}
  {H A : ℝ}

omit m₀ in
lemma fst_post {S s : ℝ} :
    Measurable[postFilt M A H S s] (Prod.fst : ℝ × State N A H → ℝ) :=
  Measurable.of_comap_le (le_sup_left.trans le_sup_left)

omit m₀ in
lemma Z_post {S s : ℝ} {i : Fin N} (hi : M.T i ≤ min s S) :
    Measurable[postFilt M A H S s] fun p : ℝ × State N A H => p.2.1 i :=
  Measurable.of_comap_le (le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)))

omit m₀ in
lemma incr_post {S s : ℝ} (q : Rat' A H) (hq : (q.1 : ℝ) ≤ min s S) :
    Measurable[postFilt M A H S s] fun p : ℝ × State N A H => p.2.2 q :=
  Measurable.of_comap_le (le_sup_of_le_right (le_iSup₂_of_le q hq le_rfl))

omit m₀ in
/-- `σ(r) ∨ (y_A, Ξ)⁻¹ σ(y, ξ_{≤s})`. -/
noncomputable abbrev regAlg (M : DiffModel Ω N) (A H S s : ℝ) : MeasurableSpace Ω :=
  resAlg M A H ⊔ MeasurableSpace.comap (fun ω => (yA M A ω, Xi M A H ω)) (postFilt M A H S s)

omit m₀ in
lemma post_G {S s : ℝ} {g : ℝ × State N A H → ℝ} (hg : Measurable[postFilt M A H S s] g) :
    Measurable[regAlg M A H S s] fun ω => g (yA M A ω, Xi M A H ω) :=
  (hg.comp (comap_measurable _)).mono le_sup_right le_rfl

omit m₀ in
lemma resid_G {S s : ℝ} (x : preIdx M A) : Measurable[regAlg M A H S s] (resid M A H x) :=
  Measurable.of_comap_le (le_sup_of_le_left (le_iSup (fun x =>
    MeasurableSpace.comap (resid M A H x) inferInstance) x))

lemma ycomb_ae (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) :
    ycomb M A =ᵐ[Q] fun ω => yA M A ω - c0 M A :=
  (yA_ae hG hA hAH).mono fun ω h => by
    show comb M (β1 M A) ((Icc 0 A).indicator 1) ω = yA M A ω - c0 M A
    rw [h]
    ring

lemma preCoord_ae (hG : GaussLaw M Q H) (hAH : A ≤ H) (x : preIdx M A) :
    preCoord M A x =ᵐ[Q] preNat M A x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hY, -⟩ := id hG
  rcases x with i | u
  · filter_upwards [I_zero hG] with ω h
    show ∑ j, preβ M A (Sum.inl i) j * M.Z j ω + M.I (pref M A (Sum.inl i)) ω = M.Z i.1 ω
    simp [preβ, pref, h, Pi.single_apply]
  · filter_upwards [hY u.1 u.2.1 (u.2.2.trans hAH)] with ω h
    show ∑ j, preβ M A (Sum.inr u) j * M.Z j ω + M.I (pref M A (Sum.inr u)) ω = M.Y u.1 ω
    simp [preβ, pref, h]

lemma resid_ae (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) (x : preIdx M A) :
    resid M A H x =ᵐ[Q] fun ω => preNat M A x ω - coef M A H x * (yA M A ω - c0 M A) := by
  filter_upwards [preCoord_ae hG hAH x, ycomb_ae hG hA hAH] with ω h1 h2
  show preCoord M A x ω - coef M A H x * ycomb M A ω = _
  rw [h1, h2]

omit m₀ in
lemma preNat_nat {S s : ℝ} (hAs : A ≤ min s S) (x : preIdx M A) :
    Measurable[natural M S s] (preNat M A x) := by
  rcases x with i | u
  · exact Z_nat (i.2.trans hAs)
  · exact Y_nat u.2.1 (u.2.2.trans hAs)

lemma preNat_G (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) {S s : ℝ} (x : preIdx M A) :
    Measurable[eventuallyMeasurableSpace (regAlg M A H S s) (ae Q)] (preNat M A x) := by
  have hy : Measurable[regAlg M A H S s] (yA M A) := post_G fst_post
  have hm : Measurable[regAlg M A H S s]
      fun ω => resid M A H x ω + coef M A H x * (yA M A ω - c0 M A) :=
    (resid_G x).add (measurable_const.mul (hy.sub measurable_const))
  refine ae_meas hm ?_
  filter_upwards [resid_ae hG hA hAH x] with ω h
  show _ = resid M A H x ω + coef M A H x * (yA M A ω - c0 M A)
  rw [h]
  ring

/-- `Y_u − Y_A`, for `A < u ≤ s ∧ S`, is a limit of rational coordinates of `Ξ`. -/
lemma incr_G (hG : GaussLaw M Q H) {S s u : ℝ} (hSH : S ≤ H) (hAu : A < u)
    (hus : u ≤ min s S) : Measurable[regAlg M A H S s] fun ω => M.Y u ω - M.Y A ω := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hYc, -⟩ := id hG
  have hq : ∀ n : ℕ, ∃ q : ℚ, max A (u - 1 / (n + 1)) < q ∧ (q : ℝ) < u := fun n =>
    exists_rat_btwn (max_lt hAu (by have : (0:ℝ) < 1 / (n + 1) := (by positivity); linarith))
  choose q hq1 hq2 using hq
  let r : ℕ → Rat' A H := fun n => ⟨q n, (le_max_left _ _).trans_lt (hq1 n),
    (hq2 n).le.trans (hus.trans ((min_le_right _ _).trans hSH))⟩
  refine @measurable_of_tendsto_metrizable Ω ℝ (regAlg M A H S s) _ _ _ _
    (fun n ω => (Xi M A H ω).2 (r n)) _ (fun n => ?_) ?_
  · exact post_G (incr_post (r n) ((hq2 n).le.trans hus))
  · rw [tendsto_pi_nhds]
    intro ω
    have h1 : Tendsto (fun n : ℕ => u - 1 / ((n : ℝ) + 1)) atTop (𝓝 u) := by
      have := (tendsto_const_nhds (x := u)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [sub_zero] at this
    have hc : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 u) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
        (fun n => (le_max_right _ _).trans (hq1 n).le) (fun n => (hq2 n).le)
    exact (((hYc ω).tendsto u).comp hc).sub_const (M.Y A ω)

/-- (C6) The filtration identity. -/
theorem filt (hG : GaussLaw M Q H) {A S s : ℝ} (hA : 0 ≤ A) (hSH : S ≤ H)
    (hAs : A ≤ min s S) :
    eventuallyMeasurableSpace (natural M S s) (ae Q) =
      eventuallyMeasurableSpace (regAlg M A H S s) (ae Q) := by
  have hAH : A ≤ H := hAs.trans ((min_le_right _ _).trans hSH)
  refine le_antisymm (evMeas_mono (sup_le (iSup₂_le fun i hi => ?_) (iSup₂_le fun u hu => ?_)))
    (evMeas_mono (sup_le (iSup_le fun x => ?_) ?_))
  · refine Measurable.comap_le ?_
    by_cases hiA : M.T i ≤ A
    · exact preNat_G hG hA hAH (Sum.inl ⟨i, hiA⟩)
    · have e : M.Z i = fun ω => (Xi M A H ω).1 i := funext fun ω => by
        simp [Xi, lt_of_not_ge hiA]
      rw [e]
      exact (post_G (Z_post hi)).mono le_eventuallyMeasurableSpace le_rfl
  · refine Measurable.comap_le ?_
    by_cases huA : u ≤ A
    · exact preNat_G hG hA hAH (Sum.inr ⟨u, hu.1, huA⟩)
    · have e : M.Y u = fun ω => (M.Y u ω - M.Y A ω) + M.Y A ω := funext fun ω => by ring
      rw [e]
      exact ((incr_G hG hSH (lt_of_not_ge huA) hu.2).mono le_eventuallyMeasurableSpace
        le_rfl).add (preNat_G hG hA hAH (Sum.inr ⟨A, hA, le_rfl⟩))
  · have hm : Measurable[natural M S s]
        fun ω => preNat M A x ω - coef M A H x * (yA M A ω - c0 M A) :=
      (preNat_nat hAs x).sub (measurable_const.mul ((yA_nat hA hAs).sub measurable_const))
    exact Measurable.comap_le (ae_meas hm (resid_ae hG hA hAH x))
  · exact (pair_natural hA hAs).comap_le.trans le_eventuallyMeasurableSpace

end Filt

theorem regressionS : regressionStatement := by
  intro Ω _ N Q _ M H hG A S hA hAS hSH
  have hAH : A ≤ H := hAS.trans hSH
  have := QS_prob hG hA hAH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  refine ⟨resAlg_le hG hAH, fun B C hB hC => ?_, fun s hs => filt hG hA hSH hs⟩
  have hF'm : Measurable fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω) :=
    (measurable_const.add (ycomb_meas hG hAH)).prodMk
      ((Xi'_meas hG hA).mono (futureAlg_le hG A) le_rfl)
  have hFF' : (fun ω => (yA M A ω, Xi M A H ω)) =ᵐ[QS M Q A]
      fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω) :=
    hac.ae_le ((yA_ae hG hA hAH).prodMk (Xi_ae hG hA))
  have hs : ((fun ω => (yA M A ω, Xi M A H ω)) ⁻¹' C : Set Ω) =ᵐ[QS M Q A]
      ((fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω)) ⁻¹' C : Set Ω) :=
    hFF'.mono fun ω h => by
      have h' : (yA M A ω, Xi M A H ω) = (c0 M A + ycomb M A ω, Xi' M A H ω) := h
      change ((yA M A ω, Xi M A H ω) ∈ C) = ((c0 M A + ycomb M A ω, Xi' M A H ω) ∈ C)
      rw [h']
  have hBB : (B : Set Ω) =ᵐ[QS M Q A] B := EventuallyEq.rfl
  rw [measure_congr (hBB.inter hs),
    (Indep_iff _ _ _).1 (resAlg_indep_pair hG hA hAH) B _ hB ⟨C, hC, rfl⟩,
    ← law_pair hG hA hAH, Measure.map_congr hFF', Measure.map_apply hF'm hC]

theorem continuousAggregationRegression : Standalone.ContinuousAggregationRegression.statement := regressionS

end Novel.ContinuousAggregationRegressionProof

import Standalone.ContinuousAggregationAmericanLower
import Novel.ContinuousAggregationEuropeanProof
import Novel.ContinuousAggregationSectioningProof
import Mathlib.MeasureTheory.Function.Floor

/-! # Claim 054 (e): the American value, its definitions, and the lower bound (proof)

* `lamJoint`: the dyadic Riemann sums depend on `t` only through a floor, a countable index
  (`riem_joint`), so `J` and `Λ_V` are jointly Borel.
* `modelFilt_iff`: under `GaussLaw`, every generator of `natural_s` is null-measurable, since `Y_s`
  is a.s. a measurable Wiener integral. So the meet with the completed σ-algebra in `modelFilt` is
  vacuous.
* `value_eq`: for an exercise time `τ`, `B_τ⁻¹ = B_A⁻¹ e^{−Λ_{V_A}(τ, y_A, Ξ)}` on every path
  (`disc_split`), and `Q^A` has density `B_A⁻¹/P(0, A)`. So the value of `τ` is `P(0, A)` times the
  `Q^A`-integral of `e^{−Λ} Φ` at `(τ, y_A, Ξ)`.
* `lowerS`: for `ρ ∈ 𝒯̃`, `ρ(y_A, Ξ)` is an `𝔽`-stopping time. `(y_A, Ξ)` is `natural_s`-measurable
  into `σ(y, ξ_{≤s})` (`pair_natural`). A `N(0, V_A) ⊗ λ_post`-null set pulls back to a `Q^A`-null
  set, hence a `Q`-null set, because `Q ≪ Q^A`: the density is positive. Its value is
  `P(0, A) ∫ e^{−Λ} Φ(ρ, ·)` by (c)'s law of `(y_A, Ξ)` under `Q^A`.

Reused, not reproved: `Novel.ContinuousAggregationEuropeanProof` (`disc_split`, `law_pair`,
`Xi_aem`, `inner_cont`, `rate_ii`), `Novel.ContinuousAggregationLevelProof` (`yA_ae`, `law_yA`),
`Novel.ContinuousAggregationSectioningProof` (`integral_completion`, `aesm_of_completion`,
`id_meas`, `times_meas`, `aug_iff`, `const_mem`), `Novel.DiffusionMeetingPricingProof.disc_ae`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.ContinuousAggregationAmericanLowerProof
open Standalone.CompoundedFuturesIdentification (w)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw rate)
open Standalone.DiffusionMeetingPricing (QS Qacc disc P0)
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationEuropean
open Standalone.ContinuousAggregationSectioning (times value₂)
open Standalone.ContinuousAggregationAmericanLower
open Novel.ContinuousAggregationSectioningProof (integral_completion aesm_of_completion id_meas
  times_meas aug_iff const_mem)

/-! ### `Λ` is jointly Borel -/

/-- The Riemann sum with a given number of terms. -/
noncomputable def riemK (A H : ℝ) (n k : ℕ) (ξ : Rat' A H → ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    (if h : A < (dy A n j : ℝ) ∧ (dy A n j : ℝ) ≤ H then ξ ⟨dy A n j, h⟩ else 0) / 2 ^ n

lemma riemK_meas (A H : ℝ) (n k : ℕ) : Measurable (riemK A H n k) := by
  unfold riemK
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases hc : A < (dy A n j : ℝ) ∧ (dy A n j : ℝ) ≤ H
  · simp only [dite_eq_left hc]
    exact (measurable_pi_apply _).div_const _
  · simp only [dite_eq_right hc, zero_div]
    exact measurable_const

lemma riem_joint (A H : ℝ) (n : ℕ) :
    Measurable fun p : ℝ × (Rat' A H → ℝ) => riem A H p.1 n p.2 := by
  have h1 : Measurable fun t : ℝ => ⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋ :=
    (measurable_id.mul_const _).floor.sub_const _
  have hk : Measurable fun t : ℝ => (⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋).toNat :=
    Measurable.comp (g := Int.toNat) measurable_from_top h1
  have hF : Measurable fun q : (Rat' A H → ℝ) × ℕ => riemK A H n q.2 q.1 :=
    measurable_from_prod_countable_left fun k => riemK_meas A H n k
  exact hF.comp (measurable_snd.prodMk (hk.comp measurable_fst))

/-- The same, composed with measurable maps. -/
lemma riem_comp {α : Type*} [MeasurableSpace α] (A H : ℝ) (n : ℕ) {f : α → ℝ}
    {g : α → (Rat' A H → ℝ)} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => riem A H (f a) n (g a) :=
  Measurable.comp (g := fun p : ℝ × (Rat' A H → ℝ) => riem A H p.1 n p.2)
    (f := fun a => (f a, g a)) (riem_joint A H n) (hf.prodMk hg)

theorem lamJoint : lamJointStatement := by
  intro Ω N M hg ⟨B, hB⟩ hf0 ⟨C, hC⟩ A H V
  have c1 : Continuous fun t => ∫ u in A..t, M.f0 u :=
    intervalIntegral.continuous_primitive
      (fun a b => Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC a b) A
  have c2 : Continuous fun t => ∫ s in A..t, ∫ u in A..s, M.g u * (s - u) :=
    intervalIntegral.continuous_primitive (fun a b =>
      (Novel.ContinuousAggregationEuropeanProof.inner_cont M hg ⟨B, hB⟩ A).intervalIntegrable a b) A
  have hsnd : Measurable fun q : ℝ × (ℝ × State N A H) => q.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hr : ∀ n, Measurable fun q : ℝ × (ℝ × State N A H) => riem A H q.1 n q.2.2.2 :=
    fun n => riem_comp A H n measurable_fst hsnd
  have hJ : Measurable fun q : ℝ × (ℝ × State N A H) => J A H q.1 q.2.2.2 := by
    unfold J
    exact Measurable.limsup hr
  have t1 : Measurable fun q : ℝ × (ℝ × State N A H) => ∫ u in A..q.1, M.f0 u :=
    c1.measurable.comp measurable_fst
  have t2 : Measurable fun q : ℝ × (ℝ × State N A H) => q.2.1 * (q.1 - A) :=
    (measurable_fst.comp measurable_snd).mul (measurable_fst.sub_const A)
  have t3 : Measurable fun q : ℝ × (ℝ × State N A H) => V * (q.1 - A) ^ 2 / 2 :=
    (measurable_const.mul ((measurable_fst.sub_const A).pow_const 2)).div_const 2
  have t4 : Measurable fun q : ℝ × (ℝ × State N A H) => ∑ i, (if A < M.T i ∧ M.T i ≤ q.1 then
      q.2.2.1 i * (q.1 - M.T i) + M.v i * (q.1 - M.T i) ^ 2 / 2 else 0) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hc : Measurable fun q : ℝ × (ℝ × State N A H) => q.2.2.1 i :=
      (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hterm : Measurable fun q : ℝ × (ℝ × State N A H) =>
        q.2.2.1 i * (q.1 - M.T i) + M.v i * (q.1 - M.T i) ^ 2 / 2 :=
      (hc.mul (measurable_fst.sub_const _)).add
        ((measurable_const.mul ((measurable_fst.sub_const _).pow_const 2)).div_const 2)
    by_cases hAT : A < M.T i
    · simp only [hAT, true_and]
      exact Measurable.ite (measurableSet_le measurable_const measurable_fst) hterm measurable_const
    · simp only [hAT, false_and, ite_false]
      exact measurable_const
  have t6 : Measurable fun q : ℝ × (ℝ × State N A H) =>
      ∫ s in A..q.1, ∫ u in A..s, M.g u * (s - u) := c2.measurable.comp measurable_fst
  unfold Lam
  exact ((((t1.add t2).add t3).add t4).add hJ).add t6

/-! ### The model filtration -/

section Model
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N}
  {H : ℝ}

/-- The completed σ-algebra, on `Ω`. -/
local notation "𝒞" => eventuallyMeasurableSpace m₀ (ae Q)

/-- Under `GaussLaw`, `natural_s ≤ 𝒞`: each generator is null-measurable. -/
lemma natural_le (hG : GaussLaw M Q H) {S : ℝ} (hSH : S ≤ H) (s : ℝ) : natural M S s ≤ 𝒞 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hZm, hIm, -, hY, -⟩ := id hG
  refine sup_le (iSup₂_le fun i _ => ?_) (iSup₂_le fun u hu => ?_)
  · exact ((hZm i).mono le_eventuallyMeasurableSpace le_rfl).comap_le
  · have hI := hIm _ (Novel.ContinuousAggregationLevelProof.f1_integrand
      (A := u) (hu.2.trans ((min_le_right _ _).trans hSH)))
    have hae := hY u hu.1 (hu.2.trans ((min_le_right _ _).trans hSH))
    refine Measurable.comap_le (m₁ := 𝒞) fun B hB => ⟨_, hI hB, ?_⟩
    filter_upwards [hae] with ω hω
    change (M.Y u ω ∈ B) = (M.I ((Icc 0 u).indicator 1) ω ∈ B)
    rw [hω]

lemma evMeas_le (hG : GaussLaw M Q H) {S : ℝ} (hSH : S ≤ H) (s : ℝ) :
    eventuallyMeasurableSpace (natural M S s) (ae Q) ≤ 𝒞 := by
  rintro B ⟨C, hC, hBC⟩
  obtain ⟨C', hC', hCC'⟩ := natural_le hG hSH s C hC
  exact ⟨C', hC', hBC.trans hCC'⟩

/-- Under `GaussLaw`, `𝔽_t` is `⋂_{s > t} (natural_s ∨ 𝒩_Q)`. -/
theorem modelFilt_iff (hG : GaussLaw M Q H) {S : ℝ} (hSH : S ≤ H) (t : ℝ) (B : Set Ω) :
    MeasurableSet[modelFilt M Q S t] B ↔
      ∀ s, t < s → ∃ C, MeasurableSet[natural M S s] C ∧ B =ᵐ[Q] C := by
  have key : MeasurableSet[⨅ s ∈ Ioi t, eventuallyMeasurableSpace (natural M S s) (ae Q)] B ↔
      ∀ s, t < s → ∃ C, MeasurableSet[natural M S s] C ∧ B =ᵐ[Q] C := by
    simp only [MeasurableSpace.measurableSet_iInf, mem_Ioi]
    rfl
  have hinf : MeasurableSet[modelFilt M Q S t] B ↔
      MeasurableSet[⨅ s ∈ Ioi t, eventuallyMeasurableSpace (natural M S s) (ae Q)] B ∧
        MeasurableSet[𝒞] B :=
    MeasurableSpace.measurableSet_inf
  rw [hinf, key]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact evMeas_le hG hSH (t + 1) B (h (t + 1) (by linarith))

end Model

/-! ### The value of an exercise time -/

section Value
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {M : DiffModel Ω N} {H : ℝ}
open Novel.DiffusionMeetingGaussProof (comb comb_meas Cst Wf Wf_integrand)
open Novel.ContinuousAggregationLevelProof (yA_ae law_yA f1_integrand)
open Novel.ContinuousAggregationEuropeanProof (disc_split law_pair Xi_aem)

omit [IsProbabilityMeasure Q] in
lemma Pay_meas (hG : GaussLaw M Q H) (A : ℝ) {Φ : ℝ × (ℝ × State N A H) → ℝ}
    (hΦ : Measurable Φ) : Measurable (Pay M A H Φ) := by
  obtain ⟨-, -, hg, hB, -, hf0, hf0B, -⟩ := id hG
  exact (Real.measurable_exp.comp (lamJoint _ _ M hg hB hf0 hf0B A H _).neg).mul hΦ

omit [IsProbabilityMeasure Q] in
/-- The density `B_A⁻¹/P(0, A)` of `Q^A` is almost everywhere measurable. -/
lemma dens_aem (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    AEMeasurable (fun ω => ENNReal.ofReal (disc M A ω / P0 M A)) Q := by
  have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (-Cst M 0 A) *
      Real.exp (-1 * comb M (fun n => w 0 A (M.T n)) (Wf 0 A) ω) / P0 M A) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (comb_meas hG (Wf_integrand (a := 0) hAH))))).div_const _)
  refine hm.aemeasurable.congr ?_
  filter_upwards [Novel.DiffusionMeetingPricingProof.disc_ae hG hA hAH] with ω hω
  simp only [hω]

omit [IsProbabilityMeasure Q] in
/-- `Q` and `Q^A` have the same null sets: `Q ≪ Q^A`. -/
lemma Q_ac (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) : Q ≪ QS M Q A :=
  withDensity_absolutelyContinuous' (dens_aem hG hA hAH) (Eventually.of_forall fun _ =>
    (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos _) (Real.exp_pos _))).ne')

omit [IsProbabilityMeasure Q] in
lemma pair_aem (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    AEMeasurable (fun ω => (yA M A ω, Xi M A H ω)) Q :=
  ((measurable_const.add (comb_meas hG (f1_integrand hAH))).aemeasurable.congr
    (yA_ae hG hA hAH).symm).prodMk (Xi_aem hG hA)

lemma pair_aem_QS (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    AEMeasurable (fun ω => (yA M A ω, Xi M A H ω)) (QS M Q A) :=
  (law_yA hG hA hAH).aemeasurable.prodMk
    ((Xi_aem hG hA).mono_ac (withDensity_absolutelyContinuous _ _))

omit [IsProbabilityMeasure Q] in
/-- The value of an exercise time: `E_Q[B_τ⁻¹ Φ(τ, y_A, Ξ)] = P(0, A) E_{Q^A}[e^{−Λ} Φ(τ, y_A, Ξ)]`. -/
theorem value_eq (hG : GaussLaw M Q H) {A S : ℝ} (hA : 0 ≤ A) (hAS : A ≤ S) (hSH : S ≤ H)
    {Φ : ℝ × (ℝ × State N A H) → ℝ} (hΦ : Measurable Φ) {τ : NullMeasurableSpace Ω Q → ℝ}
    (hτm : Measurable τ) (hτ : ∀ ω, τ ω ∈ Icc A S) :
    ∫ ω, payoff M A H Φ τ ω ∂Q.completion =
      P0 M A * ∫ ω, Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂(QS M Q A) := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -, hf0, ⟨C, hC⟩, -, -, -, -, hY, -⟩ := id hG
  have hAH : A ≤ H := hAS.trans hSH
  have hP0 : P0 M A ≠ 0 := (Real.exp_pos _).ne'
  have hd : ∀ ω, 0 ≤ disc M A ω / P0 M A := fun ω =>
    div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hpt : ∀ ω : Ω, payoff M A H Φ τ ω =
      disc M A ω * Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) := fun ω => by
    unfold payoff Pay
    rw [disc_split M hg hB hf0 hC hY (hτ ω).1 ((hτ ω).2.trans hSH) ω]
    ring
  have hτa : AEMeasurable (fun ω : Ω => τ ω) Q := (aesm_of_completion hτm).aemeasurable
  have hF : AEStronglyMeasurable (fun ω : Ω => Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω))) Q :=
    ((Pay_meas hG A hΦ).comp_aemeasurable (hτa.prodMk (pair_aem hG hA hAH))).aestronglyMeasurable
  have hdisc : AEStronglyMeasurable (fun ω => disc M A ω) Q := by
    have := (dens_aem hG hA hAH).ennreal_toReal
    refine (this.mul_const (P0 M A)).aestronglyMeasurable.congr (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hd ω)]
    exact div_mul_cancel₀ _ hP0
  have hQS : QS M Q A = Q.withDensity fun ω => ENNReal.ofReal (disc M A ω / P0 M A) := rfl
  have hwd : ∫ ω, Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂(QS M Q A) =
      ∫ ω : Ω, (disc M A ω / P0 M A) * Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂Q := by
    rw [hQS, integral_withDensity_eq_integral_toReal_smul₀ (dens_aem hG hA hAH)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hd ω)]
  calc ∫ ω, payoff M A H Φ τ ω ∂Q.completion
      = ∫ ω, disc M A ω * Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂Q.completion :=
        integral_congr_ae (Eventually.of_forall fun ω => hpt ω)
    _ = ∫ ω : Ω, disc M A ω * Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂Q :=
        integral_completion (f := fun ω : Ω => disc M A ω * Pay M A H Φ (τ ω,
          (yA M A ω, Xi M A H ω))) (hdisc.mul hF)
    _ = ∫ ω : Ω, P0 M A * ((disc M A ω / P0 M A) *
          Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω))) ∂Q :=
        integral_congr_ae (Eventually.of_forall fun ω => by
          simp only
          rw [← mul_assoc, mul_div_cancel₀ _ hP0])
    _ = _ := by rw [integral_const_mul, hwd]

end Value

theorem modelFiltS : modelFiltStatement := fun _ _ _ _ _ _ _ hG _ hSH t B =>
  modelFilt_iff hG hSH t B

/-! ### The lower bound -/

/-- A null-measurable function composed with a map whose law is absolutely continuous is
null-measurable. -/
lemma comp_null {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {F : α → β} (hF : AEMeasurable F μ) (hac : μ.map F ≪ ν)
    {g : NullMeasurableSpace β ν → ℝ} (hg : Measurable g) :
    Measurable fun a : NullMeasurableSpace α μ => g (F a) := by
  intro B hB
  obtain ⟨t, ht, heq⟩ := hg hB
  have h1 : ∀ᵐ y ∂(μ.map F), (y ∈ t) = (y ∈ g ⁻¹' B) := hac.ae_le heq.symm
  have h2 : (F ⁻¹' t : Set α) =ᵐ[μ] (F ⁻¹' (g ⁻¹' B) : Set α) := ae_of_ae_map hF h1
  exact (hF.nullMeasurable ht).congr h2

section Lower
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {M : DiffModel Ω N} {H : ℝ}
open Novel.ContinuousAggregationEuropeanProof (law_pair Xi_aem QS_prob)

omit m₀ [IsProbabilityMeasure Q] in
lemma Z_nat {S s : ℝ} {i : Fin N} (h : M.T i ≤ min s S) : Measurable[natural M S s] (M.Z i) :=
  Measurable.of_comap_le (le_sup_of_le_left (le_iSup₂_of_le i h le_rfl))

omit m₀ [IsProbabilityMeasure Q] in
lemma Y_nat {S s u : ℝ} (h0 : 0 ≤ u) (h : u ≤ min s S) : Measurable[natural M S s] (M.Y u) :=
  Measurable.of_comap_le (le_sup_of_le_right (le_iSup₂_of_le u ⟨h0, h⟩ le_rfl))

omit m₀ [IsProbabilityMeasure Q] in
lemma yA_nat {A S s : ℝ} (hA : 0 ≤ A) (hAs : A ≤ min s S) : Measurable[natural M S s] (yA M A) := by
  show Measurable[natural M S s] fun ω => M.f0 A + ∑ n, (if M.T n ≤ A then
    M.Z n ω + M.v n * (A - M.T n) else 0) + M.Y A ω + (∫ s in (0:ℝ)..A, M.g s * (A - s)) - M.f0 A
  refine (((measurable_const.add (Finset.measurable_sum _ fun n _ => ?_)).add
    (Y_nat hA hAs)).add measurable_const).sub measurable_const
  by_cases h : M.T n ≤ A
  · simp only [h, ite_true]
    exact (Z_nat (h.trans hAs)).add_const _
  · simp only [h, ite_false]
    exact measurable_const

omit m₀ [IsProbabilityMeasure Q] in
/-- `(y_A, Ξ)` is `natural_s`-measurable into `σ(y, ξ_{≤s})`. -/
lemma pair_natural {A S s : ℝ} (hA : 0 ≤ A) (hAs : A ≤ min s S) :
    @Measurable Ω (ℝ × State N A H) (natural M S s) (postFilt M A H S s)
      (fun ω => (yA M A ω, Xi M A H ω)) := by
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap _ (MeasurableSpace.comap Prod.fst inferInstance ⊔
    (⨆ (i : Fin N) (_ : M.T i ≤ min s S),
      MeasurableSpace.comap (fun p : ℝ × State N A H => p.2.1 i) inferInstance) ⊔
    ⨆ (q : Rat' A H) (_ : (q.1 : ℝ) ≤ min s S),
      MeasurableSpace.comap (fun p : ℝ × State N A H => p.2.2 q) inferInstance) ≤ _
  simp only [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine sup_le (sup_le ?_ (iSup₂_le fun i hi => ?_)) (iSup₂_le fun q hq => ?_)
  · exact (yA_nat hA hAs).comap_le
  · refine Measurable.comap_le (m₁ := natural M S s) ?_
    show Measurable[natural M S s] fun ω => if A < M.T i then M.Z i ω else 0
    by_cases h : A < M.T i
    · simp only [h, ite_true]; exact Z_nat hi
    · simp only [h, ite_false]; exact measurable_const
  · refine Measurable.comap_le (m₁ := natural M S s) ?_
    show Measurable[natural M S s] fun ω => M.Y q.1 ω - M.Y A ω
    exact (Y_nat (hA.trans q.2.1.le) hq).sub (Y_nat hA hAs)

omit [IsProbabilityMeasure Q] in
lemma modelTimes_meas {A S : ℝ} {τ : NullMeasurableSpace Ω Q → ℝ}
    (hτ : τ ∈ modelTimes M Q A S) : Measurable τ := by
  have h := hτ.2.measurable_of_le (fun ω =>
    show (τ ω : WithTop ℝ) ≤ S from WithTop.coe_le_coe.mpr (hτ.1 ω).2)
  have h' := h.untopA.mono ((modelFilt M Q S).le S) le_rfl
  simpa using h'

theorem lowerS : lowerStatement := by
  intro Ω _ N Q _ M H hG A S hA hAS hSH Φ D hΦ hDm hDi hbd
  set μ₂ := (gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))
  set F : Ω → ℝ × State N A H := fun ω => (yA M A ω, Xi M A H ω)
  have hAH : A ≤ H := hAS.trans hSH
  have hlaw : (QS M Q A).map F = μ₂ := law_pair hG hA hAH
  have hFQS : AEMeasurable F (QS M Q A) := pair_aem_QS hG hA hAH
  have hFQ : AEMeasurable F Q := pair_aem hG hA hAH
  have := QS_prob hG hA hAH
  have hPm := Pay_meas hG A hΦ
  have hP : 0 < P0 M A := Real.exp_pos _
  have hQac : Q ≪ QS M Q A := Q_ac hG hA hAH
  have hmapac : Q.map F ≪ μ₂ := by
    refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    rw [Measure.map_apply_of_aemeasurable hFQ hB]
    rw [← hlaw, Measure.map_apply_of_aemeasurable hFQS hB] at h0
    exact hQac h0
  have hDF : Integrable (fun ω => D (F ω)) (QS M Q A) := by
    have := hDi; rw [← hlaw] at this
    exact (integrable_map_measure hDm.aestronglyMeasurable hFQS).1 this
  -- the values defining `U` are bounded
  have hbdd : BddAbove ((fun τ => ∫ ω, payoff M A H Φ τ ω ∂Q.completion) ''
      modelTimes M Q A S) := by
    refine ⟨P0 M A * ∫ ω, D (F ω) ∂(QS M Q A), ?_⟩
    rintro x ⟨τ, hτ, rfl⟩
    refine (le_of_eq (value_eq hG hA hAS hSH hΦ (modelTimes_meas hτ) hτ.1)).trans ?_
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) hP.le
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hDF (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hbd _ (hτ.1 ω) _)
  -- each post-cutoff stopping rule gives an exercise time with the stated value
  have hρall : ∀ ρ ∈ times μ₂ (postFilt M A H S) A S,
      (fun ω : NullMeasurableSpace Ω Q => ρ (yA M A ω, Xi M A H ω)) ∈ modelTimes M Q A S ∧
      ∫ ω, payoff M A H Φ (fun ω => ρ (yA M A ω, Xi M A H ω)) ω ∂Q.completion =
        P0 M A * ∫ p, Pay M A H Φ (ρ p, p) ∂μ₂.completion := by
    intro ρ hρ
    have hρm := times_meas hρ
    have hτm : Measurable fun ω : NullMeasurableSpace Ω Q => ρ (F ω) := comp_null hFQ hmapac hρm
    refine ⟨⟨fun ω => hρ.1 _, fun t => ?_⟩, ?_⟩
    · refine (modelFilt_iff hG hSH t _).2 fun s hs => ?_
      by_cases htA : A ≤ t
      · have hAs : A ≤ min s S := le_min (htA.trans hs.le) hAS
        obtain ⟨C, hC, hCe⟩ := (aug_iff (E := ℝ × State N A H) (μ := μ₂)
          (F := postFilt M A H S)).1 (hρ.2 t) s hs
        refine ⟨F ⁻¹' C, pair_natural hA hAs hC, ?_⟩
        have hCe' : ∀ᵐ p ∂((QS M Q A).map F),
            (p ∈ {p | ((ρ p : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}) = (p ∈ C) := by
          rw [hlaw]; exact hCe
        have h2 : ∀ᵐ ω ∂(QS M Q A),
            (F ω ∈ {p | ((ρ p : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}) = (F ω ∈ C) :=
          ae_of_ae_map (p := fun p => (p ∈ {p | ((ρ p : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}) =
            (p ∈ C)) hFQS hCe'
        have h3 : ∀ᵐ ω ∂Q, (F ω ∈ {p | ((ρ p : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}) = (F ω ∈ C) :=
          hQac.ae_le h2
        filter_upwards [h3] with ω hω
        exact hω
      · refine ⟨∅, @MeasurableSet.empty _ (natural M S s), ?_⟩
        exact Eventually.of_forall fun ω => propext ⟨fun h => absurd (WithTop.coe_le_coe.1 h)
          (not_le.2 ((not_le.1 htA).trans_le (hρ.1 _).1)), False.elim⟩
    · refine (value_eq hG hA hAS hSH hΦ hτm (fun ω => hρ.1 _)).trans ?_
      congr 1
      have hG2 : AEStronglyMeasurable (fun p : ℝ × State N A H => Pay M A H Φ (ρ p, p)) μ₂ :=
        aesm_of_completion (f := fun p => Pay M A H Φ (ρ p, p)) (hPm.comp (hρm.prodMk (id_meas μ₂)))
      refine Eq.trans ?_ (integral_completion hG2).symm
      have hG2' : AEStronglyMeasurable (fun p : ℝ × State N A H => Pay M A H Φ (ρ p, p))
          ((QS M Q A).map F) := by
        rw [hlaw]; exact hG2
      have := integral_map hFQS hG2'
      rw [hlaw] at this
      exact this.symm
  refine ⟨hbdd, hρall, ?_⟩
  rw [mul_comm, ← le_div_iff₀ hP]
  refine csSup_le ⟨_, ⟨fun _ => S, const_mem _ _ hAS, rfl⟩⟩ fun x ⟨ρ, hρ, hx⟩ => ?_
  rw [← hx, le_div_iff₀ hP, mul_comm, ← (hρall ρ hρ).2]
  exact le_csSup hbdd ⟨_, (hρall ρ hρ).1, rfl⟩

end Lower

theorem continuousAggregationAmericanLower : Standalone.ContinuousAggregationAmericanLower.statement :=
  ⟨lamJoint, modelFiltS, lowerS⟩

end Novel.ContinuousAggregationAmericanLowerProof

import Standalone.ContinuousAggregationAmerican
import Novel.ContinuousAggregationRegressionProof

/-! # Claim 054 (e): the American value (54.6) (proof)

* `ResSp M A H` is `Ω` with the residual σ-algebra `σ(r)`, the space `E₁` of (54-S), and
  `Gam = (id, (y_A, Ξ)) : Ω → E₁ × (ℝ × E)`. By the rectangle formula of (54-R), `Gam` carries `Q^A`
  onto `Q^A|σ(r) ⊗ (N(0, V_A) ⊗ λ_post)` (`map_Gam`).
* `exists_C'`: for an exercise time `τ` and a rational `q`, `{τ ≤ q}` is `Q`-a.e. `Gam⁻¹(C_q)` with
  `C_q` in `σ(r) ⊗ σ(y, ξ_{≤s})` for every `s > q`. The filtration identity (54.7) (`filt`) gives
  such a set at each `s = q + 1/(n+1)`, and the lim sup over `n` works at every `s > q`.
* `val_upper`: the raw time `τ̂` of the `C_q` is a stopping time of the product's augmentation
  (`rawTime_times`), and `τ̂ ∘ Gam = τ` almost surely. So the value of `τ` is `P(0, A)` times the
  product integral of `e^{−Λ} Φ(τ̂, ·)`, which is at most `P(0, A) · value₂` by (54-S)'s `val_le`.
* `americanS`: this and the lower bound `lowerS`.

Reused, not reproved: `Novel.ContinuousAggregationRegressionProof` (`regressionS`, `filt`,
`resAlg_le`, `ycomb_meas`), `Novel.ContinuousAggregationSectioningProof` (`rawTime`,
`rawTime_mem`, `rawTime_meas`, `rawTime_eq`, `aug_iff`, `valProd_eq`, `val_le`),
`Novel.ContinuousAggregationAmericanLowerProof` (`value_eq`, `modelFilt_iff`, `modelTimes_meas`,
`Pay_meas`, `lowerS`), and the earlier stages of Claim 054.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.ContinuousAggregationAmericanProof
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw)
open Standalone.DiffusionMeetingPricing (QS Qacc P0)
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationEuropean (State Xi)
open Standalone.ContinuousAggregationSectioning (aug prodFilt times value₂)
open Standalone.ContinuousAggregationAmericanLower (natural modelFilt modelTimes payoff Uval
  postFilt Pay)
open Standalone.ContinuousAggregationRegression (resAlg ycomb)
open Standalone.ContinuousAggregationAmerican (americanStatement)
open Novel.ContinuousAggregationSectioningProof (rawTime rawTime_mem rawTime_meas rawTime_eq
  aug_iff valProd_eq val_le)
open Novel.ContinuousAggregationAmericanLowerProof (value_eq modelFilt_iff modelTimes_meas
  Pay_meas lowerS)
open Novel.ContinuousAggregationRegressionProof (regressionS filt regAlg resAlg_le ycomb_meas)
open Novel.ContinuousAggregationLevelProof (c0 yA_ae)
open Novel.ContinuousAggregationEuropeanProof (Xi' Xi'_meas Xi_ae Xi_aem QS_prob)

/-- The raw time of a family measurable for the product filtration is one of its stopping times. -/
lemma rawTime_times {E₁ E₂ : Type*} [MeasurableSpace E₁] [m₂ : MeasurableSpace E₂]
    {μ : Measure (E₁ × E₂)} {G : Filtration ℝ m₂} {A S : ℝ} (hAS : A ≤ S)
    (C : ℚ → Set (E₁ × E₂)) (hC : ∀ q : ℚ, ∀ s, (q : ℝ) < s → MeasurableSet[prodFilt G s] (C q)) :
    (fun e : NullMeasurableSpace (E₁ × E₂) μ => rawTime A S C (e : E₁ × E₂)) ∈
      times μ (prodFilt G) A S :=
  ⟨fun _ => rawTime_mem hAS C _, fun t => (aug_iff (E := E₁ × E₂) (μ := μ)
    (F := prodFilt G)).2 fun s hs => ⟨{e | rawTime A S C e ≤ t},
      rawTime_meas hAS (fun s => prodFilt G s) C hC t s hs,
      Eventually.of_forall fun _ => propext WithTop.coe_le_coe⟩⟩

/-- `Ω` with the residual σ-algebra `σ(r)`. -/
def ResSp {Ω : Type} {N : ℕ} (_M : DiffModel Ω N) (_A _H : ℝ) : Type := Ω

noncomputable instance {Ω : Type} {N : ℕ} (M : DiffModel Ω N) (A H : ℝ) :
    MeasurableSpace (ResSp M A H) :=
  resAlg M A H

/-- `Γ = (id, (y_A, Ξ))`. -/
noncomputable def Gam {Ω : Type} {N : ℕ} (M : DiffModel Ω N) (A H : ℝ) (ω : Ω) :
    ResSp M A H × (ℝ × State N A H) :=
  (ω, (yA M A ω, Xi M A H ω))

/-- `Q^A` restricted to `σ(r)`, on the residual space. -/
noncomputable def mu1 {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} (M : DiffModel Ω N)
    (Q : Measure Ω) (A H : ℝ) (hle : resAlg M A H ≤ m₀) : Measure (ResSp M A H) :=
  @Measure.trim Ω (resAlg M A H) m₀ (QS M Q A) hle

section Upper
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {M : DiffModel Ω N} {H A S : ℝ}

lemma mu1_prob (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAH : A ≤ H) :
    IsProbabilityMeasure (mu1 M Q A H (resAlg_le hG hAH)) := by
  have := QS_prob hG hA hAH
  exact ⟨(trim_measurableSet_eq (resAlg_le hG hAH) MeasurableSet.univ).trans measure_univ⟩

omit m₀ [IsProbabilityMeasure Q] in
/-- `σ(r) ∨ (y_A, Ξ)⁻¹ σ(y, ξ_{≤s})` is `Γ⁻¹(σ(r) ⊗ σ(y, ξ_{≤s}))`. -/
lemma regAlg_eq (s : ℝ) :
    regAlg M A H S s = MeasurableSpace.comap (Gam M A H) (prodFilt (postFilt M A H S) s) := by
  show _ = MeasurableSpace.comap _ (MeasurableSpace.comap Prod.fst _ ⊔
    MeasurableSpace.comap Prod.snd _)
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  exact congrArg₂ (· ⊔ ·) MeasurableSpace.comap_id.symm rfl

omit [IsProbabilityMeasure Q] in
/-- The rational-time events of an exercise time, as `Γ`-preimages. -/
lemma exists_C' (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAS : A ≤ S) (hSH : S ≤ H)
    {τ : NullMeasurableSpace Ω Q → ℝ} (hτ : τ ∈ modelTimes M Q A S) (q : ℚ) :
    ∃ C : Set (ResSp M A H × (ℝ × State N A H)),
      (∀ s, (q : ℝ) < s → MeasurableSet[prodFilt (postFilt M A H S) s] C) ∧
      ∀ᵐ ω ∂Q, (Gam M A H ω ∈ C ↔ τ ω ≤ q) := by
  by_cases hqA : (q : ℝ) < A
  · refine ⟨∅, fun s _ => @MeasurableSet.empty _ (prodFilt (postFilt M A H S) s),
      Eventually.of_forall fun ω => ?_⟩
    simp only [mem_empty_iff_false, false_iff, not_le]
    exact hqA.trans_le (hτ.1 ω).1
  push Not at hqA
  have h := (modelFilt_iff hG hSH q _).1 (hτ.2 (q : ℝ))
  have hpos : ∀ n : ℕ, (q : ℝ) < q + 1 / ((n : ℝ) + 1) := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have key : ∀ n : ℕ, ∃ B, MeasurableSet[prodFilt (postFilt M A H S) (q + 1 / ((n : ℝ) + 1))] B ∧
      {ω : Ω | ((τ ω : ℝ) : WithTop ℝ) ≤ ((q : ℝ) : WithTop ℝ)} =ᵐ[Q] Gam M A H ⁻¹' B := by
    intro n
    obtain ⟨C, hC, hCe⟩ := h _ (hpos n)
    have hAs : A ≤ min (q + 1 / ((n : ℝ) + 1)) S := le_min (hqA.trans (hpos n).le) hAS
    have hC' : MeasurableSet[eventuallyMeasurableSpace (regAlg M A H S (q + 1 / ((n : ℝ) + 1)))
        (ae Q)] C := by
      rw [← filt hG hA hSH hAs]
      exact le_eventuallyMeasurableSpace _ hC
    obtain ⟨D', hD', hCD'⟩ := hC'
    rw [regAlg_eq] at hD'
    obtain ⟨B, hB, rfl⟩ := hD'
    exact ⟨B, hB, hCe.trans hCD'⟩
  choose B hB hBe using key
  refine ⟨⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n, fun s hs => ?_, ?_⟩
  · obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (sub_pos.2 hs)
    have e : (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n) =
        ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : max N N₀ ≤ n), B n := by
      ext e
      simp only [mem_iInter, mem_iUnion, exists_prop]
      constructor
      · intro h N; exact h (max N N₀)
      · intro h N
        obtain ⟨n, hn, he⟩ := h N
        exact ⟨n, (le_max_left _ _).trans hn, he⟩
    rw [e]
    refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun hn => (prodFilt (postFilt M A H S)).mono ?_ _ (hB n)
    have hn' : N₀ ≤ n := (le_max_right _ _).trans hn
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn' 1)
    linarith
  · filter_upwards [ae_all_iff.2 hBe] with ω hω
    have he' : ∀ n, Gam M A H ω ∈ B n ↔ τ ω ≤ q := fun n =>
      (Iff.of_eq (hω n).symm).trans WithTop.coe_le_coe
    simp only [mem_iInter, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, -, hn⟩ := h 0
      exact (he' n).1 hn
    · intro h N
      exact ⟨N, le_rfl, (he' N).2 h⟩

/-- `Γ` carries `Q^A` onto `Q^A|σ(r) ⊗ (N(0, V_A) ⊗ λ_post)`. -/
lemma map_Gam (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAS : A ≤ S) (hSH : S ≤ H) :
    AEMeasurable (Gam M A H) (QS M Q A) ∧
    (QS M Q A).map (Gam M A H) =
      (mu1 M Q A H (resAlg_le hG (hAS.trans hSH))).prod
        ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))) := by
  have hAH : A ≤ H := hAS.trans hSH
  have := QS_prob hG hA hAH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  have := mu1_prob hG hA hAH
  have hid : @Measurable Ω (ResSp M A H) m₀ _ fun ω => ω := fun s hs => resAlg_le hG hAH s hs
  have hF'm : Measurable fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω) :=
    (measurable_const.add (ycomb_meas hG hAH)).prodMk
      ((Xi'_meas hG hA).mono (Novel.ContinuousAggregationLevelProof.futureAlg_le hG A) le_rfl)
  have hFF' : (fun ω => (yA M A ω, Xi M A H ω)) =ᵐ[Q]
      fun ω => (c0 M A + ycomb M A ω, Xi' M A H ω) :=
    (yA_ae hG hA hAH).prodMk (Xi_ae hG hA)
  have hGam : AEMeasurable (Gam M A H) (QS M Q A) := by
    refine (hid.prodMk hF'm).aemeasurable.congr (hac.ae_le ?_)
    filter_upwards [hFF'] with ω h
    exact (congrArg (Prod.mk ω) h).symm
  refine ⟨hGam, (Measure.prod_eq fun s t hs ht => ?_).symm⟩
  rw [Measure.map_apply_of_aemeasurable hGam (MeasurableSet.prod hs ht)]
  have e : Gam M A H ⁻¹' (s ×ˢ t) = s ∩ (fun ω => (yA M A ω, Xi M A H ω)) ⁻¹' t := rfl
  rw [e]
  exact ((regressionS Ω N Q M H hG A S hA hAS hSH).2.1 s t hs ht).trans
    (congrArg (· * _) (trim_measurableSet_eq (resAlg_le hG hAH) hs).symm)

/-- ≤: the value of an exercise time is at most `P(0, A) · value₂`. -/
lemma val_upper (hG : GaussLaw M Q H) (hA : 0 ≤ A) (hAS : A ≤ S) (hSH : S ≤ H)
    {Φ : ℝ × (ℝ × State N A H) → ℝ} {D : ℝ × State N A H → ℝ} (hΦ : Measurable Φ)
    (hDi : Integrable D ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))))
    (hbd : ∀ t ∈ Icc A S, ∀ p, |Pay M A H Φ (t, p)| ≤ D p)
    {τ : NullMeasurableSpace Ω Q → ℝ} (hτ : τ ∈ modelTimes M Q A S) :
    ∫ ω, payoff M A H Φ τ ω ∂Q.completion ≤
      P0 M A * value₂ ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H)))
        (postFilt M A H S) A S (Pay M A H Φ) := by
  have hAH : A ≤ H := hAS.trans hSH
  have := QS_prob hG hA hAH
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  set μ₁ := mu1 M Q A H (resAlg_le hG hAH)
  set μ₂ := (gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))
  have : IsProbabilityMeasure μ₁ := mu1_prob hG hA hAH
  obtain ⟨hGam, hmap⟩ := map_Gam hG hA hAS hSH
  have hPm := Pay_meas hG A hΦ
  choose C hCm hCe using exists_C' hG hA hAS hSH hτ
  have hmem := rawTime_times (μ := μ₁.prod μ₂) hAS C hCm
  have hτm : Measurable (rawTime A S C) := measurable_of_Iic fun x =>
    (prodFilt (postFilt M A H S)).le (x + 1) _
      (rawTime_meas hAS (fun s => prodFilt (postFilt M A H S) s) C hCm x (x + 1) (by linarith))
  have hae : ∀ᵐ ω ∂Q, rawTime A S C (Gam M A H ω) = τ ω := by
    filter_upwards [ae_all_iff.2 hCe] with ω h
    exact rawTime_eq hAS C _ (τ ω) (hτ.1 ω) fun q _ => h q
  have hGm : Measurable fun e : ResSp M A H × (ℝ × State N A H) => Pay M A H Φ (rawTime A S C e, e.2) :=
    hPm.comp (hτm.prodMk measurable_snd)
  have h1 : ∫ ω, Pay M A H Φ (τ ω, (yA M A ω, Xi M A H ω)) ∂(QS M Q A) =
      ∫ e, Pay M A H Φ (rawTime A S C e, e.2) ∂(μ₁.prod μ₂).completion := by
    rw [valProd_eq hPm hmem, ← hmap, integral_map hGam hGm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le hae] with ω h
    rw [h]
    rfl
  rw [value_eq hG hA hAS hSH hΦ (modelTimes_meas hτ) hτ.1, h1]
  exact mul_le_mul_of_nonneg_left (val_le hPm hDi hbd hAS hmem) (Real.exp_pos _).le

end Upper

theorem americanS : americanStatement := by
  intro Ω _ N Q _ M H hG A S hA hAS hSH Φ D hΦ hDm hDi hbd
  obtain ⟨-, -, hlow⟩ := lowerS Ω N Q M H hG A S hA hAS hSH Φ D hΦ hDm hDi hbd
  refine le_antisymm (csSup_le ⟨_, ⟨fun _ => S, ⟨fun _ => ⟨hAS, le_rfl⟩,
    isStoppingTime_const _ _⟩, rfl⟩⟩ ?_) hlow
  rintro x ⟨τ, hτ, rfl⟩
  exact val_upper hG hA hAS hSH hΦ hDi hbd hτ

theorem continuousAggregationAmerican : Standalone.ContinuousAggregationAmerican.statement := americanS

end Novel.ContinuousAggregationAmericanProof

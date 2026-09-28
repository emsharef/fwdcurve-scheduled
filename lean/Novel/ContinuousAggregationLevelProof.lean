import Standalone.ContinuousAggregationLevel
import Novel.ContinuousAggregationCurveProof
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalProbability

/-! # Claim 054 (a): the level under the discount density (proof)

Two general facts come first. `indep_of_dual` is Cramér–Wold for independence: a random vector in a
finite-dimensional space is independent of a σ-algebra when each continuous linear functional of it
is (the laws under `Q[|C]` and `Q` then have the same characteristic function). `indep_withDensity`:
independence of `m₁` and `m` survives a change of measure by an `m`-measurable density, and the
new measure agrees with the old on `m₁`.

In the model, `future_lin` shows that the future driving increments are closed under finite linear
combinations (almost surely), so every functional of a finite vector of them is one of them, which
`GaussLaw` makes independent of `F_A`. The directed union over finite subfamilies gives
`futureAlg_indep`. `Q^A` is Claim 046's tilt by `−L`, `L = Σ w(0, A, T_i) Z_i + I(w_{0,A})`, whose
density is `F_A`-measurable. Under that tilt `y_A = c₀ + Σ_{T_i ≤ A} Z_i + I(1_{[0,A]})` has mean
`c₀ − Cov(L, ·) = 0` and variance `V_A` (`tilt`).

Reused, not reproved: from `Novel.DiffusionMeetingGaussProof`, `comb`, `comb_meas`, `var`, `Wf`,
`Wf_integrand`, `exp_comb`; from `Novel.DiffusionMeetingPricingProof`, `comb_add`,
`integrand_add`, `tilt`, `QS_eq`, `cov`, `prod_ii`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.ContinuousAggregationLevelProof

/-! ### Two general facts -/

section General
variable {Ω : Type*}

/-- Independence is preserved when a function is replaced by an almost-everywhere equal one. -/
lemma indep_comap_congr {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {Q : Measure Ω}
    {Y Y' : Ω → ℝ} (hae : Y =ᵐ[Q] Y')
    (h : Indep (MeasurableSpace.comap Y' inferInstance) m Q) :
    Indep (MeasurableSpace.comap Y inferInstance) m Q := by
  rw [Indep_iff] at h ⊢
  rintro _ C ⟨B, hB, rfl⟩ hC
  have hs : (Y ⁻¹' B : Set Ω) =ᵐ[Q] (Y' ⁻¹' B : Set Ω) := by
    filter_upwards [hae] with ω hω
    simp only [mem_preimage, hω]
  rw [measure_congr (hs.inter (Filter.EventuallyEq.refl _ C)), measure_congr hs]
  exact h _ C ⟨B, hB, rfl⟩ hC

/-- Cramér–Wold for independence. -/
lemma indep_of_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {m : MeasurableSpace Ω}
    [m0 : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Ω → E} (hX : Measurable X) (hm : m ≤ m0)
    (h : ∀ L : StrongDual ℝ E,
      Indep (MeasurableSpace.comap (fun ω => L (X ω)) inferInstance) m Q) :
    Indep (MeasurableSpace.comap X inferInstance) m Q := by
  rw [Indep_iff]
  rintro _ C ⟨B, hB, rfl⟩ hC
  have hCm : MeasurableSet C := hm C hC
  by_cases hQC : Q C = 0
  · rw [measure_mono_null inter_subset_right hQC, hQC, mul_zero]
  have hν : IsProbabilityMeasure (Q[|C]) := cond_isProbabilityMeasure hQC
  have hQCt : Q C ≠ ∞ := measure_ne_top _ _
  have hL : ∀ L : StrongDual ℝ E,
      (Q[|C]).map (fun ω => L (X ω)) = Q.map (fun ω => L (X ω)) := by
    intro L
    have hLm : Measurable fun ω => L (X ω) := L.continuous.measurable.comp hX
    ext B' hB'
    have hi := (Indep_iff _ _ _).1 (h L) _ C ⟨B', hB', rfl⟩ hC
    rw [Measure.map_apply hLm hB', Measure.map_apply hLm hB', cond_apply hCm, inter_comm, hi,
      mul_comm (Q _) (Q C), ← mul_assoc, ENNReal.inv_mul_cancel hQC hQCt, one_mul]
  have hmap : (Q[|C]).map X = Q.map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
      Measure.map_map L.continuous.measurable hX, Measure.map_map L.continuous.measurable hX]
    exact congrArg (fun μ => charFun μ 1) (hL L)
  have e := congrArg (fun μ => μ B) hmap
  simp only [Measure.map_apply hX hB, cond_apply hCm] at e
  rw [inter_comm]
  calc Q (C ∩ X ⁻¹' B) = Q C * ((Q C)⁻¹ * Q (C ∩ X ⁻¹' B)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hQC hQCt, one_mul]
    _ = _ := by rw [e, mul_comm]

/-- Independence survives a change of measure by a density measurable for one side, and the new
measure agrees with the old on the other side. -/
lemma indep_withDensity {m1 m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hm1 : m1 ≤ m0) (hm : m ≤ m0)
    {ρ : Ω → ℝ≥0∞} (hρ : Measurable[m] ρ) (h1 : ∫⁻ ω, ρ ω ∂Q = 1) (hind : Indep m1 m Q) :
    Indep m1 m (Q.withDensity ρ) ∧ ∀ s, MeasurableSet[m1] s → Q.withDensity ρ s = Q s := by
  have key : ∀ s t, MeasurableSet[m1] s → MeasurableSet[m] t →
      Q.withDensity ρ (s ∩ t) = Q s * Q.withDensity ρ t := fun s t hs ht => by
    rw [withDensity_apply _ ((hm1 s hs).inter (hm t ht)), withDensity_apply _ (hm t ht),
      ← lintegral_indicator ((hm1 s hs).inter (hm t ht)), ← lintegral_indicator (hm t ht)]
    have e : (s ∩ t).indicator ρ = fun ω => s.indicator 1 ω * t.indicator ρ ω := by
      funext ω
      by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ t <;> simp [indicator, h1, h2]
    rw [lintegral_congr fun ω => congrFun e ω,
      lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hm1 hm hind
      (Measurable.indicator (f := (1 : Ω → ℝ≥0∞)) measurable_const hs) (hρ.indicator ht), lintegral_indicator_one (hm1 s hs)]
  have huniv : ∀ s, MeasurableSet[m1] s → Q.withDensity ρ s = Q s := fun s hs => by
    have := key s univ hs MeasurableSet.univ
    rwa [inter_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1,
      mul_one] at this
  refine ⟨(Indep_iff _ _ _).2 fun s t hs ht => ?_, huniv⟩
  rw [key s t hs ht, huniv s hs]

end General

/-! ### The model -/

open Standalone.CompoundedFuturesIdentification (w)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw Integrand rate)
open Standalone.DiffusionMeetingPricing (QS Qacc)
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationLevel
open Novel.DiffusionMeetingGaussProof (comb comb_meas var Wf Wf_integrand exp_comb)
open Novel.DiffusionMeetingPricingProof (comb_add integrand_add tilt QS_eq cov prod_ii)

section Model
variable {Ω : Type} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

omit m₀ in
lemma inc_eq (β : Fin N → ℝ) (f : ℝ → ℝ) : inc M β f = comb M β f := rfl

lemma integrand_zero (H : ℝ) : Integrand (fun _ => (0:ℝ)) 0 H :=
  ⟨measurable_const, ⟨0, fun _ => by simp⟩, fun _ h => absurd rfl h⟩

lemma I_zero (hG : GaussLaw M Q H) : M.I (fun _ => 0) =ᵐ[Q] fun _ => 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hlin, -⟩ := id hG
  have h := hlin (fun _ => 0) (fun _ => 0) 1 (integrand_zero H) (integrand_zero H)
  have e : (fun s : ℝ => (fun _ => (0:ℝ)) s + 1 * (fun _ => (0:ℝ)) s) = fun _ => 0 := by
    funext s; ring
  rw [e] at h
  filter_upwards [h] with ω hω
  linarith

/-- Future driving increments are closed under finite linear combinations. -/
lemma future_lin (hG : GaussLaw M Q H) {A : ℝ} {ι : Type*} (s : Finset ι)
    (p : ι → (Fin N → ℝ) × (ℝ → ℝ)) (hp : ∀ i, Future M H A (p i).1 (p i).2) (c : ι → ℝ) :
    ∃ β f, Future M H A β f ∧
      (fun ω => ∑ i ∈ s, c i * inc M (p i).1 (p i).2 ω) =ᵐ[Q] inc M β f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun _ => 0, ⟨fun i h => absurd rfl h, integrand_zero H, fun _ h => absurd rfl h⟩, ?_⟩
    filter_upwards [I_zero hG] with ω hω
    simp [inc, hω]
  | insert a s ha ih =>
    obtain ⟨β, f, ⟨hβ, hf, hfs⟩, hae⟩ := ih
    obtain ⟨hβa, hfa, hfsa⟩ := hp a
    refine ⟨fun i => β i + c a * (p a).1 i, fun t => f t + c a * (p a).2 t, ⟨fun i hi => ?_,
      integrand_add hf hfa (c a), fun t ht => ?_⟩, ?_⟩
    · dsimp only at hi
      by_cases h : β i = 0
      · exact hβa i fun h' => hi (by rw [h, h', mul_zero, zero_add])
      · exact hβ i h
    · dsimp only at ht
      by_cases h : f t = 0
      · exact hfsa t fun h' => ht (by rw [h, h', mul_zero, zero_add])
      · exact hfs t h
    · filter_upwards [hae, comb_add hG β (p a).1 hf hfa (c a)] with ω h1 h2
      have h2' : inc M β f ω + c a * inc M (p a).1 (p a).2 ω =
          inc M (fun i => β i + c a * (p a).1 i) (fun t => f t + c a * (p a).2 t) ω := h2
      rw [Finset.sum_insert ha, h1, ← h2']
      ring

/-- The future driving increments of a finite subfamily, as one vector. -/
noncomputable def vec {A : ℝ} (M : DiffModel Ω N) (H : ℝ)
    (s : Finset {p : (Fin N → ℝ) × (ℝ → ℝ) // Future M H A p.1 p.2}) (ω : Ω) : s → ℝ :=
  fun q => inc M q.1.1.1 q.1.1.2 ω

lemma inc_meas (hG : GaussLaw M Q H) {A : ℝ} {β : Fin N → ℝ} {f : ℝ → ℝ}
    (h : Future M H A β f) : Measurable (inc M β f) :=
  comb_meas hG h.2.1

lemma vec_meas (hG : GaussLaw M Q H) {A : ℝ} (s : Finset _) : Measurable (vec (A := A) M H s) :=
  measurable_pi_iff.2 fun q => inc_meas hG q.1.2

/-- The σ-algebra of all future driving increments is independent of `F_A` under `Q`. -/
theorem futureAlg_indep [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (A : ℝ) : Indep (futureAlg M H A) (M.F A) Q := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -, -, hind⟩ := id hG
  set ι := {p : (Fin N → ℝ) × (ℝ → ℝ) // Future M H A p.1 p.2}
  set m : Finset ι → MeasurableSpace Ω := fun s => MeasurableSpace.comap (vec M H s) inferInstance
  have hindep : ∀ s, Indep (m s) (M.F A) Q := fun s => by
    refine indep_of_dual (vec_meas hG s) (hFle A) fun L => ?_
    obtain ⟨β, f, hF, hae⟩ := future_lin hG (Finset.univ : Finset s) (fun q => q.1.1)
      (fun q => q.1.2) (fun q => L (Pi.single q 1))
    have e : (fun ω => L (vec M H s ω)) =
        fun ω => ∑ q ∈ (Finset.univ : Finset s), L (Pi.single q 1) * inc M q.1.1.1 q.1.1.2 ω := by
      funext ω
      have hL := L.toLinearMap.pi_apply_eq_sum_univ (vec M H s ω)
      simp only [ContinuousLinearMap.coe_coe] at hL
      rw [hL]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [vec, smul_eq_mul]
      rw [mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [e]
    exact indep_comap_congr hae (hind A β f hF.1 hF.2.1 hF.2.2)
  have hle : ∀ s, m s ≤ m₀ := fun s => (vec_meas hG s).comap_le
  have hsub : ∀ s t : Finset ι, s ⊆ t → m s ≤ m t := fun s t hst => by
    have hr : Measurable fun (x : ↥t → ℝ) (q : ↥s) => x ⟨q.1, hst q.2⟩ :=
      measurable_pi_iff.2 fun q => measurable_pi_apply _
    have e : vec M H s = (fun (x : ↥t → ℝ) (q : ↥s) => x ⟨q.1, hst q.2⟩) ∘ vec M H t := rfl
    show MeasurableSpace.comap (vec M H s) _ ≤ MeasurableSpace.comap (vec M H t) _
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  have hdir : Directed (· ≤ ·) m := fun s t =>
    ⟨s ∪ t, hsub s _ Finset.subset_union_left, hsub t _ Finset.subset_union_right⟩
  have hsup := indep_iSup_of_directed_le hindep hle (hFle A) hdir
  refine indep_of_indep_of_le_left hsup (iSup₂_le fun p hp => ?_)
  refine le_iSup_of_le {⟨p, hp⟩} ?_
  have e : inc M p.1 p.2 = (fun x : ↥({⟨p, hp⟩} : Finset ι) → ℝ =>
      x ⟨⟨p, hp⟩, Finset.mem_singleton_self _⟩) ∘ vec M H {⟨p, hp⟩} := rfl
  show MeasurableSpace.comap (inc M p.1 p.2) _ ≤ MeasurableSpace.comap (vec M H {⟨p, hp⟩}) _
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

lemma futureAlg_le (hG : GaussLaw M Q H) (A : ℝ) : futureAlg M H A ≤ m₀ :=
  iSup₂_le fun _ hp => (inc_meas hG hp).comap_le

/-- The exponent `L = Σ w(0, A, T_i) Z_i + I(w_{0,A})` of the density of `Q^A` is
`F_A`-measurable. -/
lemma L_meas (hG : GaussLaw M Q H) {A : ℝ} :
    Measurable[M.F A] (comb M (fun n => w 0 A (M.T n)) (Wf 0 A)) := by
  obtain ⟨hT, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hZF, hIF, -⟩ := id hG
  show Measurable[M.F A] fun ω => ∑ i, w 0 A (M.T i) * M.Z i ω + M.I (Wf 0 A) ω
  refine Measurable.add (Finset.measurable_sum _ fun n _ => ?_)
    (hIF _ A (Wf_integrand (a := 0) le_rfl))
  by_cases h : M.T n ≤ A
  · exact measurable_const.mul (hZF n A h)
  · have hw : w 0 A (M.T n) = 0 := by
      simp only [w, max_eq_right (by linarith [not_le.1 h] : A - M.T n ≤ 0),
        max_eq_right (by linarith [hT n] : (0:ℝ) - M.T n ≤ 0), sub_zero]
    simp only [hw, zero_mul]
    exact measurable_const

/-- `Q^A` is `Q` with an `F_A`-measurable density of integral one. -/
lemma QS_density [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    ∃ ρ : Ω → ℝ≥0∞, Measurable[M.F A] ρ ∧ ∫⁻ ω, ρ ω ∂Q = 1 ∧ QS M Q A = Q.withDensity ρ := by
  set L : Ω → ℝ := fun ω => -1 * comb M (fun n => w 0 A (M.T n)) (Wf 0 A) ω
  have hint : Integrable (fun ω => Real.exp (L ω)) Q :=
    (exp_comb hG (hA.trans hAH) _ (Wf_integrand (a := 0) hAH) (-1)).1
  refine ⟨fun ω => ENNReal.ofReal (Real.exp (L ω) / ∫ x, Real.exp (L x) ∂Q), ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (measurable_const.mul (L_meas hG))).div_const _)
  · have := isProbabilityMeasure_tilted hint
    have h1 := measure_univ (μ := Q.tilted L)
    rwa [Measure.tilted, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  · rw [QS_eq hG hA hAH]
    rfl

/-- The future driving increments under `Q^A`: still independent of `F_A`, with the same law. -/
theorem futureAlg_QS [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    Indep (futureAlg M H A) (M.F A) (QS M Q A) ∧
      ∀ s, MeasurableSet[futureAlg M H A] s → QS M Q A s = Q s := by
  obtain ⟨ρ, hρ, h1, hQS⟩ := QS_density hG hA hAH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -⟩ := id hG
  rw [hQS]
  exact indep_withDensity (futureAlg_le hG A) (hFle A) hρ h1 (futureAlg_indep hG A)

/-- The pre-`A` meeting weights `1{T_i ≤ A}` and the integrand `1_{[0, A]}` of `y_A`. -/
noncomputable def β1 (M : DiffModel Ω N) (A : ℝ) (i : Fin N) : ℝ := if M.T i ≤ A then 1 else 0

/-- The deterministic part `c₀ = Σ_{T_i ≤ A} v_i (A − T_i) + ∫_0^A g(s)(A − s) ds` of `y_A`. -/
noncomputable def c0 (M : DiffModel Ω N) (A : ℝ) : ℝ :=
  ∑ i, (if M.T i ≤ A then M.v i * (A - M.T i) else 0) + ∫ s in (0:ℝ)..A, M.g s * (A - s)

lemma f1_integrand {A H : ℝ} (hAH : A ≤ H) : Integrand ((Icc 0 A).indicator 1) 0 H := by
  refine ⟨measurable_one.indicator measurableSet_Icc, ⟨1, fun s => ?_⟩, fun s hs => ?_⟩
  · by_cases h : s ∈ Icc 0 A <;> simp [indicator, h]
  · by_cases h : s ∈ Icc 0 A
    · exact ⟨h.1, h.2.trans hAH⟩
    · simp [indicator, h] at hs

/-- `y_A = c₀ + Σ_{T_i ≤ A} Z_i + I(1_{[0, A]})` almost surely. -/
lemma yA_ae (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    yA M A =ᵐ[Q] fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hY, -⟩ := id hG
  filter_upwards [hY A hA hAH] with ω hω
  have hs : ∑ i, (if M.T i ≤ A then M.Z i ω + M.v i * (A - M.T i) else 0) =
      ∑ i, β1 M A i * M.Z i ω + ∑ i, (if M.T i ≤ A then M.v i * (A - M.T i) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [β1]
    split_ifs <;> ring
  simp only [yA, rate, comb, c0, hs, hω]
  ring

/-- `Cov(L, y_A − c₀) = c₀` and `Var(y_A) = V_A`. -/
lemma cov_var (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    cov M H (fun n => w 0 A (M.T n)) (Wf 0 A) (β1 M A) ((Icc 0 A).indicator 1) = c0 M A ∧
    var M H (β1 M A) ((Icc 0 A).indicator 1) = Qacc M A := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hf1 := f1_integrand (A := A) hAH
  have hWf := Wf_integrand (a := 0) hAH
  have zero_tail : ∀ φ : ℝ → ℝ, (∀ s, A < s → φ s = 0) → ∫ s in A..H, φ s = 0 := fun φ hφ => by
    rw [intervalIntegral.integral_of_le hAH, setIntegral_congr_fun measurableSet_Ioc
      (g := fun _ => (0:ℝ)) fun s hs => hφ s hs.1]
    simp
  have f1_out : ∀ s, A < s → (Icc 0 A).indicator (1 : ℝ → ℝ) s = 0 := fun s hs => by
    simp [indicator, not_le.2 hs]
  refine ⟨?_, ?_⟩
  · unfold cov c0
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [β1]
      split_ifs with h
      · rw [w, max_eq_left (sub_nonneg.2 h), max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
        ring
      · ring
    · have i1 := prod_ii hσ hB hWf hf1
      rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 A) (i1 A H),
        zero_tail _ fun s hs => by rw [f1_out s hs]; ring, add_zero]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hA] at hs
      simp only [Wf, indicator_of_mem (show s ∈ Icc 0 A from hs), Pi.one_apply,
        max_eq_left (sub_nonneg.2 hs.2), max_eq_right (by linarith [hs.1] : (0:ℝ) - s ≤ 0)]
      ring
  · unfold var Qacc
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [β1]
      split_ifs <;> ring
    · have i1 : ∀ x y, IntervalIntegrable
          (fun s => (Icc 0 A).indicator (1 : ℝ → ℝ) s ^ 2 * M.g s) volume x y := fun x y => by
        simpa only [sq] using prod_ii hσ hB hf1 hf1 x y
      rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 A) (i1 A H),
        zero_tail _ fun s hs => by rw [f1_out s hs]; ring, add_zero]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hA] at hs
      simp [indicator_of_mem (show s ∈ Icc 0 A from hs)]

/-- Under `Q^A`, `y_A ~ N(0, V_A)`. -/
theorem law_yA [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    HasLaw (yA M A) (gaussianReal 0 (Qacc M A).toNNReal) (QS M Q A) := by
  have hf1 := f1_integrand (A := A) hAH
  set X := comb M (β1 M A) ((Icc 0 A).indicator 1)
  have hX : Measurable X := comb_meas hG hf1
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  have hy : yA M A =ᵐ[QS M Q A] fun ω => c0 M A + X ω := hac.ae_le (yA_ae hG hA hAH)
  have hmap : (QS M Q A).map X = gaussianReal (-1 * c0 M A) (Qacc M A).toNNReal := by
    rw [QS_eq hG hA hAH, tilt hG (hA.trans hAH) _ _ (Wf_integrand (a := 0) hAH) hf1
      (by norm_num), (cov_var hG hA hAH).1, (cov_var hG hA hAH).2]
  refine ⟨(measurable_const.add hX).aemeasurable.congr hy.symm, ?_⟩
  rw [Measure.map_congr hy, show (fun ω => c0 M A + X ω) = (fun x => c0 M A + x) ∘ X from rfl,
    ← Measure.map_map (measurable_const_add _) hX, hmap, gaussianReal_map_const_add]
  congr 1
  ring

/-- The representative `c₀ + Σ_{T_i ≤ A} Z_i + I(1_{[0, A]})` of `y_A` is `F_A`-measurable. -/
lemma yA'_meas (hG : GaussLaw M Q H) {A : ℝ} :
    Measurable[M.F A] fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hZF, hIF, -⟩ := id hG
  show Measurable[M.F A] fun ω => c0 M A + (∑ i, β1 M A i * M.Z i ω +
    M.I ((Icc 0 A).indicator 1) ω)
  refine measurable_const.add (Measurable.add (Finset.measurable_sum _ fun n _ => ?_)
    (hIF _ A ?_))
  · by_cases h : M.T n ≤ A
    · exact measurable_const.mul (hZF n A h)
    · simp only [β1, h, ite_false, zero_mul]
      exact measurable_const
  · refine ⟨measurable_one.indicator measurableSet_Icc, ⟨1, fun s => ?_⟩, fun s hs => ?_⟩
    · by_cases h : s ∈ Icc 0 A <;> simp [indicator, h]
    · by_cases h : s ∈ Icc 0 A
      · exact h
      · simp [indicator, h] at hs

/-- Each future driving increment is independent of `y_A` under `Q^A`. -/
theorem indep_yA [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) {β : Fin N → ℝ}
    {f : ℝ → ℝ} (hF : Future M H A β f) : IndepFun (yA M A) (inc M β f) (QS M Q A) := by
  set y' : Ω → ℝ := fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω
  have hy'm : Measurable[M.F A] y' := yA'_meas hG
  have hind := (futureAlg_QS hG hA hAH).1
  have h1 : Indep (MeasurableSpace.comap (inc M β f) inferInstance)
      (MeasurableSpace.comap y' inferInstance) (QS M Q A) :=
    indep_of_indep_of_le_right (indep_of_indep_of_le_left hind
      (by unfold futureAlg; exact le_iSup₂_of_le (β, f) hF le_rfl)) hy'm.comap_le
  have h2 : IndepFun y' (inc M β f) (QS M Q A) := ((IndepFun_iff_Indep _ _ _).2 h1).symm
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  exact h2.congr (Filter.EventuallyEq.symm (hac.ae_le (yA_ae hG hA hAH)))
    (Filter.EventuallyEq.refl _ _)

/-- The σ-algebra of all future driving increments is independent of `y_A` under `Q^A`. -/
theorem futureAlg_indep_yA [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {A : ℝ} (hA : 0 ≤ A)
    (hAH : A ≤ H) :
    Indep (futureAlg M H A) (MeasurableSpace.comap (yA M A) inferInstance) (QS M Q A) := by
  have hac : QS M Q A ≪ Q := withDensity_absolutelyContinuous _ _
  have h : Indep (MeasurableSpace.comap
      (fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω) inferInstance)
      (futureAlg M H A) (QS M Q A) :=
    (indep_of_indep_of_le_right (futureAlg_QS hG hA hAH).1 (yA'_meas hG).comap_le).symm
  have hy : yA M A =ᵐ[QS M Q A]
      fun ω => c0 M A + comb M (β1 M A) ((Icc 0 A).indicator 1) ω :=
    hac.ae_le (yA_ae hG hA hAH)
  exact (indep_comap_congr hy h).symm

end Model

theorem levelS : Standalone.ContinuousAggregationLevel.levelStatement := by
  intro Ω _ N Q _ M H hG A hA hAH
  have := QS_density hG hA hAH
  exact ⟨law_yA hG hA hAH, futureAlg_indep hG A, (futureAlg_QS hG hA hAH).1,
    (futureAlg_QS hG hA hAH).2, futureAlg_indep_yA hG hA hAH, fun β f hF => indep_yA hG hA hAH hF⟩

theorem continuousAggregationLevel : Standalone.ContinuousAggregationLevel.statement := levelS

end Novel.ContinuousAggregationLevelProof

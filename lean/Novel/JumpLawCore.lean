import Novel.MGFUniqueness
import Novel.CondCalculus
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Claim 008, the single-interval core

For one interval of length `L`, with a density `D ≥ 0` (the accumulated tilt `D_k = R_k / Z_k`
of the claim), a level jump `X` and a `G`-measurable slope `y`, the hypothesis (H) of the
claim reduces (Steps 2 and 3, through the trim lemma) to the Laplace identity on `G`-sets

  `∫⁻_A D exp (-τ X) dP = ∫⁻_A exp (½ y τ²) dP`  for `τ ∈ [0, L)` and `A ∈ G`   (`LaplaceOn`).

This file draws the claim's conclusions from it without regular conditional distributions:
everything is done on one `G`-set `A` at a time, under the tilted probability measure
`(P A)⁻¹ · D · 1_A · P` (`tiltOn`).

* (8.4), `ae_nonneg_of_laplaceOn`: `y ≥ 0` a.s. On a set `A = {-M ≤ y ≤ -ε}` of positive
  measure the moment generating function `m` of `X` under `tiltOn P D A` satisfies
  `exp (-M τ²/2) ≤ m (-τ) ≤ exp (-ε τ²/2)`; iterating Claim 001's inequality
  `m (t/2)² ≤ m t` (`Novel.MGF.mgf_half_sq_le`) `k` times gives `m (-τ/2^k)^(2^k) ≤ m (-τ)`,
  hence `ε ≤ M / 2^k` for every `k`, which is false.
-/

open MeasureTheory ProbabilityTheory Set ENNReal

namespace Novel.JumpLawCore

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω}

/-- The Laplace identity on `G`-sets for one interval of length `L`. -/
def LaplaceOn (P : Measure Ω) (G : MeasurableSpace Ω) (D X y : Ω → ℝ) (L : ℝ) : Prop :=
  ∀ τ ∈ Ico (0 : ℝ) L, ∀ A : Set Ω, MeasurableSet[G] A →
    ∫⁻ ω in A, ENNReal.ofReal (D ω * Real.exp (-τ * X ω)) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y ω * τ ^ 2 / 2)) ∂P

/-- The tilted probability measure on the `G`-set `A`: `(P A)⁻¹ · D · 1_A · P`. -/
noncomputable def tiltOn (P : Measure Ω) (D : Ω → ℝ) (A : Set Ω) : Measure Ω :=
  (P A)⁻¹ • (P.restrict A).withDensity (fun ω => ENNReal.ofReal (D ω))

lemma lintegral_tiltOn {D : Ω → ℝ} (hD : Measurable[m₀] D) {f : Ω → ℝ≥0∞}
    (hf : Measurable[m₀] f) (A : Set Ω) :
    ∫⁻ ω, f ω ∂(tiltOn P D A) = (P A)⁻¹ * ∫⁻ ω in A, ENNReal.ofReal (D ω) * f ω ∂P := by
  rw [tiltOn, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hD.ennreal_ofReal hf]
  simp only [smul_eq_mul, Pi.mul_apply]

lemma lintegral_exp_tiltOn {G : MeasurableSpace Ω} {D X y : Ω → ℝ} {L : ℝ}
    (hD : Measurable[m₀] D) (hD0 : ∀ ω, 0 ≤ D ω) (hX : Measurable[m₀] X)
    (h : LaplaceOn P G D X y L) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) L) {A : Set Ω}
    (hA : MeasurableSet[G] A) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂(tiltOn P D A) =
      (P A)⁻¹ * ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y ω * τ ^ 2 / 2)) ∂P := by
  rw [lintegral_tiltOn hD (f := fun ω => ENNReal.ofReal (Real.exp (-τ * X ω))) (by fun_prop) A,
    ← h τ hτ A hA]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_mul (hD0 ω)]

lemma isProbabilityMeasure_tiltOn {G : MeasurableSpace Ω} [IsProbabilityMeasure P]
    {D X y : Ω → ℝ} {L : ℝ} (hL : 0 < L) (h : LaplaceOn P G D X y L) {A : Set Ω}
    (hA : MeasurableSet[G] A) (hPA : P A ≠ 0) : IsProbabilityMeasure (tiltOn P D A) := by
  constructor
  have h0 := h 0 ⟨le_rfl, hL⟩ A hA
  simp only [neg_zero, zero_mul, mul_zero, Real.exp_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, ENNReal.ofReal_one, setLIntegral_one] at h0
  rw [tiltOn, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    h0, smul_eq_mul, ENNReal.inv_mul_cancel hPA (measure_ne_top _ _)]

/-- (8.4): the slope is nonnegative almost surely. -/
theorem ae_nonneg_of_laplaceOn {G : MeasurableSpace Ω} (hG : G ≤ m₀) [IsProbabilityMeasure P]
    {D X y : Ω → ℝ} (hD : Measurable[m₀] D) (hD0 : ∀ ω, 0 ≤ D ω) (hX : Measurable[m₀] X)
    (hy : Measurable[G] y) {L : ℝ} (hL : 0 < L) (h : LaplaceOn P G D X y L) :
    ∀ᵐ ω ∂P, 0 ≤ y ω := by
  rw [ae_iff]
  by_contra hne
  -- the sets `A n = {-(n+1) ≤ y ≤ -1/(n+1)}` cover `{y < 0}`
  set A : ℕ → Set Ω := fun n =>
    y ⁻¹' Ici (-((n : ℝ) + 1)) ∩ y ⁻¹' Iic (-(1 / ((n : ℝ) + 1))) with hAdef
  have hAG : ∀ n, MeasurableSet[G] (A n) := fun n =>
    (hy measurableSet_Ici).inter (hy measurableSet_Iic)
  have hcover : {ω | ¬ 0 ≤ y ω} ⊆ ⋃ n, A n := by
    intro ω hω
    have hω' : y ω < 0 := not_le.1 hω
    have hpos : 0 < -y ω := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max (-y ω) (1 / -y ω))
    refine mem_iUnion.2 ⟨n, ?_, ?_⟩
    · show -((n : ℝ) + 1) ≤ y ω
      linarith [le_max_left (-y ω) (1 / -y ω)]
    · show y ω ≤ -(1 / ((n : ℝ) + 1))
      have h2 : 1 / -y ω < n + 1 := by linarith [le_max_right (-y ω) (1 / -y ω)]
      rw [div_lt_iff₀ hpos] at h2
      have : 1 / ((n : ℝ) + 1) ≤ -y ω := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
  have hex : ∃ n, P (A n) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (measure_mono_null hcover (measure_iUnion_null hall))
  obtain ⟨n, hPA⟩ := hex
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  set M : ℝ := (n : ℝ) + 1 with hM
  have hεpos : 0 < ε := by positivity
  have hMpos : 0 < M := by positivity
  set ρ := tiltOn P D (A n) with hρ
  have : IsProbabilityMeasure ρ := isProbabilityMeasure_tiltOn hL h (hAG n) hPA
  -- bounds on the lower integral of `exp (-τ X)` under `ρ`
  have hbound : ∀ τ ∈ Ico (0 : ℝ) L,
      ENNReal.ofReal (Real.exp (-M * τ ^ 2 / 2)) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂ρ ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂ρ ≤
        ENNReal.ofReal (Real.exp (-ε * τ ^ 2 / 2)) := by
    intro τ hτ
    rw [hρ, lintegral_exp_tiltOn hD hD0 hX h hτ (hAG n)]
    have hconst : ∀ c : ℝ, (P (A n))⁻¹ * ∫⁻ _ in A n, ENNReal.ofReal c ∂P = ENNReal.ofReal c := by
      intro c
      rw [setLIntegral_const, mul_left_comm, ENNReal.inv_mul_cancel hPA (measure_ne_top _ _),
        mul_one]
    constructor
    · rw [← hconst (Real.exp (-M * τ ^ 2 / 2))]
      refine mul_le_mul' le_rfl ?_
      refine lintegral_mono_ae (ae_restrict_of_forall_mem (hG _ (hAG n)) fun ω hω => ?_)
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h1 : -M ≤ y ω := hω.1
      nlinarith [sq_nonneg τ]
    · rw [← hconst (Real.exp (-ε * τ ^ 2 / 2))]
      refine mul_le_mul' le_rfl ?_
      refine lintegral_mono_ae (ae_restrict_of_forall_mem (hG _ (hAG n)) fun ω hω => ?_)
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h2 : y ω ≤ -ε := hω.2
      nlinarith [sq_nonneg τ]
  have hint : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun ω => Real.exp (-τ * X ω)) ρ := by
    intro τ hτ
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul hX)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt (hbound τ hτ).2 ENNReal.ofReal_lt_top
  have hm : ∀ τ ∈ Ico (0 : ℝ) L,
      mgf X ρ (-τ) = (∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂ρ).toReal := fun τ hτ => by
    simp only [mgf]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      (Real.exp_pos _).le) (hint τ hτ).1]
  have hup : ∀ τ ∈ Ico (0 : ℝ) L, mgf X ρ (-τ) ≤ Real.exp (-ε * τ ^ 2 / 2) := fun τ hτ => by
    rw [hm τ hτ]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hbound τ hτ).2
  have hlow : ∀ τ ∈ Ico (0 : ℝ) L, Real.exp (-M * τ ^ 2 / 2) ≤ mgf X ρ (-τ) := fun τ hτ => by
    rw [hm τ hτ]
    exact (ENNReal.ofReal_le_iff_le_toReal
      (lt_of_le_of_lt (hbound τ hτ).2 ENNReal.ofReal_lt_top).ne).1 (hbound τ hτ).1
  -- the dyadic iteration of Claim 001's inequality
  have hdy : ∀ k : ℕ, ∀ τ ∈ Ico (0 : ℝ) L,
      mgf X ρ (-(τ / 2 ^ k)) ^ (2 ^ k) ≤ mgf X ρ (-τ) := by
    intro k
    induction k with
    | zero => intro τ _; simp
    | succ k ih =>
      intro τ hτ
      have hs : τ / 2 ^ k ∈ Ico (0 : ℝ) L := by
        have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        constructor
        · exact div_nonneg hτ.1 (by positivity)
        · calc τ / 2 ^ k ≤ τ := div_le_self hτ.1 h1
            _ < L := hτ.2
      have hhalf := Novel.MGF.mgf_half_sq_le (μ := ρ) (X := X) (t := -(τ / 2 ^ k)) (hint _ hs)
      rw [neg_div] at hhalf
      have heq : τ / 2 ^ (k + 1) = τ / 2 ^ k / 2 := by rw [pow_succ, div_div]
      have hexp : mgf X ρ (-(τ / 2 ^ (k + 1))) ^ (2 ^ (k + 1)) =
          (mgf X ρ (-(τ / 2 ^ k / 2)) ^ 2) ^ (2 ^ k) := by
        rw [heq, pow_succ', pow_mul]
      rw [hexp]
      calc (mgf X ρ (-(τ / 2 ^ k / 2)) ^ 2) ^ 2 ^ k
          ≤ mgf X ρ (-(τ / 2 ^ k)) ^ 2 ^ k := pow_le_pow_left₀ (sq_nonneg _) hhalf _
        _ ≤ mgf X ρ (-τ) := ih τ hτ
  -- contradiction at depth `k` with `M / ε < 2 ^ k`
  obtain ⟨k, hk⟩ := exists_nat_gt (M / ε)
  have hk2 : M / ε < (2 : ℝ) ^ k := by
    calc M / ε < k := hk
      _ ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hτ : L / 2 ∈ Ico (0 : ℝ) L := ⟨by linarith, by linarith⟩
  have hs : L / 2 / 2 ^ k ∈ Ico (0 : ℝ) L := by
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    exact ⟨div_nonneg hτ.1 (by positivity), (div_le_self hτ.1 h1).trans_lt hτ.2⟩
  have hchain : Real.exp (-M * (L / 2 / 2 ^ k) ^ 2 / 2) ^ (2 ^ k) ≤
      Real.exp (-ε * (L / 2) ^ 2 / 2) :=
    calc Real.exp (-M * (L / 2 / 2 ^ k) ^ 2 / 2) ^ (2 ^ k)
        ≤ mgf X ρ (-(L / 2 / 2 ^ k)) ^ (2 ^ k) :=
          pow_le_pow_left₀ (Real.exp_pos _).le (hlow _ hs) _
      _ ≤ mgf X ρ (-(L / 2)) := hdy k _ hτ
      _ ≤ Real.exp (-ε * (L / 2) ^ 2 / 2) := hup _ hτ
  rw [← Real.exp_nat_mul, Real.exp_le_exp] at hchain
  push_cast at hchain
  have hc : (0 : ℝ) < 2 ^ k := by positivity
  have hL2 : 0 < (L / 2) ^ 2 := by positivity
  have hsq : (2 : ℝ) ^ k * (-M * (L / 2 / 2 ^ k) ^ 2 / 2) = -M * (L / 2) ^ 2 / 2 / 2 ^ k := by
    field_simp
  rw [hsq, div_le_iff₀ hc] at hchain
  -- `-M s ≤ -ε s 2^k` with `s = (L/2)^2/2 > 0` gives `ε 2^k ≤ M`
  have hkey : ε * 2 ^ k ≤ M := by nlinarith [hchain, hL2, hc]
  rw [div_lt_iff₀ hεpos] at hk2
  linarith

/-- A set lower integral is the supremum of its truncations to `A ∩ {y ≤ M}`, `M ∈ ℕ`. -/
lemma setLIntegral_eq_iSup_inter_le {A : Set Ω} (hA : MeasurableSet[m₀] A) {y : Ω → ℝ}
    (hy : Measurable[m₀] y) {f : Ω → ℝ≥0∞} (hf : Measurable[m₀] f) :
    ∫⁻ ω in A, f ω ∂P = ⨆ M : ℕ, ∫⁻ ω in A ∩ {ω | y ω ≤ M}, f ω ∂P := by
  have hAM : ∀ M : ℕ, MeasurableSet[m₀] (A ∩ {ω | y ω ≤ M}) := fun M =>
    hA.inter (hy measurableSet_Iic)
  simp_rw [← lintegral_indicator (hAM _), ← lintegral_indicator hA]
  rw [← lintegral_iSup (fun M => hf.indicator (hAM M)) (fun M N hMN ω => ?_)]
  · refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A
    · have hM : ω ∈ A ∩ {ω' | y ω' ≤ ((⌈y ω⌉₊ : ℕ) : ℝ)} :=
        ⟨hω, by show y ω ≤ ((⌈y ω⌉₊ : ℕ) : ℝ); exact Nat.le_ceil _⟩
      refine le_antisymm (le_iSup_of_le ⌈y ω⌉₊ ?_) (iSup_le fun M => ?_)
      · rw [indicator_of_mem hM, indicator_of_mem hω]
      · by_cases hωM : ω ∈ A ∩ {ω | y ω ≤ M}
        · rw [indicator_of_mem hωM, indicator_of_mem hω]
        · rw [indicator_of_notMem hωM]
          exact zero_le
    · have : ∀ M : ℕ, ω ∉ A ∩ {ω | y ω ≤ M} := fun M hωM => hω hωM.1
      simp only [indicator_of_notMem hω, indicator_of_notMem (this _), ciSup_const]
  · by_cases hωM : ω ∈ A ∩ {ω | y ω ≤ M}
    · have h2 : y ω ≤ (M : ℝ) := hωM.2
      have hωN : ω ∈ A ∩ {ω | y ω ≤ N} :=
        ⟨hωM.1, by show y ω ≤ (N : ℝ); exact h2.trans (by exact_mod_cast hMN)⟩
      rw [indicator_of_mem hωM, indicator_of_mem hωN]
    · rw [indicator_of_notMem hωM]
      exact zero_le

/-- The lower integral of `exp (-τ x)` against `N(0, v)`. -/
lemma lintegral_exp_gaussianReal (v : NNReal) (τ : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂(gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp (v * τ ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal (-τ))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (-τ)
  simp only [mgf, id, zero_mul, zero_add] at this
  rw [this]
  congr 1
  ring

/-- (8.5) on one `G`-set `A` on which the slope is bounded: the tilted law of `X` on `A` is the
Gaussian mixture `∫_A N(0, y(ω)) dP(ω)`, set function by set function. -/
theorem law_eq_of_laplaceOn_bounded {G : MeasurableSpace Ω} (hG : G ≤ m₀)
    [IsProbabilityMeasure P] {D X y : Ω → ℝ} (hD : Measurable[m₀] D) (hD0 : ∀ ω, 0 ≤ D ω)
    (hX : Measurable[m₀] X) (hy : Measurable[G] y) (hy0 : ∀ᵐ ω ∂P, 0 ≤ y ω) {L : ℝ}
    (hL : 0 < L) (h : LaplaceOn P G D X y L) {A : Set Ω} (hA : MeasurableSet[G] A) {M : ℝ}
    (hAM : ∀ ω ∈ A, y ω ≤ M) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ ω in A, ENNReal.ofReal (D ω) * (X ⁻¹' B).indicator 1 ω ∂P =
      ∫⁻ ω in A, gaussianReal 0 (y ω).toNNReal B ∂P := by
  let _inst : MeasurableSpace Ω := m₀
  have hy' : Measurable[m₀] y := hy.mono hG le_rfl
  have hκ : Measurable[m₀] (fun ω => gaussianReal 0 (y ω).toNNReal) :=
    (Novel.MGFUniqueness.measurable_gaussianReal 0).comp (measurable_real_toNNReal.comp hy')
  by_cases hPA : P A = 0
  · have hz : P.restrict A = 0 := Measure.restrict_eq_zero.2 hPA
    simp [hz]
  -- the tilted law on `A` and the Gaussian mixture over `A`
  set ρ := tiltOn P D A with hρ
  have : IsProbabilityMeasure ρ := isProbabilityMeasure_tiltOn hL h hA hPA
  set ν : Measure ℝ := (P A)⁻¹ • (P.restrict A).bind (fun ω => gaussianReal 0 (y ω).toNNReal)
    with hν
  have hbind : ∀ {f : ℝ → ℝ≥0∞}, Measurable f →
      ∫⁻ x, f x ∂((P.restrict A).bind (fun ω => gaussianReal 0 (y ω).toNNReal)) =
        ∫⁻ ω in A, ∫⁻ x, f x ∂(gaussianReal 0 (y ω).toNNReal) ∂P := fun hf =>
    Measure.lintegral_bind hκ.aemeasurable hf.aemeasurable
  have : IsProbabilityMeasure ν := by
    constructor
    rw [hν, Measure.smul_apply, Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
    simp only [measure_univ, setLIntegral_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hPA (measure_ne_top _ _)
  -- the two Laplace transforms agree and are finite on `[0, L)`
  have hlap : ∀ τ ∈ Ico (0 : ℝ) L,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂ρ =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂ν := by
    intro τ hτ
    rw [hρ, lintegral_exp_tiltOn hD hD0 hX h hτ hA, hν, lintegral_smul_measure, smul_eq_mul,
      hbind (by fun_prop)]
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae (hy0.mono fun ω hω => ?_))
    show ENNReal.ofReal (Real.exp (y ω * τ ^ 2 / 2)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂(gaussianReal 0 (y ω).toNNReal)
    rw [lintegral_exp_gaussianReal, Real.coe_toNNReal _ hω]
  have hfin : ∀ τ ∈ Ico (0 : ℝ) L, ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂ν < ⊤ := by
    intro τ hτ
    rw [← hlap τ hτ, hρ, lintegral_exp_tiltOn hD hD0 hX h hτ hA]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hPA)) ?_
    calc ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y ω * τ ^ 2 / 2)) ∂P
        ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.exp (M * τ ^ 2 / 2)) ∂P := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem (hG _ hA) fun ω hω => ?_)
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have := hAM ω hω
          nlinarith [sq_nonneg τ]
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hlaw : ρ.map X = ν :=
    Novel.MGFUniqueness.map_eq_of_lintegral_exp_eqOn_Ico hX hL hlap hfin
  -- read off the set `B`
  have h1 : ρ.map X B = (P A)⁻¹ * ∫⁻ ω in A, ENNReal.ofReal (D ω) * (X ⁻¹' B).indicator 1 ω ∂P := by
    rw [Measure.map_apply hX hB, hρ, tiltOn, Measure.smul_apply, withDensity_apply _ (hX hB),
      smul_eq_mul, ← lintegral_indicator (hX hB)]
    congr 1
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ X ⁻¹' B
    · simp [indicator_of_mem hω]
    · simp [indicator_of_notMem hω]
  have h2 : ν B = (P A)⁻¹ * ∫⁻ ω in A, gaussianReal 0 (y ω).toNNReal B ∂P := by
    rw [hν, Measure.smul_apply, Measure.bind_apply hB hκ.aemeasurable, smul_eq_mul]
  have := h1.symm.trans (congrArg (fun m : Measure ℝ => m B) hlaw |>.trans h2)
  exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    (ENNReal.inv_ne_top.2 hPA)).1 this

/-- (8.5) on every `G`-set: the tilted law of `X` on `A` is the Gaussian mixture over `A`,
set function by set function. The slope is truncated to `{y ≤ M}` and the bounded case is
used on each truncation. -/
theorem law_eq_of_laplaceOn {G : MeasurableSpace Ω} (hG : G ≤ m₀) [IsProbabilityMeasure P]
    {D X y : Ω → ℝ} (hD : Measurable[m₀] D) (hD0 : ∀ ω, 0 ≤ D ω) (hX : Measurable[m₀] X)
    (hy : Measurable[G] y) (hy0 : ∀ᵐ ω ∂P, 0 ≤ y ω) {L : ℝ} (hL : 0 < L)
    (h : LaplaceOn P G D X y L) {A : Set Ω} (hA : MeasurableSet[G] A) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ∫⁻ ω in A, ENNReal.ofReal (D ω) * (X ⁻¹' B).indicator 1 ω ∂P =
      ∫⁻ ω in A, gaussianReal 0 (y ω).toNNReal B ∂P := by
  let _inst : MeasurableSpace Ω := m₀
  have hy' : Measurable[m₀] y := hy.mono hG le_rfl
  have hf1 : Measurable[m₀] fun ω => ENNReal.ofReal (D ω) * (X ⁻¹' B).indicator 1 ω :=
    hD.ennreal_ofReal.mul (measurable_one.indicator (hX hB))
  have hf2 : Measurable[m₀] fun ω => gaussianReal 0 (y ω).toNNReal B :=
    (Measure.measurable_coe hB).comp
      ((Novel.MGFUniqueness.measurable_gaussianReal 0).comp (measurable_real_toNNReal.comp hy'))
  rw [setLIntegral_eq_iSup_inter_le (hG _ hA) hy' hf1, setLIntegral_eq_iSup_inter_le (hG _ hA) hy' hf2]
  refine iSup_congr fun M => ?_
  have hAM : MeasurableSet[G] (A ∩ {ω | y ω ≤ (M : ℝ)}) := hA.inter (hy measurableSet_Iic)
  exact law_eq_of_laplaceOn_bounded hG hD hD0 hX hy hy0 hL h hAM (fun ω hω => hω.2) hB

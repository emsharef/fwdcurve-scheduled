import Standalone.JumpShapeExist
import Novel.JumpShapeCondBProof
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB Standalone.JumpShapeExist
namespace Novel.JumpShapeExistProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof Novel.JumpShapeCondProof

variable {ν : Measure ℝ} {L : ℝ≥0∞}

/-- Finiteness at the rationals of `[0, L)` gives finiteness on `[0, L)`. -/
lemma lapFinite_of_rat [IsProbabilityMeasure ν] (hq : ∀ q : ℚ, InI L q → Ml ν q < ∞) : LapFinite ν L := by
  intro τ hτ
  obtain ⟨r, hτr, hrL⟩ := exists_between hτ.1 hτ.2
  obtain ⟨q, hτq, hqr⟩ := exists_rat_btwn hτr
  have hqI : InI L q := inI_of_lt (hτ.1.trans hτq.le) le_rfl
    (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hqr.le) hrL)
  refine ((integrable_const (1:ℝ)).add (integrable_of_Ml (hq q hqI))).mono'
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-τ * x)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  show Real.exp (-τ * x) ≤ 1 + Real.exp (-(q : ℝ) * x)
  rcases le_total 0 x with hx | hx
  · have : Real.exp (-τ * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hτ.1])
    linarith [Real.exp_pos (-(q : ℝ) * x)]
  · have : Real.exp (-τ * x) ≤ Real.exp (-(q : ℝ) * x) := Real.exp_le_exp.2 (by nlinarith)
    linarith

lemma lapSet_eq {Ω : Type*} {G : MeasurableSpace Ω} (κ : @Kernel Ω ℝ G _)
    [@IsMarkovKernel Ω ℝ G _ κ] (L : ℝ≥0∞) :
    LapSet κ L = ⋂ q : ℚ, {ω | InI L q → Ml (κ ω) q < ∞} := by
  ext ω
  simp only [LapSet, mem_ofPred_eq, mem_iInter]
  exact ⟨fun h q hq => by rw [Ml_eq (h q hq)]; exact ENNReal.ofReal_lt_top,
    fun h => lapFinite_of_rat h⟩

lemma lapSet_meas {Ω : Type*} {G : MeasurableSpace Ω} (κ : @Kernel Ω ℝ G _)
    [@IsMarkovKernel Ω ℝ G _ κ] (L : ℝ≥0∞) :
    MeasurableSet[G] (LapSet κ L) := by
  rw [lapSet_eq]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : InI L q
  · simp only [hq, true_imp_iff]
    exact measurableSet_lt (Ml_meas G κ q) measurable_const
  · simp [hq]

/-- `(τ, ω) ↦ Ẽ_τ[X](ω)` is `B ⊗ G`-measurable. -/
lemma tiltMean_meas {Ω : Type*} {G : MeasurableSpace Ω} (κ : @Kernel Ω ℝ G _)
    [hκ : @IsMarkovKernel Ω ℝ G _ κ] :
    @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _
      (fun p => tiltMean (κ p.2) p.1) := by
  let _ : MeasurableSpace Ω := G
  let κ' : Kernel (ℝ × Ω) ℝ := κ.comap Prod.snd measurable_snd
  have : IsMarkovKernel κ' := by infer_instance
  have hN := StronglyMeasurable.integral_kernel_prod_right (κ := κ')
    (f := fun (p : ℝ × Ω) (x : ℝ) => x * Real.exp (-p.1 * x)) (by
      apply Measurable.stronglyMeasurable
      fun_prop)
  have hM := StronglyMeasurable.integral_kernel_prod_right (κ := κ')
    (f := fun (p : ℝ × Ω) (x : ℝ) => Real.exp (-p.1 * x)) (by
      apply Measurable.stronglyMeasurable
      fun_prop)
  exact hN.measurable.div hM.measurable

/-- `K′ = −Ẽ_·[X]` is integrable on `(0, τ]`: it is nondecreasing, and `∫_a^τ K′ = K(τ) − K(a)` with
`K` bounded on `[0, τ]`. -/
lemma locInt [IsProbabilityMeasure ν] (hf : LapFinite ν L) {τ : ℝ} (hτ : InI L τ) :
    IntegrableOn (fun u => -tiltMean ν u) (Ioc 0 τ) := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0; simp
  set g : ℝ → ℝ := fun u => -tiltMean ν u
  have hIo : ∀ u, 0 < u → u ≤ τ → InIo L u := fun u h1 h2 =>
    ⟨h1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h2) hτ.2⟩
  have hK : ∀ u, 0 < u → u ≤ τ → HasDerivAt (Klap ν) (g u) u := fun u h1 h2 =>
    ((deriv_part hf).2 u (hIo u h1 h2)).1
  have hgc : ∀ a, 0 < a → ContinuousOn g (Icc a τ) := fun a ha u hu =>
    ((deriv_part hf).2 u (hIo u (ha.trans_le hu.1) hu.2)).2.neg.continuousAt.continuousWithinAt
  have hmono := (monotone_part hf).1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Klap_continuousOn hf hτ.1 hτ.2)
  set a : ℕ → ℝ := fun n => τ / ((n : ℝ) + 2)
  have ha0 : ∀ n, 0 < a n := fun n => by positivity
  have haτ : ∀ n, a n ≤ τ := fun n => div_le_self hpos.le (by
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith)
  have hfi : ∀ n, IntegrableOn g (Ioc (a n) τ) := fun n =>
    ((hgc (a n) (ha0 n)).integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  have hlim : Tendsto a atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul τ
    simp only [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun n => (ha0 n).le) fun n => ?_
    simp only [a]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < n + 2)]
    have : (0:ℝ) ≤ n := n.cast_nonneg
    field_simp
    nlinarith
  refine integrableOn_Ioc_of_intervalIntegral_norm_bounded
    (I := 2 * |g τ| * τ + |Klap ν τ| + C) hfi hlim tendsto_const_nhds
    (Eventually.of_forall fun n => ?_)
  have hI := (hgc (a n) (ha0 n)).intervalIntegrable_of_Icc (μ := volume) (haτ n)
  rw [← intervalIntegral.integral_of_le (haτ n)]
  have hle : ∀ x ∈ Icc (a n) τ, ‖g x‖ ≤ (g τ - g x) + |g τ| := fun x hx => by
    have hgx : g x ≤ g τ := hmono (hIo x ((ha0 n).trans_le hx.1) hx.2) (hIo τ hpos le_rfl) hx.2
    rw [Real.norm_eq_abs]
    rcases le_or_gt 0 (g x) with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self (g τ)]
    · rw [abs_of_neg h]; linarith [neg_abs_le (g τ)]
  have hint : ∫ x in a n..τ, g x = Klap ν τ - Klap ν (a n) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
      rw [uIcc_of_le (haτ n)] at hx
      exact hK x ((ha0 n).trans_le hx.1) hx.2) hI
  calc ∫ x in a n..τ, ‖g x‖ ≤ ∫ x in a n..τ, ((g τ - g x) + |g τ|) :=
        intervalIntegral.integral_mono_on (haτ n) hI.norm
          ((intervalIntegrable_const.sub hI).add intervalIntegrable_const) hle
    _ = (g τ + |g τ|) * (τ - a n) - (Klap ν τ - Klap ν (a n)) := by
        rw [intervalIntegral.integral_add (intervalIntegrable_const.sub hI) intervalIntegrable_const,
          intervalIntegral.integral_sub intervalIntegrable_const hI, hint,
          intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
        ring
    _ ≤ 2 * |g τ| * τ + |Klap ν τ| + C := by
        have h1 : (g τ + |g τ|) * (τ - a n) ≤ 2 * |g τ| * τ := by
          have := le_abs_self (g τ)
          have := abs_nonneg (g τ)
          nlinarith [ha0 n, haτ n]
        have h2 : Klap ν (a n) ≤ C := by
          have := hC (a n) ⟨(ha0 n).le, haτ n⟩
          rw [Real.norm_eq_abs] at this
          linarith [le_abs_self (Klap ν (a n))]
        linarith [neg_abs_le (Klap ν τ)]

lemma existS : Standalone.JumpShapeExist.existStatement := by
  intro Ω m₀ P G X L κ hP hG hX hκ hR hae
  have hE := lapSet_meas κ L
  have hmeas : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ G) _
      (Function.uncurry (hExist κ L)) := by
    let _ : MeasurableSpace Ω := G
    have hS : MeasurableSet {p : ℝ × Ω | p.2 ∈ LapSet κ L ∧ InIo L p.1} :=
      (measurable_snd hE).inter (measurable_fst isOpen_Io.measurableSet)
    exact Measurable.ite hS (tiltMean_meas κ).neg measurable_const
  have hloc : ∀ ω τ, InI L τ → IntervalIntegrable (fun u => hExist κ L u ω) volume 0 τ := by
    intro ω τ hτ
    by_cases hω : ω ∈ LapSet κ L
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1]
      refine (locInt hω hτ).congr_fun (fun u hu => ?_) measurableSet_Ioc
      have : InIo L u := ⟨hu.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hτ.2⟩
      simp [hExist, hω, this]
    · have : (fun u => hExist κ L u ω) = fun _ => 0 := funext fun u => by simp [hExist, hω]
      rw [this]
      exact intervalIntegrable_const
  refine ⟨hE, ae_iff.1 hae, hmeas, hloc, ?_⟩
  refine Novel.JumpShapeCondBProof.converseCondS Ω m₀ P G X (hExist κ L) L κ
    ⟨hP, hG, hX, hmeas, hloc, hκ, hR⟩ ?_
  filter_upwards [hae] with ω hω
  exact ⟨hω, Eventually.of_forall fun τ hτ => by
    simp [hExist, show ω ∈ LapSet κ L from hω, hτ]⟩

theorem jumpShapeExist : Standalone.JumpShapeExist.statement := existS

end Novel.JumpShapeExistProof

import Standalone.TwoStrikeInitialCurve
import Novel.DiffusionMeetingPricingProof

/-! # Claim 052: two fixed strikes with a known initial curve (proof)

(a) splits `∫_0^b g h` at `S` and compares integrands by (52.2). (b) is Claim 017's `C0177_scale`.
(c)–(e) rewrite each call by Claim 046's pricing (`pricingS`, conditional on `GaussLaw`) as
`P(0, S) K₀ c_{K/K₀}(m/K₀, q)`, and apply Claim 017's Lemma 18 (`C0177_two_strikes`) on
`{m/K₀ ≥ 1}` with strikes `1` and `K₁/K₀ > 1`.

Reused, not reproved: from `Novel.CompoundedFuturesIdentificationProof`, `C0177_two_strikes`,
`C0177_scale`, `C0177_zero`, `h_eq`, `w_nonneg`, `h_sub_j_nonneg`; from
`Novel.DiffusionMeetingPricingProof`, `pricingS`; from `Novel.SpliceCrossTermDriftProof`, `ii_bdd`.
-/

open MeasureTheory ProbabilityTheory Set
open Standalone.TwoStrikeInitialCurve
open Standalone.CompoundedFuturesIdentification (w h j k C0177)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw Aint pdiff)
open Standalone.DiffusionMeetingPricing (G P0 zdiff qdiff mdiff call)
open Novel.CompoundedFuturesIdentificationProof
  (C0177_two_strikes C0177_scale C0177_zero h_eq w_nonneg h_sub_j_nonneg)

namespace Novel.TwoStrikeInitialCurveProof

variable {Ω : Type} {N : ℕ}

/-! ### (a) the mean bound -/

lemma w_cont (a b : ℝ) : Continuous (w a b) :=
  ((continuous_const.sub continuous_id).max continuous_const).sub
    ((continuous_const.sub continuous_id).max continuous_const)

lemma h_cont (a b : ℝ) : Continuous (h a b) := by
  have e : h a b = fun s => w a b s * max (b - s) 0 := funext (h_eq a b)
  rw [e]
  exact (w_cont a b).mul ((continuous_const.sub continuous_id).max continuous_const)

/-- (52.2), the identity. -/
lemma h_sub_wS {a b S s : ℝ} (hs : s ≤ S) (hSb : S ≤ b) :
    h a b s - w a b s * (S - s) = w a b s * (b - S) := by
  rw [h_eq, max_eq_left (by linarith : (0:ℝ) ≤ b - s)]
  ring

/-- (52.2), the sign. -/
lemma h_nonneg {a b : ℝ} (hab : a ≤ b) (s : ℝ) : 0 ≤ h a b s := by
  rw [h_eq]
  exact mul_nonneg (w_nonneg hab) (le_max_right _ _)

lemma z_le_p (M : DiffModel Ω N) {S a b : ℝ} (hv : ∀ i, 0 ≤ M.v i) (hg : Measurable M.g)
    (hB : ∃ C, ∀ s, |M.g s| ≤ C) (hg0 : ∀ s, 0 ≤ M.g s) (hab : a ≤ b) (hS : 0 ≤ S)
    (hSb : S ≤ b) : zdiff M S a b ≤ pdiff M a b := by
  obtain ⟨C, hC⟩ := hB
  have hgi : ∀ x y, IntervalIntegrable M.g volume x y :=
    Novel.SpliceCrossTermDriftProof.ii_bdd hg C hC
  have iH : ∀ x y, IntervalIntegrable (fun s => M.g s * h a b s) volume x y := fun x y =>
    (hgi x y).mul_continuousOn (h_cont a b).continuousOn
  have iW : IntervalIntegrable (fun s => M.g s * (w a b s * (S - s))) volume 0 S :=
    (hgi 0 S).mul_continuousOn ((w_cont a b).mul (continuous_const.sub continuous_id)).continuousOn
  have hsum : ∑ i, j S a b (M.T i) * M.v i ≤ ∑ i, h a b (M.T i) * M.v i :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (sub_nonneg.1 (h_sub_j_nonneg hab hSb)) (hv i)
  have h1 : ∫ s in (0:ℝ)..S, M.g s * (w a b s * (S - s)) ≤ ∫ s in (0:ℝ)..S, M.g s * h a b s :=
    intervalIntegral.integral_mono_on hS iW (iH 0 S) fun s hs => by
      refine mul_le_mul_of_nonneg_left ?_ (hg0 s)
      have e := h_sub_wS (a := a) hs.2 hSb
      have := mul_nonneg (w_nonneg (T := s) hab) (sub_nonneg.2 hSb)
      linarith
  have h2 : 0 ≤ ∫ s in S..b, M.g s * h a b s :=
    intervalIntegral.integral_nonneg hSb fun s _ => mul_nonneg (hg0 s) (h_nonneg hab s)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (iH 0 S) (iH S b)
  unfold zdiff pdiff
  linarith

lemma m_ge (M : DiffModel Ω N) {S a b : ℝ} (hv : ∀ i, 0 ≤ M.v i) (hg : Measurable M.g)
    (hB : ∃ C, ∀ s, |M.g s| ≤ C) (hg0 : ∀ s, 0 ≤ M.g s) (hab : a ≤ b) (hS : 0 ≤ S)
    (hSb : S ≤ b) : Real.exp (Aint M a b) ≤ mdiff M S a b := by
  have := z_le_p M hv hg hB hg0 hab hS hSb
  unfold mdiff
  exact Real.exp_le_exp.2 (by linarith)

theorem meanS : meanStatement := by
  intro Ω N M S a b hv hg hB hg0 hab hS hSb
  exact ⟨fun s hs => h_sub_wS hs hSb, h_nonneg hab, z_le_p M hv hg hB hg0 hab hS hSb,
    m_ge M hv hg hB hg0 hab hS hSb⟩

/-! ### (b) rescaling -/

/-- (52.3). -/
lemma scale {c m : ℝ} (q : NNReal) (K : ℝ) (hc : 0 < c) (hm : 0 < m) :
    C0177 (c * m) q (c * K) = c * C0177 m q K := by
  rw [C0177_scale (mul_pos hc hm), C0177_scale hm, mul_div_mul_left _ _ hc.ne', mul_assoc]

/-- (52.3) with `c = K₀`, in the direction used below. -/
lemma scale' {K₀ m : ℝ} (hK₀ : 0 < K₀) (hm : 0 < m) (q : NNReal) (K : ℝ) :
    C0177 m q K = K₀ * C0177 (m / K₀) q (K / K₀) := by
  have := scale q (K / K₀) hK₀ (div_pos hm hK₀)
  have e1 : K₀ * (m / K₀) = m := by field_simp
  have e2 : K₀ * (K / K₀) = K := by field_simp
  rwa [e1, e2] at this

theorem scaleS : scaleStatement := by
  refine ⟨fun c m q K hc hm => scale q K hc hm, fun P K₀ m q K hP hK₀ hm => ?_,
    fun Ω N M S a b => ?_⟩
  · rw [scale' hK₀ hm q K]
    field_simp
  · unfold mdiff
    rw [← Real.exp_sub]
    congr 1
    ring

/-! ### (c) two strikes -/

lemma qdiff_nonneg (M : DiffModel Ω N) {S a b : ℝ} (hv : ∀ i, 0 ≤ M.v i)
    (hg0 : ∀ s, 0 ≤ M.g s) (hS : 0 ≤ S) : 0 ≤ qdiff M S a b := by
  unfold qdiff
  refine add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg ?_ (hv i))
    (intervalIntegral.integral_nonneg hS fun s _ => mul_nonneg (hg0 s) (sq_nonneg _))
  rw [Standalone.CompoundedFuturesIdentification.k]
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

lemma mdiff_pos (M : DiffModel Ω N) (S a b : ℝ) : 0 < mdiff M S a b := Real.exp_pos _

/-- Claim 046's (46.5), conditional on `GaussLaw`. -/
lemma call_eq [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {M : DiffModel Ω N}
    {H : ℝ} (hG : GaussLaw M Q H) {S a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H)
    (hS : 0 ≤ S) (hSH : S ≤ H) (K : ℝ) :
    call M Q S a b K = P0 M S * C0177 (mdiff M S a b) (qdiff M S a b).toNNReal K :=
  ((Novel.DiffusionMeetingPricingProof.pricingS Ω N Q M H hG a b ha hab hbH).2.2.2.2
    S hS hSH).2.2.2 K

/-- The deterministic core of (c): Lemma 18 after rescaling by `K₀`. -/
lemma two_core {P K₀ K₁ m m' q q' : ℝ} (hP : 0 < P) (hK₀ : 0 < K₀) (hK₁ : K₀ < K₁)
    (hm : K₀ ≤ m) (hm' : K₀ ≤ m') (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    (P * C0177 m q.toNNReal K₀ = P * C0177 m' q'.toNNReal K₀ ∧
      P * C0177 m q.toNNReal K₁ = P * C0177 m' q'.toNNReal K₁) ↔ m = m' ∧ q = q' := by
  have hm0 := hK₀.trans_le hm
  have hm0' := hK₀.trans_le hm'
  have hc : P * K₀ ≠ 0 := (mul_pos hP hK₀).ne'
  rw [scale' hK₀ hm0 _ K₀, scale' hK₀ hm0' _ K₀, scale' hK₀ hm0 _ K₁, scale' hK₀ hm0' _ K₁,
    div_self hK₀.ne']
  simp only [← mul_assoc]
  rw [mul_right_inj' hc, mul_right_inj' hc,
    C0177_two_strikes ((one_le_div hK₀).2 hm) ((one_le_div hK₀).2 hm') ((one_lt_div hK₀).2 hK₁),
    div_left_inj' hK₀.ne', Real.toNNReal_eq_toNNReal_iff hq hq']

theorem twoStrike : twoStrikeStatement := by
  intro Ω Ω' _ _ N N' Q Q' _ _ M M' H hG hG' S a b K₁ ha hab hbH hS hSH hSb hAe hPe hK₁
  obtain ⟨-, hv, hgm, hgb, hg0, -⟩ := id hG
  obtain ⟨-, hv', hgm', hgb', hg0', -⟩ := id hG'
  have hA : Aint M' a b = Aint M a b := hAe.symm
  have hP : P0 M' S = P0 M S := hPe.symm
  have hm := m_ge M hv hgm hgb hg0 hab hS hSb
  have hm' : Real.exp (Aint M a b) ≤ mdiff M' S a b := by
    have := m_ge M' hv' hgm' hgb' hg0' hab hS hSb
    rwa [hA] at this
  refine ⟨?_, fun hq0 => ?_⟩
  · simp only [call_eq hG ha hab hbH hS hSH, call_eq hG' ha hab hbH hS hSH, hP]
    exact two_core (Real.exp_pos _) (Real.exp_pos _) hK₁ hm hm' (qdiff_nonneg M hv hg0 hS)
      (qdiff_nonneg M' hv' hg0' hS)
  · have hK : ∀ K, call M Q S a b K = P0 M S * max (mdiff M S a b - K) 0 := fun K => by
      rw [call_eq hG ha hab hbH hS hSH, hq0, Real.toNNReal_zero, C0177_zero (mdiff_pos M S a b)]
    refine ⟨hK, ?_⟩
    have hP0 : P0 M S ≠ 0 := (Real.exp_pos _).ne'
    rw [hK, max_eq_left (sub_nonneg.2 hm), mul_div_cancel_left₀ _ hP0]
    ring

/-! ### (d) the futures quote -/

theorem futures : futuresStatement := by
  intro Ω Ω' _ _ N N' Q Q' _ _ M M' H hG hG' S a b K₁ ha hab hbH hS hSH hSb hAe hPe hK₁
  have hA : Aint M' a b = Aint M a b := hAe.symm
  have h0 := (Novel.DiffusionMeetingPricingProof.pricingS Ω N Q M H hG a b ha hab hbH).2.2.2.1
  have h0' :=
    (Novel.DiffusionMeetingPricingProof.pricingS Ω' N' Q' M' H hG' a b ha hab hbH).2.2.2.1
  have hc := (twoStrike Ω Ω' N N' Q Q' M M' H hG hG' S a b K₁ ha hab hbH hS hSH hSb hAe hPe hK₁).1
  refine ⟨h0, fun x x' hx hx' => ?_⟩
  have ex : x = Real.exp (Aint M a b + pdiff M a b) := by
    obtain ⟨_, hω⟩ := (hx.symm.trans h0).exists
    exact hω
  have ex' : x' = Real.exp (Aint M a b + pdiff M' a b) := by
    obtain ⟨_, hω⟩ := (hx'.symm.trans h0').exists
    rw [← hA]
    exact hω
  refine ⟨by rw [ex, Real.log_exp]; ring, by rw [ex, Real.log_exp, mdiff, Real.log_exp]; ring,
    ⟨fun ⟨hxx, hcc⟩ => ?_, fun ⟨hp, hz, hq⟩ => ?_⟩⟩
  · have hp : pdiff M a b = pdiff M' a b := by
      rw [ex, ex'] at hxx
      linarith [Real.exp_injective hxx]
    obtain ⟨hmm, hqq⟩ := hc.1 hcc
    refine ⟨hp, ?_, hqq⟩
    unfold mdiff at hmm
    rw [hA] at hmm
    linarith [Real.exp_injective hmm]
  · refine ⟨by rw [ex, ex', hp], hc.2 ⟨?_, hq⟩⟩
    unfold mdiff
    rw [hA, hp, hz]

/-! ### (e) the whole surface -/

theorem surface : surfaceStatement := by
  intro Ω Ω' _ _ N N' Q Q' _ _ M M' H hG hG' S a b K₁ ha hab hbH hS hSH hSb hAe hPe hK₁
  have hP : P0 M' S = P0 M S := hPe.symm
  have hc := (twoStrike Ω Ω' N N' Q Q' M M' H hG hG' S a b K₁ ha hab hbH hS hSH hSb hAe hPe hK₁).1
  refine ⟨fun h2 K _ => ?_, fun hall => ⟨hall _ (Real.exp_pos _), hall _
    ((Real.exp_pos _).trans hK₁)⟩⟩
  obtain ⟨hmm, hqq⟩ := hc.1 h2
  rw [call_eq hG ha hab hbH hS hSH, call_eq hG' ha hab hbH hS hSH, hP, hmm, hqq]

theorem twoStrikeInitialCurve : Standalone.TwoStrikeInitialCurve.statement :=
  ⟨meanS, scaleS, twoStrike, futures, surface⟩

end Novel.TwoStrikeInitialCurveProof

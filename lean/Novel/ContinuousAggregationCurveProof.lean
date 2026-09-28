import Standalone.ContinuousAggregationCurve
import Novel.DiffusionMeetingPricingProof

/-! # Claim 054 (b), (d): the post-cutoff curve and the later futures quotes (proof)

(54.2) splits each pre-`A` meeting term and the drift integral at `A`. (54.4) splits `pdiff` at `A`,
with `h(a, b, T) = δ(b − T)` for `T ≤ a` (from Claim 017's `h_eq`), and reads `G_0` from Claim 046's
`G_zero`.

Reused, not reproved: `Novel.CompoundedFuturesIdentificationProof.h_eq`,
`Novel.DiffusionMeetingPricingProof.G_zero`, `Novel.SpliceCrossTermDriftProof.ii_bdd`.
-/

open MeasureTheory Set
open Standalone.CompoundedFuturesIdentification (h w)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw rate Aint pdiff)
open Standalone.DiffusionMeetingPricing (G Qacc)
open Standalone.DiffusionMeetingConsistency (fwd)
open Standalone.ContinuousAggregationCurve

namespace Novel.ContinuousAggregationCurveProof

variable {Ω : Type*} {N : ℕ}

/-- `h(a, b, T) = δ(b − T)` for `T ≤ a ≤ b`. -/
lemma h_early {a b T : ℝ} (hTa : T ≤ a) (hab : a ≤ b) : h a b T = (b - a) * (b - T) := by
  rw [Novel.CompoundedFuturesIdentificationProof.h_eq, w, max_eq_left (by linarith : 0 ≤ b - T),
    max_eq_left (by linarith : 0 ≤ a - T)]
  ring

section
variable (M : DiffModel Ω N) (hg : Measurable M.g) (hB : ∃ C, ∀ s, |M.g s| ≤ C)
include hg hB

lemma g_ii (x y : ℝ) : IntervalIntegrable M.g volume x y := by
  obtain ⟨C, hC⟩ := hB
  exact Novel.SpliceCrossTermDriftProof.ii_bdd hg C hC x y

lemma gc_ii {φ : ℝ → ℝ} (hφ : Continuous φ) (x y : ℝ) :
    IntervalIntegrable (fun s => M.g s * φ s) volume x y :=
  (g_ii M hg hB x y).mul_continuousOn hφ.continuousOn

theorem curveS_aux (A t U : ℝ) (hAt : A ≤ t) (ω : Ω) :
    fwd M t U ω = M.f0 U + yA M A ω + Qacc M A * (U - A) +
      ∑ i, (if A < M.T i ∧ M.T i ≤ t then M.Z i ω + M.v i * (U - M.T i) else 0) +
      (M.Y t ω - M.Y A ω) + ∫ s in A..t, M.g s * (U - s) := by
  -- the meeting terms
  have hsum : ∑ i, (if M.T i ≤ t then M.Z i ω + M.v i * (U - M.T i) else 0) =
      ∑ i, (if M.T i ≤ A then M.Z i ω + M.v i * (A - M.T i) else 0) +
      (∑ i, (if M.T i ≤ A then M.v i else 0)) * (U - A) +
      ∑ i, (if A < M.T i ∧ M.T i ≤ t then M.Z i ω + M.v i * (U - M.T i) else 0) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : M.T i ≤ A
    · simp only [h1, h1.trans hAt, ite_true, not_lt.2 h1, false_and, ite_false]; ring
    · by_cases h2 : M.T i ≤ t
      · simp only [h1, h2, not_le.1 h1, and_self, ite_true, ite_false]; ring
      · simp only [h1, h2, and_false, ite_false]; ring
  -- the drift integral
  have i1 := gc_ii M hg hB (φ := fun s => U - s) (by fun_prop)
  have i2 := gc_ii M hg hB (φ := fun s => A - s) (by fun_prop)
  have hint : ∫ s in (0:ℝ)..t, M.g s * (U - s) = (∫ s in (0:ℝ)..A, M.g s * (A - s)) +
      (U - A) * (∫ s in (0:ℝ)..A, M.g s) + ∫ s in A..t, M.g s * (U - s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 A) (i1 A t),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (i2 0 A)
        ((g_ii M hg hB 0 A).const_mul _)]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => by ring
  simp only [fwd, yA, rate, Qacc]
  rw [hsum, hint]
  ring

theorem pdiffS_aux (A a b : ℝ) (hA : 0 ≤ A) (hAa : A ≤ a) (hab : a ≤ b) :
    pdiff M a b = (b - a) * (b * Qacc M A - M1 M A) + post M A a b := by
  have hhc : Continuous (h a b) := by
    have e : h a b = fun s => w a b s * max (b - s) 0 :=
      funext (Novel.CompoundedFuturesIdentificationProof.h_eq a b)
    rw [e]; unfold w; fun_prop
  have iH := gc_ii M hg hB hhc
  have hsum : ∑ i, h a b (M.T i) * M.v i =
      (b - a) * (b * ∑ i, (if M.T i ≤ A then M.v i else 0) -
        ∑ i, (if M.T i ≤ A then M.T i * M.v i else 0)) +
      ∑ i, (if A < M.T i then h a b (M.T i) * M.v i else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : M.T i ≤ A
    · simp only [h1, ite_true, not_lt.2 h1, ite_false, h_early (h1.trans hAa) hab]; ring
    · simp only [h1, ite_false, not_le.1 h1, ite_true]; ring
  have i0 := g_ii M hg hB 0 A
  have is : IntervalIntegrable (fun s => s * M.g s) volume 0 A := by
    simpa only [mul_comm, id] using gc_ii M hg hB (φ := id) continuous_id 0 A
  have hint : ∫ s in (0:ℝ)..b, M.g s * h a b s = (b - a) * (b * (∫ s in (0:ℝ)..A, M.g s) -
      ∫ s in (0:ℝ)..A, s * M.g s) + ∫ s in A..b, M.g s * h a b s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (iH 0 A) (iH A b)]
    congr 1
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (i0.const_mul _) is,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hA] at hs
    simp only [h_early (hs.2.trans hAa) hab]
    ring
  simp only [pdiff, Qacc, M1, post]
  rw [hsum, hint]
  ring

end

theorem curveS : curveStatement := fun _ _ M hg hB A t U _ hAt ω =>
  curveS_aux M hg hB A t U hAt ω

theorem pdiffSplitS : pdiffSplitStatement := fun _ _ M hg hB A a b hA hAa hab =>
  pdiffS_aux M hg hB A a b hA hAa hab

theorem futuresS : futuresStatement := by
  intro Ω _ N Q _ M H hG A a b hA hAa hab hbH
  obtain ⟨-, -, hg, hB, -⟩ := id hG
  filter_upwards [Novel.DiffusionMeetingPricingProof.G_zero hG (hA.trans hAa) hab hbH] with ω hω
  rw [hω, pdiffS_aux M hg hB A a b hA hAa hab, add_assoc]

/-- An almost-sure constant value of a function under a probability measure is unique. -/
lemma const_of_ae {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {F : Ω → ℝ} {x y : ℝ} (hx : F =ᵐ[Q] fun _ => x) (hy : F =ᵐ[Q] fun _ => y) : x = y := by
  obtain ⟨_, hω⟩ := (hx.symm.trans hy).exists
  exact hω

theorem futuresPairS : futuresPairStatement := by
  intro Ω Ω' _ _ N Q Q' _ _ M M' H hG hG' A a b hA hAa hab hbH hf hT hv hg hV hM x x' hx hx'
  have e := const_of_ae hx (futuresS Ω N Q M H hG A a b hA hAa hab hbH)
  have e' := const_of_ae hx' (futuresS Ω' N Q' M' H hG' A a b hA hAa hab hbH)
  have hAi : Aint M a b = Aint M' a b := by unfold Aint; rw [hf]
  have hpost : post M A a b = post M' A a b := by
    unfold post
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hT]
      split_ifs with h1
      · rw [hv i h1]
      · rfl
    · refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le (hAa.trans hab)] at hs
      rw [hg s hs.1 (hs.2.trans hbH)]
  rw [e, e', hAi, hV, hM, hpost]

theorem continuousAggregationCurve : Standalone.ContinuousAggregationCurve.statement :=
  ⟨curveS, pdiffSplitS, futuresS, futuresPairS⟩

end Novel.ContinuousAggregationCurveProof

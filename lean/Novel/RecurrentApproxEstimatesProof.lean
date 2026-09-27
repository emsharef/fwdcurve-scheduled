import Standalone.RecurrentApproxEstimates
import Novel.MaturityShapeIdentitiesProof

open MeasureTheory Set
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
open Novel.MaturityShapeIdentitiesProof (meas_param ii_of_bound)
namespace Novel.RecurrentApproxEstimatesProof

lemma count_le (Tm : Finset ℝ) (s T : ℝ) : count030 Tm s T ≤ Tm.card :=
  Finset.card_filter_le _ _

/-- `i(s, u)` is jointly measurable. -/
lemma count_meas (Tm : Finset ℝ) : Measurable fun p : ℝ × ℝ => count030 Tm p.1 p.2 := by
  classical
  have e : (fun p : ℝ × ℝ => count030 Tm p.1 p.2) =
      fun p => ∑ τ ∈ Tm, if p.1 < τ ∧ τ ≤ p.2 then 1 else 0 := by
    funext p; rw [count030, Finset.card_filter]
  rw [e]
  refine Finset.measurable_sum _ fun τ _ => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

lemma sig_meas (Tm : Finset ℝ) (a : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) :
    Measurable (Function.uncurry fun s u => sig048 Tm a lam s u) :=
  ((measurable_from_nat (f := a)).comp (count_meas Tm)).mul
    (hlam.comp (measurable_snd.sub measurable_fst))

section
variable {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam : ℝ → ℝ} {H Λ ε Abar : ℝ}
  (h : Hyp048 Tm a a' lam H Λ ε Abar)
include h

lemma sig_bound {s T : ℝ} (hs : s ≤ T) (hTH : T - s ≤ H) :
    |sig048 Tm a lam s T| ≤ Abar * Λ ∧ |sig048 Tm a' lam s T| ≤ Abar * Λ ∧
      |sig048 Tm a lam s T - sig048 Tm a' lam s T| ≤ ε * Λ := by
  obtain ⟨-, hΛ, hA⟩ := h
  obtain ⟨h1, h2, h3⟩ := hA _ (count_le Tm s T)
  have hl := hΛ (T - s) ⟨sub_nonneg.2 hs, hTH⟩
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans hl
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans h2
  refine ⟨?_, ?_, ?_⟩
  · rw [sig048, abs_mul]; exact mul_le_mul h2 hl (abs_nonneg _) hA0
  · rw [sig048, abs_mul]; exact mul_le_mul h3 hl (abs_nonneg _) hA0
  · rw [sig048, sig048, ← sub_mul, abs_mul]
    exact mul_le_mul h1 hl (abs_nonneg _) ((abs_nonneg _).trans h1)

lemma sig_ii (b : ℕ → ℝ) (s x y : ℝ) (hxy : x ≤ y) (hM : ∀ u ∈ Icc x y, |sig048 Tm b lam s u| ≤ Abar * Λ) :
    IntervalIntegrable (fun u => sig048 Tm b lam s u) volume x y :=
  ii_of_bound ((sig_meas Tm b h.1).comp (measurable_const.prodMk measurable_id)) hxy hM

lemma S_bound {s T : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ T) (hTH : T ≤ H) :
    |S048 Tm a lam s T| ≤ Abar * Λ * (T - s) ∧ |S048 Tm a' lam s T| ≤ Abar * Λ * (T - s) ∧
      |S048 Tm a lam s T - S048 Tm a' lam s T| ≤ ε * Λ * (T - s) := by
  have hb : ∀ u ∈ Icc s T, T - s ≤ H → |sig048 Tm a lam s u| ≤ Abar * Λ ∧
      |sig048 Tm a' lam s u| ≤ Abar * Λ ∧
      |sig048 Tm a lam s u - sig048 Tm a' lam s u| ≤ ε * Λ := fun u hu _ =>
    sig_bound h hu.1 (by linarith [hu.2])
  have hTs : T - s ≤ H := by linarith
  have i1 := sig_ii h a s s T hs fun u hu => (hb u hu hTs).1
  have i2 := sig_ii h a' s s T hs fun u hu => (hb u hu hTs).2.1
  have bnd : ∀ (f : ℝ → ℝ) (C : ℝ), (∀ u ∈ Icc s T, |f u| ≤ C) →
      |∫ u in s..T, f u| ≤ C * (T - s) := fun f C hf => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := T) (f := f) (C := C)
      fun u hu => by
        rw [uIoc_of_le hs] at hu
        rw [Real.norm_eq_abs]; exact hf u (Ioc_subset_Icc_self hu)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hs)] at this
  refine ⟨bnd _ _ fun u hu => (hb u hu hTs).1, bnd _ _ fun u hu => (hb u hu hTs).2.1, ?_⟩
  rw [S048, S048, ← intervalIntegral.integral_sub i1 i2]
  exact bnd _ _ fun u hu => (hb u hu hTs).2.2

lemma vol_aux {s T : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ T) (hTH : T ≤ H) :
    |sig048 Tm a lam s T - sig048 Tm a' lam s T| ≤ ε * Λ ∧
    |alpha048 Tm a lam s T - alpha048 Tm a' lam s T| ≤ 2 * ε * Abar * Λ ^ 2 * (T - s) := by
  obtain ⟨h1, h2, h3⟩ := sig_bound h hs (by linarith)
  obtain ⟨g1, g2, g3⟩ := S_bound h hs0 hs hTH
  refine ⟨h3, ?_⟩
  have e : alpha048 Tm a lam s T - alpha048 Tm a' lam s T =
      (sig048 Tm a lam s T - sig048 Tm a' lam s T) * S048 Tm a lam s T +
        sig048 Tm a' lam s T * (S048 Tm a lam s T - S048 Tm a' lam s T) := by
    simp only [alpha048]; ring
  rw [e]
  have hTs : 0 ≤ T - s := sub_nonneg.2 hs
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, hs0.trans (hs.trans hTH)⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  calc _ ≤ |(sig048 Tm a lam s T - sig048 Tm a' lam s T) * S048 Tm a lam s T| +
        |sig048 Tm a' lam s T * (S048 Tm a lam s T - S048 Tm a' lam s T)| := abs_add_le _ _
    _ ≤ (ε * Λ) * (Abar * Λ * (T - s)) + (Abar * Λ) * (ε * Λ * (T - s)) := by
        have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h3 g1 (abs_nonneg _) (mul_nonneg hε0 hl0))
          (mul_le_mul h2 g3 (abs_nonneg _) (mul_nonneg hA0 hl0))
    _ = 2 * ε * Abar * Λ ^ 2 * (T - s) := by ring
end

lemma volS : volStatement := fun _ _ _ _ _ _ _ _ h _ _ hs0 hs hTH => vol_aux h hs0 hs hTH

lemma S_meas (Tm : Finset ℝ) (b : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) (T : ℝ) :
    Measurable fun s => S048 Tm b lam s T :=
  meas_param measurable_id measurable_const (K := fun s u => sig048 Tm b lam s u)
    (sig_meas Tm b hlam)

lemma alpha_meas (Tm : Finset ℝ) (b : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) (T : ℝ) :
    Measurable fun s => alpha048 Tm b lam s T :=
  ((sig_meas Tm b hlam).comp (measurable_id.prodMk measurable_const)).mul (S_meas Tm b hlam T)

/-- `∫_0^t c (T − s) ds = c (tT − t²/2)`. -/
lemma int_lin (c t T : ℝ) : ∫ s in (0:ℝ)..t, c * (T - s) = c * (t * T - t ^ 2 / 2) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (f := fun _ => T)
    (g := fun x => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

lemma meanS : meanStatement := by
  intro Tm a a' lam H Λ ε Abar h t T ht htT hTH
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (htT.trans hTH)⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hb : ∀ s ∈ Icc 0 t, |sig048 Tm a lam s T - sig048 Tm a' lam s T| ≤ ε * Λ ∧
      |alpha048 Tm a lam s T - alpha048 Tm a' lam s T| ≤ 2 * ε * Abar * Λ ^ 2 * (T - s) :=
    fun s hs => vol_aux h hs.1 (hs.2.trans htT) hTH
  have hc : 0 ≤ 2 * ε * Abar * Λ ^ 2 := by positivity
  -- the mean
  have iα : IntervalIntegrable (fun s => alpha048 Tm a lam s T - alpha048 Tm a' lam s T) volume 0 t :=
    ii_of_bound ((alpha_meas Tm a h.1 T).sub (alpha_meas Tm a' h.1 T)) ht
      (M := 2 * ε * Abar * Λ ^ 2 * T) fun s hs =>
        (hb s hs).2.trans (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hc)
  have hm : |m048 Tm a a' lam t T| ≤ 2 * ε * Abar * Λ ^ 2 * (t * T - t ^ 2 / 2) := by
    rw [m048, ← int_lin]
    refine (intervalIntegral.abs_integral_le_integral_abs ht).trans
      (intervalIntegral.integral_mono_on ht iα.abs
        ((by fun_prop : Continuous fun s : ℝ => 2 * ε * Abar * Λ ^ 2 * (T - s)).intervalIntegrable _ _)
        fun s hs => (hb s hs).2)
  -- the variance
  have iσ : IntervalIntegrable (fun s => (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2) volume 0 t :=
    ii_of_bound ((((sig_meas Tm a h.1).comp (measurable_id.prodMk measurable_const)).sub
      ((sig_meas Tm a' h.1).comp (measurable_id.prodMk measurable_const))).pow_const 2) ht
      (M := (ε * Λ) ^ 2) fun s hs => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb s hs).1 2
  have hv : ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 ≤ ε ^ 2 * Λ ^ 2 * t := by
    have := intervalIntegral.integral_mono_on ht iσ
      (intervalIntegrable_const (c := (ε * Λ) ^ 2)) fun s hs => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb s hs).1 2
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    nlinarith
  have hm2 : m048 Tm a a' lam t T ^ 2 ≤ (2 * ε * Abar * Λ ^ 2 * (t * T - t ^ 2 / 2)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hm 2
  have hq0 : 0 ≤ t * T - t ^ 2 / 2 := by nlinarith
  have hq1 : t * T - t ^ 2 / 2 ≤ H ^ 2 / 2 := by nlinarith
  refine ⟨hm, hv, by nlinarith, ?_⟩
  have : (t * T - t ^ 2 / 2) ^ 2 ≤ (H ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hq0 hq1 2
  have hA : 4 * Abar ^ 2 * Λ ^ 4 * (t * T - t ^ 2 / 2) ^ 2 ≤ Abar ^ 2 * Λ ^ 4 * H ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg Abar) (pow_nonneg hl0 4)]
  have : Λ ^ 2 * t ≤ Λ ^ 2 * H := mul_le_mul_of_nonneg_left (htT.trans hTH) (sq_nonneg _)
  nlinarith [sq_nonneg ε]

lemma sharpS : sharpStatement := by
  intro Tm lam H Λ ε Abar hlam t T ht htT hTH
  have hS : ∀ (c s : ℝ), s ∈ Icc 0 T → S048 Tm (fun _ => c) lam s T = c * Λ * (T - s) := fun c s hs => by
    rw [S048, intervalIntegral.integral_congr (g := fun _ => c * Λ) fun u hu => by
      rw [uIcc_of_le hs.2] at hu
      simp [sig048, hlam (u - s) ⟨by linarith [hu.1], by linarith [hu.2, hs.1]⟩]]
    simp; ring
  have hsig : ∀ (c s : ℝ), s ∈ Icc 0 T → sig048 Tm (fun _ => c) lam s T = c * Λ := fun c s hs => by
    simp [sig048, hlam (T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]
  refine ⟨fun s hs => by rw [hsig _ s hs, hsig _ s hs]; ring, ?_⟩
  rw [m048, intervalIntegral.integral_congr (g := fun s => (2 * Abar - ε) * ε * Λ ^ 2 * (T - s))
    fun s hs => by
      rw [uIcc_of_le ht] at hs
      have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans htT⟩
      simp only [alpha048, hsig _ s hs', hS _ s hs']
      ring, int_lin]

theorem recurrentApproxEstimates : Standalone.RecurrentApproxEstimates.statement :=
  ⟨volS, meanS, sharpS⟩

end Novel.RecurrentApproxEstimatesProof

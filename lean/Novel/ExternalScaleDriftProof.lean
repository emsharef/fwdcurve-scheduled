import Standalone.ExternalScaleDrift
import Novel.RecurrentLoadingDriftProof

open Matrix NormedSpace MeasureTheory Filter
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.ExternalScaleDrift Novel.RecurrentLoadingDriftProof
namespace Novel.ExternalScaleDriftProof

lemma ax01 : Standalone.ExternalScaleDrift.ax01Statement := by
  intro p r Tm u v M c b A h s T
  have h0 := Novel.RecurrentLoadingDriftProof.ax01 p r Tm u v M c b A s T
  have e : ∀ y, alpha031 Tm u v M c b A h s y = h s ^ 2 * alpha030 Tm u v M c b A s y := by
    intro y
    rw [alpha031, alpha030, intervalIntegral.integral_const_mul]
    ring
  simp only [e, intervalIntegral.integral_const_mul, h0]
  ring

lemma drift : Standalone.ExternalScaleDrift.driftStatement := by
  intro p r Tm u v M c b A h hhm hhb t x ht hx
  classical
  set D := dist030 Tm t
  set k := k030 u M c A x D
  set K := Kvec030 u M c A x D
  set w : ℝ → Fin p × Fin r → ℝ := fun s => w030 Tm v M b A s t with hw
  obtain ⟨G, hGm, hG⟩ := J_measurable Tm u v M c b A t
  have hfac : ∀ s, s ≤ t → ∀ y, 0 ≤ y →
      sigma030 Tm u v M c b A s (t + y) = k030 u M c A y D ⬝ᵥ w s := by
    intro s hs y hy
    have h := Novel.RecurrentLoadingAlgebraProof.factor p r Tm u v M c b A s t (t + y) hs
      (by linarith)
    rwa [add_sub_cancel_left] at h
  have hsplit : ∀ s, s ≤ t →
      (∫ y in s..(t + x), sigma030 Tm u v M c b A s y) = J030 Tm u v M c b A s t + K ⬝ᵥ w s := by
    intro s hs
    rw [← intervalIntegral.integral_add_adjacent_intervals (sigma_ii Tm u v M c b A s s t)
      (sigma_ii Tm u v M c b A s t (t + x))]
    congr 1
    have e1 : (∫ y in t..(t + x), sigma030 Tm u v M c b A s y) =
        ∫ y in (0:ℝ)..x, sigma030 Tm u v M c b A s (t + y) := by
      rw [intervalIntegral.integral_comp_add_left (fun y => sigma030 Tm u v M c b A s y) t,
        add_zero]
    have e2 : (∫ y in (0:ℝ)..x, sigma030 Tm u v M c b A s (t + y)) =
        ∫ y in (0:ℝ)..x, ∑ ab, k030 u M c A y D ab * w s ab := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hx] at hy
      exact hfac s hs y hy.1
    rw [e1, e2, intervalIntegral.integral_finsetSum
      (fun ab _ => (k_ii u M c A D ab 0 x).mul_const _)]
    simp only [intervalIntegral.integral_mul_const]
    rfl
  -- bounds on [0, t]
  obtain ⟨Sb, hSb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
    (shape_continuous c b A).continuousOn
  have hGb : ∀ s ∈ Set.uIcc 0 t, |G s| ≤ loadBound Tm u v M * Sb * t := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    rw [← hG s hs.2, J030]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := loadBound Tm u v M * Sb) (f := fun y => sigma030 Tm u v M c b A s y) (fun y hy => by
        rw [Set.uIoc_of_le hs.2] at hy
        simp only [sigma030, norm_mul, Real.norm_eq_abs]
        have h1 := loading_le Tm u v M _ (count_le_card Tm s y)
        have h2 := hSb (y - s) ⟨by linarith [hy.1], by linarith [hy.2, hs.1]⟩
        rw [Real.norm_eq_abs] at h2
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2] : (0:ℝ) ≤ t - s)] at h
    have hLS : 0 ≤ loadBound Tm u v M * Sb :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ((norm_nonneg _).trans (hSb 0 ⟨le_rfl, ht⟩))
    calc |∫ y in s..t, sigma030 Tm u v M c b A s y| ≤ loadBound Tm u v M * Sb * (t - s) := h
      _ ≤ loadBound Tm u v M * Sb * t := by
          apply mul_le_mul_of_nonneg_left _ hLS; linarith [hs.1]
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Ch, hCh⟩ := hhb
  have hC0 : 0 ≤ Ch := (abs_nonneg _).trans (hCh 0)
  have hh2 : ∀ s, |h s ^ 2| ≤ Ch ^ 2 := fun s => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCh s) 2
  have hhm2 : Measurable fun s => h s ^ 2 := hhm.pow_const 2
  -- integrability in `s` on `[0, t]`
  have hww : ∀ a b' : Fin p × Fin r,
      IntervalIntegrable (fun s => h s ^ 2 * (w s a * w s b')) volume 0 t := by
    intro a b'
    have h1 : IntervalIntegrable (fun s => h s ^ 2 * (((M ^ count030 Tm s t) *ᵥ v) a.1 *
        ((M ^ count030 Tm s t) *ᵥ v) b'.1)) volume 0 t :=
      ii_bdd (hhm2.mul ((vec_measurable Tm v M t a.1).mul
          (vec_measurable Tm v M t b'.1))).aestronglyMeasurable
        (Ch ^ 2 * (vecBound Tm v M * vecBound Tm v M)) (fun s _ => by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hh2 s) (mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1)
            (vec_le Tm v M _ (count_le_card Tm s t) b'.1) (abs_nonneg _) hvb0)
            (by positivity) (by positivity))
    have h2 := h1.mul_continuousOn
      ((expv_continuous b A t a.2).mul (expv_continuous b A t b'.2)).continuousOn
    have e : (fun s => h s ^ 2 * (w s a * w s b')) = fun s => (h s ^ 2 *
        (((M ^ count030 Tm s t) *ᵥ v) a.1 * ((M ^ count030 Tm s t) *ᵥ v) b'.1)) *
        ((exp ((t - s) • A) *ᵥ b) a.2 * (exp ((t - s) • A) *ᵥ b) b'.2) := by
      funext s; simp only [hw, w030]; ring
    rw [e]; exact h2
  have hwG : ∀ a : Fin p × Fin r,
      IntervalIntegrable (fun s => h s ^ 2 * (w s a * G s)) volume 0 t := by
    intro a
    have h1 : IntervalIntegrable (fun s => h s ^ 2 * (((M ^ count030 Tm s t) *ᵥ v) a.1 * G s))
        volume 0 t :=
      ii_bdd (hhm2.mul ((vec_measurable Tm v M t a.1).mul hGm)).aestronglyMeasurable
        (Ch ^ 2 * (vecBound Tm v M * (loadBound Tm u v M * Sb * t))) (fun s hs => by
          rw [abs_mul, abs_mul]
          have hGs := hGb s hs
          exact mul_le_mul (hh2 s) (mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1) hGs
            (abs_nonneg _) hvb0) (by positivity) (by positivity))
    have h2 := h1.mul_continuousOn (expv_continuous b A t a.2).continuousOn
    have e : (fun s => h s ^ 2 * (w s a * G s)) = fun s => (h s ^ 2 *
        (((M ^ count030 Tm s t) *ᵥ v) a.1 * G s)) * (exp ((t - s) • A) *ᵥ b) a.2 := by
      funext s; simp only [hw, w030]; ring
    rw [e]; exact h2
  have hS : ∀ a : Fin p × Fin r,
      IntervalIntegrable (fun s => ∑ b', h s ^ 2 * (w s a * w s b') * K b') volume 0 t := by
    intro a
    have hsum := IntervalIntegrable.sum Finset.univ (fun b' _ => (hww a b').mul_const (K b'))
    convert hsum using 1
    funext s
    simp
  -- the pointwise algebra
  have hpt : ∀ s ∈ Set.uIcc 0 t, alpha031 Tm u v M c b A h s (t + x) =
      ∑ a, k a * (∑ b', h s ^ 2 * (w s a * w s b') * K b' + h s ^ 2 * (w s a * G s)) := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    rw [alpha031, intervalIntegral.integral_const_mul, hsplit s hs.2, hfac s hs.2 x hx, hG s hs.2]
    simp only [dotProduct]
    have e1 : (h s * ∑ i, k030 u M c A x D i * w s i) * (h s * (G s + ∑ i, K i * w s i)) =
        h s ^ 2 * ((∑ i, k030 u M c A x D i * w s i) * (G s + ∑ i, K i * w s i)) := by ring
    rw [e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_add, Finset.mul_sum]
    have e2 : ∀ b' ∈ Finset.univ, k030 u M c A x D a * w s a * (K b' * w s b') =
        k a * (w s a * w s b' * K b') := fun b' _ => by ring
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
    simp only [mul_add, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum
    (fun a _ => ((hS a).add (hwG a)).const_mul (k a))]
  simp only [dotProduct, mulVec, Pi.add_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hS a) (hwG a),
    intervalIntegral.integral_finsetSum (fun b' _ => (hww a b').mul_const _)]
  simp only [intervalIntegral.integral_mul_const]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  simp only [hw]
  rw [hG s hs.2]

theorem externalScaleDrift : Standalone.ExternalScaleDrift.statement := ⟨ax01, drift⟩

end Novel.ExternalScaleDriftProof

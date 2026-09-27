import Standalone.SpliceCrossTermDrift
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter
open Standalone.SpliceCrossTermDrift
namespace Novel.SpliceCrossTermDriftProof

lemma idx_mono (Tm : Finset ℝ) : Monotone (idx033 Tm) := by
  intro x x' h
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hd.2.trans h⟩

lemma idx_meas (Tm : Finset ℝ) : Measurable (idx033 Tm) := (idx_mono Tm).measurable

lemma sigS_meas2 (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (Tm : Finset ℝ) :
    Measurable fun q : ℝ × ℝ => sigS033 s Tm q.1 q.2 := by
  have h : Measurable fun p : ℕ × ℝ => s p.1 p.2 := measurable_from_prod_countable_right hs
  exact h.comp ((idx_meas Tm).comp measurable_snd |>.prodMk measurable_fst)

/-- Bounded Borel functions are interval integrable. -/
lemma ii_bdd {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by show ‖f x‖ ≤ C; rw [Real.norm_eq_abs]; exact hC x)

/-- `u ↦ S^S(u, T₀)` agrees with a Borel function on `u ≤ T₀`. -/
lemma SS_measurable (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (Tm : Finset ℝ) (T0 : ℝ) :
    ∃ G : ℝ → ℝ, Measurable G ∧ ∀ u ≤ T0, SS033 s Tm u T0 = G u := by
  classical
  let F : ℝ × ℝ → ℝ := fun q => if q.1 < q.2 ∧ q.2 ≤ T0 then sigS033 s Tm q.1 q.2 else 0
  have hFm : Measurable F :=
    Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) (sigS_meas2 s hs Tm) measurable_const
  refine ⟨fun u => ∫ v, F (u, v), (hFm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable, fun u hu => ?_⟩
  rw [SS033, intervalIntegral.integral_of_le hu, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext v
  simp only [Set.indicator_apply, Set.mem_Ioc, F]

lemma cross : crossStatement := by
  intro Tm s hs C hC a b ρ ha j t ht
  classical
  by_cases hne : ∃ T0, idx033 Tm T0 = j ∧ t ≤ T0
  swap
  · push Not at hne
    exact ⟨0, 0, fun T hT htT => absurd htT (not_le.2 (hne T hT))⟩
  obtain ⟨T0, hT0, htT0⟩ := hne
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  obtain ⟨G, hGm, hG⟩ := SS_measurable s hs Tm T0
  -- the three coefficient functions
  let g1 : ℝ → ℝ := fun u => ρ * (b / a) * s j u
  let g2 : ℝ → ℝ := fun u => ρ * b * Real.exp (a * u) * (G u - s j u * T0 - s j u / a)
  let g3 : ℝ → ℝ := fun u => ρ * b * (Real.exp (a * u) * s j u)
  have hsj : Measurable (s j) := hs j
  have hGb : ∀ u ∈ Set.uIcc 0 t, |G u| ≤ C * T0 := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [← hG u (hu.2.trans htT0), SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T0) (C := C)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by
        rw [Real.norm_eq_abs]; exact hC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ T0 - u)] at hb
    nlinarith [hu.1]
  have hi1 : IntervalIntegrable g1 volume 0 t :=
    (ii_bdd hsj C (hC j) 0 t).const_mul _
  have hi3 : IntervalIntegrable g3 volume 0 t :=
    ((ii_bdd hsj C (hC j) 0 t).continuousOn_mul (by fun_prop)).const_mul _
  have hi2 : IntervalIntegrable g2 volume 0 t := by
    have hGi : IntervalIntegrable G volume 0 t :=
      (intervalIntegrable_const (c := C * T0)).mono_fun' hGm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun u hu => by
          show ‖G u‖ ≤ C * T0
          rw [Real.norm_eq_abs]; exact hGb u (Set.uIoc_subset_uIcc hu)))
    have := ((hGi.sub ((ii_bdd hsj C (hC j) 0 t).mul_const T0)).sub
      ((ii_bdd hsj C (hC j) 0 t).div_const a)).continuousOn_mul
      (g := fun u => ρ * b * Real.exp (a * u)) (by fun_prop)
    refine this.congr fun u _ => ?_
    simp only [g2, Pi.sub_apply]
  refine ⟨∫ u in (0:ℝ)..t, g1 u, ∫ u in (0:ℝ)..t, g2 u, fun T hT htT => ?_⟩
  -- on the segment between `T₀` and `T` the step volatility is `s_j`
  have hseg : ∀ v ∈ Set.uIcc T0 T, sigS033 s Tm 0 v = s j 0 ∧ ∀ u, sigS033 s Tm u v = s j u := by
    intro v hv
    have hidx : idx033 Tm v = j := by
      rcases le_total T0 T with h | h
      · rw [Set.uIcc_of_le h] at hv
        exact le_antisymm (hT ▸ idx_mono Tm hv.2) (hT0 ▸ idx_mono Tm hv.1)
      · rw [Set.uIcc_of_ge h] at hv
        exact le_antisymm (hT0 ▸ idx_mono Tm hv.2) (hT ▸ idx_mono Tm hv.1)
    exact ⟨by simp [sigS033, hidx], fun u => by simp [sigS033, hidx]⟩
  have hpt : ∀ u ∈ Set.uIcc 0 t, cross033 a b ρ s Tm u T =
      g1 u + Real.exp (-a * T) * (g2 u + T * g3 u) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have huT0 : u ≤ T0 := hu.2.trans htT0
    have hiv : ∀ x y, IntervalIntegrable (fun v => sigS033 s Tm u v) volume x y := fun x y =>
      ii_bdd ((sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)) C
        (fun v => hC _ _) x y
    have hSS : SS033 s Tm u T = G u + s j u * (T - T0) := by
      rw [← hG u huT0, SS033, SS033, ← intervalIntegral.integral_add_adjacent_intervals
        (hiv u T0) (hiv T0 T)]
      congr 1
      rw [intervalIntegral.integral_congr (g := fun _ => s j u) (fun v hv => (hseg v hv).2 u),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hTj : sigS033 s Tm u T = s j u := by simp [sigS033, hT]
    rw [cross033, hSS, hTj]
    simp only [g1, g2, g3]
    have e : Real.exp (-a * (T - u)) = Real.exp (-a * T) * Real.exp (a * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hi1
    ((hi2.add (hi3.const_mul T)).const_mul _)]
  have h23 : (∫ u in (0:ℝ)..t, Real.exp (-a * T) * (g2 u + T * g3 u)) =
      Real.exp (-a * T) * ((∫ u in (0:ℝ)..t, g2 u) + T * ∫ u in (0:ℝ)..t, g3 u) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2 (hi3.const_mul T),
      intervalIntegral.integral_const_mul]
  have hb : (∫ u in (0:ℝ)..t, g3 u) = beta033 a b ρ s j t := by
    simp only [g3, beta033, intervalIntegral.integral_const_mul]
  rw [h23, hb]
  ring

lemma jump : jumpStatement := by
  intro s hs C hC a b ρ m t
  have hi : ∀ i, IntervalIntegrable (fun u => Real.exp (a * u) * s i u) volume 0 t := fun i =>
    (ii_bdd (hs i) C (hC i) 0 t).continuousOn_mul (by fun_prop)
  simp only [beta033]
  rw [← mul_sub, ← intervalIntegral.integral_sub (hi _) (hi _)]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  ring

theorem spliceCrossTermDrift : Standalone.SpliceCrossTermDrift.statement := ⟨cross, jump⟩

end Novel.SpliceCrossTermDriftProof

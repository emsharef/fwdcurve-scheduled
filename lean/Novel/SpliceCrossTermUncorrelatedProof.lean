import Standalone.SpliceCrossTermUncorrelated
import Novel.SpliceCrossTermDriftProof

open MeasureTheory Filter Set
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermUncorrelated
open Novel.SpliceCrossTermDriftProof
namespace Novel.SpliceCrossTermUncorrelatedProof

lemma uncorrelated : uncorrelatedStatement := by
  intro Tm s hs C hC a b ρ ha t ht hcase
  classical
  rcases hcase with hρ | hae
  · refine ⟨0, 0, 0, fun T _ => ?_⟩
    simp [cross033, hρ]
  set j := idx033 Tm t
  obtain ⟨G, hGm, hG⟩ := SS_measurable s hs Tm t
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  let g1 : ℝ → ℝ := fun u => ρ * (b / a) * s j u
  let g2 : ℝ → ℝ := fun u => ρ * b * Real.exp (a * u) * (G u - s j u * t - s j u / a)
  let g3 : ℝ → ℝ := fun u => ρ * b * (Real.exp (a * u) * s j u)
  have hsj : Measurable (s j) := hs j
  have hGb : ∀ u ∈ Set.uIcc 0 t, |G u| ≤ C * t := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [← hG u hu.2, SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := t) (C := C)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by
        rw [Real.norm_eq_abs]; exact hC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ t - u)] at hb
    nlinarith [hu.1]
  have hi1 : IntervalIntegrable g1 volume 0 t :=
    (ii_bdd hsj C (hC j) 0 t).const_mul _
  have hi3 : IntervalIntegrable g3 volume 0 t :=
    ((ii_bdd hsj C (hC j) 0 t).continuousOn_mul (by fun_prop)).const_mul _
  have hi2 : IntervalIntegrable g2 volume 0 t := by
    have hGi : IntervalIntegrable G volume 0 t :=
      (intervalIntegrable_const (c := C * t)).mono_fun' hGm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun u hu => by
          show ‖G u‖ ≤ C * t
          rw [Real.norm_eq_abs]; exact hGb u (Set.uIoc_subset_uIcc hu)))
    have := ((hGi.sub ((ii_bdd hsj C (hC j) 0 t).mul_const t)).sub
      ((ii_bdd hsj C (hC j) 0 t).div_const a)).continuousOn_mul
      (g := fun u => ρ * b * Real.exp (a * u)) (by fun_prop)
    refine this.congr fun u _ => ?_
    simp only [g2, Pi.sub_apply]
  refine ⟨∫ u in (0:ℝ)..t, g1 u, ∫ u in (0:ℝ)..t, g2 u, ∫ u in (0:ℝ)..t, g3 u,
    fun T htT => ?_⟩
  have hpt : ∀ᵐ u ∂volume, u ∈ Set.uIoc 0 t → cross033 a b ρ s Tm u T =
      g1 u + Real.exp (-a * T) * (g2 u + T * g3 u) := by
    filter_upwards [hae] with u hu hmem
    rw [Set.uIoc_of_le ht] at hmem
    have hu' := hu (Set.Ioc_subset_Icc_self hmem)
    have hiv : ∀ x y, IntervalIntegrable (fun v => sigS033 s Tm u v) volume x y := fun x y =>
      ii_bdd ((sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)) C
        (fun v => hC _ _) x y
    have hSS : SS033 s Tm u T = G u + s j u * (T - t) := by
      rw [← hG u hmem.2, SS033, SS033, ← intervalIntegral.integral_add_adjacent_intervals
        (hiv u t) (hiv t T)]
      congr 1
      rw [intervalIntegral.integral_congr (g := fun _ => s j u) (fun v hv => by
          rw [Set.uIcc_of_le htT] at hv
          exact hu' v hv.1),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hTj : sigS033 s Tm u T = s j u := hu' T htT
    rw [cross033, hSS, hTj]
    simp only [g1, g2, g3]
    have e : Real.exp (-a * (T - u)) = Real.exp (-a * T) * Real.exp (a * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    field_simp
    ring
  rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_add hi1
    ((hi2.add (hi3.const_mul T)).const_mul _)]
  have h23 : (∫ u in (0:ℝ)..t, Real.exp (-a * T) * (g2 u + T * g3 u)) =
      Real.exp (-a * T) * ((∫ u in (0:ℝ)..t, g2 u) + T * ∫ u in (0:ℝ)..t, g3 u) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2 (hi3.const_mul T),
      intervalIntegral.integral_const_mul]
  rw [h23]
  ring

theorem spliceCrossTermUncorrelated : Standalone.SpliceCrossTermUncorrelated.statement := uncorrelated

end Novel.SpliceCrossTermUncorrelatedProof

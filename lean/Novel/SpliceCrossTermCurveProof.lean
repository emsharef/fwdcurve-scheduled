import Standalone.SpliceCrossTermCurve
import Novel.SpliceCrossTermDriftProof
import Novel.RecurrenceNecessityCurveProof

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermCurve
open Novel.SpliceCrossTermDriftProof
namespace Novel.SpliceCrossTermCurveProof

/-- A Borel function bounded on `[a, b]` is interval integrable there. -/
lemma ii_on {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) {a b : ℝ}
    (hB : ∀ x ∈ Set.uIcc a b, |f x| ≤ B) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := B)).mono_fun' hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => by
      show ‖f x‖ ≤ B
      rw [Real.norm_eq_abs]; exact hB x (Set.uIoc_subset_uIcc hx)))

lemma step : stepStatement := by
  intro Tm s hs C hC j t ht
  classical
  by_cases hne : ∃ T0, idx033 Tm T0 = j ∧ t ≤ T0
  swap
  · push Not at hne
    exact ⟨0, 0, fun T hT htT => absurd htT (not_le.2 (hne T hT))⟩
  obtain ⟨T0, hT0, htT0⟩ := hne
  obtain ⟨G, hGm, hG⟩ := SS_measurable s hs Tm T0
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
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
  let g0 : ℝ → ℝ := fun u => s j u * (G u - s j u * T0)
  let g1 : ℝ → ℝ := fun u => s j u * s j u
  have hi0 : IntervalIntegrable g0 volume 0 t := by
    refine ii_on (hsj.mul (hGm.sub (hsj.mul_const T0))) (C * (C * T0 + C * |T0|)) fun u hu => ?_
    show |s j u * (G u - s j u * T0)| ≤ _
    rw [abs_mul]
    have h1 := hC j u
    have h2 : |G u - s j u * T0| ≤ C * T0 + C * |T0| :=
      (abs_sub _ _).trans (add_le_add (hGb u hu) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)))
    exact mul_le_mul h1 h2 (abs_nonneg _) hC0
  have hi1 : IntervalIntegrable g1 volume 0 t :=
    ii_on (hsj.mul hsj) (C * C) fun u _ => by
      show |s j u * s j u| ≤ _
      rw [abs_mul]; exact mul_le_mul (hC j u) (hC j u) (abs_nonneg _) hC0
  refine ⟨∫ u in (0:ℝ)..t, g0 u, ∫ u in (0:ℝ)..t, g1 u, fun T hT htT => ?_⟩
  have hseg : ∀ v ∈ Set.uIcc T0 T, ∀ u, sigS033 s Tm u v = s j u := by
    intro v hv u
    have hidx : idx033 Tm v = j := by
      rcases le_total T0 T with h | h
      · rw [Set.uIcc_of_le h] at hv
        exact le_antisymm (hT ▸ idx_mono Tm hv.2) (hT0 ▸ idx_mono Tm hv.1)
      · rw [Set.uIcc_of_ge h] at hv
        exact le_antisymm (hT0 ▸ idx_mono Tm hv.2) (hT ▸ idx_mono Tm hv.1)
    simp [sigS033, hidx]
  have hpt : ∀ u ∈ Set.uIcc 0 t, sigS033 s Tm u T * SS033 s Tm u T = g0 u + T * g1 u := by
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
      rw [intervalIntegral.integral_congr (g := fun _ => s j u) (fun v hv => hseg v hv u),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hTj : sigS033 s Tm u T = s j u := by simp [sigS033, hT]
    rw [hSS, hTj]
    simp only [g0, g1]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hi0 (hi1.const_mul T),
    intervalIntegral.integral_const_mul]
  ring

lemma block : blockStatement := by
  intro a b t ha
  refine ⟨b ^ 2 / a * ∫ u in (0:ℝ)..t, Real.exp (a * u),
    -(b ^ 2 / a) * ∫ u in (0:ℝ)..t, Real.exp (2 * a * u), fun T => ?_⟩
  have hpt : ∀ u, b * Real.exp (-a * (T - u)) * (b * (1 - Real.exp (-a * (T - u))) / a) =
      b ^ 2 / a * Real.exp (-a * T) * Real.exp (a * u) -
        b ^ 2 / a * Real.exp (-2 * a * T) * Real.exp (2 * a * u) := by
    intro u
    have e1 : Real.exp (-a * (T - u)) = Real.exp (-a * T) * Real.exp (a * u) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-a * (T - u)) * Real.exp (-a * (T - u)) =
        Real.exp (-2 * a * T) * Real.exp (2 * a * u) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [show b * Real.exp (-a * (T - u)) * (b * (1 - Real.exp (-a * (T - u))) / a) =
      b ^ 2 / a * Real.exp (-a * (T - u)) -
        b ^ 2 / a * (Real.exp (-a * (T - u)) * Real.exp (-a * (T - u))) by ring, e2, e1]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun u =>
      b ^ 2 / a * Real.exp (-a * T) * Real.exp (a * u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u =>
      b ^ 2 / a * Real.exp (-2 * a * T) * Real.exp (2 * a * u)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

section Random
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma exp_U4 (a : ℝ) : U4 S.ℱ S.μ (fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) :=
  Novel.RecurrenceNecessityCurveProof.U4_det S _
    ((by fun_prop : Continuous fun u : ℝ≥0 => Real.exp (a * u)).measurable)
    (Novel.RecurrenceNecessityCurveProof.bdd_of_cont _ (by fun_prop))

lemma step_U4 (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ) (hC : ∀ i u, |s i u| ≤ C)
    (j : ℕ) : U4 S.ℱ S.μ (fun (u : ℝ≥0) (_ : Ω) => s j u) :=
  Novel.RecurrenceNecessityCurveProof.U4_det S _ ((hs j).comp NNReal.continuous_coe.measurable)
    (fun _ => ⟨C, fun u _ => hC j u⟩)

end Random

lemma random : randomStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ T t
  set c₁ := ρ * b * Real.exp (-a * T)
  set c₂ := Real.sqrt (1 - ρ ^ 2) * b * Real.exp (-a * T)
  have h1 := S.int_linear k₁ (fun (u : ℝ≥0) (_ : Ω) => s (idx033 Tm T) u)
    (fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) 1 c₁ (step_U4 S s hs C hC _) (exp_U4 S a) t
  have h2 := S.int_linear k₂ (fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u))
    (fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) c₂ 0 (exp_U4 S a) (exp_U4 S a) t
  have e1 : ((1:ℝ) • (fun (u : ℝ≥0) (_ : Ω) => s (idx033 Tm T) u) +
      c₁ • fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) =
      fun (u : ℝ≥0) (_ : Ω) => sigS033 s Tm u T + ρ * (b * Real.exp (-a * (T - u))) := by
    funext u ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, sigS033, c₁]
    congr 1
    rw [show -a * (T - (u:ℝ)) = -a * T + a * u by ring, Real.exp_add]
    ring
  have e2 : (c₂ • (fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) +
      (0:ℝ) • fun (u : ℝ≥0) (_ : Ω) => Real.exp (a * u)) =
      fun (u : ℝ≥0) (_ : Ω) => Real.sqrt (1 - ρ ^ 2) * (b * Real.exp (-a * (T - u))) := by
    funext u ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, c₂]
    rw [show -a * (T - (u:ℝ)) = -a * T + a * u by ring, Real.exp_add]
    ring
  rw [e1] at h1
  rw [e2] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1, hω2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_mul, add_zero, c₁, c₂]
  ring

theorem spliceCrossTermCurve : Standalone.SpliceCrossTermCurve.statement := ⟨step, block, random⟩

end Novel.SpliceCrossTermCurveProof

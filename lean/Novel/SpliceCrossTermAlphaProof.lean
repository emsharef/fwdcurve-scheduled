import Standalone.SpliceCrossTermAlpha
import Novel.SpliceCrossTermDriftProof
import Novel.SpliceCrossTermCurveProof

open MeasureTheory Filter Set
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
namespace Novel.SpliceCrossTermAlphaProof
open Novel.SpliceCrossTermDriftProof

/-- Between two maturities of `I_j` the maturity interval is `I_j`. -/
lemma idx_between (Tm : Finset ℝ) (j : ℕ) {T0 T1 v : ℝ} (h0 : idx033 Tm T0 = j)
    (h1 : idx033 Tm T1 = j) (hv : v ∈ uIcc T0 T1) : idx033 Tm v = j := by
  rcases le_total T0 T1 with h | h
  · rw [uIcc_of_le h] at hv
    exact le_antisymm (h1 ▸ idx_mono Tm hv.2) (h0 ▸ idx_mono Tm hv.1)
  · rw [uIcc_of_ge h] at hv
    exact le_antisymm (h0 ▸ idx_mono Tm hv.2) (h1 ▸ idx_mono Tm hv.1)

/-- `S^S(u, ·)` has slope `s_j(u)` across a segment inside `I_j` (up to its right end). -/
lemma SS_shift (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (j : ℕ) (u T0 T1 : ℝ)
    (hseg : ∀ v ∈ Ioo (min T0 T1) (max T0 T1), idx033 Tm v = j) :
    SS033 s Tm u T1 = SS033 s Tm u T0 + s j u * (T1 - T0) := by
  have hiv : ∀ x y, IntervalIntegrable (fun v => sigS033 s Tm u v) volume x y := fun x y =>
    ii_bdd ((sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)) C
      (fun v => hC _ _) x y
  have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ max T0 T1 := by
    simp [ae_iff, measure_singleton]
  have hcongr : (∫ v in T0..T1, sigS033 s Tm u v) = ∫ _ in T0..T1, s j u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with v hv hmem
    rw [Set.uIoc, mem_Ioc] at hmem
    simp only [sigS033, hseg v ⟨hmem.1, lt_of_le_of_ne hmem.2 hv⟩]
  rw [SS033, SS033, ← intervalIntegral.integral_add_adjacent_intervals (hiv u T0) (hiv T0 T1),
    hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma kappa : kappaStatement := by
  intro Tm s hs C hC j T0 T1 u h0 h1 _ _
  have h := SS_shift Tm s hs C hC j u T0 T1 fun v hv =>
    idx_between Tm j h0 h1 (by rw [uIcc]; exact ⟨hv.1.le, hv.2.le⟩)
  simp only [kappa033, h]
  ring

/-- `u ↦ e^{au} (κ_j(u) − s_j(u)/a)` is interval integrable on `[0, t]`, `t ≤ T₀`. -/
lemma kappa_ii (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a : ℝ) (j : ℕ) (T0 t : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0) :
    IntervalIntegrable (fun u => Real.exp (a * u) * (kappa033 s Tm j T0 u - s j u / a))
      volume 0 t := by
  obtain ⟨G, hGm, hG⟩ := SS_measurable s hs Tm T0
  have hGb : ∀ u ∈ uIcc 0 t, |G u| ≤ C * T0 := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    rw [← hG u (hu.2.trans htT0), SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T0) (C := C)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by rw [Real.norm_eq_abs]; exact hC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ T0 - u)] at hb
    nlinarith [hu.1, (abs_nonneg _).trans (hC 0 0)]
  have hGi := Novel.SpliceCrossTermCurveProof.ii_on hGm (C * T0) hGb
  have hsj := ii_bdd (hs j) C (hC j) 0 t
  refine (((hGi.sub (hsj.mul_const T0)).sub (hsj.div_const a)).continuousOn_mul
    (g := fun u => Real.exp (a * u)) (by fun_prop)).congr fun u hu => ?_
  rw [uIoc_of_le ht] at hu
  simp only [kappa033, hG u (hu.2.trans htT0)]

lemma explicit : explicitStatement := by
  intro Tm s hs C hC a b ρ ha j t T0 ht hT0 htT0
  classical
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  obtain ⟨G, hGm, hG⟩ := SS_measurable s hs Tm T0
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
      Novel.SpliceCrossTermCurveProof.ii_on hGm (C * T0) hGb
    have := ((hGi.sub ((ii_bdd hsj C (hC j) 0 t).mul_const T0)).sub
      ((ii_bdd hsj C (hC j) 0 t).div_const a)).continuousOn_mul
      (g := fun u => ρ * b * Real.exp (a * u)) (by fun_prop)
    refine this.congr fun u _ => ?_
    simp only [g2]
  refine ⟨∫ u in (0:ℝ)..t, g1 u, fun T hT htT => ?_⟩
  have hseg : ∀ v ∈ Set.uIcc T0 T, ∀ u, sigS033 s Tm u v = s j u := fun v hv u => by
    simp [sigS033, idx_between Tm j hT0 hT hv]
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
      rw [intervalIntegral.integral_congr (g := fun _ => s j u) (fun v hv => hseg v hv u),
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
  have ha2 : (∫ u in (0:ℝ)..t, g2 u) = alphaCoef033 a b ρ s Tm j T0 t := by
    rw [alphaCoef033, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le ht] at hu
    simp only [g2, kappa033, hG u (hu.2.trans htT0)]
    ring
  rw [h23, hb, ha2]
  ring

lemma alphaJump : alphaJumpStatement := by
  intro Tm s hs C hC a b ρ m τ τl τr T0 T1 t hl hr hidxl hidxr hT0 hT1 ht htT0
  have hk1 : ∀ u, kappa033 s Tm (m + 1) T1 u = kappa033 s Tm (m + 1) τ u := fun u => by
    have h := SS_shift Tm s hs C hC (m + 1) u τ T1 fun v hv => by
      rw [min_eq_left hT1.1, max_eq_right hT1.1] at hv
      exact hidxr v ⟨hv.1.le, hv.2.trans hT1.2⟩
    simp only [kappa033, h]
    ring
  have hSS : ∀ u, SS033 s Tm u τ = SS033 s Tm u T0 + s m u * (τ - T0) := fun u =>
    SS_shift Tm s hs C hC m u T0 τ fun v hv => by
      rw [min_eq_left hT0.2.le, max_eq_right hT0.2.le] at hv
      exact hidxl v ⟨hT0.1.trans hv.1, hv.2⟩
  have hF0 := kappa_ii Tm s hs C hC a m T0 t ht htT0
  have hg : IntervalIntegrable (fun u => Real.exp (a * u) * (τ + 1 / a) *
      (s (m + 1) u - s m u)) volume 0 t :=
    ((ii_bdd (hs (m + 1)) C (hC _) 0 t).sub (ii_bdd (hs m) C (hC _) 0 t)).continuousOn_mul
      (g := fun u => Real.exp (a * u) * (τ + 1 / a)) (by fun_prop)
  have hpt : ∀ u ∈ uIcc 0 t, Real.exp (a * u) *
      (kappa033 s Tm (m + 1) T1 u - s (m + 1) u / a) =
      Real.exp (a * u) * (kappa033 s Tm m T0 u - s m u / a) -
        Real.exp (a * u) * (τ + 1 / a) * (s (m + 1) u - s m u) := fun u _ => by
    rw [hk1]
    simp only [kappa033, hSS]
    ring
  rw [alphaCoef033, alphaCoef033, intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub hF0 hg]
  ring

theorem spliceCrossTermAlpha : Standalone.SpliceCrossTermAlpha.statement := ⟨kappa, explicit, alphaJump⟩

end Novel.SpliceCrossTermAlphaProof

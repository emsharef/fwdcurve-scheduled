import Standalone.SpliceQuasiExponentialCross
import Novel.SpliceCrossTermAlphaProof
import Novel.SpliceQuasiExponentialKeyProof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceQuasiExponentialKey Standalone.SpliceQuasiExponentialCross
namespace Novel.SpliceQuasiExponentialCrossProof
open Novel.SpliceCrossTermDriftProof

variable {r : ℕ}

lemma exp_split (A : Matrix (Fin r) (Fin r) ℝ) (T u : ℝ) :
    exp ((T - u) • A) = exp (T • A) * exp (u • (-A)) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).neg_right.smul_left T).smul_right u),
    smul_neg, ← sub_eq_add_neg, ← sub_smul]

lemma inv_comm (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (T : ℝ) :
    A⁻¹ * exp (T • A) = exp (T • A) * A⁻¹ := by
  have hc : Commute A⁻¹ A := by
    unfold Commute SemiconjBy
    rw [nonsing_inv_mul _ hA, mul_nonsing_inv _ hA]
  exact (Commute.exp_right (hc.smul_right T)).eq

lemma lam_eq (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (T u : ℝ) :
    lam035 c A b (T - u) = (c ᵥ* exp (T • A)) ⬝ᵥ (exp (u • (-A)) *ᵥ b) := by
  rw [lam035, exp_split, ← mulVec_mulVec, dotProduct_mulVec]

lemma Lam_eq (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (b : Fin r → ℝ)
    (T u : ℝ) : Lam035 c A b (T - u) =
      (c ᵥ* exp (T • A)) ⬝ᵥ (A⁻¹ *ᵥ (exp (u • (-A)) *ᵥ b)) - c ⬝ᵥ (A⁻¹ *ᵥ b) := by
  rw [Lam035, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub, exp_split,
    ← Matrix.mul_assoc, inv_comm A hA, Matrix.mul_assoc]
  simp only [← mulVec_mulVec]
  rw [dotProduct_mulVec]

/-- Entries of `M e^{uC} b` are continuous in `u`. -/
lemma gv_cont (M C : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (i : Fin r) :
    Continuous fun u : ℝ => (M *ᵥ (exp (u • C) *ᵥ b)) i := by
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul
    (by simpa [mulVec, dotProduct] using
      Novel.RecurrenceNecessityReductionProof.phi_cont C b k)

lemma int_dot (w : Fin r → ℝ) (V : ℝ → Fin r → ℝ) (t : ℝ)
    (hV : ∀ i, IntervalIntegrable (fun u => V u i) volume 0 t) :
    ∫ u in (0:ℝ)..t, w ⬝ᵥ V u = w ⬝ᵥ (fun i => ∫ u in (0:ℝ)..t, V u i) := by
  simp only [dotProduct]
  rw [intervalIntegral.integral_finsetSum fun i _ => (hV i).const_mul (w i)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- `κ_j` is interval integrable on `[0, t]`, `t ≤ T₀`. -/
lemma kappa_ii (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (j : ℕ) (T0 t : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0) :
    IntervalIntegrable (fun u => kappa033 s Tm j T0 u) volume 0 t := by
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
  refine (hGi.sub ((ii_bdd (hs j) C (hC j) 0 t).mul_const T0)).congr fun u hu => ?_
  rw [uIoc_of_le ht] at hu
  simp only [kappa033, hG u (hu.2.trans htT0)]

lemma ii_dot (w : Fin r → ℝ) (V : ℝ → Fin r → ℝ) (t : ℝ)
    (hV : ∀ i, IntervalIntegrable (fun u => V u i) volume 0 t) :
    IntervalIntegrable (fun u => w ⬝ᵥ V u) volume 0 t := by
  have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := t) Finset.univ
    (fun i _ => (hV i).const_mul (w i))
  convert this using 1
  funext u
  simp [dotProduct, Finset.sum_apply]

lemma explicit : Standalone.SpliceQuasiExponentialCross.explicitStatement := by
  intro Tm s hs C hC r A hA b c ρ j t T0 ht hT0 htT0 T hT htT
  set w := c ᵥ* exp (T • A)
  let gv : ℝ → Fin r → ℝ := fun u => exp (u • (-A)) *ᵥ b
  let Y : ℝ → Fin r → ℝ := fun u =>
    ρ • (s j u • (A⁻¹ *ᵥ gv u) + kappa033 s Tm j T0 u • gv u)
  let Z : ℝ → Fin r → ℝ := fun u => ρ • (s j u • gv u)
  have hsj := ii_bdd (hs j) C (hC j) 0 t
  have hκ := kappa_ii Tm s hs C hC j T0 t ht htT0
  have hgc : ∀ i, Continuous fun u => gv u i := fun i =>
    Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i
  have hYi : ∀ i, IntervalIntegrable (fun u => Y u i) volume 0 t := fun i => by
    have := ((hsj.mul_continuousOn (gv_cont A⁻¹ (-A) b i).continuousOn).add
      (hκ.mul_continuousOn (hgc i).continuousOn)).const_mul ρ
    refine this.congr fun u _ => ?_
    simp [Y, gv, smul_eq_mul, mul_add]
  have hZi : ∀ i, IntervalIntegrable (fun u => Z u i) volume 0 t := fun i => by
    have := (hsj.mul_continuousOn (hgc i).continuousOn).const_mul ρ
    refine this.congr fun u _ => ?_
    simp [Z, gv, smul_eq_mul]
  have hpt : ∀ u ∈ uIcc 0 t, cross035 ρ s Tm c A b u T =
      -(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * s j u + (w ⬝ᵥ Y u + T * (w ⬝ᵥ Z u)) := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    have hsig : sigS033 s Tm u T = s j u := by simp [sigS033, hT]
    have hSS : SS033 s Tm u T = kappa033 s Tm j T0 u + s j u * T := by
      rw [Novel.SpliceCrossTermAlphaProof.SS_shift Tm s hs C hC j u T0 T fun v hv =>
        Novel.SpliceCrossTermAlphaProof.idx_between Tm j hT0 hT (by
          rw [uIcc]; exact ⟨hv.1.le, hv.2.le⟩)]
      simp only [kappa033]
      ring
    rw [cross035, hsig, hSS, lam_eq, Lam_eq c A hA]
    simp only [Y, Z, gv, dotProduct_smul, dotProduct_add, smul_eq_mul]
    ring
  have iY := ii_dot w Y t hYi
  have iZ := ii_dot w Z t hZi
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (hsj.const_mul _)
    (iY.add (iZ.const_mul T)), intervalIntegral.integral_add iY (iZ.const_mul T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    int_dot w Y t hYi, int_dot w Z t hZi]
  have hy : (fun i => ∫ u in (0:ℝ)..t, Y u i) = yCoef035 ρ s Tm A b j T0 t := by
    funext i
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp [Y, gv, smul_eq_mul, mul_add]
  have hz : (fun i => ∫ u in (0:ℝ)..t, Z u i) = zCoef035 ρ s A b j t := by
    funext i
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp [Z, gv, smul_eq_mul]
  rw [hy, hz, dotProduct_mulVec c (exp (T • A)), dotProduct_add, dotProduct_smul, smul_eq_mul]

lemma yint_ii (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (ρ : ℝ) (j : ℕ)
    (T0 t : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0) (i : Fin r) :
    IntervalIntegrable (fun u => ρ * (s j u * (A⁻¹ *ᵥ (exp (u • (-A)) *ᵥ b)) i +
      kappa033 s Tm j T0 u * (exp (u • (-A)) *ᵥ b) i)) volume 0 t :=
  (((ii_bdd (hs j) C (hC j) 0 t).mul_continuousOn (gv_cont A⁻¹ (-A) b i).continuousOn).add
    ((kappa_ii Tm s hs C hC j T0 t ht htT0).mul_continuousOn
      (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i).continuousOn)).const_mul ρ

lemma zint_ii (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ) (hC : ∀ i u, |s i u| ≤ C)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (ρ : ℝ) (j : ℕ) (t : ℝ) (i : Fin r) :
    IntervalIntegrable (fun u => ρ * (s j u * (exp (u • (-A)) *ᵥ b) i)) volume 0 t :=
  ((ii_bdd (hs j) C (hC j) 0 t).mul_continuousOn
    (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i).continuousOn).const_mul ρ

/-- `M v(t) = ∫_0^t Δ(u) M e^{−Au} b du`, componentwise. -/
lemma mulVec_vvec (M A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (Δ : ℝ → ℝ) (t : ℝ)
    (hΔ : IntervalIntegrable Δ volume 0 t) :
    M *ᵥ vvec A b Δ t = fun i => ∫ u in (0:ℝ)..t, Δ u * (M *ᵥ (exp (u • (-A)) *ᵥ b)) i := by
  funext i
  have hk : ∀ k, IntervalIntegrable (fun u => M i k * (Δ u * (exp (u • (-A)) *ᵥ b) k))
      volume 0 t := fun k =>
    (hΔ.mul_continuousOn
      (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b k).continuousOn).const_mul _
  have e : ∀ v : Fin r → ℝ, (M *ᵥ v) i = ∑ k, M i k * v k := fun v => rfl
  simp only [e, vvec]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun k _ => hk k]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `κ_{m+1} − κ_m = −Δ τ` across the meeting `τ`. -/
lemma kappa_jump (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (m : ℕ) (τ τl τr T0 T1 : ℝ)
    (hidxl : ∀ v ∈ Ioo τl τ, idx033 Tm v = m) (hidxr : ∀ v ∈ Ico τ τr, idx033 Tm v = m + 1)
    (hT0 : T0 ∈ Ioo τl τ) (hT1 : T1 ∈ Ico τ τr) (u : ℝ) :
    kappa033 s Tm (m + 1) T1 u = kappa033 s Tm m T0 u - (s (m + 1) u - s m u) * τ := by
  have h1 := Novel.SpliceCrossTermAlphaProof.SS_shift Tm s hs C hC (m + 1) u τ T1 fun v hv => by
    rw [min_eq_left hT1.1, max_eq_right hT1.1] at hv
    exact hidxr v ⟨hv.1.le, hv.2.trans hT1.2⟩
  have h2 := Novel.SpliceCrossTermAlphaProof.SS_shift Tm s hs C hC m u T0 τ fun v hv => by
    rw [min_eq_left hT0.2.le, max_eq_right hT0.2.le] at hv
    exact hidxl v ⟨hT0.1.trans hv.1, hv.2⟩
  simp only [kappa033, h1, h2]
  ring

lemma jump : Standalone.SpliceQuasiExponentialCross.jumpStatement := by
  intro Tm s hs C hC r A b ρ m τ τl τr T0 T1 t hl hr hidxl hidxr hT0 hT1 ht htT0
  have htT1 : t ≤ T1 := htT0.trans (hT0.2.le.trans hT1.1)
  have hΔ : IntervalIntegrable (fun u => s (m + 1) u - s m u) volume 0 t :=
    (ii_bdd (hs (m + 1)) C (hC _) 0 t).sub (ii_bdd (hs m) C (hC _) 0 t)
  refine ⟨?_, ?_⟩
  · rw [mulVec_vvec _ A b _ t hΔ]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, yCoef035]
    rw [← intervalIntegral.integral_sub (yint_ii Tm s hs C hC A b ρ (m + 1) T1 t ht htT1 i)
      (yint_ii Tm s hs C hC A b ρ m T0 t ht htT0 i), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [kappa_jump Tm s hs C hC m τ τl τr T0 T1 hidxl hidxr hT0 hT1 u]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zCoef035, vvec]
    rw [← intervalIntegral.integral_sub (zint_ii s hs C hC A b ρ (m + 1) t i)
      (zint_ii s hs C hC A b ρ m t i), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring

/-- If the step volatility at `u` is the same on every maturity interval after `t`,
`S^S(u, ·)` has slope `s_{j(t)}(u)` after `t`. -/
lemma SS_after (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (u t T : ℝ) (htT : t ≤ T)
    (h : ∀ v, t ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u) :
    SS033 s Tm u T = SS033 s Tm u t + s (idx033 Tm t) u * (T - t) := by
  have hiv : ∀ x y, IntervalIntegrable (fun v => sigS033 s Tm u v) volume x y := fun x y =>
    ii_bdd ((sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)) C
      (fun v => hC _ _) x y
  rw [SS033, SS033, ← intervalIntegral.integral_add_adjacent_intervals (hiv u t) (hiv t T)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun _ => s (idx033 Tm t) u) (fun v hv => by
      rw [uIcc_of_le htT] at hv
      exact h v hv.1), intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma uncorrelated : Standalone.SpliceQuasiExponentialCross.uncorrelatedStatement := by
  intro Tm s hs C hC r A hA b c ρ t ht hcase
  rcases hcase with hρ | hae
  · exact ⟨0, 0, 0, fun T _ => by simp [cross035, hρ]⟩
  set j := idx033 Tm t
  refine ⟨-(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * (∫ u in (0:ℝ)..t, s j u), yCoef035 ρ s Tm A b j t t,
    zCoef035 ρ s A b j t, fun T htT => ?_⟩
  rw [explicit Tm s hs C hC r A hA b c ρ (idx033 Tm T) t T ht rfl htT T rfl htT]
  have hae' : ∀ᵐ u ∂volume, u ∈ uIoc (0:ℝ) t → ∀ v, t ≤ v → s (idx033 Tm v) u = s j u := by
    filter_upwards [hae] with u hu hmem
    exact hu (by rw [uIoc_of_le ht] at hmem; exact ⟨hmem.1.le, hmem.2⟩)
  have hs1 : (∫ u in (0:ℝ)..t, s (idx033 Tm T) u) = ∫ u in (0:ℝ)..t, s j u :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hae'] with u hu hmem using hu hmem T htT)
  have hy : yCoef035 ρ s Tm A b (idx033 Tm T) T t = yCoef035 ρ s Tm A b j t t := by
    funext i
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae'] with u hu hmem
    have h := hu hmem
    have hSS := SS_after Tm s hs C hC u t T htT h
    simp only [kappa033, hSS, h T htT]
    ring
  have hz : zCoef035 ρ s A b (idx033 Tm T) t = zCoef035 ρ s A b j t := by
    funext i
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae'] with u hu hmem
    rw [hu hmem T htT]
  rw [hs1, hy, hz]

theorem spliceQuasiExponentialCross : Standalone.SpliceQuasiExponentialCross.statement := ⟨explicit, jump, uncorrelated⟩

end Novel.SpliceQuasiExponentialCrossProof

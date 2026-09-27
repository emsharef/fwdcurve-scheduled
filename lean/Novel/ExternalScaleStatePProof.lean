import Standalone.ExternalScaleStateP
import Novel.RecurrentLoadingRestartPProof

open Matrix NormedSpace MeasureTheory Filter Topology
open scoped Kronecker
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Standalone.ExternalScaleDrift Standalone.ExternalScaleStateP
open Novel.RecurrentLoadingDriftProof Novel.RecurrentLoadingStatePProof
open Novel.RecurrentLoadingRestartPProof
namespace Novel.ExternalScaleStatePProof

variable {p r : ℕ}

lemma wwh (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (hh : Continuous h) (t : ℝ) (a e : Fin p × Fin r)
    (x y : ℝ) : IntervalIntegrable (fun s => h s ^ 2 * (w030 Tm v M b A s t a * w030 Tm v M b A s t e))
      volume x y :=
  (ww_ii Tm v M b A t a e x y).continuousOn_mul (hh.pow 2).continuousOn

/-- `P̃^h(u) = P^h_{t₀} + ∫_{t₀}^u h(s)^2 e^{Â(t₀−s)} β βᵀ e^{Â(t₀−s)}ᵀ ds`. -/
noncomputable def Ptilh (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (t₀ u : ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  fun e f => P031 Tm v M b A h t₀ e f + ∫ s in t₀..u, h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f)

lemma quad_int_h (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (hh : Continuous h) (t₀ u : ℝ) (ht₀ : 0 ≤ t₀)
    (htu : t₀ ≤ u)
    (X : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ)
    (h1 : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s u = X *ᵥ w030 Tm v M b A s t₀)
    (h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ u →
      w030 Tm v M b A s u = X *ᵥ gvec A v b t₀ s) :
    P031 Tm v M b A h u = X * Ptilh Tm v M b A h t₀ u * Xᵀ := by
  classical
  ext ab cd
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (wwh Tm v M b A h hh u ab cd 0 t₀) (wwh Tm v M b A h hh u ab cd t₀ u)
  have hA : (∫ s in (0:ℝ)..t₀, h s ^ 2 * (w030 Tm v M b A s u ab * w030 Tm v M b A s u cd)) =
      ∑ e, ∑ f, X ab e * X cd f * P031 Tm v M b A h t₀ e f := by
    have hc : ∀ s ∈ Set.uIcc 0 t₀, h s ^ 2 * (w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
        ∑ e, ∑ f, X ab e * X cd f * (h s ^ 2 * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f)) := by
      intro s hs
      rw [h1 s hs]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hgg : ∀ e f, IntervalIntegrable (fun s => h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f))
      volume t₀ u := fun e f =>
    ((hh.pow 2).mul ((gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f))).intervalIntegrable _ _
  have hB : (∫ s in t₀..u, h s ^ 2 * (w030 Tm v M b A s u ab * w030 Tm v M b A s u cd)) =
      ∑ e, ∑ f, X ab e * X cd f * ∫ s in t₀..u, h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f) := by
    have hc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ u →
        h s ^ 2 * (w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
        ∑ e, ∑ f, X ab e * X cd f * (h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f)) := by
      filter_upwards [h2] with s hs hmem
      rw [hs hmem]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr_ae hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
  show (∫ s in (0:ℝ)..u, h s ^ 2 * (w030 Tm v M b A s u ab * w030 Tm v M b A s u cd)) = _
  rw [← hsplit, hA, hB, ← Finset.sum_add_distrib]
  simp only [mul_apply, transpose_apply, Ptilh, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by ring


lemma closed_h (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (hh : Continuous h) (t₀ u : ℝ) (ht₀ : 0 ≤ t₀)
    (htu : t₀ ≤ u) (hnone : ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ u)) :
    P031 Tm v M b A h u = Ehat030 A (u - t₀) * Ptilh Tm v M b A h t₀ u * (Ehat030 A (u - t₀))ᵀ := by
  obtain ⟨hp1, hp2⟩ := propagate p r Tm v M b A t₀ u htu hnone
  refine quad_int_h Tm v M b A h hh t₀ u ht₀ htu _ (fun s hs => ?_)
    (Eventually.of_forall fun s hs => ?_)
  · rw [Set.uIcc_of_le ht₀] at hs
    exact hp1 s hs.2
  · rw [Set.uIoc_of_le htu] at hs
    rw [hp2 s hs.1 hs.2, gvec, mulVec_mulVec, ← Ehat_add]
    congr 2; ring

lemma pEquation_h : Standalone.ExternalScaleStateP.pEquationStatement := by
  intro p r Tm v M b A h hh t₀ t t₁ ht₀ htt htt₁ hnone ab cd
  classical
  have hnone' : ∀ u, u < t₁ → ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ u) :=
    fun u hu τ hτ h => hnone τ hτ ⟨h.1, lt_of_le_of_lt h.2 hu⟩
  let X : ℝ → Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ := fun u => Ehat030 A (u - t₀)
  let Y : ℝ → Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ := fun u => Ptilh Tm v M b A h t₀ u
  let g := gvec A v b t₀ t
  have hX : ∀ i k, HasDerivAt (fun u => X u i k)
      ((Ahat030 A * X t : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i k) t :=
    fun i k => Ehat_entry_hasDerivAt A t₀ t i k
  have hXT : ∀ i k, HasDerivAt (fun u => (X u)ᵀ i k)
      ((Ahat030 A * X t : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ)ᵀ i k) t :=
    fun i k => by simpa only [transpose_apply] using hX k i
  have hY : ∀ e f, HasDerivAt (fun u => Y u e f) ((h t ^ 2 • vecMulVec g g) e f) t := by
    intro e f
    have hcont : Continuous fun s => h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f) :=
      (hh.pow 2).mul ((gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f))
    have hc := hcont.integral_hasStrictDerivAt t₀ t
    simpa only [Y, Ptilh, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, g] using
      hc.hasDerivAt.const_add (P031 Tm v M b A h t₀ e f)
  have hXY := mul_entry_hasDerivAt X Y _ _ t hX hY
  have hXYZ := mul_entry_hasDerivAt (fun u => X u * Y u) (fun u => (X u)ᵀ) _ _ t hXY hXT ab cd
  have hev : (fun u => (X u * Y u * (X u)ᵀ) ab cd) =ᶠ[nhds t] fun u => P031 Tm v M b A h u ab cd := by
    filter_upwards [Ioo_mem_nhds htt htt₁] with u hu
    rw [closed_h Tm v M b A h hh t₀ u ht₀ hu.1.le (hnone' u hu.2)]
  have hP := hXYZ.congr_of_eventuallyEq hev.symm
  have hPt : P031 Tm v M b A h t = X t * Y t * (X t)ᵀ :=
    closed_h Tm v M b A h hh t₀ t ht₀ htt.le (hnone' t htt₁)
  have hβ : X t *ᵥ g = beta030 v b := by
    simp only [X, g, gvec, mulVec_mulVec, ← Ehat_add, show t - t₀ + (t₀ - t) = 0 by ring,
      Ehat_zero, one_mulVec]
  convert hP using 1
  rw [hPt, add_mul, transpose_mul, Matrix.mul_smul, Matrix.smul_mul, sandwich_vecMulVec, hβ]
  simp only [Matrix.mul_assoc]
  rw [add_right_comm]

lemma jump_pre (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t₀ T : ℝ) (htT : t₀ < T) (hT : T ∈ Tm)
    (hnone : ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) (s : ℝ) (hs : s ≤ t₀) :
    w030 Tm v M b A s T = (Mhat030 M * Ehat030 A (T - t₀)) *ᵥ w030 Tm v M b A s t₀ := by
  have hc := (Novel.RecurrentLoadingAlgebraProof.count Tm s t₀ T 0).1 hs htT.le
  rw [count_one Tm t₀ T hT htT hnone] at hc
  rw [show w030 Tm v M b A s t₀ = fun ij : Fin p × Fin r =>
      ((M ^ count030 Tm s t₀) *ᵥ v) ij.1 * (exp ((t₀ - s) • A) *ᵥ b) ij.2 from rfl,
    ← mulVec_mulVec, Ehat_mulVec_kron, Mhat_mulVec_kron]
  have hexp : exp ((T - t₀) • A) *ᵥ (exp ((t₀ - s) • A) *ᵥ b) = exp ((T - s) • A) *ᵥ b := by
    rw [mulVec_mulVec, ← Matrix.exp_add_of_commute _ _
      ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
    congr 3; ring
  funext ij
  simp only [w030, hc, pow_succ', ← mulVec_mulVec, hexp]

lemma jump_post (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t₀ T : ℝ) (hT : T ∈ Tm)
    (hnone : ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) (s : ℝ) (hs1 : t₀ < s) (hs2 : s < T) :
    w030 Tm v M b A s T = (Mhat030 M * Ehat030 A (T - t₀)) *ᵥ gvec A v b t₀ s := by
  have hc : count030 Tm s T = 1 := count_one Tm s T hT hs2 fun τ hτ h =>
    hnone τ hτ ⟨lt_trans hs1 h.1, h.2⟩
  rw [gvec, show beta030 v b = fun ij : Fin p × Fin r => v ij.1 * b ij.2 from rfl,
    Ehat_mulVec_kron, ← mulVec_mulVec, Ehat_mulVec_kron, Mhat_mulVec_kron]
  have hexp : exp ((T - t₀) • A) *ᵥ (exp ((t₀ - s) • A) *ᵥ b) = exp ((T - s) • A) *ᵥ b := by
    rw [mulVec_mulVec, ← Matrix.exp_add_of_commute _ _
      ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
    congr 3; ring
  funext ij
  simp only [w030, hc, pow_one, hexp]

lemma restart_h : Standalone.ExternalScaleStateP.restartStatement := by
  intro p r Tm v M b A h hh t₀ T ht₀ htT hT hnone
  classical
  set E := Ehat030 (p := p) A (T - t₀)
  refine ⟨E * Ptilh Tm v M b A h t₀ T * Eᵀ, fun ab cd => ?_, ?_⟩
  · have hE : ∀ i k, Continuous fun u => Ehat030 (p := p) A (u - t₀) i k := fun i k =>
      continuous_iff_continuousAt.2 fun t => (Ehat_entry_hasDerivAt A t₀ t i k).continuousAt
    have hY : ∀ e f, Continuous fun u => Ptilh Tm v M b A h t₀ u e f := by
      intro e f
      have hcont : Continuous fun s => h s ^ 2 * (gvec A v b t₀ s e * gvec A v b t₀ s f) :=
        (hh.pow 2).mul ((gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f))
      exact continuous_iff_continuousAt.2 fun t =>
        ((hcont.integral_hasStrictDerivAt t₀ t).hasDerivAt.const_add _).continuousAt
    have hcont : Continuous fun u => (Ehat030 A (u - t₀) * Ptilh Tm v M b A h t₀ u *
        (Ehat030 A (u - t₀))ᵀ : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd := by
      simp only [mul_apply, transpose_apply]
      exact continuous_finsetSum _ fun f _ => (continuous_finsetSum _ fun e _ =>
        (hE ab e).mul (hY e f)).mul (hE cd f)
    have hev : (fun u => (Ehat030 A (u - t₀) * Ptilh Tm v M b A h t₀ u *
        (Ehat030 A (u - t₀))ᵀ : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd) =ᶠ[𝓝[<] T]
        fun u => P031 Tm v M b A h u ab cd := by
      filter_upwards [Ioo_mem_nhdsLT htT] with u hu
      rw [closed_h Tm v M b A h hh t₀ u ht₀ hu.1.le fun τ hτ h' =>
        hnone τ hτ ⟨h'.1, lt_of_le_of_lt h'.2 hu.2⟩]
    exact ((hcont.tendsto T).mono_left nhdsWithin_le_nhds).congr' hev
  · have h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ T →
        w030 Tm v M b A s T = (Mhat030 M * E) *ᵥ gvec A v b t₀ s := by
      filter_upwards [Measure.ae_ne volume T] with s hsT hs
      rw [Set.uIoc_of_le htT.le] at hs
      exact jump_post Tm v M b A t₀ T hT hnone s hs.1 (lt_of_le_of_ne hs.2 hsT)
    rw [quad_int_h Tm v M b A h hh t₀ T ht₀ htT.le _ (fun s hs => by
      rw [Set.uIcc_of_le ht₀] at hs
      exact jump_pre Tm v M b A t₀ T htT hT hnone s hs.2) h2]
    simp only [transpose_mul, Matrix.mul_assoc]

theorem externalScaleStateP : Standalone.ExternalScaleStateP.statement := ⟨pEquation_h, restart_h⟩

end Novel.ExternalScaleStatePProof

import Standalone.RecurrentLoadingRestartP
import Novel.RecurrentLoadingStatePProof

open Matrix NormedSpace MeasureTheory Filter Topology
open scoped Kronecker
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Novel.RecurrentLoadingDriftProof Novel.RecurrentLoadingStatePProof
namespace Novel.RecurrentLoadingRestartPProof

variable {p r : ℕ}

/-- `P_u = X P̃(u) Xᵀ` whenever `w(·,u) = X w(·,t₀)` before `t₀` and
`w(·,u) = X e^{Â(t₀−·)} β` almost everywhere after it. -/
lemma quad_int (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t₀ u : ℝ) (ht₀ : 0 ≤ t₀) (htu : t₀ ≤ u)
    (X : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ)
    (h1 : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s u = X *ᵥ w030 Tm v M b A s t₀)
    (h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ u →
      w030 Tm v M b A s u = X *ᵥ gvec A v b t₀ s) :
    P030 Tm v M b A u = X * Ptil Tm v M b A t₀ u * Xᵀ := by
  classical
  ext ab cd
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (ww_ii Tm v M b A u ab cd 0 t₀) (ww_ii Tm v M b A u ab cd t₀ u)
  have hA : (∫ s in (0:ℝ)..t₀, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
      ∑ e, ∑ f, X ab e * X cd f * P030 Tm v M b A t₀ e f := by
    have hc : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd =
        ∑ e, ∑ f, X ab e * X cd f * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f) := by
      intro s hs
      rw [h1 s hs]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hgg : ∀ e f, IntervalIntegrable (fun s => gvec A v b t₀ s e * gvec A v b t₀ s f)
      volume t₀ u := fun e f =>
    ((gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f)).intervalIntegrable _ _
  have hB : (∫ s in t₀..u, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
      ∑ e, ∑ f, X ab e * X cd f * ∫ s in t₀..u, gvec A v b t₀ s e * gvec A v b t₀ s f := by
    have hc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ u →
        w030 Tm v M b A s u ab * w030 Tm v M b A s u cd =
        ∑ e, ∑ f, X ab e * X cd f * (gvec A v b t₀ s e * gvec A v b t₀ s f) := by
      filter_upwards [h2] with s hs hmem
      rw [hs hmem]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr_ae hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
  show (∫ s in (0:ℝ)..u, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) = _
  rw [← hsplit, hA, hB, ← Finset.sum_add_distrib]
  simp only [mul_apply, transpose_apply, Ptil, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- `M̂` acts on Kronecker vectors through the first factor. -/
lemma Mhat_mulVec_kron (M : Matrix (Fin p) (Fin p) ℝ) (y : Fin p → ℝ) (z : Fin r → ℝ) :
    Mhat030 (r := r) M *ᵥ (fun ij : Fin p × Fin r => y ij.1 * z ij.2) =
      fun ij : Fin p × Fin r => (M *ᵥ y) ij.1 * z ij.2 := by
  classical
  funext ij
  obtain ⟨i, j⟩ := ij
  simp only [mulVec, dotProduct, Mhat030, kroneckerMap_apply, Fintype.sum_prod_type, one_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j]
  · simp only [if_true, mul_one]; ring
  · intro j' _ hj'
    simp [Ne.symm hj']
  · intro h; exact absurd (Finset.mem_univ _) h

lemma count_one (Tm : Finset ℝ) (s T : ℝ) (hT : T ∈ Tm) (hsT : s < T)
    (hnone : ∀ τ ∈ Tm, ¬ (s < τ ∧ τ < T)) : count030 Tm s T = 1 := by
  classical
  rw [count030, Finset.card_eq_one]
  refine ⟨T, ?_⟩
  ext τ
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hτ, h1, h2⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact absurd ⟨h1, h⟩ (hnone τ hτ)
    · exact h
  · rintro rfl
    exact ⟨hT, hsT, le_rfl⟩

lemma closed_continuous (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (ab cd : Fin p × Fin r) :
    Continuous fun u => (Ehat030 A (u - t₀) * Ptil Tm v M b A t₀ u *
      (Ehat030 A (u - t₀))ᵀ : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd := by
  have hE : ∀ i k, Continuous fun u => Ehat030 (p := p) A (u - t₀) i k := fun i k =>
    continuous_iff_continuousAt.2 fun t => (Ehat_entry_hasDerivAt A t₀ t i k).continuousAt
  have hY : ∀ e f, Continuous fun u => Ptil Tm v M b A t₀ u e f := by
    intro e f
    have hcont : Continuous fun s => gvec A v b t₀ s e * gvec A v b t₀ s f :=
      (gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f)
    exact continuous_iff_continuousAt.2 fun t =>
      ((hcont.integral_hasStrictDerivAt t₀ t).hasDerivAt.const_add _).continuousAt
  simp only [mul_apply, transpose_apply]
  exact continuous_finset_sum _ fun f _ => (continuous_finset_sum _ fun e _ =>
    (hE ab e).mul (hY e f)).mul (hE cd f)

lemma restartP : restartPStatement := by
  intro p r Tm v M b A t₀ T ht₀ htT hT hnone
  classical
  set E := Ehat030 (p := p) A (T - t₀)
  refine ⟨E * Ptil Tm v M b A t₀ T * Eᵀ, fun ab cd => ?_, ?_⟩
  · -- the left limit
    have hc := (closed_continuous Tm v M b A t₀ ab cd).tendsto T
    have hev : (fun u => (Ehat030 A (u - t₀) * Ptil Tm v M b A t₀ u *
        (Ehat030 A (u - t₀))ᵀ : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd) =ᶠ[𝓝[<] T] fun u => P030 Tm v M b A u ab cd := by
      filter_upwards [Ioo_mem_nhdsLT htT] with u hu
      rw [closed Tm v M b A t₀ u ht₀ hu.1.le fun τ hτ h =>
        hnone τ hτ ⟨h.1, lt_of_le_of_lt h.2 hu.2⟩]
    exact (hc.mono_left nhdsWithin_le_nhds).congr' hev
  · -- the jump at `T`
    set X := Mhat030 (r := r) M * E
    have hjump1 : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s T = X *ᵥ w030 Tm v M b A s t₀ := by
      intro s hs
      rw [Set.uIcc_of_le ht₀] at hs
      have hc := (Novel.RecurrentLoadingAlgebraProof.count Tm s t₀ T 0).1 hs.2 htT.le
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
    have hjump2 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ T →
        w030 Tm v M b A s T = X *ᵥ gvec A v b t₀ s := by
      filter_upwards [Measure.ae_ne volume T] with s hsT hs
      rw [Set.uIoc_of_le htT.le] at hs
      have hs2 : s < T := lt_of_le_of_ne hs.2 hsT
      have hc : count030 Tm s T = 1 := count_one Tm s T hT hs2 fun τ hτ h =>
        hnone τ hτ ⟨lt_trans hs.1 h.1, h.2⟩
      rw [gvec, show beta030 v b = fun ij : Fin p × Fin r => v ij.1 * b ij.2 from rfl,
        Ehat_mulVec_kron, ← mulVec_mulVec, Ehat_mulVec_kron, Mhat_mulVec_kron]
      have hexp : exp ((T - t₀) • A) *ᵥ (exp ((t₀ - s) • A) *ᵥ b) = exp ((T - s) • A) *ᵥ b := by
        rw [mulVec_mulVec, ← Matrix.exp_add_of_commute _ _
          ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
        congr 3; ring
      funext ij
      simp only [w030, hc, pow_one, hexp]
    rw [quad_int Tm v M b A t₀ T ht₀ htT.le X hjump1 hjump2]
    simp only [X, transpose_mul, Matrix.mul_assoc]

theorem recurrentLoadingRestartP : Standalone.RecurrentLoadingRestartP.statement := restartP

end Novel.RecurrentLoadingRestartPProof

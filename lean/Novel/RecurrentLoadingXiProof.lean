import Standalone.RecurrentLoadingXi
import Novel.RecurrentLoadingDiffusionProof
import Novel.RecurrentLoadingRestartQProof
import Novel.MeetingLoadingCurveProof

open MeasureTheory Matrix NormedSpace Filter Topology
open scoped NNReal ENNReal Kronecker
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Standalone.RecurrentLoadingDiffusion Standalone.RecurrentLoadingXi
open Novel.RecurrentLoadingDriftProof Novel.RecurrentLoadingStatePProof
open Novel.RecurrentLoadingRestartPProof Novel.RecurrentLoadingDiffusionProof
namespace Novel.RecurrentLoadingXiProof

variable {p r : ℕ}

lemma gt_measurable (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (e : Fin p × Fin r) :
    Measurable fun s : ℝ≥0 => gt030 Tm v M b A t₀ s e := by
  classical
  have h1 : Measurable fun s : ℝ≥0 => w030 Tm v M b A s t₀ e :=
    ((vec_measurable Tm v M t₀ e.1).comp NNReal.continuous_coe.measurable).mul
      ((expv_continuous b A t₀ e.2).measurable.comp NNReal.continuous_coe.measurable)
  have h2 : Measurable fun s : ℝ≥0 => (Ehat030 (p := p) A (t₀ - s) *ᵥ beta030 v b) e :=
    ((gvec_continuous A v b t₀ e).comp NNReal.continuous_coe).measurable
  have e1 : (fun s : ℝ≥0 => gt030 Tm v M b A t₀ s e) = fun s : ℝ≥0 =>
      if (s:ℝ) ≤ t₀ then w030 Tm v M b A s t₀ e
      else (Ehat030 (p := p) A (t₀ - s) *ᵥ beta030 v b) e := by
    funext s; simp only [gt030]; split_ifs <;> rfl
  rw [e1]
  exact Measurable.ite (measurableSet_le NNReal.continuous_coe.measurable measurable_const) h1 h2

lemma gt_bounded (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (e : Fin p × Fin r) (T' : ℝ≥0) :
    ∃ B : ℝ, ∀ s ≤ T', |gt030 Tm v M b A t₀ s e| ≤ B := by
  obtain ⟨Eb, hEb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T')).exists_bound_of_continuousOn
    (expv_continuous b A t₀ e.2).continuousOn
  obtain ⟨Gb, hGb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T')).exists_bound_of_continuousOn
    (gvec_continuous A v b t₀ e).continuousOn
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨vecBound Tm v M * Eb + |Gb|, fun s hs => ?_⟩
  have hs' : (s:ℝ) ∈ Set.Icc (0:ℝ) T' := ⟨NNReal.coe_nonneg s, by exact_mod_cast hs⟩
  have hE := hEb s hs'
  have hG := hGb s hs'
  rw [Real.norm_eq_abs] at hE hG
  have hEb0 : 0 ≤ Eb := (abs_nonneg _).trans hE
  unfold gt030
  split_ifs
  · rw [w030, abs_mul]
    have := mul_le_mul (vec_le Tm v M _ (count_le_card Tm (s:ℝ) t₀) e.1) hE (abs_nonneg _) hvb0
    linarith [abs_nonneg Gb]
  · have : |gvec A v b t₀ s e| ≤ |Gb| := hG.trans (le_abs_self _)
    have h0 : 0 ≤ vecBound Tm v M * Eb := mul_nonneg hvb0 hEb0
    simp only [gvec] at this
    linarith

section Lin
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma U4_sum (K : Fin p × Fin r → ℝ≥0 → Ω → ℝ) (c : Fin p × Fin r → ℝ)
    (hK : ∀ ab, U4 S.ℱ S.μ (K ab)) : U4 S.ℱ S.μ (fun s ω => ∑ ab, c ab * K ab s ω) := by
  let e := (finProdFinEquiv : Fin p × Fin r ≃ Fin (p * r))
  have h := Novel.SeparableMeetingRepresentationProof.domain_sum S (fun j => K (e.symm j))
    (fun j => c (e.symm j)) (fun j => hK _) Finset.univ
  convert h using 3 with s ω
  exact (Fintype.sum_equiv e.symm _ _ fun j => rfl).symm

lemma I_sum (k : Fin S.m) (K : Fin p × Fin r → ℝ≥0 → Ω → ℝ) (c : Fin p × Fin r → ℝ)
    (hK : ∀ ab, U4 S.ℱ S.μ (K ab)) (t : ℝ≥0) :
    S.I k (fun s ω => ∑ ab, c ab * K ab s ω) t =ᵐ[S.μ]
      fun ω => ∑ ab, c ab * S.I k (K ab) t ω := by
  let e := (finProdFinEquiv : Fin p × Fin r ≃ Fin (p * r))
  have h := Novel.SeparableMeetingRepresentationProof.integral_sum S k (fun j => K (e.symm j))
    (fun j => c (e.symm j)) (fun j => hK _) Finset.univ t
  have e1 : (fun s ω => ∑ ab, c ab * K ab s ω) =
      fun s ω => ∑ j ∈ Finset.univ, c (e.symm j) * K (e.symm j) s ω := by
    funext s ω; exact (Fintype.sum_equiv e.symm _ _ fun j => rfl).symm
  rw [e1]
  filter_upwards [h] with ω hω
  rw [hω]
  exact Fintype.sum_equiv e.symm _ _ fun j => rfl

end Lin

section Main
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma gh_U4 (h : ℝ≥0 → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ h) (C : ℝ)
    (hC : ∀ s ω, |h s ω| ≤ C) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (e : Fin p × Fin r) :
    U4 S.ℱ S.μ (ghInt Tm v M b A h t₀ e) :=
  U4_scaled S h hP C hC _ (gt_measurable Tm v M b A t₀ e) (gt_bounded Tm v M b A t₀ e)

lemma ghStop_U4 (h : ℝ≥0 → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ h) (C : ℝ)
    (hC : ∀ s ω, |h s ω| ≤ C) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (x : ℝ≥0) (e : Fin p × Fin r) :
    U4 S.ℱ S.μ (fun s ω => Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s *
      ghInt Tm v M b A h t₀ e s ω) := by
  have e1 : (fun s ω => Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s *
      ghInt Tm v M b A h t₀ e s ω) = fun s ω => h s ω *
      (Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s * gt030 Tm v M b A t₀ s e) := by
    funext s ω; simp only [ghInt]; ring
  rw [e1]
  refine U4_scaled S h hP C hC _ ((measurable_const.indicator measurableSet_Iic).mul
    (gt_measurable Tm v M b A t₀ e)) fun T' => ?_
  obtain ⟨B, hB⟩ := gt_bounded Tm v M b A t₀ e T'
  refine ⟨B, fun s hs => ?_⟩
  by_cases hsx : s ∈ {s | s ≤ x}
  · simpa [Set.indicator_of_mem hsx] using hB s hs
  · simp only [Set.indicator_of_notMem hsx, zero_mul, abs_zero]
    exact (abs_nonneg _).trans (hB 0 zero_le)

/-- The stopped integrand of a combination, from linearity and stopping. -/
lemma combine (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ h) (C : ℝ)
    (hC : ∀ s ω, |h s ω| ≤ C) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (x : ℝ≥0) (c : Fin p × Fin r → ℝ) :
    ∀ᵐ ω ∂S.μ, S.I k (fun s ω => ∑ e, c e * (Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s *
      ghInt Tm v M b A h t₀ e s ω)) x ω = ∑ e, c e * S.I k (ghInt Tm v M b A h t₀ e) x ω := by
  have hstop : ∀ e, (fun ω => S.I k (ghInt Tm v M b A h t₀ e) (min x x) ω) =ᵐ[S.μ]
      fun ω => S.I k (fun s ω => Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s *
        ghInt Tm v M b A h t₀ e s ω) x ω := fun e =>
    S.int_stopped k _ (fun _ => x) (gh_U4 S h hP C hC Tm v M b A t₀ e)
      (Novel.ZeroMeanReversionUpstreamBridgeProof.stopped_const S x) x
  filter_upwards [I_sum S k _ c (fun e => ghStop_U4 S h hP C hC Tm v M b A t₀ x e) x,
    ae_all_iff.2 hstop] with ω h1 h2
  rw [h1]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← h2 e, min_self]

lemma representation : representationStatement := by
  intro Ω mΩ S k h hP C hC p r Tm v M b A t₀ t₁ ht₀ hnone
  classical
  refine ⟨gh_U4 S h hP C hC Tm v M b A t₀, fun x hx1 hx2 a => ?_⟩
  have hnone' : ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ x) :=
    fun τ hτ h' => hnone τ hτ ⟨h'.1, lt_of_le_of_lt h'.2 hx2⟩
  obtain ⟨hp1, hp2⟩ := propagate p r Tm v M b A t₀ x hx1 hnone'
  set X := Ehat030 (p := p) A ((x:ℝ) - t₀)
  have hpt : xiInt Tm v M b A h x a = fun s ω => ∑ e, X a e *
      (Set.indicator {s | s ≤ x} (fun _ => (1:ℝ)) s * ghInt Tm v M b A h t₀ e s ω) := by
    funext s ω
    by_cases hsx : s ≤ x
    · have hw : w030 Tm v M b A s x = X *ᵥ gt030 Tm v M b A t₀ s := by
        by_cases hs0 : (s:ℝ) ≤ t₀
        · rw [hp1 s hs0, gt030, if_pos hs0]
        · rw [hp2 s (lt_of_not_ge hs0) (by exact_mod_cast hsx), gt030, if_neg hs0, mulVec_mulVec,
            ← Ehat_add]
          congr 2; ring
      simp only [xiInt, ghInt, Set.indicator_of_mem (show s ∈ {s | s ≤ x} from hsx), hw,
        mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    · simp [xiInt, ghInt, Set.indicator_of_notMem (show s ∉ {s | s ≤ x} from hsx)]
  filter_upwards [combine S k h hP C hC Tm v M b A t₀ x (fun e => X a e)] with ω hω
  rw [hpt, hω]
  rfl

lemma restart : restartStatement := by
  intro Ω mΩ S k h hP C hC p r Tm v M b A t₀ T ht₀ htT hT hnone
  classical
  refine ⟨fun a => ?_, ?_⟩
  · set X := Mhat030 (r := r) M * Ehat030 (p := p) A ((T:ℝ) - t₀)
    let H' : ℝ≥0 → Ω → ℝ := fun s ω => ∑ e, X a e *
      (Set.indicator {s | s ≤ T} (fun _ => (1:ℝ)) s * ghInt Tm v M b A h t₀ e s ω)
    have hxiU := ((diffusion Ω mΩ S k h hP C hC p r Tm (fun _ => 0) v M (fun _ => 0) b A T).2.1 a)
    have hH'U : U4 S.ℱ S.μ H' :=
      U4_sum S _ (fun e => X a e) fun e => ghStop_U4 S h hP C hC Tm v M b A t₀ T e
    have hcongr := Novel.MeetingLoadingCurveProof.int_congr_time S k
      (xiInt Tm v M b A h T a) H' hxiU hH'U (fun ω => by
        filter_upwards [Measure.ae_ne volume (T:ℝ)] with s hsT hpos
        have hsT' : Real.toNNReal s ≠ T := by
          intro h'; apply hsT; rw [← h', Real.coe_toNNReal s hpos.le]
        rcases lt_or_gt_of_ne hsT' with hlt | hgt
        · have hw : w030 Tm v M b A (Real.toNNReal s) T = X *ᵥ gt030 Tm v M b A t₀ (Real.toNNReal s) := by
            by_cases hs0 : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ t₀
            · rw [Novel.RecurrentLoadingRestartQProof.jump_pre Tm v M b A t₀ T htT hT hnone _ hs0,
                gt030, if_pos hs0]
            · rw [Novel.RecurrentLoadingRestartQProof.jump_post Tm v M b A t₀ T hT hnone _
                (lt_of_not_ge hs0) (by exact_mod_cast hlt), gt030, if_neg hs0]
              rfl
          have hmem : Real.toNNReal s ∈ {s | s ≤ T} := hlt.le
          simp only [xiInt, H', ghInt, Set.indicator_of_mem hmem, hw, mulVec, dotProduct,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
        · have hmem : Real.toNNReal s ∉ {s | s ≤ T} := not_le.2 hgt
          simp [xiInt, H', ghInt, Set.indicator_of_notMem hmem])
    filter_upwards [hcongr, combine S k h hP C hC Tm v M b A t₀ T (fun e => X a e)] with ω h1 h2
    rw [h1 T, h2, mulVec_mulVec]
    rfl
  · have hc : ∀ᵐ ω ∂S.μ, ∀ e, Continuous fun x => S.I k (ghInt Tm v M b A h t₀ e) x ω :=
      ae_all_iff.2 fun e => S.int_continuous k _ (gh_U4 S h hP C hC Tm v M b A t₀ e)
    filter_upwards [hc] with ω hω a
    have hE : ∀ i j, Continuous fun x : ℝ≥0 => Ehat030 (p := p) A ((x:ℝ) - t₀) i j := fun i j =>
      (continuous_iff_continuousAt.2 fun t => (Ehat_entry_hasDerivAt A t₀ t i j).continuousAt).comp
        NNReal.continuous_coe
    have hcont : Continuous fun x : ℝ≥0 => (Ehat030 A ((x:ℝ) - t₀) *ᵥ
        fun e => S.I k (ghInt Tm v M b A h t₀ e) x ω) a := by
      simp only [mulVec, dotProduct]
      exact continuous_finsetSum _ fun e _ => (hE a e).mul (hω e)
    exact (hcont.tendsto T).mono_left nhdsWithin_le_nhds

end Main

theorem recurrentLoadingXi : Standalone.RecurrentLoadingXi.statement := ⟨representation, restart⟩

end Novel.RecurrentLoadingXiProof

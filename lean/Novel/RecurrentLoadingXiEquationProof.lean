import Standalone.RecurrentLoadingXiEquation
import Novel.RecurrentLoadingXiProof
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Novel.BoundedVarianceIntegralComparisonProof

open MeasureTheory Matrix NormedSpace Filter Topology
open scoped NNReal ENNReal Kronecker
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingXi
open Standalone.RecurrentLoadingXiEquation
open Novel.RecurrentLoadingStatePProof Novel.RecurrentLoadingDiffusionProof
open Novel.RecurrentLoadingXiProof
namespace Novel.RecurrentLoadingXiEquationProof

variable {p r : ℕ}

/-- The entries of `e^{hA}` are smooth in `h`. -/
lemma exp_entry_contDiff (A : Matrix (Fin r) (Fin r) ℝ) (j j' : Fin r) :
    ContDiff ℝ 2 (fun h : ℝ => exp (h • A) j j') := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ 2 (fun h : ℝ => exp (h • A)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (exp_analytic (𝕂 := ℝ) (t • A)).contDiffAt.comp t
      (contDiff_id.smul contDiff_const).contDiffAt
  let L : Matrix (Fin r) (Fin r) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => X j j'
        map_add' := fun X Y => rfl
        map_smul' := fun c X => rfl }
  exact L.contDiff.comp h1

/-- The entries of `e^{Â(u−t₀)}` are smooth in `u`. -/
lemma Ehat_entry_contDiff (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (a e : Fin p × Fin r) :
    ContDiff ℝ 2 (fun u : ℝ => Ehat030 (p := p) A (u - t₀) a e) := by
  have e1 : (fun u : ℝ => Ehat030 (p := p) A (u - t₀) a e) =
      fun u => (1 : Matrix (Fin p) (Fin p) ℝ) a.1 e.1 * exp ((u - t₀) • A) a.2 e.2 := by
    funext u; simp only [Ehat030, kroneckerMap_apply]
  rw [e1]
  exact contDiff_const.mul ((exp_entry_contDiff A a.2 e.2).comp (contDiff_id.sub contDiff_const))

section Ito
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
open Novel.ZeroMeanReversionUpstreamBridgeProof

/-- Itô's product rule, AX-05, for a smooth deterministic weight and one integral. -/
lemma prodRule (k : Fin S.m) (G : ℝ≥0 → Ω → ℝ) (hG : U4 S.ℱ S.μ G) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 2 R) :
    U4 S.ℱ S.μ (fun s ω => R (s : ℝ) * G s ω) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, R t * S.I k G t ω =
      (∫ s in (0 : ℝ)..t, deriv R s * S.I k G (Real.toNNReal s) ω) +
        S.I k (fun s ω => R (s : ℝ) * G s ω) t ω := by
  classical
  let H : Fin 1 → Fin S.m → ℝ≥0 → Ω → ℝ := fun _ k' => if k' = k then G else fun _ _ => 0
  have hH : ∀ i k', U4 S.ℱ S.μ (H i k') := fun i k' => by
    by_cases hk : k' = k
    · simp only [H, hk, ite_true]; exact hG
    · simp only [H, hk, ite_false]; exact U4_zero S
  obtain ⟨hU4, hae⟩ := S.ito_formula 1 0 H (fun _ _ _ => 0) (fprod R 0) hH
    (fun _ => zeroDrift S) (fprod_contDiff R hR 0)
  have hint : ∀ k', (fun (s : ℝ≥0) ω => dX (fprod R 0)
      ((s : ℝ), driverForm S.I 0 H (fun _ _ _ => 0) s ω) 0 * H 0 k' s ω) =
      if k' = k then (fun (s : ℝ≥0) ω => R (s : ℝ) * G s ω) else fun _ _ => 0 := by
    intro k'
    funext s ω
    rw [fprod_dX R hR 0, if_pos rfl]
    by_cases hk : k' = k <;> simp [H, hk]
  refine ⟨by have := hU4 0 k; rwa [hint k, if_pos rfl] at this, ?_⟩
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hdf : ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I 0 H (fun _ _ _ => 0) t ω = fun _ => S.I k G t ω := by
    filter_upwards [hz] with ω hz t
    funext i
    simp only [driverForm, Pi.zero_apply, zero_add, intervalIntegral.integral_zero, add_zero]
    rw [Finset.sum_eq_single k]
    · simp [H]
    · intro k' _ hk'
      simp only [H, hk', ite_false]
      exact hz k' t
    · intro hh; exact absurd (Finset.mem_univ _) hh
  filter_upwards [hae, hdf, hz] with ω hω hdf hz
  intro t
  have h := hω t
  have hsum : (∑ i, ∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (fprod R 0)
      ((s : ℝ), driverForm S.I 0 H (fun _ _ _ => 0) s ω) i * H i k' s ω) t ω) =
      S.I k (fun s ω => R (s : ℝ) * G s ω) t ω := by
    rw [Fin.sum_univ_one, Finset.sum_eq_single k]
    · rw [hint, if_pos rfl]
    · intro k' _ hk'
      rw [hint, if_neg hk']
      exact hz k' t
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [hsum] at h
  have hdrift : (∫ s in (0 : ℝ)..t, (dT (fprod R 0)
      (s, driverForm S.I 0 H (fun _ _ _ => 0) (Real.toNNReal s) ω) +
      ∑ i, dX (fprod R 0) (s, driverForm S.I 0 H (fun _ _ _ => 0) (Real.toNNReal s) ω) i * (0 : ℝ) +
      (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ k', ∑ l', dXX (fprod R 0)
        (s, driverForm S.I 0 H (fun _ _ _ => 0) (Real.toNNReal s) ω) i i' *
          H i k' (Real.toNNReal s) ω * H i' l' (Real.toNNReal s) ω * S.c k' l' (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..t, deriv R s * S.I k G (Real.toNNReal s) ω := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Fin.sum_univ_one, fprod_dXX R hR 0, zero_mul, Finset.sum_const_zero, mul_zero,
      add_zero, fprod_dT R hR 0]
    rw [hdf (Real.toNNReal s)]
  rw [hdrift, hdf t] at h
  simpa only [fprod, Pi.zero_apply, mul_zero, zero_add] using h

end Ito

section Main
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
open Novel.ZeroMeanReversionUpstreamBridgeProof

/-- After `t₀`, the combined integrand is `β_a h`. -/
lemma after_t0 (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ≥0 → Ω → ℝ) (t₀ : ℝ) (a : Fin p × Fin r)
    (s : ℝ≥0) (hs : ¬ (s : ℝ) ≤ t₀) (ω : Ω) :
    ∑ e, Ehat030 (p := p) A ((s : ℝ) - t₀) a e * ghInt Tm v M b A h t₀ e s ω =
      beta030 v b a * h s ω := by
  have hv : Ehat030 (p := p) A ((s : ℝ) - t₀) *ᵥ (Ehat030 A (t₀ - s) *ᵥ beta030 v b) =
      beta030 v b := by
    rw [mulVec_mulVec, ← Ehat_add, show (s : ℝ) - t₀ + (t₀ - s) = 0 by ring, Ehat_zero, one_mulVec]
  have := congrFun hv a
  simp only [mulVec, dotProduct] at this
  simp only [ghInt, gt030, if_neg hs]
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mulVec, dotProduct]
  ring

/-- The increment of the combined integral after `t₀` is `β_a` times that of `I(h)`. -/
lemma incr (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ) (hU : U4 S.ℱ S.μ h)
    (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (a : Fin p × Fin r)
    (hK : ∀ e, U4 S.ℱ S.μ (fun s ω => Ehat030 (p := p) A ((s : ℝ) - t₀) a e *
      ghInt Tm v M b A h t₀ e s ω))
    (x : ℝ≥0) (hx : Real.toNNReal t₀ ≤ x) :
    ∀ᵐ ω ∂S.μ, (∑ e, S.I k (fun s ω => Ehat030 (p := p) A ((s : ℝ) - t₀) a e *
        ghInt Tm v M b A h t₀ e s ω) x ω) -
      (∑ e, S.I k (fun s ω => Ehat030 (p := p) A ((s : ℝ) - t₀) a e *
        ghInt Tm v M b A h t₀ e s ω) (Real.toNNReal t₀) ω) =
      beta030 v b a * (S.I k h x ω - S.I k h (Real.toNNReal t₀) ω) := by
  set y₀ := Real.toNNReal t₀
  set K : Fin p × Fin r → ℝ≥0 → Ω → ℝ := fun e s ω => Ehat030 (p := p) A ((s : ℝ) - t₀) a e *
      ghInt Tm v M b A h t₀ e s ω with hKdef
  let F : ℝ≥0 → Ω → ℝ := fun s ω => ∑ e, (1 : ℝ) * K e s ω
  have hFU : U4 S.ℱ S.μ F := U4_sum S K (fun _ => 1) hK
  have hFI : ∀ t, S.I k F t =ᵐ[S.μ] fun ω => ∑ e, (1 : ℝ) * S.I k (K e) t ω :=
    fun t => I_sum S k K (fun _ => 1) hK t
  let Hs : Fin 2 → ℝ≥0 → Ω → ℝ := ![F, h]
  let cs : Fin 2 → ℝ := ![1, -beta030 v b a]
  let G : ℝ≥0 → Ω → ℝ := fun s ω => ∑ j ∈ Finset.univ, cs j * Hs j s ω
  have hHs : ∀ j, U4 S.ℱ S.μ (Hs j) := fun j => by
    fin_cases j
    · exact hFU
    · exact hU
  have hGU : U4 S.ℱ S.μ G :=
    Novel.SeparableMeetingRepresentationProof.domain_sum S Hs cs hHs Finset.univ
  have hGI : ∀ t, S.I k G t =ᵐ[S.μ] fun ω => ∑ j ∈ Finset.univ, cs j * S.I k (Hs j) t ω :=
    fun t => Novel.SeparableMeetingRepresentationProof.integral_sum S k Hs cs hHs Finset.univ t
  have hG0 : ∀ s ω, ¬ (s ≤ y₀) → G s ω = 0 := by
    intro s ω hs
    have hs' : ¬ (s : ℝ) ≤ t₀ := fun h' => hs ((Real.le_toNNReal_iff_coe_le ht₀).2 h')
    simp only [G, Hs, cs, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, F, one_mul, hKdef]
    rw [after_t0 Tm v M b A h t₀ a s hs' ω]
    ring
  have hGst : (fun s ω => Set.indicator {s | s ≤ y₀} (fun _ => (1 : ℝ)) s * G s ω) = G := by
    funext s ω
    by_cases hs : s ≤ y₀
    · rw [Set.indicator_of_mem (show s ∈ {s | s ≤ y₀} from hs), one_mul]
    · rw [Set.indicator_of_notMem (show s ∉ {s | s ≤ y₀} from hs), zero_mul, hG0 s ω hs]
  have hstop := S.int_stopped k G (fun _ => y₀) hGU (stopped_const S y₀) x
  rw [hGst, min_eq_right hx] at hstop
  filter_upwards [hstop, hGI x, hGI y₀, hFI x, hFI y₀] with ω h1 h2 h3 h4 h5
  simp only [Hs, cs, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h2 h3
  simp only [one_mul] at h4 h5
  have h1' : S.I k G y₀ ω = S.I k G x ω := h1
  rw [h2, h3, h4, h5] at h1'
  linarith

/-- Almost surely every coordinate of the continuous version has continuous paths. -/
lemma continuity : continuityStatement := by
  intro Ω mΩ S k h hP C hC p r Tm v M b A t₀
  have hc : ∀ᵐ ω ∂S.μ, ∀ e, Continuous fun x => S.I k (ghInt Tm v M b A h t₀ e) x ω :=
    ae_all_iff.2 fun e => S.int_continuous k _ (gh_U4 S h hP C hC Tm v M b A t₀ e)
  filter_upwards [hc] with ω hω a
  have hE : ∀ i j, Continuous fun x : ℝ≥0 => Ehat030 (p := p) A ((x:ℝ) - t₀) i j := fun i j =>
    (continuous_iff_continuousAt.2 fun t => (Ehat_entry_hasDerivAt A t₀ t i j).continuousAt).comp
      NNReal.continuous_coe
  simp only [xiCont, mulVec, dotProduct]
  exact continuous_finsetSum _ fun e _ => (hE a e).mul (hω e)

/-- `dΞ = Â Ξ dt + β h dW` after `t₀`, almost surely and simultaneously in time. -/
lemma equation : equationStatement := by
  intro Ω mΩ S k h hP C hC p r Tm v M b A t₀ ht₀
  classical
  set y₀ := Real.toNNReal t₀
  let φ : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ := fun a e u => Ehat030 (p := p) A (u - t₀) a e
  have hφ : ∀ a e, ContDiff ℝ 2 (φ a e) := fun a e => Ehat_entry_contDiff A t₀ a e
  have hghU := gh_U4 S h hP C hC Tm v M b A t₀
  have hpr := fun a e => prodRule S k (ghInt Tm v M b A h t₀ e) (hghU e) (φ a e) (hφ a e)
  have hU : U4 S.ℱ S.μ h := by
    have := U4_scaled S h hP C hC (fun _ => 1) measurable_const
      (fun T => ⟨1, fun s _ => by simp⟩)
    simpa using this
  let K : Fin p × Fin r → Fin p × Fin r → ℝ≥0 → Ω → ℝ := fun a e s ω =>
    Ehat030 (p := p) A ((s : ℝ) - t₀) a e * ghInt Tm v M b A h t₀ e s ω
  have hK : ∀ a e, U4 S.ℱ S.μ (K a e) := fun a e => (hpr a e).1
  let SI : Fin p × Fin r → ℝ≥0 → Ω → ℝ := fun a t ω => ∑ e, S.I k (K a e) t ω
  -- the increments after `t₀`, simultaneously in time
  have hinc : ∀ a, ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, SI a (max t y₀) ω - SI a y₀ ω =
      beta030 v b a * (S.I k h (max t y₀) ω - S.I k h y₀ ω) := by
    intro a
    apply Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ
      (fun t ω => SI a (max t y₀) ω - SI a y₀ ω)
      (fun t ω => beta030 v b a * (S.I k h (max t y₀) ω - S.I k h y₀ ω))
    · filter_upwards [ae_all_iff.2 fun e => S.int_continuous k _ (hK a e)] with ω hω
      exact ((continuous_finsetSum _ fun e _ => hω e).comp
        (continuous_id.max continuous_const)).sub continuous_const
    · filter_upwards [S.int_continuous k h hU] with ω hω
      exact continuous_const.mul ((hω.comp (continuous_id.max continuous_const)).sub
        continuous_const)
    · intro t
      exact incr S k h hU Tm v M b A t₀ ht₀ a (hK a) (max t y₀) (le_max_right _ _)
  have hZc := ae_all_iff.2 fun e => S.int_continuous k _ (hghU e)
  filter_upwards [ae_all_iff.2 hinc, ae_all_iff.2 fun a => ae_all_iff.2 fun e => (hpr a e).2,
    hZc] with ω hinc hito hZc
  intro y x hy hyx a
  have hy₀ : y₀ ≤ y := Real.toNNReal_le_iff_le_coe.2 hy
  let Fi : ℝ → ℝ := fun s => ∑ e, deriv (φ a e) s *
    S.I k (ghInt Tm v M b A h t₀ e) (Real.toNNReal s) ω
  have hFc : Continuous Fi := continuous_finsetSum _ fun e _ =>
    ((hφ a e).continuous_deriv (by norm_num)).mul ((hZc e).comp continuous_real_toNNReal)
  have hY : ∀ t : ℝ≥0, xiCont (S.I k) Tm v M b A h t₀ t ω a =
      (∫ s in (0:ℝ)..t, Fi s) + SI a t ω := by
    intro t
    have hint : ∀ e ∈ Finset.univ, IntervalIntegrable (fun s => deriv (φ a e) s *
        S.I k (ghInt Tm v M b A h t₀ e) (Real.toNNReal s) ω) volume 0 t := fun e _ =>
      (((hφ a e).continuous_deriv (by norm_num)).mul
        ((hZc e).comp continuous_real_toNNReal)).intervalIntegrable _ _
    rw [show (∫ s in (0:ℝ)..t, Fi s) = ∑ e, ∫ s in (0:ℝ)..t, deriv (φ a e) s *
        S.I k (ghInt Tm v M b A h t₀ e) (Real.toNNReal s) ω from
      intervalIntegral.integral_finsetSum hint, ← Finset.sum_add_distrib]
    simp only [xiCont, mulVec, dotProduct]
    exact Finset.sum_congr rfl fun e _ => hito a e t
  have hix := hinc a x
  have hiy := hinc a y
  rw [max_eq_left (hy₀.trans hyx)] at hix
  rw [max_eq_left hy₀] at hiy
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume) (hFc.intervalIntegrable 0 (x:ℝ))
    (hFc.intervalIntegrable 0 (y:ℝ))
  have hcongr : (∫ s in (y:ℝ)..x, Fi s) =
      ∫ s in (y:ℝ)..x, (Ahat030 A *ᵥ xiCont (S.I k) Tm v M b A h t₀ (Real.toNNReal s) ω) a := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by exact_mod_cast hyx)] at hs
    have hs0 : 0 ≤ s := y.coe_nonneg.trans hs.1
    simp only [Fi, xiCont, Real.coe_toNNReal s hs0, mulVec_mulVec]
    simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun e _ => by rw [(Ehat_entry_hasDerivAt A t₀ s a e).deriv]
  rw [hY x, hY y, ← hcongr, ← hsub]
  have : SI a x ω - SI a y ω = beta030 v b a * (S.I k h x ω - S.I k h y ω) := by
    linear_combination hix - hiy
  linear_combination this

end Main

theorem recurrentLoadingXiEquation : Standalone.RecurrentLoadingXiEquation.statement := ⟨continuity, equation⟩

end Novel.RecurrentLoadingXiEquationProof

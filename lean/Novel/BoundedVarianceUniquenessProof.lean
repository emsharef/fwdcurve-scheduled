import Standalone.BoundedVarianceUniqueness
import Novel.BoundedVarianceItoProof

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceUniqueness
open Standalone.ZeroMeanReversionUpstreamBridge
open Novel.BoundedVarianceItoProof
open Novel.BoundedVarianceStateProof Novel.BoundedVarianceExistenceProof
open Novel.ZeroMeanReversionUpstreamBridgeProof (stoppedInt)
namespace Novel.BoundedVarianceUniquenessProof

lemma coefficients (m : ℕ) (k : Fin m) (lam : ℝ) (hl : 0 < lam) (tau : ℝ≥0) :
    Coefficients6 (b025Stopped lam tau) (a025Stopped k tau) := by
  classical
  obtain ⟨hb,hσ,⟨K,hK,hLip⟩,hbound⟩ := Novel.BoundedVarianceExistenceProof.coefficients lam hl m
  have hm : MeasurableSet {p : ℝ≥0 × (Fin 1 → ℝ) | p.1 ≤ tau} :=
    measurableSet_le measurable_fst measurable_const
  refine ⟨hb.ite hm measurable_const,?_,⟨K,hK,?_⟩,?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    by_cases hj : j = k
    · have h := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)
      simpa only [a025Stopped,hj,and_true,diffusion025,Function.comp_apply] using h.ite hm (measurable_const (a := (0:ℝ)))
    · simp only [a025Stopped,hj,and_false,ite_false]
      exact measurable_const
  · intro t x y
    constructor
    · by_cases ht : t ≤ tau
      · simpa only [b025Stopped,ht,ite_true] using (hLip t x y).1
      · simp only [b025Stopped,ht,ite_false,sub_self,norm_zero]
        positivity
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).2
      intro i
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).2
      intro j
      by_cases h : t ≤ tau ∧ j = k
      · have he := (norm_le_pi_norm ((diffusion025 m (t,x) - diffusion025 m (t,y)) i) j).trans
          ((norm_le_pi_norm (diffusion025 m (t,x) - diffusion025 m (t,y)) i).trans (hLip t x y).2)
        simpa only [Pi.sub_apply,a025Stopped,h,and_self,ite_true,diffusion025] using he
      · simp only [Pi.sub_apply,a025Stopped,h,ite_false,sub_self,norm_zero]
        positivity
  · intro T R hR
    obtain ⟨C,hC,hCbound⟩ := hbound T R hR
    refine ⟨C,hC,?_⟩
    intro t ht x hx
    constructor
    · by_cases h : t ≤ tau
      · simpa only [b025Stopped,h,ite_true] using (hCbound t ht x hx).1
      · simpa only [b025Stopped,h,ite_false,norm_zero] using hC
    · apply (pi_norm_le_iff_of_nonneg hC).2
      intro i
      apply (pi_norm_le_iff_of_nonneg hC).2
      intro j
      by_cases h : t ≤ tau ∧ j = k
      · have he := (norm_le_pi_norm (diffusion025 m (t,x) i) j).trans
          ((norm_le_pi_norm (diffusion025 m (t,x)) i).trans (hCbound t ht x hx).2)
        simpa only [a025Stopped,h,and_self,ite_true,diffusion025] using he
      · simpa only [a025Stopped,h,ite_false,norm_zero] using hC

lemma initial {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (b : ℝ≥0 × (Fin 1 → ℝ) → Fin 1 → ℝ)
    (σ : ℝ≥0 × (Fin 1 → ℝ) → Fin 1 → Fin S.m → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) (hX : Solution6 S b σ (fun _ _ => 0) X) :
    X 0 =ᵐ[S.μ] 0 ∧ Solution6 S b σ (X 0) X := by
  have hI : ∀ᵐ ω ∂S.μ, ∀ i j, S.I j (fun s ω => σ (s,X s ω) i j) 0 ω = 0 :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => S.int_zero j _ (hX.2.2.1 i j)
  have hz : X 0 =ᵐ[S.μ] 0 := by
    filter_upwards [hI,hX.2.2.2.2] with ω hI he
    funext i
    simpa only [hI,Finset.sum_const_zero,NNReal.coe_zero,Pi.zero_apply,intervalIntegral.integral_same,add_zero] using he 0 i
  refine ⟨hz,hX.1,hX.2.1,hX.2.2.1,hX.2.2.2.1,?_⟩
  filter_upwards [hz,hX.2.2.2.2] with ω hz he t i
  simpa only [hz,Pi.zero_apply] using he t i

lemma uniqueness : Standalone.BoundedVarianceUniqueness.uniquenessStatement := by
  intro Ω mΩ S E hB k lam hl tau X X' hX hX'
  have h := initial S _ _ X hX
  have h' := initial S _ _ X' hX'
  exact E.lipschitz_uniqueness hB 1 (b025Stopped lam tau) (a025Stopped k tau)
    (coefficients S.m k lam hl tau) X X' h.2 h'.2 (h.1.trans h'.1.symm)

lemma masked_integral (f : ℝ → ℝ) (tau t : ℝ≥0) :
    (∫ s in (0:ℝ)..(t:ℝ), if Real.toNNReal s ≤ tau then f s else 0) =
      ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), f s := by
  by_cases ht : t ≤ tau
  · rw [min_eq_left ht]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [ite_eq_left (Real.toNNReal_le_iff_le_coe.2
      (((Set.uIcc_of_le t.coe_nonneg ▸ hs).2).trans (NNReal.coe_le_coe.2 ht)))]
  · have he : (fun s => if Real.toNNReal s ≤ tau then f s else 0) =
        Set.indicator {s : ℝ | s ≤ tau} f := by
      funext s
      simp only [Set.indicator,Set.mem_ofPred_eq,Real.toNNReal_le_iff_le_coe]
    rw [he,min_eq_right (le_of_not_ge ht)]
    exact intervalIntegral.integral_indicator ⟨tau.coe_nonneg,NNReal.coe_le_coe.2 (le_of_not_ge ht)⟩

lemma stopped : stoppedStatement := by
  intro Ω mΩ S P k lam hl tau Y hsol hY
  let G : ℝ≥0 → Ω → ℝ := fun s ω => a025 (Y s ω)
  let K : ℝ≥0 → Ω → ℝ := fun s ω => b025 lam (Y s ω)
  let H : ℝ≥0 → Ω → ℝ := fun s ω => if s ≤ tau then G s ω else 0
  let L : ℝ≥0 → Ω → ℝ := fun s ω => if s ≤ tau then K s ω else 0
  have hstop : IsStoppingTime S.ℱ (fun _ : Ω => (tau : WithTop ℝ≥0)) :=
    isStoppingTime_const S.ℱ _
  have hHdef : H = stoppedInt (fun _ => tau) G := by
    funext s ω
    simp only [H,stoppedInt,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp
  have hLdef : L = stoppedInt (fun _ => tau) K := by
    funext s ω
    simp only [L,stoppedInt,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp
  have hHG : U4 S.ℱ S.μ G := hsol.2.2.1
  have hH : U4 S.ℱ S.μ H := by
    rw [hHdef]
    exact (Novel.ZeroMeanReversionUpstreamBridgeProof.stoppedInt_U5 S (fun _ => tau)
      hstop G hHG 2 (Eventually.of_forall fun ω s _ => by
        have h := (density (Y s ω)).1
        change |a025 (Y s ω)| ≤ 2
        apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
        rw [sq_abs,h]
        linarith [(bounds025 (Y s ω)).2.1]) 0).1
  have hb : Continuous (b025 lam) := continuous_iff_continuousAt.2 fun z =>
    ((Novel.BoundedVarianceStateProof.coefficient lam hl).1 z).2.2.2.2.2.1.continuousAt
  have hKpred := P.continuous_predictable K (fun t => hb.measurable.comp (hsol.1 t))
    (fun ω => hb.comp (hY ω))
  have hLpred : IsStronglyPredictable S.ℱ L := by
    rw [hLdef]
    exact Novel.ZeroMeanReversionUpstreamBridgeProof.stoppedInt_predictable S (fun _ => tau) hstop K hKpred
  have hL : LocallyIntegrableDrift S.ℱ S.μ L := by
    refine ⟨hLpred.isStronglyProgressive,fun t => Eventually.of_forall fun ω => ?_⟩
    have hbnd (s : ℝ) : |L (Real.toNNReal s) ω| ≤ 1/(2*lam) := by
      dsimp only [L,K]
      split_ifs
      · exact ((Novel.BoundedVarianceStateProof.coefficient lam hl).1 _).2.2.1
      · simp only [abs_zero]; positivity
    calc
      _ ≤ ∫⁻ _s in Set.Icc (0:ℝ) t, ENNReal.ofReal (1/(2*lam)) :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hbnd s)
      _ < ⊤ := by
        rw [setLIntegral_const,Real.volume_Icc,sub_zero]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hcoeff (i : Fin 1) (j : Fin S.m) :
      (fun t ω => a025Stopped k tau (t,fun _ => Y (min t tau) ω) i j) =
      if j = k then H else fun _ _ => 0 := by
    funext t ω
    by_cases ht : t ≤ tau
    · by_cases hj : j = k <;> simp [a025Stopped,H,G,hj,ht]
    · by_cases hj : j = k <;> simp [a025Stopped,H,G,ht,hj]
  have hdrift (i : Fin 1) :
      (fun t ω => b025Stopped lam tau (t,fun _ => Y (min t tau) ω) i) = L := by
    funext t ω
    by_cases ht : t ≤ tau <;>
      simp [b025Stopped,drift025,L,K,ht]
  have hInt : ∀ᵐ ω ∂S.μ, ∀ t, S.I k G (min t tau) ω = S.I k H t ω := by
    apply Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ _ _
      ((S.int_continuous k G hHG).mono fun ω h => h.comp (continuous_id.min continuous_const))
      (S.int_continuous k H hH)
    intro t
    change (fun ω => S.I k G (min t tau) ω) =ᵐ[S.μ] S.I k H t
    rw [hHdef]
    exact S.int_stopped k G (fun _ => tau) hHG hstop t
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t
    change Measurable[S.ℱ t] (fun ω (_ : Fin 1) => Y (min t tau) ω)
    exact (continuous_pi (fun _ : Fin 1 => continuous_id)).measurable.comp
      ((hsol.1 (min t tau)).mono (S.ℱ.mono (min_le_left _ _)) le_rfl)
  · exact Eventually.of_forall fun ω => continuous_pi fun _ =>
      (hY ω).comp (continuous_id.min continuous_const)
  · intro i j
    rw [hcoeff]
    split_ifs
    · exact hH
    · exact Novel.ZeroMeanReversionUpstreamBridgeProof.U4_zero S
  · intro i
    rw [hdrift]
    exact hL
  · have hz : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t, S.I j (fun _ _ => 0) t ω = 0 :=
      ae_all_iff.2 fun j => Novel.ZeroMeanReversionUpstreamBridgeProof.zero_integral S j
    filter_upwards [hsol.2.2.2.2,hInt,hz] with ω hy hI hz t i
    have hsum : (∑ j, S.I j (fun s ω => a025Stopped k tau (s,fun _ => Y (min s tau) ω) i j) t ω) = S.I k H t ω := by
      rw [Finset.sum_eq_single k]
      · rw [hcoeff]; simp only [ite_true]
      · intro j _ hj
        rw [hcoeff,ite_eq_right hj,hz j t]
      · simp
    rw [hsum,← hI t,zero_add]
    have hd : (∫ s in (0:ℝ)..(t:ℝ), b025Stopped lam tau
        (Real.toNNReal s,fun _ => Y (min (Real.toNNReal s) tau) ω) i) =
        ∫ s in (0:ℝ)..((min t tau:ℝ≥0):ℝ), b025 lam (Y (Real.toNNReal s) ω) := by
      change (∫ s in (0:ℝ)..(t:ℝ),
        (fun u ω => b025Stopped lam tau (u,fun _ => Y (min u tau) ω) i) (Real.toNNReal s) ω) = _
      rw [hdrift]
      exact masked_integral _ tau t
    rw [hd]
    exact hy (min t tau)

theorem boundedVarianceUniqueness : Standalone.BoundedVarianceUniqueness.statement := ⟨stopped,uniqueness⟩

end Novel.BoundedVarianceUniquenessProof

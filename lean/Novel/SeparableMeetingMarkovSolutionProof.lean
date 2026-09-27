import Standalone.SeparableMeetingMarkovSolution
import Novel.SeparableMeetingMarkovCoefficientsProof
import Novel.SeparableMeetingMarkovRealizationProof
import Novel.SeparableMeetingScaleVersionProof
import Novel.BoundedVarianceIntegralComparisonProof

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingAssembly Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization Standalone.SeparableMeetingMarkovSolution
namespace Novel.SeparableMeetingMarkovSolutionProof

lemma ind_measurable {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (k : Fin (N+1)) :
    Measurable (ind028 Td k) :=
  Measurable.ite (measurableSet_Ioc (a := lo026 Td k) (b := hi026 Td k))
    measurable_const measurable_const

lemma ind_abs {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (k : Fin (N+1)) (s : ℝ≥0) :
    |ind028 Td k s| ≤ 1 := by
  unfold ind028; split_ifs <;> simp

lemma eH_measurable (Hor : ℝ≥0) : Measurable (eH028 Hor) :=
  Measurable.ite (measurableSet_Iic (a := Hor)) measurable_const measurable_const

lemma eH_abs (Hor : ℝ≥0) (s : ℝ≥0) : |eH028 Hor s| ≤ 1 := by
  unfold eH028; split_ifs <;> simp

lemma G_continuous {d N : ℕ} (g : Fin d → Fin (N+1) → ℝ → ℝ) (Hor : ℝ≥0)
    (hg : ∀ j k x y, IntervalIntegrable (g j k) volume x y) (j : Fin d) (k : Fin (N+1)) :
    Continuous (G028 g Hor j k) :=
  (intervalIntegral.continuous_primitive (hg j k) 0).comp
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

lemma G_bound {d N : ℕ} (g : Fin d → Fin (N+1) → ℝ → ℝ) (Hor : ℝ≥0)
    (hg : ∀ j k x y, IntervalIntegrable (g j k) volume x y) :
    ∃ Gbar : ℝ, ∀ j k s, |G028 g Hor j k s| ≤ Gbar := by
  have hb (j : Fin d) (k : Fin (N+1)) : ∃ C, ∀ x ∈ Set.Icc (0:ℝ) Hor, ‖G026 (g j k) x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn
      (intervalIntegral.continuous_primitive (hg j k) 0).continuousOn
  choose C hC using hb
  refine ⟨∑ j, ∑ k, |C j k|, fun j k s => ?_⟩
  have h1 : |G028 g Hor j k s| ≤ |C j k| := by
    have := hC j k ((min s Hor : ℝ≥0) : ℝ) ⟨NNReal.coe_nonneg _, by
      exact_mod_cast min_le_right s Hor⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  refine h1.trans ?_
  calc |C j k| ≤ ∑ k', |C j k'| :=
        Finset.single_le_sum (f := fun k' => |C j k'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', |C j' k'| :=
        Finset.single_le_sum (f := fun j' => ∑ k', |C j' k'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)

lemma coefficients : Standalone.SeparableMeetingMarkovSolution.coefficientsStatement := by
  intro p d N m Td Hor beta Sigma psi g drv Kψ Lψ hZ hψc hψ hψL hg
  obtain ⟨Gbar, hGb⟩ := G_bound g Hor hg
  exact Novel.SeparableMeetingMarkovCoefficientsProof.coefficients p d N m beta Sigma psi
    (ind028 Td) (eH028 Hor) (G028 g Hor) drv Kψ Lψ Gbar hZ (fun j => (hψc j).measurable) hψ
    hψL (ind_measurable Td) (ind_abs Td) (eH_measurable Hor) (eH_abs Hor)
    (fun j k => (G_continuous g Hor hg j k).measurable) hGb

section Paths
variable {p d N : ℕ}

lemma zpart_state (z : Fin p → ℝ) (M A : Fin d → Fin (N+1) → ℝ) :
    zpart (state028 (N := N) z M A) = z := by
  funext i
  simp [zpart, state028]

lemma norm_state_le (z : Fin p → ℝ) :
    ‖state028 (N := N) z (0 : Fin d → Fin (N+1) → ℝ) 0‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => ?_
  obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
  rcases s with i' | jk | jk
  · simpa [state028] using norm_le_pi_norm z i'
  · simp [state028]
  · simp [state028]

lemma drift_zpart (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ)
    (eH : ℝ≥0 → ℝ) (G : Fin d → Fin (N+1) → ℝ≥0 → ℝ) (s : ℝ≥0)
    (x : Fin (dim028 p d N) → ℝ) :
    drift028 beta psi ind eH G (s, x) = drift028 beta psi ind eH G (s, state028 (zpart x) 0 0) := by
  unfold drift028
  rw [zpart_state]

lemma diffusion_zpart {m : ℕ} (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ)
    (eH : ℝ≥0 → ℝ) (drv : Fin d → Fin m) (s : ℝ≥0) (x : Fin (dim028 p d N) → ℝ) :
    diffusion028 Sigma psi ind eH drv (s, x) =
      diffusion028 Sigma psi ind eH drv (s, state028 (zpart x) 0 0) := by
  unfold diffusion028
  rw [zpart_state]

end Paths

section Generic
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) {p : ℕ}

/-- A process with every path continuous: bounded Borel functions of time and of
it, bounded on boxes, are in (U4) and locally integrable on every path. -/
lemma box_U4 (P : Predictability S.ℱ) (Y : ℝ≥0 → Ω → Fin p → ℝ)
    (hYm : ∀ t, Measurable[S.ℱ t] (Y t)) (hYc : ∀ ω, Continuous fun t => Y t ω)
    (F : ℝ≥0 × (Fin p → ℝ) → ℝ) (hF : Measurable F)
    (hFb : ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |F (t, z)| ≤ C) :
    U4 S.ℱ S.μ (fun s ω => F (s, Y s ω)) ∧
      LocallyIntegrableDrift S.ℱ S.μ (fun s ω => F (s, Y s ω)) := by
  have hpredi (i : Fin p) : IsStronglyPredictable S.ℱ (fun t ω => Y t ω i) :=
    P.continuous_predictable _ (fun t => (measurable_pi_apply i).comp (hYm t))
      (fun ω => (continuous_apply i).comp (hYc ω))
  have hpred : IsStronglyPredictable S.ℱ (fun s ω => F (s, Y s ω)) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := S.ℱ.predictable
    have hY : Measurable (fun q : ℝ≥0 × Ω => Y q.1 q.2) :=
      measurable_pi_iff.2 fun i => (hpredi i).measurable
    exact (hF.comp ((Upstream.ItoCalculus.measurable_fst_predictable S.ℱ).prodMk hY)).stronglyMeasurable
  -- a bound of the integrand on `[0, t]` along each path
  have hbound : ∀ (t : ℝ≥0) (ω : Ω), ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) t → |F (Real.toNNReal s, Y (Real.toNNReal s) ω)| ≤ C := by
    intro t ω
    obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0:ℝ≥0)) (b := t)).exists_bound_of_continuousOn
      (hYc ω).continuousOn
    obtain ⟨C, hC0, hC⟩ := hFb t |R| (abs_nonneg _)
    refine ⟨C, hC0, fun s hs => hC _ ?_ _ ((hR _ ⟨zero_le, ?_⟩).trans (le_abs_self _))⟩
    · exact Real.toNNReal_le_iff_le_coe.2 hs.2
    · exact Real.toNNReal_le_iff_le_coe.2 hs.2
  refine ⟨⟨hpred, fun t => Eventually.of_forall fun ω => ?_⟩,
    ⟨hpred.isStronglyProgressive, fun t => Eventually.of_forall fun ω => ?_⟩⟩
  · obtain ⟨C, hC0, hC⟩ := hbound t ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (F (Real.toNNReal s,
          Y (Real.toNNReal s) ω) ^ 2))
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (C ^ 2) := by
          refine setLIntegral_mono measurable_const fun s hs => ENNReal.ofReal_le_ofReal ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC s hs) 2
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
  · obtain ⟨C, hC0, hC⟩ := hbound t ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal |F (Real.toNNReal s,
          Y (Real.toNNReal s) ω)|)
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, ENNReal.ofReal C :=
          setLIntegral_mono measurable_const fun s hs => ENNReal.ofReal_le_ofReal (hC s hs)
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

end Generic

/-- Continuity on every `[0, n]` gives continuity in `ℝ≥0` time. -/
lemma continuous_of_nat {F : ℝ → ℝ} (hF : ∀ n : ℕ, ContinuousOn F (Set.Icc 0 (n:ℝ))) :
    Continuous fun t : ℝ≥0 => F t := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t:ℝ)
  have hc : ContinuousOn (fun t : ℝ≥0 => F t) (Set.Iic (n : ℝ≥0)) :=
    (hF n).comp NNReal.continuous_coe.continuousOn (fun u hu =>
      ⟨NNReal.coe_nonneg u, by exact_mod_cast (Set.mem_Iic.1 hu)⟩)
  exact hc.continuousAt (Iic_mem_nhds (by exact_mod_cast hn))

/-- A bounded Borel function of time and of a continuous path is interval integrable. -/
lemma path_intervalIntegrable {p : ℕ} (F : ℝ≥0 × (Fin p → ℝ) → ℝ) (hF : Measurable F)
    (hFb : ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |F (t, z)| ≤ C)
    (y : ℝ≥0 → Fin p → ℝ) (hy : Continuous y) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => F (Real.toNNReal s, y (Real.toNNReal s))) volume 0 t := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0:ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    hy.continuousOn
  obtain ⟨C, hC0, hC⟩ := hFb t |R| (abs_nonneg _)
  have hm : Measurable fun s : ℝ => F (Real.toNNReal s, y (Real.toNNReal s)) :=
    hF.comp (measurable_real_toNNReal.prodMk (hy.measurable.comp measurable_real_toNNReal))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg]
  refine Integrable.of_bound hm.aestronglyMeasurable C ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]
  have hst : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
  exact hC _ hst _ ((hR _ ⟨zero_le, hst⟩).trans (le_abs_self _))

/-- Truncating the integrand after `H` truncates the integral at `t min H`. -/
lemma integral_trunc (f : ℝ → ℝ) (Hor t : ℝ≥0)
    (hf : IntervalIntegrable f volume 0 t) :
    (∫ s in (0:ℝ)..t, if Real.toNNReal s ≤ Hor then f s else 0) =
      ∫ s in (0:ℝ)..((min t Hor : ℝ≥0) : ℝ), f s := by
  rcases le_total t Hor with h | h
  · rw [min_eq_left h]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    have : Real.toNNReal s ≤ Hor := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans h
    simp [this]
  · rw [min_eq_right h]
    have hH : (Hor:ℝ) ≤ t := by exact_mod_cast h
    have hmeas : MeasurableSet {s : ℝ | Real.toNNReal s ≤ Hor} :=
      measurableSet_le measurable_real_toNNReal measurable_const
    have he : (fun s => if Real.toNNReal s ≤ Hor then f s else 0) =
        Set.indicator {s : ℝ | Real.toNNReal s ≤ Hor} f := by
      funext s
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    have hg : IntervalIntegrable (Set.indicator {s : ℝ | Real.toNNReal s ≤ Hor} f)
        volume 0 t := ⟨hf.1.indicator hmeas, hf.2.indicator hmeas⟩
    have h1 : IntervalIntegrable (Set.indicator {s : ℝ | Real.toNNReal s ≤ Hor} f)
        volume 0 Hor := hg.mono_set (by
          rw [Set.uIcc_of_le Hor.coe_nonneg, Set.uIcc_of_le t.coe_nonneg]
          exact Set.Icc_subset_Icc le_rfl hH)
    have h2 : IntervalIntegrable (Set.indicator {s : ℝ | Real.toNNReal s ≤ Hor} f)
        volume Hor t := hg.mono_set (by
          rw [Set.uIcc_of_le hH, Set.uIcc_of_le t.coe_nonneg]
          exact Set.Icc_subset_Icc Hor.coe_nonneg le_rfl)
    rw [he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have hz : (∫ s in (Hor:ℝ)..t, Set.indicator {s : ℝ | Real.toNNReal s ≤ Hor} f s) = 0 := by
      rw [intervalIntegral.integral_of_le hH]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      have hs' : Hor < Real.toNNReal s := by
        rw [Real.lt_toNNReal_iff_coe_lt]; exact hs.1
      simp [Set.indicator_apply, not_le.mpr hs']
    rw [hz, add_zero]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le Hor.coe_nonneg] at hs
    have : Real.toNNReal s ≤ Hor := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp [Set.indicator_apply, this]

lemma hi_le {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0) (hTd : Monotone Td)
    (hlast : Td (Fin.last (N+1)) = Hor) (k : Fin (N+1)) : hi026 Td k ≤ Hor :=
  hlast ▸ hTd (Fin.le_last _)

section Pointwise
variable {Ω : Type*} {p d N m : ℕ} (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
  (hTd : Monotone Td) (hlast : Td (Fin.last (N+1)) = Hor)
  (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
  (drv : Fin d → Fin m) (Z : ℝ≥0 → Ω → Fin p → ℝ)
  (s : ℝ≥0) (ω : Ω) (x : Fin (dim028 p d N) → ℝ) (hz : zpart x = Z (min s Hor) ω)
include hz

lemma P_zdiff (i : Fin p) (l : Fin m) :
    diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv (s, x) (equiv028 p d N (Sum.inl i)) l =
      Set.indicator {s | s ≤ Hor} (fun _ => (1:ℝ)) s * Sigma (s, Z s ω) i l := by
  simp only [diffusion028, Equiv.symm_apply_apply, Sum.elim_inl, hz, eH028,
    Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with h
  · rw [min_eq_left h]
  · simp

lemma P_zdrift (i : Fin p) :
    drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor) (s, x) (equiv028 p d N (Sum.inl i)) =
      if s ≤ Hor then beta (s, Z s ω) i else 0 := by
  simp only [drift028, Equiv.symm_apply_apply, Sum.elim_inl, hz, eH028]
  split_ifs with h
  · rw [min_eq_left h, one_mul]
  · simp


include hTd hlast in
lemma P_mdiff (j : Fin d) (k : Fin (N+1)) (l : Fin m) :
    diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv (s, x)
        (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) l =
      if l = drv j then H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k) s ω else 0 := by
  simp only [diffusion028, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl, hz]
  rw [Novel.SeparableMeetingIntegralsProof.mask _ _ _ (Novel.SeparableMeetingAssemblyProof.lo_le_hi hTd k)]
  by_cases hin : lo026 Td k < s ∧ s ≤ hi026 Td k
  · have hs : s ≤ Hor := hin.2.trans (hi_le Td Hor hTd hlast k)
    simp [ind028, eH028, hin, hs, min_eq_left hs, chi028]
  · simp [ind028, hin]

include hTd hlast in
lemma P_mdrift (j : Fin d) (k : Fin (N+1)) :
    drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor) (s, x)
        (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) =
      -(H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k) s ω ^ 2 * G026 (g j k) s) := by
  simp only [drift028, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl, hz]
  rw [Novel.SeparableMeetingIntegralsProof.mask _ _ _ (Novel.SeparableMeetingAssemblyProof.lo_le_hi hTd k)]
  by_cases hin : lo026 Td k < s ∧ s ≤ hi026 Td k
  · have hs : s ≤ Hor := hin.2.trans (hi_le Td Hor hTd hlast k)
    simp [ind028, eH028, G028, hin, hs, min_eq_left hs, chi028]
  · simp [ind028, hin]

include hTd hlast in
lemma P_adrift (j : Fin d) (k : Fin (N+1)) :
    drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor) (s, x)
        (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) =
      H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k) s ω ^ 2 * 1 := by
  simp only [drift028, Equiv.symm_apply_apply, Sum.elim_inr, hz]
  rw [Novel.SeparableMeetingIntegralsProof.mask _ _ _ (Novel.SeparableMeetingAssemblyProof.lo_le_hi hTd k)]
  by_cases hin : lo026 Td k < s ∧ s ≤ hi026 Td k
  · have hs : s ≤ Hor := hin.2.trans (hi_le Td Hor hTd hlast k)
    simp [ind028, eH028, hin, hs, min_eq_left hs, chi028]
  · simp [ind028, hin]

omit hz in
lemma P_adiff (j : Fin d) (k : Fin (N+1)) (l : Fin m) :
    diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv (s, x)
        (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) l = 0 := by
  simp [diffusion028]

end Pointwise

section Main
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) {p d N : ℕ}
  (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
  (Z : ℝ≥0 → Ω → Fin p → ℝ)

lemma XH_z (t : ℝ≥0) (ω : Ω) (i : Fin p) :
    XH028 S drv Td Hor psi g Z t ω (equiv028 p d N (Sum.inl i)) = Z (min t Hor) ω i := by
  simp [XH028, state028]

lemma XH_M (t : ℝ≥0) (ω : Ω) (j : Fin d) (k : Fin (N+1)) :
    XH028 S drv Td Hor psi g Z t ω (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) =
      M0262 S (drv j) (chi028 psi Z j) (lo026 Td k) (hi026 Td k) (G026 (g j k)) t ω := by
  simp [XH028, state028]

lemma XH_A (t : ℝ≥0) (ω : Ω) (j : Fin d) (k : Fin (N+1)) :
    XH028 S drv Td Hor psi g Z t ω (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) =
      D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω := by
  simp [XH028, state028]

lemma XH_zpart (t : ℝ≥0) (ω : Ω) :
    zpart (XH028 S drv Td Hor psi g Z t ω) = Z (min t Hor) ω := by
  simp only [XH028, zpart_state]

end Main

lemma solution : Standalone.SeparableMeetingMarkovSolution.solutionStatement := by
  intro Ω mΩ S P p d N drv Td Hor hTd hlast beta Sigma psi g Kψ Lψ z0 Z hcoef hψc hψ hψL hg
    hZc hZsol
  obtain ⟨hZm, -, hZU4, -, hZeq⟩ := hZsol
  obtain ⟨hbm, hσm, -, hbox⟩ :=
    coefficients p d N S.m Td Hor beta Sigma psi g drv Kψ Lψ hcoef hψc hψ hψL hg
  obtain ⟨hbetam, -, -, hZbox⟩ := hcoef
  set XH := XH028 S drv Td Hor psi g Z with hXH
  set b := drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor) with hb
  set σ := diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv with hσ
  -- the frozen scale block
  set Y : ℝ≥0 → Ω → Fin p → ℝ := fun t ω => Z (min t Hor) ω with hY
  have hYm : ∀ t, Measurable[S.ℱ t] (Y t) :=
    fun t => (hZm (min t Hor)).mono (S.ℱ.mono (min_le_left _ _)) le_rfl
  have hYc : ∀ ω, Continuous fun t => Y t ω :=
    fun ω => (hZc ω).comp (continuous_id.min continuous_const)
  -- box bounds of the coefficients through the scale block
  have hboxF : ∀ (F : ℝ≥0 × (Fin p → ℝ) → ℝ),
      (∀ q, ∀ T R, 0 ≤ R → ∀ C, (∀ t, t ≤ T → ∀ x : Fin (dim028 p d N) → ℝ, ‖x‖ ≤ R →
        ‖b (t, x)‖ ≤ C ∧ ‖σ (t, x)‖ ≤ C) → q.1 ≤ T → ‖q.2‖ ≤ R → |F q| ≤ C) →
      ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
        ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |F (t, z)| ≤ C := by
    intro F hF T R hR
    obtain ⟨C, hC0, hC⟩ := hbox T R hR
    exact ⟨C, hC0, fun t ht z hz => hF (t, z) T R hR C hC ht hz⟩
  have hσbox (i) (l : Fin S.m) : ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |σ (t, state028 z 0 0) i l| ≤ C :=
    hboxF (fun q => σ (q.1, state028 q.2 0 0) i l) fun q T R hR C hC hT hz =>
      (Novel.SeparableMeetingMarkovCoefficientsProof.abs_coord2_le _ i l).trans
        (hC q.1 hT _ ((norm_state_le q.2).trans hz)).2
  have hbbox (i) : ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |b (t, state028 z 0 0) i| ≤ C :=
    hboxF (fun q => b (q.1, state028 q.2 0 0) i) fun q T R hR C hC hT hz => by
      have h1 := norm_le_pi_norm (b (q.1, state028 q.2 0 0)) i
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (hC q.1 hT _ ((norm_state_le q.2).trans hz)).1
  have hstate_m : Measurable fun q : ℝ≥0 × (Fin p → ℝ) =>
      (q.1, (state028 q.2 0 0 : Fin (dim028 p d N) → ℝ)) := by
    refine measurable_fst.prodMk (measurable_pi_iff.2 fun i => ?_)
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    rcases s with i' | jk | jk
    · simp only [state028, Equiv.symm_apply_apply, Sum.elim_inl]
      exact (measurable_pi_apply i').comp measurable_snd
    · simp [state028]
    · simp [state028]
  have hσeq (i) (l : Fin S.m) :
      (fun s ω => σ (s, XH s ω) i l) = fun s ω => σ (s, state028 (Y s ω) 0 0) i l := by
    funext s ω
    simp only [hσ, hXH, hY]
    rw [diffusion_zpart, XH_zpart]
  have hbeq (i) : (fun s ω => b (s, XH s ω) i) = fun s ω => b (s, state028 (Y s ω) 0 0) i := by
    funext s ω
    simp only [hb, hXH, hY]
    rw [drift_zpart, XH_zpart]
  have hσU4 (i) (l : Fin S.m) : U4 S.ℱ S.μ (fun s ω => σ (s, XH s ω) i l) := by
    rw [hσeq]
    exact (box_U4 S P Y hYm hYc (fun q => σ (q.1, state028 q.2 0 0) i l)
      ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp (hσm.comp hstate_m)))
      (hσbox i l)).1
  have hbD (i) : LocallyIntegrableDrift S.ℱ S.μ (fun s ω => b (s, XH s ω) i) := by
    rw [hbeq]
    exact (box_U4 S P Y hYm hYc (fun q => b (q.1, state028 q.2 0 0) i)
      ((measurable_pi_apply i).comp (hbm.comp hstate_m)) (hbbox i)).2
  -- the scales and their masked forms
  have hchi (j : Fin d) : U4 S.ℱ S.μ (chi028 psi Z j) := by
    have h := (box_U4 S P Z hZm hZc (psi j) (hψc j).measurable
      (fun T R hR => ⟨|Kψ|, abs_nonneg _, fun t _ z _ => (hψ j _).trans (le_abs_self _)⟩)).1
    exact h
  have hle (k : Fin (N+1)) := Novel.SeparableMeetingAssemblyProof.lo_le_hi hTd k
  have hdomH (j : Fin d) (k : Fin (N+1)) :
      U4 S.ℱ S.μ (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) :=
    Novel.SeparableMeetingIntegralsProof.domain S _ _ _ (hle k) (hchi j)
  have hGc (j : Fin d) (k : Fin (N+1)) : Continuous (G026 (g j k)) :=
    intervalIntegral.continuous_primitive (hg j k) 0
  have hcoefM (j : Fin d) (k : Fin (N+1)) :=
    Novel.SeparableMeetingCoefficientsProof.coefficient Ω mΩ S (drv j) (chi028 psi Z j)
      (lo026 Td k) (hi026 Td k) (hle k) (hchi j) (G026 (g j k)) (hGc j k)
  have hord (j : Fin d) (k : Fin (N+1)) :=
    Novel.SeparableMeetingCoefficientsProof.ordinary Ω mΩ S _ (hdomH j k) (fun _ => 1)
      continuous_const
  refine ⟨?_, ?_, hσU4, hbD, ?_⟩
  · -- adaptedness
    intro t
    have hi : ∀ i, Measurable[S.ℱ t] (fun ω => XH t ω i) := by
      intro i
      obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
      rcases s with i' | ⟨j, k⟩ | ⟨j, k⟩
      · simp only [hXH, XH_z]
        exact (measurable_pi_apply i').comp (hYm t)
      · simp only [hXH, XH_M]
        exact (hcoefM j k).1 t
      · simp only [hXH, XH_A]
        exact (hord j k).1 t
    letI : MeasurableSpace Ω := S.ℱ t
    exact measurable_pi_iff.2 hi
  · -- continuity
    have hM : ∀ᵐ ω ∂S.μ, ∀ (n : ℕ) (j : Fin d) (k : Fin (N+1)),
        ContinuousOn (fun t => M0262 S (drv j) (chi028 psi Z j) (lo026 Td k) (hi026 Td k)
          (G026 (g j k)) t ω) (Set.Icc 0 (n:ℝ)) := by
      simp only [ae_all_iff]
      exact fun n j k => by exact_mod_cast (hcoefM j k).2.1 n
    have hA : ∀ᵐ ω ∂S.μ, ∀ (n : ℕ) (j : Fin d) (k : Fin (N+1)),
        ContinuousOn (fun t => D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k))
          (fun _ => 1) t ω) (Set.Icc 0 (n:ℝ)) := by
      simp only [ae_all_iff]
      exact fun n j k => ((hord j k).2 n).mono fun ω hω => by exact_mod_cast hω.2.1
    filter_upwards [hM, hA] with ω hMω hAω
    refine continuous_pi fun i => ?_
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    rcases s with i' | ⟨j, k⟩ | ⟨j, k⟩
    · simp only [hXH, XH_z]
      exact (continuous_apply i').comp (hYc ω)
    · simp only [hXH, XH_M]
      exact continuous_of_nat fun n => hMω n j k
    · simp only [hXH, XH_A]
      exact continuous_of_nat fun n => hAω n j k
  · -- the equation
    have hstop : ∀ᵐ ω ∂S.μ, ∀ (i' : Fin p) (l : Fin S.m) (t : ℝ≥0),
        S.I l (fun s ω => Sigma (s, Z s ω) i' l) (min t Hor) ω =
          S.I l (fun s ω => σ (s, XH s ω) (equiv028 p d N (Sum.inl i')) l) t ω := by
      simp only [ae_all_iff]
      intro i' l
      have hfun : (fun s ω => σ (s, XH s ω) (equiv028 p d N (Sum.inl i')) l) =
          fun s ω => Set.indicator {s | s ≤ Hor} (fun _ => (1:ℝ)) s * Sigma (s, Z s ω) i' l := by
        funext s ω
        rw [hσ]
        exact P_zdiff Td Hor Sigma psi drv Z s ω (XH s ω) (XH_zpart S drv Td Hor psi g Z s ω) i' l
      refine Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ _ _ ?_
        (S.int_continuous l _ (hσU4 _ l)) fun t => ?_
      · filter_upwards [S.int_continuous l _ (hZU4 i' l)] with ω hω
        exact hω.comp (continuous_id.min continuous_const)
      · have h := S.int_stopped l (fun s ω => Sigma (s, Z s ω) i' l) (fun _ => Hor) (hZU4 i' l)
          (Novel.ZeroMeanReversionUpstreamBridgeProof.stopped_const S Hor) t
        rw [hfun]
        exact h
    have hzero : ∀ᵐ ω ∂S.μ, ∀ (l : Fin S.m) (t : ℝ≥0), S.I l (fun _ _ => (0:ℝ)) t ω = 0 :=
      ae_all_iff.2 fun l => Novel.ZeroMeanReversionUpstreamBridgeProof.zero_integral S l
    filter_upwards [hZeq, hstop, hzero] with ω hZe hst hz0 t i
    obtain ⟨s', rfl⟩ := (equiv028 p d N).surjective i
    rcases s' with i' | ⟨j, k⟩ | ⟨j, k⟩
    · have e1 : XH t ω (equiv028 p d N (Sum.inl i')) = Z (min t Hor) ω i' := XH_z S drv Td Hor psi g Z t ω i'
      have e2 : (state028 z0 0 0 : Fin (dim028 p d N) → ℝ) (equiv028 p d N (Sum.inl i')) = z0 i' := by
        simp [state028]
      have hbF : ∀ (T : ℝ≥0) (R : ℝ), 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          ∀ t, t ≤ T → ∀ z, ‖z‖ ≤ R → |beta (t, z) i'| ≤ C := by
        intro T R hR
        obtain ⟨C, hC0, hC⟩ := hZbox T R hR
        refine ⟨C, hC0, fun t ht z hz => ?_⟩
        have h1 := norm_le_pi_norm (beta (t, z)) i'
        rw [Real.norm_eq_abs] at h1
        exact h1.trans (hC t ht z hz).1
      have e4 : (∫ s in (0:ℝ)..(t:ℝ), b (Real.toNNReal s, XH (Real.toNNReal s) ω)
            (equiv028 p d N (Sum.inl i'))) =
          ∫ s in (0:ℝ)..((min t Hor : ℝ≥0) : ℝ), beta (Real.toNNReal s, Z (Real.toNNReal s) ω) i' := by
        have hfun : (fun s : ℝ => b (Real.toNNReal s, XH (Real.toNNReal s) ω)
              (equiv028 p d N (Sum.inl i'))) =
            fun s => if Real.toNNReal s ≤ Hor then beta (Real.toNNReal s, Z (Real.toNNReal s) ω) i'
              else 0 := by
          funext s
          rw [hb]
          exact P_zdrift Td Hor beta psi g Z (Real.toNNReal s) ω _
            (XH_zpart S drv Td Hor psi g Z _ ω) i'
        rw [hfun, integral_trunc _ Hor t (path_intervalIntegrable (fun q => beta q i')
          ((measurable_pi_apply i').comp hbetam) hbF (fun s => Z s ω) (hZc ω) t)]
      rw [e1, e2, e4, Finset.sum_congr rfl (fun l _ => (hst i' l t).symm)]
      exact hZe (min t Hor) i'
    · have e1 : XH t ω (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) =
          S.I (drv j) (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) t ω -
            D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (G026 (g j k)) t ω := by
        rw [hXH, XH_M]
        simp [M0262, J026]
      have e2 : (state028 z0 0 0 : Fin (dim028 p d N) → ℝ)
          (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) = 0 := by
        simp [state028]
      have hint (l : Fin S.m) : (fun s ω => σ (s, XH s ω) (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) l) =
          if l = drv j then H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k) else fun _ _ => 0 := by
        funext s ω
        rw [hσ, P_mdiff Td Hor hTd hlast Sigma psi drv Z s ω _ (XH_zpart S drv Td Hor psi g Z s ω)]
        split_ifs <;> rfl
      have e3 : (∑ l, S.I l (fun s ω => σ (s, XH s ω)
            (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) l) t ω) =
          S.I (drv j) (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) t ω := by
        rw [Finset.sum_eq_single (drv j)]
        · rw [hint, if_pos rfl]
        · intro l _ hl
          rw [hint, if_neg hl]
          exact hz0 l t
        · intro h; exact absurd (Finset.mem_univ _) h
      have e4 : (∫ s in (0:ℝ)..(t:ℝ), b (Real.toNNReal s, XH (Real.toNNReal s) ω)
            (equiv028 p d N (Sum.inr (Sum.inl (j, k))))) =
          -D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (G026 (g j k)) t ω := by
        rw [D026, ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le t.coe_nonneg] at hs
        simp only
        rw [hb, P_mdrift Td Hor hTd hlast beta psi g Z _ ω _ (XH_zpart S drv Td Hor psi g Z _ ω),
          Real.coe_toNNReal s hs.1]
      rw [e1, e2, e3, e4]
      ring
    · have e1 : XH t ω (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) =
          D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω :=
        XH_A S drv Td Hor psi g Z t ω j k
      have e2 : (state028 z0 0 0 : Fin (dim028 p d N) → ℝ)
          (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) = 0 := by
        simp [state028]
      have e3 : (∑ l, S.I l (fun s ω => σ (s, XH s ω)
            (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) l) t ω) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have hfun : (fun s ω => σ (s, XH s ω) (equiv028 p d N (Sum.inr (Sum.inr (j, k)))) l) =
            fun _ _ => (0:ℝ) := by
          funext s ω
          rw [hσ]
          exact P_adiff Td Hor Sigma psi drv s _ j k l
        rw [hfun]
        exact hz0 l t
      have e4 : (∫ s in (0:ℝ)..(t:ℝ), b (Real.toNNReal s, XH (Real.toNNReal s) ω)
            (equiv028 p d N (Sum.inr (Sum.inr (j, k))))) =
          D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω := by
        rw [D026]
        apply intervalIntegral.integral_congr
        intro s _
        simp only
        rw [hb, P_adrift Td Hor hTd hlast beta psi g Z _ ω _ (XH_zpart S drv Td Hor psi g Z _ ω)]
      rw [e1, e2, e3, e4]
      ring

theorem separableMeetingMarkovSolution : Standalone.SeparableMeetingMarkovSolution.statement :=
  ⟨coefficients, solution⟩

end Novel.SeparableMeetingMarkovSolutionProof

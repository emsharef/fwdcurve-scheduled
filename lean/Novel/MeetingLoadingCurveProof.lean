import Standalone.MeetingLoadingCurve
import Novel.SeparableMeetingRepresentationProof
import Novel.SeparableMeetingShapesProof

open MeasureTheory Filter
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve
namespace Novel.MeetingLoadingCurveProof

lemma count_le (n R : ℕ) (s T : ℝ) : count029 n R s T ≤ n + R :=
  (Finset.card_filter_le _ _).trans (by simp)

lemma count_anti (n R : ℕ) (T : ℝ) : Antitone fun s : ℝ => count029 n R s T := by
  intro s s' h
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_le_of_lt h hj.2.1, hj.2.2⟩

lemma count_mono (n R : ℕ) (s : ℝ) : Monotone fun T : ℝ => count029 n R s T := by
  intro T T' h
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.1, hj.2.2.trans h⟩

/-- A bound for the loadings that occur. -/
noncomputable def bound029 (a : ℕ → ℝ) (n R : ℕ) : ℝ := ∑ j ∈ Finset.range (n + R + 1), |a j|

lemma abs_le_bound (a : ℕ → ℝ) (n R j : ℕ) (hj : j ≤ n + R) : |a j| ≤ bound029 a n R :=
  Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

lemma time_coe (n : ℕ) : ((time029 n : ℝ≥0) : ℝ) = (n : ℝ) + 1/2 := by
  simp [time029]

lemma upper_le (n : ℕ) (l : Fin (n+1)) : upper029 n l ≤ time029 n := by
  unfold upper029
  split_ifs with h
  · exact le_rfl
  · rw [← NNReal.coe_le_coe, time_coe, NNReal.coe_natCast]
    have : ((n - l + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - (l:ℕ) + 1 ≤ n)
    linarith

lemma lower_le_upper (n : ℕ) (l : Fin (n+1)) : lower029 n l ≤ upper029 n l := by
  unfold upper029 lower029
  split_ifs with h
  · rw [← NNReal.coe_le_coe, time_coe, h]
    simp only [Nat.sub_zero, NNReal.coe_natCast]
    linarith
  · exact_mod_cast (by omega : n - (l:ℕ) ≤ n - l + 1)

lemma count_value (n R : ℕ) (i : ℕ) (hi : i ≤ R) (s : ℝ) (m : ℕ) (hm1 : (m:ℝ) < s)
    (hm2 : s < (m:ℝ) + 1) : count029 n R s (mat029 n i) = n + i - m := by
  have hset : ((Finset.range (n+R)).filter fun j : ℕ => s < (j:ℝ) + 1 ∧
      (j:ℝ) + 1 ≤ mat029 n i) = Finset.Ico m (n+i) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    simp only [mat029]
    constructor
    · rintro ⟨-, h1, h2⟩
      constructor
      · have h3 : (m:ℝ) < (j:ℝ) + 1 := hm1.trans h1
        have h4 : m < j + 1 := by exact_mod_cast h3
        omega
      · have h3 : ((j + 1 : ℕ) : ℝ) < ((n + i + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h4 := Nat.cast_lt.1 h3
        omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_, ?_⟩
      · have : (m:ℝ) + 1 ≤ (j:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h1
        linarith
      · have h3 : ((j + 1 : ℕ) : ℝ) ≤ ((n + i : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at h3
        linarith
  rw [count029, hset, Nat.card_Ico]

/-- The stopped step volatility equals the sum of the elementary pieces off the
integer times `0, ..., n`. -/
lemma pointwise {Ω : Type*} (a : ℕ → ℝ) (n R : ℕ) (i : Fin (R+1)) (s : ℝ≥0) (ω : Ω)
    (hs : ∀ m : ℕ, m ≤ n → (s:ℝ) ≠ m) :
    Set.indicator {s | s ≤ time029 n} (fun _ => (1:ℝ)) s *
        sigma029 (Ω := Ω) a n R (mat029 n i) s ω =
      ∑ l : Fin (n+1), a (i + l) *
        ((fun _ : Ω => (1:ℝ)) ω * Set.indicator (Set.Ioc (lower029 n l) (upper029 n l)) 1 s) := by
  by_cases hst : s ≤ time029 n
  · set m := ⌊(s:ℝ)⌋₊ with hmdef
    have hm0 : (m:ℝ) ≤ s := Nat.floor_le (NNReal.coe_nonneg s)
    have hm2 : (s:ℝ) < (m:ℝ) + 1 := Nat.lt_floor_add_one _
    have hsn : (s:ℝ) ≤ (n:ℝ) + 1/2 := by rw [← time_coe]; exact_mod_cast hst
    have hmn : m ≤ n := by
      have : (m:ℝ) < (n:ℝ) + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hm1 : (m:ℝ) < s := lt_of_le_of_ne hm0 (fun h => hs m hmn h.symm)
    have hcount := count_value n R i (Nat.lt_succ_iff.1 i.isLt) s m hm1 hm2
    let l0 : Fin (n+1) := ⟨n - m, by omega⟩
    have hmem : s ∈ Set.Ioc (lower029 n l0) (upper029 n l0) := by
      simp only [Set.mem_Ioc, lower029, upper029, l0]
      constructor
      · rw [← NNReal.coe_lt_coe]
        simp only [NNReal.coe_natCast]
        rw [show n - (n - m) = m by omega]
        exact hm1
      · split_ifs with h
        · exact hst
        · rw [← NNReal.coe_le_coe]
          simp only [NNReal.coe_natCast]
          rw [show n - (n - m) + 1 = m + 1 by omega]
          push_cast
          exact hm2.le
    rw [Finset.sum_eq_single l0]
    · simp only [Set.indicator_of_mem (show s ∈ {s | s ≤ time029 n} from hst),
        Set.indicator_of_mem hmem, sigma029, hcount, Pi.one_apply, one_mul, mul_one]
      congr 1
      simp only [l0]
      omega
    · intro l _ hl
      have hnot : s ∉ Set.Ioc (lower029 n l) (upper029 n l) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne (fun h : (l:ℕ) = n - m => hl (Fin.ext h)) with hlt | hgt
        · -- the piece lies to the right of s
          rw [← NNReal.coe_lt_coe] at h1
          simp only [lower029, NNReal.coe_natCast] at h1
          have : ((m + 1 : ℕ) : ℝ) ≤ ((n - l : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ n - l)
          push_cast at this
          linarith
        · -- the piece lies to the left of s
          have hl0 : (l:ℕ) ≠ 0 := by omega
          simp only [upper029, hl0, ite_false] at h2
          rw [← NNReal.coe_le_coe] at h2
          simp only [NNReal.coe_natCast] at h2
          have : ((n - l + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n - l + 1 ≤ m)
          linarith
      simp [Set.indicator_of_notMem hnot]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hz : ∀ l : Fin (n+1), s ∉ Set.Ioc (lower029 n l) (upper029 n l) :=
      fun l h => hst (h.2.trans (upper_le n l))
    simp [Set.indicator_of_notMem (show s ∉ {s | s ≤ time029 n} from hst),
      Set.indicator_of_notMem (hz _)]

section Det
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- Deterministic bounded Borel integrands are in (U4). -/
lemma det_U4 (h : ℝ≥0 → ℝ) (hm : Measurable h) (C : ℝ) (hb : ∀ s, |h s| ≤ C) :
    U4 S.ℱ S.μ (fun s (_ : Ω) => h s) := by
  refine ⟨(hm.comp (Upstream.ItoCalculus.measurable_fst_predictable S.ℱ)).stronglyMeasurable,
    fun t => Eventually.of_forall fun ω => ?_⟩
  calc (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (h (Real.toNNReal s) ^ 2))
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (C ^ 2) := by
        refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb _) 2
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

/-- Integrands that agree, on every path, at almost every positive time have almost
surely equal integrals at every time: the zero-variance argument of AX-03c. -/
lemma int_congr_time (k : Fin S.m) (H H' : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H)
    (hH' : U4 S.ℱ S.μ H')
    (hHH' : ∀ ω, ∀ᵐ s ∂(volume : Measure ℝ), 0 < s →
      H (Real.toNNReal s) ω = H' (Real.toNNReal s) ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k H t ω = S.I k H' t ω := by
  set K : ℝ≥0 → Ω → ℝ := (1 : ℝ) • H + (-1 : ℝ) • H' with hKdef
  have hK0 : ∀ ω, ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → K (Real.toNNReal s) ω = 0 := by
    intro ω
    filter_upwards [hHH' ω] with s hs hpos
    simp [hKdef, hs hpos]
  have hKsq : ∀ ω (T : ℝ≥0),
      (∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((K (Real.toNNReal s) ω) ^ 2)) = 0 := by
    intro ω T
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := Measure.ae_ne volume 0
    have hz : (fun s : ℝ => ENNReal.ofReal ((K (Real.toNNReal s) ω) ^ 2)) =ᵐ[volume.restrict
        (Set.Icc (0:ℝ) T)] fun _ => 0 := by
      filter_upwards [ae_restrict_of_ae (hK0 ω), ae_restrict_of_ae hne,
        ae_restrict_mem measurableSet_Icc] with s h1 h2 h3
      simp [h1 (lt_of_le_of_ne h3.1 (Ne.symm h2))]
    rw [lintegral_congr_ae hz, lintegral_zero]
  have hKU4 : U4 S.ℱ S.μ K := by
    refine ⟨?_, fun t => Eventually.of_forall fun ω => ?_⟩
    · have h1 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H) := hH.1
      have h2 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H') := hH'.1
      exact (h1.const_smul (1 : ℝ)).add (h2.const_smul (-1 : ℝ))
    · rw [hKsq]; exact ENNReal.zero_lt_top
  have hKU5 : ∀ T, U5 S.ℱ S.μ K T := fun T => ⟨hKU4, by
    have : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((K (Real.toNNReal s) ω) ^ 2)) =
        fun _ => 0 := funext fun ω => hKsq ω T
    rw [this, lintegral_zero]
    exact ENNReal.zero_lt_top⟩
  have hzero : ∀ t, S.I k K t =ᵐ[S.μ] 0 := by
    intro t
    have hM := S.int_product_martingale k k K K t (hKU5 t) (hKU5 t)
    set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k K (min u t) ω * S.I k K (min u t) ω -
      ∫ s in (0 : ℝ)..(min u t : ℝ≥0), K (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
        S.c k k (Real.toNNReal s) with hMdef
    have hcond : S.μ[M t | S.ℱ 0] =ᵐ[S.μ] M 0 := hM.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t)
    have hM0 : M 0 =ᵐ[S.μ] 0 := by
      filter_upwards [S.int_zero k K hKU4] with ω hω
      simp [hMdef, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t), hω]
    have hMt : M t =ᵐ[S.μ] fun ω => (S.I k K t ω) ^ 2 := by
      refine Eventually.of_forall fun ω => ?_
      have hint : (∫ s in (0 : ℝ)..(t : ℝ), K (Real.toNNReal s) ω *
          K (Real.toNNReal s) ω * S.c k k (Real.toNNReal s)) = 0 := by
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
        · simp
        · filter_upwards [hK0 ω] with s hs hmem
          rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hmem
          simp [hs hmem.1]
      simp only [hMdef, min_self, hint, sub_zero, sq]
    have hL2 : MemLp (S.I k K t) 2 S.μ := (S.int_martingale k K t (hKU5 t)).2 t le_rfl
    have hint : ∫ ω, (S.I k K t ω) ^ 2 ∂S.μ = 0 := by
      calc ∫ ω, (S.I k K t ω) ^ 2 ∂S.μ = ∫ ω, M t ω ∂S.μ := integral_congr_ae hMt.symm
        _ = ∫ ω, (S.μ[M t | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
        _ = ∫ ω, M 0 ω ∂S.μ := integral_congr_ae hcond
        _ = 0 := by rw [integral_congr_ae hM0]; simp
    have hsq := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      hL2.integrable_sq).mp hint
    filter_upwards [hsq] with ω hω
    exact pow_eq_zero_iff two_ne_zero |>.mp hω
  have heach : ∀ t, S.I k H t =ᵐ[S.μ] S.I k H' t := by
    intro t
    filter_upwards [hzero t, S.int_linear k H H' 1 (-1) hH hH' t] with ω h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul,
      Pi.zero_apply] at h1 h2
    linarith
  exact Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ _ _
    (S.int_continuous k H hH) (S.int_continuous k H' hH') heach

end Det

lemma sigma_measurable (a : ℕ → ℝ) (n R : ℕ) (T : ℝ) :
    Measurable fun s : ℝ≥0 => a (count029 n R s T) :=
  (measurable_from_nat (f := a)).comp
    ((count_anti n R T).comp_monotone NNReal.coe_mono).measurable

lemma curve : Standalone.MeetingLoadingCurve.curveStatement := by
  intro Ω mΩ S k a n R
  have hU : ∀ T : ℝ, U4 S.ℱ S.μ (sigma029 (Ω := Ω) a n R T) := fun T =>
    det_U4 S (fun s => a (count029 n R s T)) (sigma_measurable a n R T) (bound029 a n R)
      (fun s => abs_le_bound a n R _ (count_le n R s T))
  refine ⟨hU, ?_⟩
  rw [ae_all_iff]
  intro i
  set T := mat029 n i
  set t := time029 n
  let J : Fin (n+1) → ℝ≥0 → Ω → ℝ := fun l s ω =>
    (fun _ : Ω => (1:ℝ)) ω * Set.indicator (Set.Ioc (lower029 n l) (upper029 n l)) 1 s
  have hJU : ∀ l, U4 S.ℱ S.μ (J l) := fun l =>
    det_U4 S (fun s => 1 * Set.indicator (Set.Ioc (lower029 n l) (upper029 n l)) 1 s)
      (measurable_const.mul (measurable_one.indicator measurableSet_Ioc)) 1
      (fun s => by by_cases h : s ∈ Set.Ioc (lower029 n l) (upper029 n l) <;> simp [h])
  let H2 : ℝ≥0 → Ω → ℝ := fun s ω => ∑ l : Fin (n+1), a (i + l) * J l s ω
  have hH2 : U4 S.ℱ S.μ H2 :=
    Novel.SeparableMeetingRepresentationProof.domain_sum S J (fun l => a (i + l)) hJU Finset.univ
  let Hs : ℝ≥0 → Ω → ℝ := fun s ω =>
    Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * sigma029 a n R T s ω
  have hb0 : 0 ≤ bound029 a n R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hHs : U4 S.ℱ S.μ Hs :=
    det_U4 S (fun s => Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * a (count029 n R s T))
      ((measurable_const.indicator measurableSet_Iic).mul (sigma_measurable a n R T))
      (bound029 a n R) (fun s => by
        by_cases h : s ∈ {s | s ≤ t}
        · simp only [Set.indicator_of_mem h, one_mul]
          exact abs_le_bound a n R _ (count_le n R s T)
        · simp only [Set.indicator_of_notMem h, zero_mul, abs_zero]
          exact hb0)
  -- the exceptional times
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∉ ((Finset.range (n+1)).image fun m : ℕ => (m:ℝ) : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Finset.finite_toSet _).measure_zero volume)
  have hcongr := int_congr_time S k Hs H2 hHs hH2 (fun ω => by
    filter_upwards [hnull] with s hs hpos
    apply pointwise a n R i (Real.toNNReal s) ω
    intro m hm h
    rw [Real.coe_toNNReal s hpos.le] at h
    apply hs
    rw [Finset.coe_image, Finset.coe_range]
    exact ⟨m, Set.mem_Iio.2 (by omega), h.symm⟩)
  have hst := S.int_stopped k (sigma029 a n R T) (fun _ => t) (hU T)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.stopped_const S t) t
  have hsum := Novel.SeparableMeetingRepresentationProof.integral_sum S k J (fun l => a (i + l))
    hJU Finset.univ t
  have helem : ∀ l : Fin (n+1), (fun ω => S.I k (J l) t ω) =ᵐ[S.μ]
      fun ω => (1:ℝ) * (S.B k (min t (upper029 n l)) ω - S.B k (min t (lower029 n l)) ω) :=
    fun l => S.int_elementary k (lower029 n l) (upper029 n l) (fun _ => 1) (lower_le_upper n l)
      measurable_const ⟨1, fun _ => by simp⟩ t
  filter_upwards [hst, hcongr, hsum, ae_all_iff.2 helem] with ω h1 h2 h3 h4
  calc S.I k (sigma029 a n R T) t ω = S.I k (sigma029 a n R T) (min t t) ω := by rw [min_self]
    _ = S.I k Hs t ω := h1
    _ = S.I k H2 t ω := h2 t
    _ = ∑ l : Fin (n+1), a (i + l) * S.I k (J l) t ω := h3
    _ = _ := by
        apply Finset.sum_congr rfl
        intro l _
        rw [h4 l, min_eq_right (upper_le n l),
          min_eq_right ((lower_le_upper n l).trans (upper_le n l)), one_mul]
        rfl

lemma drift : Standalone.MeetingLoadingCurve.driftStatement := by
  intro a n R s T
  have hm : Measurable fun u : ℝ => a (count029 n R s u) :=
    (measurable_from_nat (f := a)).comp (count_mono n R s).measurable
  have hint : IntervalIntegrable (fun u => a (count029 n R s u)) volume s T :=
    (intervalIntegrable_const (c := bound029 a n R)).mono_fun' hm.aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖a (count029 n R s u)‖ ≤ bound029 a n R
        rw [Real.norm_eq_abs]
        exact abs_le_bound a n R _ (count_le n R s u))
  exact Novel.SeparableMeetingShapesProof.drift _ s T hint

theorem meetingLoadingCurve : Standalone.MeetingLoadingCurve.statement := ⟨curve, drift⟩

end Novel.MeetingLoadingCurveProof

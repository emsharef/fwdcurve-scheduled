import Standalone.RecurrenceNecessityCurve
import Novel.MeetingLoadingCurveProof
import Novel.RecurrentLoadingXiProof
import Novel.RecurrenceNecessityReductionProof

open MeasureTheory Filter Matrix NormedSpace
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve Standalone.RecurrenceNecessityCurve
namespace Novel.RecurrenceNecessityCurveProof

variable {r : ℕ}

lemma lam_cont (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    Continuous (lam032 c A b) := by
  unfold lam032
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Novel.RecurrenceNecessityReductionProof.phi_cont A b i)

/-- A continuous function on `[0, ∞)` is bounded on every `[0, T']`. -/
lemma bdd_of_cont (f : ℝ≥0 → ℝ) (hf : Continuous f) (T' : ℝ≥0) :
    ∃ B : ℝ, ∀ s ≤ T', |f s| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ≥0)) (b := T')).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨B, fun s hs => by simpa [Real.norm_eq_abs] using hB s ⟨zero_le, hs⟩⟩

section Det
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- A deterministic Borel integrand bounded on compacts is in (U4). -/
lemma U4_det (g : ℝ≥0 → ℝ) (hg : Measurable g) (hb : ∀ T' : ℝ≥0, ∃ B : ℝ, ∀ s ≤ T', |g s| ≤ B) :
    U4 S.ℱ S.μ (fun s (_ : Ω) => g s) := by
  simpa using Novel.RecurrentLoadingDiffusionProof.U4_scaled S (fun _ _ => (1:ℝ))
    stronglyMeasurable_const 1 (fun _ _ => by simp) g hg hb

end Det

lemma lamT_cont (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (T : ℝ) :
    Continuous fun s : ℝ≥0 => lam032 c A b (T - s) :=
  (lam_cont c A b).comp (continuous_const.sub NNReal.continuous_coe)

lemma sigma_meas (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (n R : ℕ) (T : ℝ) :
    Measurable fun s : ℝ≥0 => a (count029 n R s T) * lam032 c A b (T - s) :=
  (Novel.MeetingLoadingCurveProof.sigma_measurable a n R T).mul (lamT_cont c A b T).measurable

lemma sigma_bdd (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (n R : ℕ) (T : ℝ) (T' : ℝ≥0) :
    ∃ B : ℝ, ∀ s ≤ T', |a (count029 n R s T) * lam032 c A b (T - s)| ≤ B := by
  obtain ⟨B, hB⟩ := bdd_of_cont _ (lamT_cont c A b T) T'
  refine ⟨Novel.MeetingLoadingCurveProof.bound029 a n R * B, fun s hs => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (Novel.MeetingLoadingCurveProof.abs_le_bound a n R _
    (Novel.MeetingLoadingCurveProof.count_le n R s T)) (hB s hs) (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma xi_cont (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u : ℝ) (j : Fin r) :
    Continuous fun s : ℝ≥0 => (exp ((u - s) • A) *ᵥ b) j :=
  (Novel.RecurrenceNecessityReductionProof.phi_cont A b j).comp
    (continuous_const.sub NNReal.continuous_coe)

lemma xi_meas (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) (lj : Fin (n+1) × Fin r) :
    Measurable fun s : ℝ≥0 => Set.indicator (Set.Ioc (lower029 n lj.1) (upper029 n lj.1)) 1 s *
      (exp (((upper029 n lj.1 : ℝ) - s) • A) *ᵥ b) lj.2 :=
  (measurable_one.indicator measurableSet_Ioc).mul (xi_cont A b _ lj.2).measurable

lemma xi_bdd (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ) (lj : Fin (n+1) × Fin r)
    (T' : ℝ≥0) : ∃ B : ℝ, ∀ s ≤ T',
      |Set.indicator (Set.Ioc (lower029 n lj.1) (upper029 n lj.1)) 1 s *
        (exp (((upper029 n lj.1 : ℝ) - s) • A) *ᵥ b) lj.2| ≤ B := by
  obtain ⟨B, hB⟩ := bdd_of_cont _ (xi_cont A b (upper029 n lj.1) lj.2) T'
  refine ⟨B, fun s hs => ?_⟩
  by_cases h : s ∈ Set.Ioc (lower029 n lj.1) (upper029 n lj.1)
  · rw [Set.indicator_of_mem h, Pi.one_apply, one_mul]; exact hB s hs
  · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact (abs_nonneg _).trans (hB 0 zero_le)

/-- On each piece the shape factors through the piece's right end. -/
lemma lam_split (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (T τ s : ℝ) :
    (c ᵥ* exp ((T - τ) • A)) ⬝ᵥ (exp ((τ - s) • A) *ᵥ b) = lam032 c A b (T - s) := by
  rw [lam032, ← dotProduct_mulVec, mulVec_mulVec,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
  congr 3
  ring

/-- The stopped volatility equals the combination of the `ξ` integrands off the integer times
`0, ..., n`. -/
lemma pointwise032 {Ω : Type*} (a : ℕ → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (n R : ℕ) (i : Fin (R+1)) (s : ℝ≥0) (ω : Ω) (hs : ∀ m : ℕ, m ≤ n → (s:ℝ) ≠ m) :
    Set.indicator {s | s ≤ time029 n} (fun _ => (1:ℝ)) s *
        sigma032 (Ω := Ω) a c A b n R (mat029 n i) s ω =
      ∑ lj : Fin (n+1) × Fin r, coef032 a c A n i lj * xiInt032 (Ω := Ω) A b n lj s ω := by
  have P : Set.indicator {s | s ≤ time029 n} (fun _ => (1:ℝ)) s * a (count029 n R s (mat029 n i)) =
      ∑ l : Fin (n+1), a (i + l) *
        ((fun _ : Ω => (1:ℝ)) ω * Set.indicator (Set.Ioc (lower029 n l) (upper029 n l)) 1 s) :=
    Novel.MeetingLoadingCurveProof.pointwise a n R i s ω hs
  simp only [sigma032, xiInt032, coef032]
  rw [← mul_assoc, P, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← lam_split c A b (mat029 n i) (upper029 n l) s]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma curve : Standalone.RecurrenceNecessityCurve.curveStatement := by
  intro Ω mΩ S k a r c b A n R
  have hU : ∀ T : ℝ, U4 S.ℱ S.μ (sigma032 (Ω := Ω) a c A b n R T) := fun T =>
    U4_det S _ (sigma_meas a c A b n R T) (sigma_bdd a c A b n R T)
  have hXU : ∀ lj, U4 S.ℱ S.μ (xiInt032 (Ω := Ω) A b n lj) := fun lj =>
    U4_det S _ (xi_meas A b n lj) (xi_bdd A b n lj)
  refine ⟨hU, hXU, ?_⟩
  rw [ae_all_iff]
  intro i
  set T := mat029 n i
  set t := time029 n
  let H2 : ℝ≥0 → Ω → ℝ := fun s ω =>
    ∑ lj : Fin (n+1) × Fin r, coef032 a c A n i lj * xiInt032 A b n lj s ω
  have hH2 : U4 S.ℱ S.μ H2 :=
    Novel.RecurrentLoadingXiProof.U4_sum S (xiInt032 A b n) (coef032 a c A n i) hXU
  let Hs : ℝ≥0 → Ω → ℝ := fun s ω =>
    Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * sigma032 a c A b n R T s ω
  have hHs : U4 S.ℱ S.μ Hs := by
    refine U4_det S (fun s => Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s *
      (a (count029 n R s T) * lam032 c A b (T - s)))
      ((measurable_const.indicator measurableSet_Iic).mul (sigma_meas a c A b n R T))
      fun T' => ?_
    obtain ⟨B, hB⟩ := sigma_bdd a c A b n R T T'
    refine ⟨B, fun s hs => ?_⟩
    by_cases h : s ∈ {s | s ≤ t}
    · simp only [Set.indicator_of_mem h, one_mul]; exact hB s hs
    · simp only [Set.indicator_of_notMem h, zero_mul, abs_zero]
      exact (abs_nonneg _).trans (hB 0 zero_le)
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∉ ((Finset.range (n+1)).image fun m : ℕ => (m:ℝ) : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Finset.finite_toSet _).measure_zero volume)
  have hcongr := Novel.MeetingLoadingCurveProof.int_congr_time S k Hs H2 hHs hH2 (fun ω => by
    filter_upwards [hnull] with s hs hpos
    apply pointwise032 a c b A n R i (Real.toNNReal s) ω
    intro m hm h
    rw [Real.coe_toNNReal s hpos.le] at h
    apply hs
    rw [Finset.coe_image, Finset.coe_range]
    exact ⟨m, Set.mem_Iio.2 (by omega), h.symm⟩)
  have hst := S.int_stopped k (sigma032 a c A b n R T) (fun _ => t) (hU T)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.stopped_const S t) t
  have hsum := Novel.RecurrentLoadingXiProof.I_sum S k (xiInt032 A b n) (coef032 a c A n i) hXU t
  filter_upwards [hst, hcongr, hsum] with ω h1 h2 h3
  calc S.I k (sigma032 a c A b n R T) t ω = S.I k (sigma032 a c A b n R T) (min t t) ω := by
        rw [min_self]
    _ = S.I k Hs t ω := h1
    _ = S.I k H2 t ω := h2 t
    _ = _ := h3

theorem recurrenceNecessityCurve : Standalone.RecurrenceNecessityCurve.statement := curve

end Novel.RecurrenceNecessityCurveProof

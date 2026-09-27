import Standalone.RecurrentLoadingDrift
import Novel.RecurrentLoadingAlgebraProof
import Novel.SeparableMeetingShapesProof
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.Prod

open Matrix NormedSpace MeasureTheory Filter
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
namespace Novel.RecurrentLoadingDriftProof

variable {p r : ℕ}

lemma exp_continuous (A : Matrix (Fin r) (Fin r) ℝ) : Continuous fun x : ℝ => exp (x • A) := by
  open scoped Matrix.Norms.Operator in
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const A t).continuousAt

lemma shape_continuous (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) :
    Continuous (shape030 c b A) :=
  continuous_const.dotProduct ((exp_continuous A).matrix_mulVec continuous_const)

lemma count_le_card (Tm : Finset ℝ) (s t : ℝ) : count030 Tm s t ≤ Tm.card :=
  Finset.card_filter_le _ _

lemma count_mono (Tm : Finset ℝ) (s : ℝ) : Monotone fun t => count030 Tm s t := by
  intro t t' h
  apply Finset.card_le_card
  intro τ hτ
  simp only [Finset.mem_filter] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, hτ.2.2.trans h⟩

lemma count_anti (Tm : Finset ℝ) (t : ℝ) : Antitone fun s => count030 Tm s t := by
  intro s s' h
  apply Finset.card_le_card
  intro τ hτ
  simp only [Finset.mem_filter] at hτ ⊢
  exact ⟨hτ.1, lt_of_le_of_lt h hτ.2.1, hτ.2.2⟩

lemma count_measurable2 (Tm : Finset ℝ) : Measurable fun q : ℝ × ℝ => count030 Tm q.1 q.2 := by
  classical
  have h : (fun q : ℝ × ℝ => count030 Tm q.1 q.2) =
      fun q => ∑ τ ∈ Tm, if q.1 < τ ∧ τ ≤ q.2 then 1 else 0 := by
    funext q; rw [count030, Finset.card_filter]
  rw [h]
  refine Finset.measurable_sum _ fun τ _ => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

lemma idx_mono (D : Finset ℝ) : Monotone fun x => idx030 x D := by
  intro x x' h
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hd.2.trans h⟩

/-- A bound for the loadings that occur on a schedule. -/
noncomputable def loadBound (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Tm.card + 1), |loading030 u v M i|

lemma loading_le (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (i : ℕ)
    (hi : i ≤ Tm.card) : |loading030 u v M i| ≤ loadBound Tm u v M :=
  Finset.single_le_sum (f := fun i => |loading030 u v M i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- Bounded Borel functions are interval integrable. -/
lemma ii_bdd {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)))
    (C : ℝ) (hC : ∀ x ∈ Set.uIcc a b, |f x| ≤ C) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hf
    ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => by
      show ‖f x‖ ≤ C
      rw [Real.norm_eq_abs]; exact hC x (Set.uIoc_subset_uIcc hx)))

lemma sigma_ii (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s a₁ b₁ : ℝ) :
    IntervalIntegrable (fun y => sigma030 Tm u v M c b A s y) volume a₁ b₁ := by
  have hl : IntervalIntegrable (fun y => loading030 u v M (count030 Tm s y)) volume a₁ b₁ :=
    ii_bdd ((measurable_from_nat (f := loading030 u v M)).comp
        (count_mono Tm s).measurable).aestronglyMeasurable (loadBound Tm u v M)
      (fun y _ => loading_le Tm u v M _ (count_le_card Tm s y))
  exact hl.mul_continuousOn
    ((shape_continuous c b A).comp (continuous_id.sub continuous_const)).continuousOn

lemma sigma_measurable2 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) :
    Measurable fun q : ℝ × ℝ => sigma030 Tm u v M c b A q.1 q.2 :=
  ((measurable_from_nat (f := loading030 u v M)).comp (count_measurable2 Tm)).mul
    ((shape_continuous c b A).measurable.comp (measurable_snd.sub measurable_fst))

/-- `J(·, t)` agrees with a Borel function on `s ≤ t`. -/
lemma J_measurable (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) :
    ∃ G : ℝ → ℝ, Measurable G ∧ ∀ s ≤ t, J030 Tm u v M c b A s t = G s := by
  classical
  let F : ℝ × ℝ → ℝ := fun q =>
    if q.1 < q.2 ∧ q.2 ≤ t then sigma030 Tm u v M c b A q.1 q.2 else 0
  have hFm : Measurable F :=
    Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) (sigma_measurable2 Tm u v M c b A)
      measurable_const
  refine ⟨fun s => ∫ y, F (s, y), (hFm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable, fun s hs => ?_⟩
  rw [J030, intervalIntegral.integral_of_le hs, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext y
  simp only [Set.indicator_apply, Set.mem_Ioc, F]

/-- A bound for the loading vectors `M^n v` that occur. -/
noncomputable def vecBound (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Tm.card + 1), ∑ i, |((M ^ n) *ᵥ v) i|

lemma vec_le (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (n : ℕ)
    (hn : n ≤ Tm.card) (i : Fin p) : |((M ^ n) *ᵥ v) i| ≤ vecBound Tm v M := by
  have h1 : |((M ^ n) *ᵥ v) i| ≤ ∑ i', |((M ^ n) *ᵥ v) i'| :=
    Finset.single_le_sum (f := fun i' => |((M ^ n) *ᵥ v) i'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hmem : n ∈ Finset.range (Tm.card + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hn)
  have h2 := Finset.single_le_sum (s := Finset.range (Tm.card + 1))
    (f := fun n' => ∑ i', |((M ^ n') *ᵥ v) i'|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hmem
  exact h1.trans h2

lemma vec_measurable (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (t : ℝ)
    (i : Fin p) : Measurable fun s => ((M ^ count030 Tm s t) *ᵥ v) i :=
  (measurable_from_nat (f := fun n => ((M ^ n) *ᵥ v) i)).comp (count_anti Tm t).measurable

lemma expv_continuous (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (j : Fin r) :
    Continuous fun s : ℝ => (exp ((t - s) • A) *ᵥ b) j :=
  (continuous_apply j).comp (((exp_continuous A).comp (continuous_const.sub continuous_id)).matrix_mulVec
    continuous_const)

lemma ax01 : ax01Statement := by
  intro p r Tm u v M c b A s T
  exact Novel.SeparableMeetingShapesProof.drift _ s T (sigma_ii Tm u v M c b A s s T)

/-- A step function of a Borel `ℕ`-valued index, bounded by `N`, is interval integrable. -/
lemma step_ii (F : ℕ → ℝ) (N : ℕ) (g : ℝ → ℕ) (hg : Measurable g) (hN : ∀ y, g y ≤ N)
    (a b : ℝ) : IntervalIntegrable (fun y => F (g y)) volume a b :=
  ii_bdd ((measurable_from_nat (f := F)).comp hg).aestronglyMeasurable
    (∑ n ∈ Finset.range (N + 1), |F n|) (fun y _ =>
      Finset.single_le_sum (f := fun n => |F n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le (hN y))))

lemma k_ii (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (D : Finset ℝ) (ab : Fin p × Fin r) (a₁ b₁ : ℝ) :
    IntervalIntegrable (fun y => k030 u M c A y D ab) volume a₁ b₁ :=
  (step_ii (fun n => (u ᵥ* (M ^ n)) ab.1) D.card (fun y => idx030 y D) (idx_mono D).measurable
    (fun y => Finset.card_filter_le _ _) a₁ b₁).mul_continuousOn
    ((continuous_apply ab.2).comp (continuous_const.matrix_vecMul (exp_continuous A))).continuousOn

lemma drift : driftStatement := by
  intro p r Tm u v M c b A t x ht hx
  classical
  set D := dist030 Tm t
  set k := k030 u M c A x D
  set K := Kvec030 u M c A x D
  set w : ℝ → Fin p × Fin r → ℝ := fun s => w030 Tm v M b A s t with hw
  obtain ⟨G, hGm, hG⟩ := J_measurable Tm u v M c b A t
  have hfac : ∀ s, s ≤ t → ∀ y, 0 ≤ y →
      sigma030 Tm u v M c b A s (t + y) = k030 u M c A y D ⬝ᵥ w s := by
    intro s hs y hy
    have h := Novel.RecurrentLoadingAlgebraProof.factor p r Tm u v M c b A s t (t + y) hs
      (by linarith)
    rwa [add_sub_cancel_left] at h
  have hsplit : ∀ s, s ≤ t →
      (∫ y in s..(t + x), sigma030 Tm u v M c b A s y) = J030 Tm u v M c b A s t + K ⬝ᵥ w s := by
    intro s hs
    rw [← intervalIntegral.integral_add_adjacent_intervals (sigma_ii Tm u v M c b A s s t)
      (sigma_ii Tm u v M c b A s t (t + x))]
    congr 1
    have e1 : (∫ y in t..(t + x), sigma030 Tm u v M c b A s y) =
        ∫ y in (0:ℝ)..x, sigma030 Tm u v M c b A s (t + y) := by
      rw [intervalIntegral.integral_comp_add_left (fun y => sigma030 Tm u v M c b A s y) t,
        add_zero]
    have e2 : (∫ y in (0:ℝ)..x, sigma030 Tm u v M c b A s (t + y)) =
        ∫ y in (0:ℝ)..x, ∑ ab, k030 u M c A y D ab * w s ab := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hx] at hy
      exact hfac s hs y hy.1
    rw [e1, e2, intervalIntegral.integral_finsetSum
      (fun ab _ => (k_ii u M c A D ab 0 x).mul_const _)]
    simp only [intervalIntegral.integral_mul_const]
    rfl
  -- bounds on [0, t]
  obtain ⟨Sb, hSb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
    (shape_continuous c b A).continuousOn
  have hGb : ∀ s ∈ Set.uIcc 0 t, |G s| ≤ loadBound Tm u v M * Sb * t := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    rw [← hG s hs.2, J030]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := loadBound Tm u v M * Sb) (f := fun y => sigma030 Tm u v M c b A s y) (fun y hy => by
        rw [Set.uIoc_of_le hs.2] at hy
        simp only [sigma030, norm_mul, Real.norm_eq_abs]
        have h1 := loading_le Tm u v M _ (count_le_card Tm s y)
        have h2 := hSb (y - s) ⟨by linarith [hy.1], by linarith [hy.2, hs.1]⟩
        rw [Real.norm_eq_abs] at h2
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2] : (0:ℝ) ≤ t - s)] at h
    have hLS : 0 ≤ loadBound Tm u v M * Sb :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ((norm_nonneg _).trans (hSb 0 ⟨le_rfl, ht⟩))
    calc |∫ y in s..t, sigma030 Tm u v M c b A s y| ≤ loadBound Tm u v M * Sb * (t - s) := h
      _ ≤ loadBound Tm u v M * Sb * t := by
          apply mul_le_mul_of_nonneg_left _ hLS; linarith [hs.1]
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- integrability in `s` on `[0, t]`
  have hww : ∀ a b' : Fin p × Fin r, IntervalIntegrable (fun s => w s a * w s b') volume 0 t := by
    intro a b'
    have h1 : IntervalIntegrable (fun s => ((M ^ count030 Tm s t) *ᵥ v) a.1 *
        ((M ^ count030 Tm s t) *ᵥ v) b'.1) volume 0 t :=
      ii_bdd ((vec_measurable Tm v M t a.1).mul (vec_measurable Tm v M t b'.1)).aestronglyMeasurable
        (vecBound Tm v M * vecBound Tm v M) (fun s _ => by
          rw [abs_mul]
          exact mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1)
            (vec_le Tm v M _ (count_le_card Tm s t) b'.1) (abs_nonneg _) hvb0)
    have h2 := h1.mul_continuousOn
      ((expv_continuous b A t a.2).mul (expv_continuous b A t b'.2)).continuousOn
    have e : (fun s => w s a * w s b') = fun s => (((M ^ count030 Tm s t) *ᵥ v) a.1 *
        ((M ^ count030 Tm s t) *ᵥ v) b'.1) * ((exp ((t - s) • A) *ᵥ b) a.2 *
        (exp ((t - s) • A) *ᵥ b) b'.2) := by
      funext s; simp only [hw, w030]; ring
    rw [e]; exact h2
  have hwG : ∀ a : Fin p × Fin r, IntervalIntegrable (fun s => w s a * G s) volume 0 t := by
    intro a
    have h1 : IntervalIntegrable (fun s => ((M ^ count030 Tm s t) *ᵥ v) a.1 * G s) volume 0 t :=
      ii_bdd ((vec_measurable Tm v M t a.1).mul hGm).aestronglyMeasurable
        (vecBound Tm v M * (loadBound Tm u v M * Sb * t)) (fun s hs => by
          rw [abs_mul]
          exact mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1) (hGb s hs) (abs_nonneg _)
            hvb0)
    have h2 := h1.mul_continuousOn (expv_continuous b A t a.2).continuousOn
    have e : (fun s => w s a * G s) = fun s => (((M ^ count030 Tm s t) *ᵥ v) a.1 * G s) *
        (exp ((t - s) • A) *ᵥ b) a.2 := by
      funext s; simp only [hw, w030]; ring
    rw [e]; exact h2
  have hS : ∀ a : Fin p × Fin r,
      IntervalIntegrable (fun s => ∑ b', w s a * w s b' * K b') volume 0 t := by
    intro a
    have h := IntervalIntegrable.sum Finset.univ (fun b' _ => (hww a b').mul_const (K b'))
    convert h using 1
    funext s
    simp
  -- the pointwise algebra
  have hpt : ∀ s ∈ Set.uIcc 0 t, alpha030 Tm u v M c b A s (t + x) =
      ∑ a, k a * (∑ b', w s a * w s b' * K b' + w s a * G s) := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    rw [alpha030, hsplit s hs.2, hfac s hs.2 x hx, hG s hs.2]
    simp only [dotProduct]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum, add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum
    (fun a _ => ((hS a).add (hwG a)).const_mul (k a))]
  simp only [dotProduct, mulVec, Pi.add_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hS a) (hwG a),
    intervalIntegral.integral_finsetSum (fun b' _ => (hww a b').mul_const _)]
  simp only [intervalIntegral.integral_mul_const]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  simp only [hw]
  rw [hG s hs.2]

theorem recurrentLoadingDrift : Standalone.RecurrentLoadingDrift.statement := ⟨ax01, drift⟩

end Novel.RecurrentLoadingDriftProof

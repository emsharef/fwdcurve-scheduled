import Standalone.RecurrentLoadingStateQ
import Novel.RecurrentLoadingRestartPProof

open Matrix NormedSpace MeasureTheory Filter Topology
open scoped Kronecker
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingStateQ
open Novel.RecurrentLoadingDriftProof Novel.RecurrentLoadingStatePProof
namespace Novel.RecurrentLoadingStateQProof

variable {p r : ℕ}

lemma k_zero (Tm : Finset ℝ) (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) : k030 u M c A 0 (dist030 Tm y) = gamma030 u c := by
  have h := (Novel.RecurrentLoadingAlgebraProof.count Tm y y y 0).2
  rw [add_zero, count_zero_of_none Tm y y fun τ _ h => by linarith [h.1, h.2]] at h
  funext ij
  simp [k030, h, gamma030]

/-- On a meeting interval the volatility is `γ · w`. -/
lemma sigma_gamma (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s y : ℝ) (hsy : s ≤ y) :
    sigma030 Tm u v M c b A s y = gamma030 u c ⬝ᵥ w030 Tm v M b A s y := by
  have h := Novel.RecurrentLoadingAlgebraProof.factor p r Tm u v M c b A s y y hsy le_rfl
  rwa [sub_self, k_zero] at h

/-- `w(s,t) J(s,t)` is interval integrable on `[0, t]`. -/
lemma wJ_ii (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (ht : 0 ≤ t) (a : Fin p × Fin r) :
    IntervalIntegrable (fun s => w030 Tm v M b A s t a * J030 Tm u v M c b A s t) volume 0 t := by
  obtain ⟨G, hGm, hG⟩ := J_measurable Tm u v M c b A t
  obtain ⟨Sb, hSb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
    (shape_continuous c b A).continuousOn
  have hLS : 0 ≤ loadBound Tm u v M * Sb :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ((norm_nonneg _).trans (hSb 0 ⟨le_rfl, ht⟩))
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
    calc |∫ y in s..t, sigma030 Tm u v M c b A s y| ≤ loadBound Tm u v M * Sb * (t - s) := h
      _ ≤ loadBound Tm u v M * Sb * t := by
          apply mul_le_mul_of_nonneg_left _ hLS; linarith [hs.1]
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : IntervalIntegrable (fun s => ((M ^ count030 Tm s t) *ᵥ v) a.1 * G s) volume 0 t :=
    ii_bdd ((vec_measurable Tm v M t a.1).mul hGm).aestronglyMeasurable
      (vecBound Tm v M * (loadBound Tm u v M * Sb * t)) (fun s hs => by
        rw [abs_mul]
        exact mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1) (hGb s hs) (abs_nonneg _)
          hvb0)
  have h2 := h1.mul_continuousOn (expv_continuous b A t a.2).continuousOn
  refine h2.congr_ae ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => ?_)
  rw [Set.uIoc_of_le ht] at hs
  simp only [w030, hG s hs.2]
  ring

lemma qEquation : qEquationStatement := by
  intro p r Tm u v M c b A t₀ t t₁ ht₀ htt htt₁ hnone a
  classical
  have hnone' : ∀ x, x < t₁ → ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ x) :=
    fun x hx τ hτ h => hnone τ hτ ⟨h.1, lt_of_le_of_lt h.2 hx⟩
  let X : ℝ → Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ := fun x => Ehat030 A (x - t₀)
  let γ := gamma030 u c
  let φ : ℝ → Fin p × Fin r → ℝ := fun y => (X y)ᵀ *ᵥ γ
  let gv := gvec A v b t₀
  have hXc : ∀ i k, Continuous fun x => X x i k := fun i k =>
    continuous_iff_continuousAt.2 fun t => (Ehat_entry_hasDerivAt A t₀ t i k).continuousAt
  have hφc : ∀ f, Continuous fun y => φ y f := by
    intro f
    simp only [φ, mulVec, dotProduct, transpose_apply]
    exact continuous_finset_sum _ fun g _ => (hXc g f).mul continuous_const
  have hφi : ∀ f x y, IntervalIntegrable (fun y => φ y f) volume x y :=
    fun f x y => (hφc f).intervalIntegrable x y
  let Φ : Fin p × Fin r → ℝ → ℝ := fun f x => ∫ y in t₀..x, φ y f
  have hΦc : ∀ f, Continuous (Φ f) := fun f => intervalIntegral.continuous_primitive (hφi f) t₀
  have hgc : ∀ e, Continuous fun s => gv s e := gvec_continuous A v b t₀
  -- `w` on `[t₀, t₁)`
  have hwpre : ∀ x, t₀ ≤ x → x < t₁ → ∀ s, s ≤ t₀ →
      w030 Tm v M b A s x = X x *ᵥ w030 Tm v M b A s t₀ :=
    fun x hx1 hx2 => (propagate p r Tm v M b A t₀ x hx1 (hnone' x hx2)).1
  have hwpost : ∀ x, t₀ ≤ x → x < t₁ → ∀ s, t₀ < s → s ≤ x →
      w030 Tm v M b A s x = X x *ᵥ gv s := by
    intro x hx1 hx2 s hs1 hs2
    rw [(propagate p r Tm v M b A t₀ x hx1 (hnone' x hx2)).2 s hs1 hs2]
    simp only [X, gv, gvec]
    rw [mulVec_mulVec, ← Ehat_add]
    congr 2; ring
  have hdot : ∀ y (g : Fin p × Fin r → ℝ), γ ⬝ᵥ (X y *ᵥ g) = ∑ f, φ y f * g f := by
    intro y g
    rw [dotProduct_mulVec, ← mulVec_transpose]
    rfl
  -- the volatility separates
  have hσpre : ∀ s y, s ≤ t₀ → t₀ ≤ y → y < t₁ →
      sigma030 Tm u v M c b A s y = ∑ f, φ y f * w030 Tm v M b A s t₀ f := by
    intro s y hs hy1 hy2
    rw [sigma_gamma Tm u v M c b A s y (hs.trans hy1), hwpre y hy1 hy2 s hs, hdot]
  have hσpost : ∀ s y, t₀ < s → s ≤ y → y < t₁ →
      sigma030 Tm u v M c b A s y = ∑ f, φ y f * gv s f := by
    intro s y hs hsy hy
    rw [sigma_gamma Tm u v M c b A s y hsy, hwpost y (hs.le.trans hsy) hy s hs hsy, hdot]
  -- the formulas for `J`
  have hJpre : ∀ x, t₀ ≤ x → x < t₁ → ∀ s, s ≤ t₀ →
      J030 Tm u v M c b A s x = J030 Tm u v M c b A s t₀ + ∑ f, Φ f x * w030 Tm v M b A s t₀ f := by
    intro x hx1 hx2 s hs
    rw [J030, J030, ← intervalIntegral.integral_add_adjacent_intervals
      (sigma_ii Tm u v M c b A s s t₀) (sigma_ii Tm u v M c b A s t₀ x)]
    congr 1
    rw [intervalIntegral.integral_congr (g := fun y => ∑ f, φ y f * w030 Tm v M b A s t₀ f)
      (fun y hy => by
        rw [Set.uIcc_of_le hx1] at hy
        exact hσpre s y hs hy.1 (lt_of_le_of_lt hy.2 hx2)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f t₀ x).mul_const _]
    simp only [intervalIntegral.integral_mul_const]
    rfl
  have hJpost : ∀ x, x < t₁ → ∀ s, t₀ < s → s ≤ x →
      J030 Tm u v M c b A s x = ∑ f, (Φ f x - Φ f s) * gv s f := by
    intro x hx s hs1 hs2
    rw [J030, intervalIntegral.integral_congr (g := fun y => ∑ f, φ y f * gv s f)
      (fun y hy => by
        rw [Set.uIcc_of_le hs2] at hy
        exact hσpost s y hs1 hy.1 (lt_of_le_of_lt hy.2 hx)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f s x).mul_const _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_mul_const]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hφi f t₀ x) (hφi f t₀ s)).symm
  -- the representation `Q_x = X(x) R(x)`
  let Gm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ := fun e f x => ∫ s in t₀..x, gv s e * gv s f
  let Hm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ :=
    fun e f x => ∫ s in t₀..x, gv s e * gv s f * Φ f s
  let R : ℝ → Fin p × Fin r → ℝ := fun x e => Q030 Tm u v M c b A t₀ e +
    ∑ f, Φ f x * P030 Tm v M b A t₀ e f + ∑ f, (Φ f x * Gm e f x - Hm e f x)
  have hgg : ∀ e f x y, IntervalIntegrable (fun s => gv s e * gv s f) volume x y :=
    fun e f x y => ((hgc e).mul (hgc f)).intervalIntegrable x y
  have hggΦ : ∀ e f x y, IntervalIntegrable (fun s => gv s e * gv s f * Φ f s) volume x y :=
    fun e f x y => (((hgc e).mul (hgc f)).mul (hΦc f)).intervalIntegrable x y
  have hQ : ∀ x, t₀ ≤ x → x < t₁ → ∀ g, Q030 Tm u v M c b A x g = ∑ e, X x g e * R x e := by
    intro x hx1 hx2 g
    have hx0 : 0 ≤ x := ht₀.trans hx1
    have hii := wJ_ii Tm u v M c b A x hx0 g
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le ht₀, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc le_rfl hx1))
      (hii.mono_set (by rw [Set.uIcc_of_le hx1, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc ht₀ le_rfl))
    have hpart1 : (∫ s in (0:ℝ)..t₀, w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
        ∑ e, X x g e * (Q030 Tm u v M c b A t₀ e + ∑ f, Φ f x * P030 Tm v M b A t₀ e f) := by
      have hc : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s x g * J030 Tm u v M c b A s x =
          ∑ e, X x g e * (w030 Tm v M b A s t₀ e * J030 Tm u v M c b A s t₀ +
            ∑ f, Φ f x * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f)) := by
        intro s hs
        rw [Set.uIcc_of_le ht₀] at hs
        rw [hwpre x hx1 hx2 s hs.2, hJpre x hx1 hx2 s hs.2]
        simp only [mulVec, dotProduct]
        rw [mul_add, Finset.sum_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun f _ => by ring
      rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
        ((wJ_ii Tm u v M c b A t₀ ht₀ e).add (ii_fsum _ _ fun f _ =>
          (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _)).const_mul _]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (wJ_ii Tm u v M c b A t₀ ht₀ e) (ii_fsum _ _ fun f _ =>
          (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _),
        intervalIntegral.integral_finsetSum fun f _ => (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    have hpart2 : (∫ s in t₀..x, w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
        ∑ e, X x g e * ∑ f, (Φ f x * Gm e f x - Hm e f x) := by
      have hc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ x →
          w030 Tm v M b A s x g * J030 Tm u v M c b A s x =
          ∑ e, X x g e * ∑ f, (Φ f x * (gv s e * gv s f) - gv s e * gv s f * Φ f s) :=
        Eventually.of_forall fun s hs => by
          rw [Set.uIoc_of_le hx1] at hs
          rw [hwpost x hx1 hx2 s hs.1 hs.2, hJpost x hx2 s hs.1 hs.2]
          simp only [mulVec, dotProduct]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => by ring
      rw [intervalIntegral.integral_congr_ae hc, intervalIntegral.integral_finsetSum fun e _ =>
        (ii_fsum _ _ fun f _ => ((hgg e f t₀ x).const_mul _).sub (hggΦ e f t₀ x)).const_mul _]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun f _ =>
        ((hgg e f t₀ x).const_mul _).sub (hggΦ e f t₀ x)]
      congr 1
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [intervalIntegral.integral_sub ((hgg e f t₀ x).const_mul _) (hggΦ e f t₀ x),
        intervalIntegral.integral_const_mul]
    show (∫ s in (0:ℝ)..x, w030 Tm v M b A s x g * J030 Tm u v M c b A s x) = _
    rw [← hsplit, hpart1, hpart2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [R]
    ring
  -- the derivative of `R`
  have hΦd : ∀ f, HasDerivAt (Φ f) (φ t f) t := fun f =>
    ((hφc f).integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hR : ∀ e, HasDerivAt (fun x => R x e)
      (∑ f, φ t f * (P030 Tm v M b A t₀ e f + Gm e f t)) t := by
    intro e
    have hG : ∀ f, HasDerivAt (Gm e f) (gv t e * gv t f) t := fun f =>
      (((hgc e).mul (hgc f)).integral_hasStrictDerivAt t₀ t).hasDerivAt
    have hH : ∀ f, HasDerivAt (Hm e f) (gv t e * gv t f * Φ f t) t := fun f =>
      ((((hgc e).mul (hgc f)).mul (hΦc f)).integral_hasStrictDerivAt t₀ t).hasDerivAt
    have h1 := HasDerivAt.sum (u := Finset.univ) fun f _ => (hΦd f).mul_const
      (P030 Tm v M b A t₀ e f)
    have h2 := HasDerivAt.sum (u := Finset.univ) fun f _ => ((hΦd f).mul (hG f)).sub (hH f)
    have h3 := ((hasDerivAt_const t (Q030 Tm u v M c b A t₀ e)).add h1).add h2
    convert h3 using 1
    · funext x
      simp [R, Finset.sum_apply]
    · simp only [zero_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => by ring
  -- the derivative of `Q`
  have hXd : ∀ i k, HasDerivAt (fun x => X x i k)
      ((Ahat030 A * X t : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i k) t :=
    fun i k => Ehat_entry_hasDerivAt A t₀ t i k
  have hD := HasDerivAt.sum (u := Finset.univ) fun e _ => (hXd a e).mul (hR e)
  have hev : (fun x => ∑ e, X x a e * R x e) =ᶠ[𝓝 t] fun x => Q030 Tm u v M c b A x a := by
    filter_upwards [Ioo_mem_nhds htt htt₁] with x hx
    rw [hQ x hx.1.le hx.2 a]
  have hD' := (show HasDerivAt (fun x => ∑ e, X x a e * R x e) _ t by
    convert hD using 1; funext x; simp [Finset.sum_apply]).congr_of_eventuallyEq hev.symm
  convert hD' using 1
  -- identify the derivative
  have hQt : Q030 Tm u v M c b A t = X t *ᵥ R t := funext fun g => hQ t htt.le htt₁ g
  have hPt : P030 Tm v M b A t = X t * Ptil Tm v M b A t₀ t * (X t)ᵀ :=
    closed Tm v M b A t₀ t ht₀ htt.le (hnone' t htt₁)
  rw [hQt, hPt]
  have e1 : (X t * Ptil Tm v M b A t₀ t * (X t)ᵀ) *ᵥ gamma030 u c =
      X t *ᵥ (Ptil Tm v M b A t₀ t *ᵥ φ t) := by
    simp only [φ, γ, mulVec_mulVec, Matrix.mul_assoc]
  rw [Pi.add_apply, mulVec_mulVec, e1]
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Ptil, Gm, gv]
  ring

theorem recurrentLoadingStateQ : Standalone.RecurrentLoadingStateQ.statement := qEquation

end Novel.RecurrentLoadingStateQProof

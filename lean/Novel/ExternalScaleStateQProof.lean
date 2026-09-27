import Standalone.ExternalScaleStateQ
import Novel.ExternalScaleStatePProof
import Novel.RecurrentLoadingRestartQProof

open Matrix NormedSpace MeasureTheory Filter Topology
open scoped Kronecker
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingStateQ
open Standalone.RecurrentLoadingRestartP Standalone.ExternalScaleDrift
open Standalone.ExternalScaleStateP Standalone.ExternalScaleStateQ
open Novel.RecurrentLoadingDriftProof Novel.RecurrentLoadingStatePProof
open Novel.RecurrentLoadingRestartPProof Novel.RecurrentLoadingStateQProof
open Novel.RecurrentLoadingRestartQProof Novel.ExternalScaleStatePProof
namespace Novel.ExternalScaleStateQProof

variable {p r : ℕ}

lemma wJh (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (hh : Continuous h) (t : ℝ)
    (ht : 0 ≤ t) (a : Fin p × Fin r) :
    IntervalIntegrable (fun s => h s ^ 2 * (w030 Tm v M b A s t a * J030 Tm u v M c b A s t))
      volume 0 t :=
  (wJ_ii Tm u v M c b A t ht a).continuousOn_mul (hh.pow 2).continuousOn

lemma restart_h : Standalone.ExternalScaleStateQ.restartStatement := by
  intro p r Tm u v M c b A h hh t₀ T ht₀ htT hT hnone
  classical
  have hnone' : ∀ x, x < T → ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ x) :=
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
  -- `w` on `[t₀, T)`
  have hwpre : ∀ x, t₀ ≤ x → x < T → ∀ s, s ≤ t₀ →
      w030 Tm v M b A s x = X x *ᵥ w030 Tm v M b A s t₀ :=
    fun x hx1 hx2 => (propagate p r Tm v M b A t₀ x hx1 (hnone' x hx2)).1
  have hwpost : ∀ x, t₀ ≤ x → x < T → ∀ s, t₀ < s → s ≤ x →
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
  have hσpre : ∀ s y, s ≤ t₀ → t₀ ≤ y → y < T →
      sigma030 Tm u v M c b A s y = ∑ f, φ y f * w030 Tm v M b A s t₀ f := by
    intro s y hs hy1 hy2
    rw [sigma_gamma Tm u v M c b A s y (hs.trans hy1), hwpre y hy1 hy2 s hs, hdot]
  have hσpost : ∀ s y, t₀ < s → s ≤ y → y < T →
      sigma030 Tm u v M c b A s y = ∑ f, φ y f * gv s f := by
    intro s y hs hsy hy
    rw [sigma_gamma Tm u v M c b A s y hsy, hwpost y (hs.le.trans hsy) hy s hs hsy, hdot]
  -- the formulas for `J`
  have hJpre : ∀ x, t₀ ≤ x → x ≤ T → ∀ s, s ≤ t₀ →
      J030 Tm u v M c b A s x = J030 Tm u v M c b A s t₀ + ∑ f, Φ f x * w030 Tm v M b A s t₀ f := by
    intro x hx1 hx2 s hs
    rw [J030, J030, ← intervalIntegral.integral_add_adjacent_intervals
      (sigma_ii Tm u v M c b A s s t₀) (sigma_ii Tm u v M c b A s t₀ x)]
    congr 1
    rw [intervalIntegral.integral_congr_ae (g := fun y => ∑ f, φ y f * w030 Tm v M b A s t₀ f)
      (by
        filter_upwards [Measure.ae_ne volume T] with y hyT hy
        rw [Set.uIoc_of_le hx1] at hy
        exact hσpre s y hs hy.1.le (lt_of_le_of_ne (hy.2.trans hx2) hyT)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f t₀ x).mul_const _]
    simp only [intervalIntegral.integral_mul_const]
    rfl
  have hJpost : ∀ x, x ≤ T → ∀ s, t₀ < s → s ≤ x →
      J030 Tm u v M c b A s x = ∑ f, (Φ f x - Φ f s) * gv s f := by
    intro x hx s hs1 hs2
    rw [J030, intervalIntegral.integral_congr_ae (g := fun y => ∑ f, φ y f * gv s f)
      (by
        filter_upwards [Measure.ae_ne volume T] with y hyT hy
        rw [Set.uIoc_of_le hs2] at hy
        exact hσpost s y hs1 hy.1.le (lt_of_le_of_ne (hy.2.trans hx) hyT)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f s x).mul_const _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_mul_const]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hφi f t₀ x) (hφi f t₀ s)).symm
  -- the representation `Q_x = X(x) R(x)`
  let Gm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ :=
    fun e f x => ∫ s in t₀..x, h s ^ 2 * (gv s e * gv s f)
  let Hm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ :=
    fun e f x => ∫ s in t₀..x, h s ^ 2 * (gv s e * gv s f) * Φ f s
  let R : ℝ → Fin p × Fin r → ℝ := fun x e => Q031 Tm u v M c b A h t₀ e +
    ∑ f, Φ f x * P031 Tm v M b A h t₀ e f + ∑ f, (Φ f x * Gm e f x - Hm e f x)
  have hgg : ∀ e f x y, IntervalIntegrable (fun s => h s ^ 2 * (gv s e * gv s f)) volume x y :=
    fun e f x y => ((hh.pow 2).mul ((hgc e).mul (hgc f))).intervalIntegrable x y
  have hggΦ : ∀ e f x y, IntervalIntegrable (fun s => h s ^ 2 * (gv s e * gv s f) * Φ f s)
      volume x y :=
    fun e f x y => (((hh.pow 2).mul ((hgc e).mul (hgc f))).mul (hΦc f)).intervalIntegrable x y
  have hQ : ∀ x, t₀ ≤ x → x ≤ T → ∀ Y : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
      (∀ s, s ≤ t₀ → w030 Tm v M b A s x = Y *ᵥ w030 Tm v M b A s t₀) →
      (∀ s, t₀ < s → s < x → w030 Tm v M b A s x = Y *ᵥ gv s) →
      ∀ g, Q031 Tm u v M c b A h x g = ∑ e, Y g e * R x e := by
    intro x hx1 hx2 Y hYpre hYpost g
    have hx0 : 0 ≤ x := ht₀.trans hx1
    have hii := wJh Tm u v M c b A h hh x hx0 g
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le ht₀, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc le_rfl hx1))
      (hii.mono_set (by rw [Set.uIcc_of_le hx1, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc ht₀ le_rfl))
    have hpart1 : (∫ s in (0:ℝ)..t₀, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) =
        ∑ e, Y g e * (Q031 Tm u v M c b A h t₀ e + ∑ f, Φ f x * P031 Tm v M b A h t₀ e f) := by
      have hc : ∀ s ∈ Set.uIcc 0 t₀, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
          ∑ e, Y g e * (h s ^ 2 * (w030 Tm v M b A s t₀ e * J030 Tm u v M c b A s t₀) +
            ∑ f, Φ f x * (h s ^ 2 * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f))) := by
        intro s hs
        rw [Set.uIcc_of_le ht₀] at hs
        rw [hYpre s hs.2, hJpre x hx1 hx2 s hs.2]
        simp only [mulVec, dotProduct]
        rw [mul_add, Finset.sum_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun f _ => by ring
      rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
        ((wJh Tm u v M c b A h hh t₀ ht₀ e).add (ii_fsum _ _ fun f _ =>
          (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _)).const_mul _]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (wJh Tm u v M c b A h hh t₀ ht₀ e) (ii_fsum _ _ fun f _ =>
          (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _),
        intervalIntegral.integral_finsetSum fun f _ => (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    have hpart2 : (∫ s in t₀..x, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) =
        ∑ e, Y g e * ∑ f, (Φ f x * Gm e f x - Hm e f x) := by
      have hc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ x →
          h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
          ∑ e, Y g e * ∑ f, (Φ f x * (h s ^ 2 * (gv s e * gv s f)) -
            h s ^ 2 * (gv s e * gv s f) * Φ f s) :=
        by
          filter_upwards [Measure.ae_ne volume x] with s hsx hs
          rw [Set.uIoc_of_le hx1] at hs
          rw [hYpost s hs.1 (lt_of_le_of_ne hs.2 hsx), hJpost x hx2 s hs.1 hs.2]
          simp only [mulVec, dotProduct]
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
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
    show (∫ s in (0:ℝ)..x, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) = _
    rw [← hsplit, hpart1, hpart2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [R]
    ring
  -- continuity of `R`
  have hRc : ∀ e, Continuous fun x => R x e := by
    intro e
    have hG : ∀ f, Continuous (Gm e f) := fun f =>
      intervalIntegral.continuous_primitive (hgg e f) t₀
    have hH : ∀ f, Continuous (Hm e f) := fun f =>
      intervalIntegral.continuous_primitive (hggΦ e f) t₀
    exact (continuous_const.add (continuous_finset_sum _ fun f _ => (hΦc f).mul continuous_const)).add
      (continuous_finset_sum _ fun f _ => ((hΦc f).mul (hG f)).sub (hH f))
  refine ⟨X T *ᵥ R T, fun a => ?_, ?_⟩
  · -- the left limit
    have hcont : Continuous fun x => ∑ e, X x a e * R x e :=
      continuous_finset_sum _ fun e _ => (hXc a e).mul (hRc e)
    have hev : (fun x => ∑ e, X x a e * R x e) =ᶠ[𝓝[<] T] fun x => Q031 Tm u v M c b A h x a := by
      filter_upwards [Ioo_mem_nhdsLT htT] with x hx
      rw [hQ x hx.1.le hx.2.le (X x) (fun s hs => hwpre x hx.1.le hx.2 s hs)
        (fun s hs1 hs2 => hwpost x hx.1.le hx.2 s hs1 hs2.le) a]
    exact ((hcont.tendsto T).mono_left nhdsWithin_le_nhds).congr' hev
  · -- the jump
    funext g
    rw [hQ T htT.le le_rfl (Mhat030 M * Ehat030 A (T - t₀))
      (fun s hs => Novel.RecurrentLoadingRestartQProof.jump_pre Tm v M b A t₀ T htT hT hnone s hs)
      (fun s hs1 hs2 => Novel.RecurrentLoadingRestartQProof.jump_post Tm v M b A t₀ T hT hnone s hs1 hs2) g, mulVec_mulVec]
    rfl


lemma qEquation_h : Standalone.ExternalScaleStateQ.qEquationStatement := by
  intro p r Tm u v M c b A h hh t₀ t t₁ ht₀ htt htt₁ hnone a
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
  have hJpre : ∀ x, t₀ ≤ x → x ≤ t₁ → ∀ s, s ≤ t₀ →
      J030 Tm u v M c b A s x = J030 Tm u v M c b A s t₀ + ∑ f, Φ f x * w030 Tm v M b A s t₀ f := by
    intro x hx1 hx2 s hs
    rw [J030, J030, ← intervalIntegral.integral_add_adjacent_intervals
      (sigma_ii Tm u v M c b A s s t₀) (sigma_ii Tm u v M c b A s t₀ x)]
    congr 1
    rw [intervalIntegral.integral_congr_ae (g := fun y => ∑ f, φ y f * w030 Tm v M b A s t₀ f)
      (by
        filter_upwards [Measure.ae_ne volume t₁] with y hyT hy
        rw [Set.uIoc_of_le hx1] at hy
        exact hσpre s y hs hy.1.le (lt_of_le_of_ne (hy.2.trans hx2) hyT)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f t₀ x).mul_const _]
    simp only [intervalIntegral.integral_mul_const]
    rfl
  have hJpost : ∀ x, x ≤ t₁ → ∀ s, t₀ < s → s ≤ x →
      J030 Tm u v M c b A s x = ∑ f, (Φ f x - Φ f s) * gv s f := by
    intro x hx s hs1 hs2
    rw [J030, intervalIntegral.integral_congr_ae (g := fun y => ∑ f, φ y f * gv s f)
      (by
        filter_upwards [Measure.ae_ne volume t₁] with y hyT hy
        rw [Set.uIoc_of_le hs2] at hy
        exact hσpost s y hs1 hy.1.le (lt_of_le_of_ne (hy.2.trans hx) hyT)),
      intervalIntegral.integral_finsetSum fun f _ => (hφi f s x).mul_const _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_mul_const]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hφi f t₀ x) (hφi f t₀ s)).symm
  -- the representation `Q_x = X(x) R(x)`
  let Gm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ :=
    fun e f x => ∫ s in t₀..x, h s ^ 2 * (gv s e * gv s f)
  let Hm : Fin p × Fin r → Fin p × Fin r → ℝ → ℝ :=
    fun e f x => ∫ s in t₀..x, h s ^ 2 * (gv s e * gv s f) * Φ f s
  let R : ℝ → Fin p × Fin r → ℝ := fun x e => Q031 Tm u v M c b A h t₀ e +
    ∑ f, Φ f x * P031 Tm v M b A h t₀ e f + ∑ f, (Φ f x * Gm e f x - Hm e f x)
  have hgg : ∀ e f x y, IntervalIntegrable (fun s => h s ^ 2 * (gv s e * gv s f)) volume x y :=
    fun e f x y => ((hh.pow 2).mul ((hgc e).mul (hgc f))).intervalIntegrable x y
  have hggΦ : ∀ e f x y, IntervalIntegrable (fun s => h s ^ 2 * (gv s e * gv s f) * Φ f s)
      volume x y :=
    fun e f x y => (((hh.pow 2).mul ((hgc e).mul (hgc f))).mul (hΦc f)).intervalIntegrable x y
  have hQ : ∀ x, t₀ ≤ x → x ≤ t₁ → ∀ Y : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
      (∀ s, s ≤ t₀ → w030 Tm v M b A s x = Y *ᵥ w030 Tm v M b A s t₀) →
      (∀ s, t₀ < s → s < x → w030 Tm v M b A s x = Y *ᵥ gv s) →
      ∀ g, Q031 Tm u v M c b A h x g = ∑ e, Y g e * R x e := by
    intro x hx1 hx2 Y hYpre hYpost g
    have hx0 : 0 ≤ x := ht₀.trans hx1
    have hii := wJh Tm u v M c b A h hh x hx0 g
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le ht₀, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc le_rfl hx1))
      (hii.mono_set (by rw [Set.uIcc_of_le hx1, Set.uIcc_of_le hx0]; exact Set.Icc_subset_Icc ht₀ le_rfl))
    have hpart1 : (∫ s in (0:ℝ)..t₀, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) =
        ∑ e, Y g e * (Q031 Tm u v M c b A h t₀ e + ∑ f, Φ f x * P031 Tm v M b A h t₀ e f) := by
      have hc : ∀ s ∈ Set.uIcc 0 t₀, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
          ∑ e, Y g e * (h s ^ 2 * (w030 Tm v M b A s t₀ e * J030 Tm u v M c b A s t₀) +
            ∑ f, Φ f x * (h s ^ 2 * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f))) := by
        intro s hs
        rw [Set.uIcc_of_le ht₀] at hs
        rw [hYpre s hs.2, hJpre x hx1 hx2 s hs.2]
        simp only [mulVec, dotProduct]
        rw [mul_add, Finset.sum_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun f _ => by ring
      rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
        ((wJh Tm u v M c b A h hh t₀ ht₀ e).add (ii_fsum _ _ fun f _ =>
          (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _)).const_mul _]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (wJh Tm u v M c b A h hh t₀ ht₀ e) (ii_fsum _ _ fun f _ =>
          (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _),
        intervalIntegral.integral_finsetSum fun f _ => (wwh Tm v M b A h hh t₀ e f 0 t₀).const_mul _]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    have hpart2 : (∫ s in t₀..x, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) =
        ∑ e, Y g e * ∑ f, (Φ f x * Gm e f x - Hm e f x) := by
      have hc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc t₀ x →
          h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x) =
          ∑ e, Y g e * ∑ f, (Φ f x * (h s ^ 2 * (gv s e * gv s f)) -
            h s ^ 2 * (gv s e * gv s f) * Φ f s) :=
        by
          filter_upwards [Measure.ae_ne volume x] with s hsx hs
          rw [Set.uIoc_of_le hx1] at hs
          rw [hYpost s hs.1 (lt_of_le_of_ne hs.2 hsx), hJpost x hx2 s hs.1 hs.2]
          simp only [mulVec, dotProduct]
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
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
    show (∫ s in (0:ℝ)..x, h s ^ 2 * (w030 Tm v M b A s x g * J030 Tm u v M c b A s x)) = _
    rw [← hsplit, hpart1, hpart2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [R]
    ring
  -- the derivative of `R`
  have hΦd : ∀ f, HasDerivAt (Φ f) (φ t f) t := fun f =>
    ((hφc f).integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hR : ∀ e, HasDerivAt (fun x => R x e)
      (∑ f, φ t f * (P031 Tm v M b A h t₀ e f + Gm e f t)) t := by
    intro e
    have hG : ∀ f, HasDerivAt (Gm e f) (h t ^ 2 * (gv t e * gv t f)) t := fun f =>
      (((hh.pow 2).mul ((hgc e).mul (hgc f))).integral_hasStrictDerivAt t₀ t).hasDerivAt
    have hH : ∀ f, HasDerivAt (Hm e f) (h t ^ 2 * (gv t e * gv t f) * Φ f t) t := fun f =>
      ((((hh.pow 2).mul ((hgc e).mul (hgc f))).mul (hΦc f)).integral_hasStrictDerivAt t₀ t).hasDerivAt
    have h1 := HasDerivAt.sum (u := Finset.univ) fun f _ => (hΦd f).mul_const
      (P031 Tm v M b A h t₀ e f)
    have h2 := HasDerivAt.sum (u := Finset.univ) fun f _ => ((hΦd f).mul (hG f)).sub (hH f)
    have h3 := ((hasDerivAt_const t (Q031 Tm u v M c b A h t₀ e)).add h1).add h2
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
  have hev : (fun x => ∑ e, X x a e * R x e) =ᶠ[𝓝 t] fun x => Q031 Tm u v M c b A h x a := by
    filter_upwards [Ioo_mem_nhds htt htt₁] with x hx
    rw [hQ x hx.1.le hx.2.le (X x) (fun s hs => hwpre x hx.1.le hx.2 s hs)
      (fun s hs1 hs2 => hwpost x hx.1.le hx.2 s hs1 hs2.le) a]
  have hD' := (show HasDerivAt (fun x => ∑ e, X x a e * R x e) _ t by
    convert hD using 1; funext x; simp [Finset.sum_apply]).congr_of_eventuallyEq hev.symm
  convert hD' using 1
  -- identify the derivative
  have hQt : Q031 Tm u v M c b A h t = X t *ᵥ R t := funext fun g =>
    hQ t htt.le htt₁.le (X t) (fun s hs => hwpre t htt.le htt₁ s hs)
      (fun s hs1 hs2 => hwpost t htt.le htt₁ s hs1 hs2.le) g
  have hPt : P031 Tm v M b A h t = X t * Ptilh Tm v M b A h t₀ t * (X t)ᵀ :=
    closed_h Tm v M b A h hh t₀ t ht₀ htt.le (hnone' t htt₁)
  rw [hQt, hPt]
  have e1 : (X t * Ptilh Tm v M b A h t₀ t * (X t)ᵀ) *ᵥ gamma030 u c =
      X t *ᵥ (Ptilh Tm v M b A h t₀ t *ᵥ φ t) := by
    simp only [φ, γ, mulVec_mulVec, Matrix.mul_assoc]
  rw [Pi.add_apply, mulVec_mulVec, e1]
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Ptilh, Gm, gv]
  ring


theorem externalScaleStateQ : Standalone.ExternalScaleStateQ.statement := ⟨qEquation_h, restart_h⟩

end Novel.ExternalScaleStateQProof

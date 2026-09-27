import Standalone.AnalyticPrimitive
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter Topology FormalMultilinearSeries
open scoped NNReal ENNReal
open Standalone.AnalyticPrimitive
namespace Novel.AnalyticPrimitiveProof

lemma primitive : primitiveStatement := by
  intro f hf x0 _
  have hfc : Continuous f := continuousOn_univ.1 hf.continuousOn
  obtain ⟨p, r, hp⟩ := hf x0 (mem_univ _)
  set c : ℕ → ℝ := fun n => p.coeff n
  obtain ⟨r₂, hr₂0, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  obtain ⟨C, hC0, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hr₂.trans_le hp.r_le)
  have hc : ∀ n, |c n| * (r₂ : ℝ) ^ n ≤ C := fun n => by
    have := hC n; rwa [p.norm_apply_eq_norm_coef, Real.norm_eq_abs] at this
  have hr₂p : (0 : ℝ) < r₂ := by exact_mod_cast hr₂0
  set r₁ : ℝ := (r₂ : ℝ) / 2
  have hr₁ : 0 < r₁ := by positivity
  set t := Metric.ball (0 : ℝ) r₁
  -- the geometric bound on `t`
  have hpow : ∀ n (y : ℝ), y ∈ t → |c n| * |y| ^ n ≤ C * (1 / 2) ^ n := fun n y hy => by
    have hy' : |y| ≤ r₁ := by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy; exact hy.le
    calc |c n| * |y| ^ n ≤ |c n| * r₁ ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' n) (abs_nonneg _)
      _ = |c n| * (r₂ : ℝ) ^ n * (1 / 2) ^ n := by simp only [r₁]; rw [div_pow, one_div, inv_pow]; ring
      _ ≤ C * (1 / 2) ^ n := mul_le_mul_of_nonneg_right (hc n) (by positivity)
  have hpowr : ∀ n, |c n| * r₁ ^ n ≤ C * (1 / 2) ^ n := fun n => by
    calc |c n| * r₁ ^ n = |c n| * (r₂ : ℝ) ^ n * (1 / 2) ^ n := by
          simp only [r₁]; rw [div_pow, one_div, inv_pow]; ring
      _ ≤ C * (1 / 2) ^ n := mul_le_mul_of_nonneg_right (hc n) (by positivity)
  have hu : Summable fun n : ℕ => C * ((1 : ℝ) / 2) ^ n := summable_geometric_two.mul_left C
  have hg : ∀ n (y : ℝ), HasDerivAt (fun y => c n * y ^ (n + 1) / ((n : ℝ) + 1)) (c n * y ^ n) y :=
    fun n y => by
      have := ((hasDerivAt_pow (n + 1) y).const_mul (c n)).div_const ((n : ℝ) + 1)
      convert this using 1
      push_cast
      field_simp
  have hg' : ∀ n (y : ℝ), y ∈ t → ‖c n * y ^ n‖ ≤ C * (1 / 2) ^ n := fun n y hy => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]; exact hpow n y hy
  set G : ℝ → ℝ := fun z => ∑' n, c n * z ^ (n + 1) / ((n : ℝ) + 1)
  have hG : ∀ y ∈ t, HasDerivAt G (∑' n, c n * y ^ n) y := fun y hy =>
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball (0:ℝ) r₁).isPreconnected
      (fun n y _ => hg n y) hg' (Metric.mem_ball_self hr₁) (by simp) hy
  -- the series of `f`
  have hfs : ∀ y ∈ t, ∑' n, c n * y ^ n = f (x0 + y) := fun y hy => by
    have hyr : y ∈ Metric.eball (0 : ℝ) r := by
      rw [Metric.mem_eball, edist_dist]
      refine lt_trans ?_ hr₂
      rw [ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg ENNReal.coe_ne_top, ENNReal.coe_toReal]
      rw [Metric.mem_ball] at hy
      linarith [show r₁ < r₂ by simp only [r₁]; linarith]
    have := hp.hasSum hyr
    simp only [apply_eq_pow_smul_coeff, smul_eq_mul] at this
    rw [← this.tsum_eq]
    exact tsum_congr fun n => by ring
  -- the primitive differs from `G` by a constant on `t`
  set F : ℝ → ℝ := fun x => ∫ η in (0:ℝ)..x, f η
  have hF : ∀ y, HasDerivAt (fun y => F (x0 + y)) (f (x0 + y)) y := fun y => by
    have h1 : HasDerivAt F (f (x0 + y)) (x0 + y) :=
      (hfc.integral_hasStrictDerivAt 0 (x0 + y)).hasDerivAt
    have h2 := h1.comp y ((hasDerivAt_id y).const_add x0)
    convert h2 using 1 <;> first | rfl | ring
  have hconst : ∀ y ∈ t, F (x0 + y) - G y = F (x0 + 0) - G 0 := fun y hy => by
    have hd : ∀ z ∈ t, HasDerivAt (fun z => F (x0 + z) - G z) 0 z := fun z hz => by
      have := (hF z).sub (hG z hz)
      rwa [hfs z hz, sub_self] at this
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℝ) r₁).isPreconnected
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) hy (Metric.mem_ball_self hr₁)
  have hG0 : G 0 = 0 := by simp [G]
  -- `G` is a power series with positive radius
  let d : ℕ → ℝ := fun n => if n = 0 then 0 else c (n - 1) / n
  have hdb : ∀ n, ‖ofScalars ℝ d n‖ * (⟨r₁, hr₁.le⟩ : ℝ≥0) ^ n ≤ C * r₁ := fun n => by
    rw [ofScalars_norm, Real.norm_eq_abs]
    rcases n with _ | m
    · have h0 : d 0 = 0 := if_pos rfl
      rw [h0, abs_zero, zero_mul]; positivity
    · simp only [d, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      have hm := hpowr m
      rw [abs_div, pow_succ]
      have h1 : |c m| / |((m + 1 : ℕ) : ℝ)| ≤ |c m| := div_le_self (abs_nonneg _)
        (by rw [abs_of_pos (by positivity)]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
      have h2 : C * (1 / 2) ^ m ≤ C := mul_le_of_le_one_right hC0.le (pow_le_one₀ (by norm_num) (by norm_num))
      calc |c m| / |((m + 1 : ℕ) : ℝ)| * (r₁ ^ m * r₁) ≤ |c m| * (r₁ ^ m * r₁) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = |c m| * r₁ ^ m * r₁ := by ring
        _ ≤ C * r₁ := mul_le_mul_of_nonneg_right (hm.trans h2) hr₁.le
  have hrad : 0 < (ofScalars ℝ d).radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.2 (show (0 : ℝ≥0) < (⟨r₁, hr₁.le⟩ : ℝ≥0) from hr₁))
      ((ofScalars ℝ d).le_radius_of_bound (C * r₁) hdb)
  have hq := ((ofScalars ℝ d).hasFPowerSeriesOnBall hrad).analyticAt
  have hGq : ∀ y ∈ t, G y = (ofScalars ℝ d).sum y := fun y hy => by
    have hsum : Summable fun n => c n * y ^ (n + 1) / ((n : ℝ) + 1) := by
      refine Summable.of_norm_bounded (hu.mul_left r₁) fun n => ?_
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, pow_succ]
      have hy' : |y| ≤ r₁ := by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy; exact hy.le
      have hn1 : (1 : ℝ) ≤ |(n : ℝ) + 1| := by rw [abs_of_pos (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      calc |c n| * (|y| ^ n * |y|) / |(n : ℝ) + 1| ≤ |c n| * (|y| ^ n * |y|) :=
            div_le_self (by positivity) hn1
        _ = (|c n| * |y| ^ n) * |y| := by ring
        _ ≤ (C * (1 / 2) ^ n) * r₁ := mul_le_mul (hpow n y hy) hy' (abs_nonneg _) (by positivity)
        _ = r₁ * (C * (1 / 2) ^ n) := by ring
    show G y = ofScalarsSum d y
    rw [ofScalars_sum_eq, tsum_eq_zero_add' (by
      simpa [d, smul_eq_mul, div_mul_eq_mul_div] using hsum)]
    simp only [d, ite_true, zero_smul, zero_add, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      smul_eq_mul, G, zero_mul]
    exact tsum_congr fun n => by push_cast; ring
  have hGa : AnalyticAt ℝ G 0 := hq.congr (by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₁)] with y hy
    exact (hGq y hy).symm)
  -- so `F` is analytic at `x₀`
  have hcomp : AnalyticAt ℝ (fun x => F (x0 + 0) - G 0 + G (x - x0)) x0 := by
    refine analyticAt_const.add ?_
    have : AnalyticAt ℝ (fun x : ℝ => x - x0) x0 := analyticAt_id.sub analyticAt_const
    have hG' : AnalyticAt ℝ G ((fun x : ℝ => x - x0) x0) := by simpa using hGa
    exact AnalyticAt.comp (g := G) (f := fun x : ℝ => x - x0) (x := x0) hG' this
  refine hcomp.congr ?_
  have hmem : ∀ᶠ x in 𝓝 x0, x - x0 ∈ t := by
    have : Tendsto (fun x : ℝ => x - x0) (𝓝 x0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 x0)).sub_const x0
      rwa [sub_self] at this
    exact this (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₁))
  filter_upwards [hmem] with x hx
  have := hconst (x - x0) hx
  simp only [add_sub_cancel] at this
  simp only [F] at this ⊢
  linarith

theorem analyticPrimitive : Standalone.AnalyticPrimitive.statement := primitive

end Novel.AnalyticPrimitiveProof

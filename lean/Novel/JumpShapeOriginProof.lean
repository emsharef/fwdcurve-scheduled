import Standalone.JumpShapeOrigin
import Novel.JumpShapeForwardProof

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeForward Standalone.JumpShapeOrigin
namespace Novel.JumpShapeOriginProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof

/-- `e^a − 1 ≤ a e^a`. -/
lemma exp_sub_one_le (a : ℝ) : Real.exp a - 1 ≤ a * Real.exp a := by
  have h1 := Real.add_one_le_exp (-a)
  have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos a]

/-- `y ≤ e^{δy}/(e δ)` for `δ > 0`. -/
lemma le_exp_div {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : y ≤ Real.exp (δ * y) / (Real.exp 1 * δ) := by
  have h := Real.add_one_le_exp (δ * y - 1)
  rw [Real.exp_sub] at h
  rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) hδ)]
  have he := Real.exp_pos 1
  rw [le_div_iff₀ he] at h
  nlinarith

/-- The difference quotient `(e^{−εx} − 1)/ε`. -/
noncomputable def qd (ε x : ℝ) : ℝ := (Real.exp (-ε * x) - 1) / ε

/-- For `0 < ε ≤ ε₀`: `−x ≤ q ≤ 0` when `x ≥ 0`, and `0 ≤ q ≤ e^{−(ε₀ + δ)x}/(e δ)` when
`x < 0`. -/
lemma qd_bounds {ε ε₀ δ : ℝ} (hε : 0 < ε) (hεε : ε ≤ ε₀) (hδ : 0 < δ) (x : ℝ) :
    (0 ≤ x → -x ≤ qd ε x ∧ qd ε x ≤ 0) ∧
    (x < 0 → 0 ≤ qd ε x ∧ qd ε x ≤ Real.exp (-(ε₀ + δ) * x) / (Real.exp 1 * δ)) := by
  refine ⟨fun hx => ⟨?_, ?_⟩, fun hx => ⟨?_, ?_⟩⟩
  · rw [qd, le_div_iff₀ hε]
    nlinarith [Real.add_one_le_exp (-ε * x)]
  · exact div_nonpos_of_nonpos_of_nonneg
      (by linarith [Real.exp_le_one_iff.2 (by nlinarith : -ε * x ≤ 0)]) hε.le
  · exact div_nonneg (by linarith [Real.one_le_exp (by nlinarith : 0 ≤ -ε * x)]) hε.le
  · set y := -x
    have hy : 0 < y := by simp only [y]; linarith
    have e1 : Real.exp (-ε * x) = Real.exp (ε * y) := by congr 1; simp only [y]; ring
    rw [qd, e1, div_le_iff₀ hε]
    have h1 := exp_sub_one_le (ε * y)
    have h2 : Real.exp (ε * y) ≤ Real.exp (ε₀ * y) := Real.exp_le_exp.2 (by nlinarith)
    have h3 := le_exp_div hδ y
    have h4 : Real.exp (-(ε₀ + δ) * x) = Real.exp (δ * y) * Real.exp (ε₀ * y) := by
      rw [← Real.exp_add]; congr 1; simp only [y]; ring
    rw [h4]
    have hc : 0 < Real.exp 1 * δ := mul_pos (Real.exp_pos 1) hδ
    have h5 : y * Real.exp (ε₀ * y) ≤ Real.exp (δ * y) / (Real.exp 1 * δ) * Real.exp (ε₀ * y) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    have h6 : ε * y * Real.exp (ε * y) ≤ ε * (y * Real.exp (ε₀ * y)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hy.le) hε.le
    calc Real.exp (ε * y) - 1 ≤ ε * y * Real.exp (ε * y) := h1
      _ ≤ ε * (y * Real.exp (ε₀ * y)) := h6
      _ ≤ ε * (Real.exp (δ * y) / (Real.exp 1 * δ) * Real.exp (ε₀ * y)) :=
          mul_le_mul_of_nonneg_left h5 hε.le
      _ = Real.exp (δ * y) * Real.exp (ε₀ * y) / (Real.exp 1 * δ) * ε := by ring

lemma qd_tendsto (x : ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝[≠] 0)) :
    Tendsto (fun n => qd (ε n) x) atTop (𝓝 (-x)) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s * x)) (-x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => -s * x) (-x) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).neg.mul_const x
    simpa using h1.exp
  have := (hasDerivAt_iff_tendsto_slope.1 hd).comp hε
  refine this.congr fun n => ?_
  simp [slope_def_field, qd]

lemma originS : Standalone.JumpShapeOrigin.originStatement := by
  intro ν _ L h hL hf hl hs hc
  obtain ⟨r, hr0, hr⟩ := exists_between le_rfl (by simpa using hL)
  have hIr : ∀ s, 0 ≤ s → s ≤ r → InI L s := fun s h0 h1 => inI_of_lt h0 h1 hr
  -- the right derivative of `M` at `0` is `h(0)`
  have hI : IntervalIntegrable h volume 0 r := hl r (hIr r hr0.le le_rfl)
  have hmeas : StronglyMeasurableAtFilter h (𝓝[Ioi 0] 0) volume :=
    ⟨Icc 0 r, Icc_mem_nhdsGT hr0,
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hr0.le).1 hI).aestronglyMeasurable⟩
  have hF := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
    (a := 0) (b := 0) IntervalIntegrable.refl hmeas (hc.mono Ioi_subset_Ici_self)
  have hK : HasDerivWithinAt (Klap ν) (h 0) (Ici 0) 0 := by
    refine hF.congr_of_eventuallyEq ?_ (by rw [hs 0 (hIr 0 le_rfl hr0.le)])
    filter_upwards [Icc_mem_nhdsGE hr0] with y hy
    exact (hs y (hIr y hy.1 hy.2)).symm
  have hM : HasDerivWithinAt (Mlap ν) (h 0) (Ici 0) 0 := by
    have := hK.exp
    rw [Klap_zero, Real.exp_zero, one_mul] at this
    refine this.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Icc_mem_nhdsGE hr0] with y hy
      rw [Klap, Real.exp_log (Mlap_pos hf (hIr y hy.1 hy.2))]
    · rw [Klap, Real.exp_log (Mlap_pos hf (hIr 0 le_rfl hr0.le))]
  -- along `ε_n = (r/2)/(n+1)`
  set ε : ℕ → ℝ := fun n => r / 2 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεle : ∀ n, ε n ≤ r / 2 := fun n => div_le_self (by positivity) (by
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith)
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
    simp only [mul_zero] at this
    exact this.congr fun n => by simp only [ε]; ring
  have hεne : Tendsto ε atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun n => (hεpos n).ne'⟩
  have hεIci : Tendsto ε atTop (𝓝[Ici 0 \ {0}] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun n =>
      ⟨(hεpos n).le, (hεpos n).ne'⟩⟩
  have hQ : Tendsto (fun n => ∫ x, qd (ε n) x ∂ν) atTop (𝓝 (h 0)) := by
    refine ((hasDerivWithinAt_iff_tendsto_slope.1 hM).comp hεIci).congr fun n => ?_
    have hint := hf (ε n) (hIr _ (hεpos n).le ((hεle n).trans (by linarith)))
    simp only [Function.comp_apply, slope_def_field, sub_zero]
    rw [show Mlap ν 0 = 1 by simp [Mlap]]
    simp only [qd]
    rw [integral_div, integral_sub hint (integrable_const 1), integral_const]
    simp [Mlap]
  -- the dominating functions
  set δ := r / 4
  have hδ : 0 < δ := by positivity
  set D : ℝ → ℝ := fun x => Real.exp (-(r / 2 + δ) * x) / (Real.exp 1 * δ)
  have hD : Integrable D ν :=
    (hf (r / 2 + δ) (hIr _ (by positivity) (by simp only [δ]; linarith))).div_const _
  have hD0 : ∀ x, 0 ≤ D x := fun x => by positivity
  have hb := fun n x => qd_bounds (hεpos n) (hεle n) hδ x
  have hqi : ∀ n, Integrable (fun x => qd (ε n) x) ν := fun n =>
    ((hf (ε n) (hIr _ (hεpos n).le ((hεle n).trans (by linarith)))).sub
      (integrable_const 1)).div_const _
  -- `∫ x⁺ < ∞` by Fatou
  have hpos : ∫⁻ x, ENNReal.ofReal x ∂ν < ∞ := by
    have hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (-qd (ε n) x)) atTop
        (𝓝 (ENNReal.ofReal x)) := fun x => by
      have := (qd_tendsto x hεne).neg
      rw [neg_neg] at this
      exact (ENNReal.continuous_ofReal.tendsto x).comp this
    have hle : ∀ n, ∫⁻ x, ENNReal.ofReal (-qd (ε n) x) ∂ν ≤
        ENNReal.ofReal (-(∫ x, qd (ε n) x ∂ν) + ∫ x, D x ∂ν) := fun n => by
      have hn : Integrable (fun x => -qd (ε n) x) ν := (hqi n).neg
      have hnD : Integrable (fun x => -qd (ε n) x + D x) ν := hn.add hD
      rw [← integral_neg, ← integral_add hn hD,
        ofReal_integral_eq_lintegral_ofReal hnD (Eventually.of_forall fun x => ?_)]
      · refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        linarith [hD0 x]
      · simp only [Pi.zero_apply]
        rcases le_or_gt 0 x with hx | hx
        · linarith [(hb n x).1 hx, hD0 x]
        · linarith [(hb n x).2 hx]
    calc ∫⁻ x, ENNReal.ofReal x ∂ν
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (-qd (ε n) x)) atTop ∂ν :=
          lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (-qd (ε n) x) ∂ν) atTop :=
          lintegral_liminf_le fun n => by simp only [qd]; fun_prop
      _ ≤ liminf (fun n => ENNReal.ofReal (-(∫ x, qd (ε n) x ∂ν) + ∫ x, D x ∂ν)) atTop :=
          liminf_le_liminf (Eventually.of_forall hle)
      _ = ENNReal.ofReal (-h 0 + ∫ x, D x ∂ν) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp
            ((hQ.neg).add_const _)).liminf_eq
      _ < ∞ := ENNReal.ofReal_lt_top
  -- so `x` is integrable
  set D' : ℝ → ℝ := fun x => Real.exp (-(r / 2) * x) / (Real.exp 1 * (r / 2))
  have hD' : Integrable D' ν := (hf (r / 2) (hIr _ (by positivity) (by linarith))).div_const _
  have hid : Integrable (fun x => x) ν := by
    refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hneg : ∀ x : ℝ, ENNReal.ofReal (-x) ≤ ENNReal.ofReal (D' x) := fun x =>
      ENNReal.ofReal_le_ofReal (by
        have := le_exp_div (δ := r / 2) (by positivity) (-x)
        simp only [D']
        convert this using 3; ring)
    calc ∫⁻ x, ‖x‖ₑ ∂ν ≤ ∫⁻ x, (ENNReal.ofReal x + ENNReal.ofReal (D' x)) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs]
          rcases le_or_gt 0 x with hx | hx
          · rw [abs_of_nonneg hx]; exact le_self_add
          · rw [abs_of_neg hx]; exact (hneg x).trans le_add_self
      _ = ∫⁻ x, ENNReal.ofReal x ∂ν + ∫⁻ x, ENNReal.ofReal (D' x) ∂ν :=
          lintegral_add_left (by fun_prop) _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨hpos, by
          rw [← ofReal_integral_eq_lintegral_ofReal hD'
            (Eventually.of_forall fun x => by positivity)]
          exact ENNReal.ofReal_lt_top⟩
  refine ⟨hid, ?_⟩
  -- dominated convergence identifies the limit
  have hdom : Tendsto (fun n => ∫ x, qd (ε n) x ∂ν) atTop (𝓝 (∫ x, -x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |x| + D x)
      (fun n => (hqi n).aestronglyMeasurable) (hid.abs.add hD)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        rcases le_or_gt 0 x with hx | hx
        · obtain ⟨b1, b2⟩ := (hb n x).1 hx
          rw [abs_of_nonpos b2, abs_of_nonneg hx]
          linarith [hD0 x]
        · obtain ⟨b1, b2⟩ := (hb n x).2 hx
          rw [abs_of_nonneg b1]
          linarith [abs_nonneg x])
      (Eventually.of_forall fun x => qd_tendsto x hεne)
  rw [tendsto_nhds_unique hQ hdom, integral_neg]

lemma forwardOriginS : Standalone.JumpShapeOrigin.forwardOriginStatement := by
  intro Ω m₀ P Ft G r J fT Tn L κ κt hL hS hκ hR hκt hRt hH hc
  have hSet := Novel.JumpShapeForwardProof.setting_of hS hS.2.1 hS.2.2.1 hκ hR
  obtain ⟨N, -, hN0, hN⟩ := Novel.JumpShapeCondBProof.null_of_hyp hSet
    (Novel.JumpShapeForwardProof.hyp_iff.1 hH)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0,
    (Novel.JumpShapeForwardProof.lawS Ω m₀ P Ft G r J fT Tn L κ κt hL hS hκ hR hκt hRt hH).1]
    with ω hω he
  obtain ⟨hf, hs⟩ := hN ω hω
  have hcont : ContinuousWithinAt (fun u => Novel.JumpShapeForwardProof.hD r fT Tn u ω) (Ici 0) 0 := by
    have h1 : ContinuousWithinAt (fun u : ℝ => Tn + u) (Ici 0) 0 :=
      (continuous_const.add continuous_id).continuousWithinAt
    refine continuousWithinAt_const.sub ((hc ω).comp_of_eq h1 (fun u hu => ?_) (by simp))
    simp only [mem_Ici] at hu ⊢
    linarith
  obtain ⟨hid, h0⟩ := originS (κ ω) L _ hL hf (fun τ hτ => hSet.2.2.2.2.1 ω τ hτ) hs hcont
  rw [he]
  refine ⟨hid, ?_⟩
  simp only [Novel.JumpShapeForwardProof.hD, add_zero] at h0
  linarith

theorem jumpShapeOrigin : Standalone.JumpShapeOrigin.statement := ⟨originS, forwardOriginS⟩

end Novel.JumpShapeOriginProof

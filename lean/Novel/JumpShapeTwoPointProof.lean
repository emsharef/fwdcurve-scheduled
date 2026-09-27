import Standalone.JumpShapeTwoPoint
import Novel.JumpShapeAffineProof

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeTwoPoint
namespace Novel.JumpShapeTwoPointProof

variable {p Δ : ℝ}

/-- `M(τ) = 1 − p + p e^{−τΔ}`. -/
noncomputable def M2 (p Δ τ : ℝ) : ℝ := 1 - p + p * Real.exp (-τ * Δ)

lemma M2_pos (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) : 0 < M2 p Δ τ := by
  unfold M2; nlinarith [Real.exp_pos (-τ * Δ)]

lemma int_two (f : ℝ → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable f (twoPoint p Δ) ∧ ∫ x, f x ∂twoPoint p Δ = (1 - p) * f 0 + p * f Δ := by
  have h0 : Integrable f (Measure.dirac (0:ℝ)) := integrable_dirac (by simp)
  have hΔ : Integrable f (Measure.dirac Δ) := integrable_dirac (by simp)
  have h0' := h0.smul_measure (c := ENNReal.ofReal (1 - p)) ENNReal.ofReal_ne_top
  have hΔ' := hΔ.smul_measure (c := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  refine ⟨h0'.add_measure hΔ', ?_⟩
  rw [twoPoint, integral_add_measure h0' hΔ', integral_smul_measure, integral_smul_measure,
    MeasureTheory.integral_dirac, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0, smul_eq_mul, smul_eq_mul]

lemma prob (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbabilityMeasure (twoPoint p Δ) :=
  ⟨by simp [twoPoint, ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - p) hp0]⟩

lemma Mlap_two (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (τ : ℝ) : Mlap (twoPoint p Δ) τ = M2 p Δ τ := by
  rw [Mlap, (int_two _ hp0 hp1).2, M2]
  simp

lemma tiltMean_two (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (τ : ℝ) :
    tiltMean (twoPoint p Δ) τ = Δ * qTwo p Δ τ := by
  rw [tiltMean, (int_two _ hp0 hp1).2, Mlap_two hp0 hp1, qTwo, M2]
  simp only [zero_mul, mul_zero, zero_add]
  ring

lemma hasDerivAt_exp (τ : ℝ) :
    HasDerivAt (fun τ => Real.exp (-τ * Δ)) (Real.exp (-τ * Δ) * (-Δ)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => -τ * Δ) (-Δ) τ := by
    simpa using (hasDerivAt_id τ).neg.mul_const Δ
  exact h1.exp

lemma hasDerivAt_M2 (τ : ℝ) : HasDerivAt (M2 p Δ) (-p * Δ * Real.exp (-τ * Δ)) τ := by
  have := ((hasDerivAt_exp (Δ := Δ) τ).const_mul p).const_add (1 - p)
  exact this.congr_deriv (by ring)

lemma hasDerivAt_q (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) :
    HasDerivAt (qTwo p Δ) (-Δ * qTwo p Δ τ * (1 - qTwo p Δ τ)) τ := by
  have hM := M2_pos (Δ := Δ) hp0 hp1 τ
  have := ((hasDerivAt_exp (Δ := Δ) τ).const_mul p).div (hasDerivAt_M2 τ) hM.ne'
  have e : qTwo p Δ = fun τ => p * Real.exp (-τ * Δ) / M2 p Δ τ := funext fun τ => rfl
  rw [e]
  convert this using 1
  beta_reduce
  have hM' : M2 p Δ τ = 1 - p + p * Real.exp (-τ * Δ) := rfl
  field_simp
  rw [hM']
  ring

lemma deriv_parts (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) :
    HasDerivAt (hTwo p Δ) (h1Two p Δ τ) τ ∧ HasDerivAt (h1Two p Δ) (h2Two p Δ τ) τ := by
  have hq := hasDerivAt_q (Δ := Δ) hp0 hp1 τ
  refine ⟨?_, ?_⟩
  · have := hq.const_mul (-Δ)
    rw [show hTwo p Δ = fun y => -Δ * qTwo p Δ y from rfl]
    convert this using 1
    unfold h1Two
    ring
  · have := (hq.const_mul (Δ ^ 2)).mul ((hasDerivAt_const τ (1:ℝ)).sub hq)
    have e : h1Two p Δ = fun τ => Δ ^ 2 * qTwo p Δ τ * (1 - qTwo p Δ τ) := funext fun τ => rfl
    rw [e]
    convert this using 1
    simp only [h2Two, Pi.sub_apply]
    ring

lemma q_pos (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) : 0 < qTwo p Δ τ ∧ qTwo p Δ τ < 1 := by
  have hM := M2_pos (Δ := Δ) hp0 hp1 τ
  have he := Real.exp_pos (-τ * Δ)
  simp only [M2] at hM
  refine ⟨div_pos (mul_pos hp0 he) hM, (div_lt_one hM).2 (by linarith)⟩

lemma h1_pos (hp0 : 0 < p) (hp1 : p < 1) (hΔ : Δ ≠ 0) (τ : ℝ) : 0 < h1Two p Δ τ := by
  obtain ⟨h1, h2⟩ := q_pos (Δ := Δ) hp0 hp1 τ
  unfold h1Two
  exact mul_pos (mul_pos (lt_of_le_of_ne (sq_nonneg Δ) (Ne.symm (pow_ne_zero 2 hΔ))) h1)
    (by linarith)

lemma shapeS : Standalone.JumpShapeTwoPoint.shapeStatement := by
  intro p Δ hp0 hp1 hΔ
  have hP := prob (Δ := Δ) hp0.le hp1.le
  have hK : ∀ τ, HasDerivAt (Klap (twoPoint p Δ)) (hTwo p Δ τ) τ := fun τ => by
    have hM := M2_pos (Δ := Δ) hp0 hp1 τ
    have e : Klap (twoPoint p Δ) = fun τ => Real.log (M2 p Δ τ) :=
      funext fun τ => by rw [Klap, Mlap_two hp0.le hp1.le]
    rw [e]
    convert (hasDerivAt_M2 (p := p) (Δ := Δ) τ).log hM.ne' using 1
    simp only [hTwo, qTwo, M2] at hM ⊢
    field_simp
  refine ⟨hP, fun τ _ => (int_two _ hp0.le hp1.le).1, fun τ hτ => ?_, fun τ => ?_,
    fun τ => ⟨(deriv_parts hp0 hp1 τ).1, (deriv_parts hp0 hp1 τ).2, h1_pos hp0 hp1 hΔ τ⟩⟩
  · have hc : Continuous (hTwo p Δ) := continuous_iff_continuousAt.2 fun τ =>
      (deriv_parts hp0 hp1 τ).1.continuousAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hK x) (hc.intervalIntegrable _ _),
      Klap, Klap, Mlap_two hp0.le hp1.le, Mlap_two hp0.le hp1.le, M2, M2]
    simp
  · rw [tiltMean_two hp0.le hp1.le, hTwo]
    ring

/-! ### Concavity -/

lemma hTwo_cont (hp0 : 0 < p) (hp1 : p < 1) : Continuous (hTwo p Δ) :=
  continuous_iff_continuousAt.2 fun τ => (deriv_parts hp0 hp1 τ).1.continuousAt

lemma h1_cont (hp0 : 0 < p) (hp1 : p < 1) : Continuous (h1Two p Δ) :=
  continuous_iff_continuousAt.2 fun τ => (deriv_parts hp0 hp1 τ).2.continuousAt

lemma deriv2 (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) : deriv^[2] (hTwo p Δ) τ = h2Two p Δ τ := by
  have e : deriv (hTwo p Δ) = h1Two p Δ := funext fun x => (deriv_parts hp0 hp1 x).1.deriv
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, e]
  exact (deriv_parts hp0 hp1 τ).2.deriv

/-- `h″ = −A · Δ(1 − p − p e^{−τΔ})` with `A > 0`. -/
lemma h2_eq (hp0 : 0 < p) (hp1 : p < 1) (τ : ℝ) :
    h2Two p Δ τ = -(Δ ^ 2 * p * (1 - p) * Real.exp (-τ * Δ) / M2 p Δ τ ^ 3) *
      (Δ * (1 - p - p * Real.exp (-τ * Δ))) := by
  have hM := M2_pos (Δ := Δ) hp0 hp1 τ
  have hM' : M2 p Δ τ = 1 - p + p * Real.exp (-τ * Δ) := rfl
  rw [h2Two, show qTwo p Δ τ = p * Real.exp (-τ * Δ) / M2 p Δ τ from rfl]
  field_simp
  rw [hM']
  ring_nf

lemma A_pos (hp0 : 0 < p) (hp1 : p < 1) (hΔ : Δ ≠ 0) (τ : ℝ) :
    0 < Δ ^ 2 * p * (1 - p) * Real.exp (-τ * Δ) / M2 p Δ τ ^ 3 := by
  have := M2_pos (Δ := Δ) hp0 hp1 τ
  have hΔ2 : 0 < Δ ^ 2 := lt_of_le_of_ne (sq_nonneg Δ) (Ne.symm (pow_ne_zero 2 hΔ))
  have : 0 < 1 - p := by linarith
  positivity

/-- `Δ(1 − e^{−yΔ})` has the sign of `y`. -/
lemma sgn_pos (hΔ : Δ ≠ 0) {y : ℝ} (hy : 0 < y) : 0 < Δ * (1 - Real.exp (-y * Δ)) := by
  rcases lt_or_gt_of_ne hΔ with h | h
  · have : 1 < Real.exp (-y * Δ) := Real.one_lt_exp_iff.2 (by nlinarith)
    nlinarith
  · have : Real.exp (-y * Δ) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    nlinarith

lemma sgn_neg (hΔ : Δ ≠ 0) {y : ℝ} (hy : y < 0) : Δ * (1 - Real.exp (-y * Δ)) < 0 := by
  rcases lt_or_gt_of_ne hΔ with h | h
  · have : Real.exp (-y * Δ) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    nlinarith
  · have : 1 < Real.exp (-y * Δ) := Real.one_lt_exp_iff.2 (by nlinarith)
    nlinarith

lemma caseA (hp0 : 0 < p) (hp1 : p < 1) (hΔ : Δ ≠ 0) (hA : 0 ≤ Δ * (1 - 2 * p)) {τ : ℝ}
    (hτ : 0 < τ) : h2Two p Δ τ < 0 := by
  rw [h2_eq hp0 hp1]
  refine mul_neg_of_neg_of_pos (neg_neg_of_pos (A_pos hp0 hp1 hΔ τ)) ?_
  rcases lt_or_gt_of_ne hΔ with h | h
  · have : 1 < Real.exp (-τ * Δ) := Real.one_lt_exp_iff.2 (by nlinarith)
    have h12 : 1 - 2 * p ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    have : 0 < p * (Real.exp (-τ * Δ) - 1) := mul_pos hp0 (by linarith)
    exact mul_pos_of_neg_of_neg h (by linarith)
  · have : Real.exp (-τ * Δ) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have h12 : 0 ≤ 1 - 2 * p := by
      by_contra hc
      push Not at hc
      nlinarith
    have : 0 < p * (1 - Real.exp (-τ * Δ)) := mul_pos hp0 (by linarith)
    exact mul_pos h (by linarith)

/-- With `τ* = log(p/(1 − p))/Δ`, `1 − p − p e^{−τΔ} = (1 − p)(1 − e^{−(τ − τ*)Δ})`. -/
lemma star_eq (hp0 : 0 < p) (hp1 : p < 1) (hΔ : Δ ≠ 0) (τ : ℝ) :
    1 - p - p * Real.exp (-τ * Δ) =
      (1 - p) * (1 - Real.exp (-(τ - Real.log (p / (1 - p)) / Δ) * Δ)) := by
  have hq : 0 < p / (1 - p) := div_pos hp0 (by linarith)
  have h1p : (1:ℝ) - p ≠ 0 := by linarith
  have e : Real.exp (-τ * Δ) = (1 - p) / p *
      Real.exp (-(τ - Real.log (p / (1 - p)) / Δ) * Δ) := by
    rw [show -(τ - Real.log (p / (1 - p)) / Δ) * Δ = -τ * Δ + Real.log (p / (1 - p)) by
      field_simp; ring, Real.exp_add, Real.exp_log hq]
    field_simp
  rw [e]
  field_simp

lemma concavityS : Standalone.JumpShapeTwoPoint.concavityStatement := by
  intro p Δ hp0 hp1 hΔ
  have hc := hTwo_cont (Δ := Δ) hp0 hp1
  refine ⟨fun hA => strictConcaveOn_of_deriv2_neg (convex_Ici 0) hc.continuousOn fun x hx => ?_,
    fun hB => ?_, ?_⟩
  · rw [interior_Ici] at hx
    rw [deriv2 hp0 hp1]
    exact caseA hp0 hp1 hΔ hA hx
  · set τs := Real.log (p / (1 - p)) / Δ
    have hsign : ∀ x, h2Two p Δ x = -(Δ ^ 2 * p * (1 - p) * Real.exp (-x * Δ) / M2 p Δ x ^ 3) *
        ((1 - p) * (Δ * (1 - Real.exp (-(x - τs) * Δ)))) := fun x => by
      rw [h2_eq hp0 hp1, star_eq hp0 hp1 hΔ]
      ring
    have h1p : 0 < 1 - p := by linarith
    refine ⟨?_, strictConvexOn_of_deriv2_pos (convex_Icc 0 τs) hc.continuousOn fun x hx => ?_,
      strictConcaveOn_of_deriv2_neg (convex_Ici τs) hc.continuousOn fun x hx => ?_⟩
    · rcases lt_or_gt_of_ne hΔ with h | h
      · have hp : p < 1 - p := by nlinarith
        have : Real.log (p / (1 - p)) < 0 :=
          Real.log_neg (div_pos hp0 h1p) ((div_lt_one h1p).2 hp)
        exact div_pos_of_neg_of_neg this h
      · have hp : 1 - p < p := by nlinarith
        have : 0 < Real.log (p / (1 - p)) := Real.log_pos ((one_lt_div h1p).2 hp)
        exact div_pos this h
    · rw [interior_Icc] at hx
      rw [deriv2 hp0 hp1, hsign]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (A_pos hp0 hp1 hΔ x))
        (mul_neg_of_pos_of_neg h1p (sgn_neg hΔ (by linarith [hx.2])))
    · rw [interior_Ici] at hx
      rw [deriv2 hp0 hp1, hsign]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (A_pos hp0 hp1 hΔ x))
        (mul_pos h1p (sgn_pos hΔ (by linarith [hx.out])))
  · rintro ⟨a, b, hab⟩
    have hzero : ∀ τ, 0 < τ → h2Two p Δ τ = 0 := fun τ hτ => by
      have hb : ∀ x, 0 < x → h1Two p Δ x = b := fun x hx => by
        have hev : hTwo p Δ =ᶠ[𝓝 x] fun y => a + b * y := by
          filter_upwards [Ioi_mem_nhds hx] with y hy using hab y hy.out.le
        have := (deriv_parts hp0 hp1 x).1.congr_of_eventuallyEq hev.symm
        exact this.unique (((hasDerivAt_id x).const_mul b).const_add a |>.congr_deriv (by simp))
      have hev : h1Two p Δ =ᶠ[𝓝 τ] fun _ => b := by
        filter_upwards [Ioi_mem_nhds hτ] with y hy using hb y hy
      exact ((deriv_parts hp0 hp1 τ).2.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const τ b)
    have k : ∀ τ, 0 < τ → 1 - p - p * Real.exp (-τ * Δ) = 0 := fun τ hτ => by
      have := hzero τ hτ
      rw [h2_eq hp0 hp1] at this
      have hA := A_pos hp0 hp1 hΔ τ
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact (mul_eq_zero.1 h).resolve_left hΔ
    have e1 := k 1 one_pos
    have e2 := k 2 two_pos
    have : Real.exp (-1 * Δ) = Real.exp (-2 * Δ) := by
      have := hp0.ne'
      field_simp at e1 e2 ⊢
      nlinarith
    have := Real.exp_injective this
    exact hΔ (by linarith)

/-! ### `p = ½` -/

lemma halfS : Standalone.JumpShapeTwoPoint.halfStatement := by
  intro Δ τ
  set x := Δ * τ / 2
  have hb := Real.exp_pos (-x)
  have ha : Real.exp x = (Real.exp (-x))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have he : Real.exp (-τ * Δ) = Real.exp (-x) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [x]
    ring
  rw [hTwo, qTwo, he, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, ha]
  field_simp
  ring

/-! ### The tangent Gaussian ramp -/

lemma q_zero (p Δ : ℝ) : qTwo p Δ 0 = p := by simp [qTwo]

lemma gaussianS : Standalone.JumpShapeTwoPoint.gaussianStatement := by
  intro p Δ hp0 hp1 hΔ
  have hy : 0 ≤ p * (1 - p) * Δ ^ 2 := mul_nonneg (mul_nonneg hp0.le (by linarith)) (sq_nonneg _)
  have hG := (Novel.JumpShapeAffineProof.affineS (gaussianReal (p * Δ) (p * (1 - p) * Δ ^ 2).toNNReal)
    ⊤ (-p * Δ) (p * (1 - p) * Δ ^ 2) (by simp)).2 ⟨hy, by congr 1; ring⟩
  have htan : ∀ τ, hGauss p Δ τ = hTwo p Δ 0 + h1Two p Δ 0 * τ := fun τ => by
    simp only [hGauss, hTwo, h1Two, q_zero]
    ring
  refine ⟨hG.1, hG.2, htan, fun hA => ?_⟩
  have hanti : StrictAntiOn (h1Two p Δ) (Ici 0) :=
    strictAntiOn_of_deriv_neg (convex_Ici 0) (h1_cont hp0 hp1).continuousOn fun x hx => by
      rw [interior_Ici] at hx
      rw [(deriv_parts hp0 hp1 x).2.deriv]
      exact caseA hp0 hp1 hΔ hA hx
  have hg : ∀ τ, HasDerivAt (fun τ => hGauss p Δ τ - hTwo p Δ τ)
      (p * (1 - p) * Δ ^ 2 - h1Two p Δ τ) τ := fun τ => by
    have := (((hasDerivAt_id τ).const_mul (p * (1 - p) * Δ ^ 2)).const_add (-p * Δ)).sub
      (deriv_parts (Δ := Δ) hp0 hp1 τ).1
    exact this.congr_deriv (by simp)
  have h10 : h1Two p Δ 0 = p * (1 - p) * Δ ^ 2 := by
    simp only [h1Two, q_zero]
    ring
  have hmono : MonotoneOn (fun τ => hGauss p Δ τ - hTwo p Δ τ) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 fun τ => (hg τ).continuousAt).continuousOn
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) fun x hx => by
        rw [interior_Ici] at hx
        rw [(hg x).deriv]
        have := hanti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.out.le) hx.out.le
        linarith
  refine ⟨fun τ hτ => ?_, hmono⟩
  have := hmono (Set.mem_Ici.2 le_rfl) (show τ ∈ Ici (0:ℝ) from hτ) hτ
  have h0 : hGauss p Δ 0 - hTwo p Δ 0 = 0 := by
    simp only [hGauss, hTwo, q_zero]
    ring
  simp only at this
  linarith

/-! ### The gap for `p = ½`, (45.10) -/

lemma tanh_hasDerivAt (z : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh z ^ 2) z := by
  have e : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [e]
  convert (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne' using 1
  congr 1
  linear_combination (-1 : ℝ) * Real.cosh_sq z

lemma tanh_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Real.tanh z := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hz) (Real.cosh_pos z).le

lemma one_sub_inv (z : ℝ) : 1 - 1 / Real.cosh z ^ 2 = Real.tanh z ^ 2 := by
  have := Real.cosh_pos z
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_sq]
  field_simp
  ring

/-- `0 ≤ z − tanh z ≤ z³/3` for `z ≥ 0`. -/
lemma tanh_bounds {z : ℝ} (hz : 0 ≤ z) : 0 ≤ z - Real.tanh z ∧ z - Real.tanh z ≤ z ^ 3 / 3 := by
  have hψ : ∀ x, HasDerivAt (fun x => x - Real.tanh x) (1 - 1 / Real.cosh x ^ 2) x := fun x =>
    (hasDerivAt_id x).sub (tanh_hasDerivAt x)
  have hψm : MonotoneOn (fun x => x - Real.tanh x) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt).continuousOn
      (fun x _ => (hψ x).differentiableAt.differentiableWithinAt) fun x _ => by
        rw [(hψ x).deriv, one_sub_inv]
        exact sq_nonneg _
  have hle : ∀ x, 0 ≤ x → Real.tanh x ≤ x := fun x hx => by
    have := hψm (Set.mem_Ici.2 le_rfl) (show x ∈ Ici (0:ℝ) from hx) hx
    simp only [Real.tanh_zero, sub_zero] at this
    linarith
  have hφ : ∀ x, HasDerivAt (fun x => Real.tanh x - x + x ^ 3 / 3)
      (1 / Real.cosh x ^ 2 - 1 + x ^ 2) x := fun x => by
    have := ((tanh_hasDerivAt x).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 3 x).div_const 3)
    exact this.congr_deriv (by simp)
  have hφm : MonotoneOn (fun x => Real.tanh x - x + x ^ 3 / 3) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt).continuousOn
      (fun x _ => (hφ x).differentiableAt.differentiableWithinAt) fun x hx => by
        rw [interior_Ici] at hx
        rw [(hφ x).deriv]
        have h1 := one_sub_inv x
        have h2 := tanh_nonneg hx.out.le
        have h3 := hle x hx.out.le
        nlinarith
  have := hψm (Set.mem_Ici.2 le_rfl) (show z ∈ Ici (0:ℝ) from hz) hz
  have := hφm (Set.mem_Ici.2 le_rfl) (show z ∈ Ici (0:ℝ) from hz) hz
  simp only [Real.tanh_zero, sub_zero] at *
  constructor <;> nlinarith

lemma gap_pt (Δ s : ℝ) (hs : 0 ≤ s) :
    hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s = |Δ| / 2 * (|Δ| * s / 2 - Real.tanh (|Δ| * s / 2)) ∧
    0 ≤ hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s ∧
    hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s ≤ |Δ| ^ 4 * s ^ 3 / 48 := by
  have hf : hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s =
      |Δ| / 2 * (|Δ| * s / 2 - Real.tanh (|Δ| * s / 2)) := by
    rw [halfS]
    rcases le_or_gt 0 Δ with h | h
    · rw [abs_of_nonneg h, hGauss]
      ring
    · rw [abs_of_neg h, hGauss, show -Δ * s / 2 = -(Δ * s / 2) by ring, Real.tanh_neg]
      ring
  have hz : 0 ≤ |Δ| * s / 2 := by positivity
  obtain ⟨b1, b2⟩ := tanh_bounds hz
  refine ⟨hf, by rw [hf]; positivity, ?_⟩
  rw [hf]
  calc |Δ| / 2 * (|Δ| * s / 2 - Real.tanh (|Δ| * s / 2)) ≤ |Δ| / 2 * ((|Δ| * s / 2) ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left b2 (by positivity)
    _ = |Δ| ^ 4 * s ^ 3 / 48 := by ring

lemma gapS : Standalone.JumpShapeTwoPoint.gapStatement := by
  intro Δ τ hτ
  obtain ⟨hf, h0, h1⟩ := gap_pt Δ τ hτ
  refine ⟨hf, h0, h1, fun hτp => ?_⟩
  have hc : Continuous fun s => hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s := by
    have := hTwo_cont (p := 1 / 2) (Δ := Δ) (by norm_num) (by norm_num)
    unfold hGauss
    fun_prop
  have hI0 : 0 ≤ ∫ s in (0:ℝ)..τ, (hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s) :=
    intervalIntegral.integral_nonneg hτ fun s hs => (gap_pt Δ s hs.1).2.1
  have hI1 : ∫ s in (0:ℝ)..τ, (hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s) ≤
      ∫ s in (0:ℝ)..τ, |Δ| ^ 4 * s ^ 3 / 48 :=
    intervalIntegral.integral_mono_on hτ (hc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => |Δ| ^ 4 * s ^ 3 / 48).intervalIntegrable _ _)
      fun s hs => (gap_pt Δ s hs.1).2.2
  have hI2 : ∫ s in (0:ℝ)..τ, |Δ| ^ 4 * s ^ 3 / 48 = |Δ| ^ 4 * τ ^ 4 / 192 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hτi : 0 < 1 / τ := by positivity
  refine ⟨mul_nonneg hτi.le hI0, ?_⟩
  calc 1 / τ * ∫ s in (0:ℝ)..τ, (hGauss (1 / 2) Δ s - hTwo (1 / 2) Δ s)
      ≤ 1 / τ * (|Δ| ^ 4 * τ ^ 4 / 192) := by
        rw [← hI2]
        exact mul_le_mul_of_nonneg_left hI1 hτi.le
    _ = |Δ| ^ 4 * τ ^ 3 / 192 := by
        field_simp

theorem jumpShapeTwoPoint : Standalone.JumpShapeTwoPoint.statement :=
  ⟨shapeS, concavityS, halfS, gaussianS, gapS⟩

end Novel.JumpShapeTwoPointProof

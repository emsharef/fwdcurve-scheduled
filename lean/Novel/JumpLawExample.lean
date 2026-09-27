import Novel.MGFUniqueness
import Novel.JumpLawCore
import Novel.PiecewiseAffineIntegralProof
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Claim 008, Part (d): the non-Gaussian example

The claim's construction with `L₁ = 1`, `y₁ = y₂ = 1`: under `Q = N(-1, 1) ⊗ N(0, 1)` the
measure `P = exp (L₁ X₁ + ½ L₁² y₁) · Q` is the product `N(0, 1) ⊗ N(0, 1)` (tilting a
product by a function of the first coordinate tilts the first marginal, and `N(-1, 1)` tilted
by `exp x` is `N(0, 1)`), so the example is set up directly on `P = N(0, 1) ⊗ N(0, 1)` with
`X₁ = fst`, `Z = snd`, and `X₂ = sign (X₁ + 1) · |Z|`.

This file proves the ingredients: the law of `X₁`, and the two Laplace identities behind (H),
`E[exp (-t X₁)] = exp (t²/2)` and `E[exp (-X₁ - t X₂)] = exp (1/2 + t²/2)`. The second uses
Fubini, the symmetry of the tilted density `exp (-x) φ(x)` about `-1` (through
`gaussianReal_tilted`), and the pointwise identity `exp (t|z|) + exp (-t|z|) = exp (tz) + exp (-tz)`.
-/

open MeasureTheory ProbabilityTheory Set

namespace Novel.JumpLawExample

/-- The probability space of the example: `N(0, 1) ⊗ N(0, 1)`. -/
noncomputable def P : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure P := by unfold P; infer_instance

/-- `X₁ = fst`. -/
def X1 (ω : ℝ × ℝ) : ℝ := ω.1

/-- `X₂ = sign (X₁ + 1) · |Z|` with `Z = snd`. -/
noncomputable def X2 (ω : ℝ × ℝ) : ℝ := if -1 < ω.1 then |ω.2| else -|ω.2|

lemma measurable_X1 : Measurable X1 := measurable_fst

lemma measurable_X2 : Measurable X2 := by
  unfold X2
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    measurable_snd.norm measurable_snd.norm.neg

/-- The law of `X₁` under `P` is `N(0, 1)`. -/
lemma hasLaw_X1 : HasLaw X1 (gaussianReal 0 1) P :=
  ⟨measurable_fst.aemeasurable, by
    show ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.fst = gaussianReal 0 1
    exact Measure.fst_prod⟩

/-- `E[exp (-t X₁)] = exp (t²/2)`. -/
lemma integral_exp_X1 (t : ℝ) : ∫ ω, Real.exp (-t * X1 ω) ∂P = Real.exp (t ^ 2 / 2) := by
  have := mgf_gaussianReal hasLaw_X1 (-t)
  simp only [mgf, NNReal.coe_one] at this
  rw [this]
  congr 1
  ring

/-- The pointwise identity `exp (t|z|) + exp (-t|z|) = exp (tz) + exp (-tz)`. -/
lemma exp_abs_add (t z : ℝ) :
    Real.exp (t * |z|) + Real.exp (-t * |z|) = Real.exp (t * z) + Real.exp (-t * z) := by
  rcases le_or_gt 0 z with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    ring_nf

/-- `∫ exp (u |z|) dN(0,1)` is finite. -/
lemma integrable_exp_abs (u : ℝ) :
    Integrable (fun z : ℝ => Real.exp (u * |z|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) u).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-u))).mono ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul measurable_norm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
    rcases le_or_gt 0 z with h | h
    · rw [abs_of_nonneg h]
      linarith [Real.exp_pos (-u * z)]
    · rw [abs_of_neg h]
      have : u * -z = -u * z := by ring
      rw [this]
      linarith [Real.exp_pos (u * z)]

/-- `E_{N(0,1)}[exp (t|Z|)] + E[exp (-t|Z|)] = 2 exp (t²/2)`. -/
lemma integral_exp_abs_add (t : ℝ) :
    ∫ z, Real.exp (t * |z|) ∂(gaussianReal 0 1) + ∫ z, Real.exp (-t * |z|) ∂(gaussianReal 0 1) =
      2 * Real.exp (t ^ 2 / 2) := by
  rw [← integral_add (integrable_exp_abs t) (integrable_exp_abs (-t))]
  simp_rw [exp_abs_add]
  rw [integral_add (integrable_exp_mul_gaussianReal t) (integrable_exp_mul_gaussianReal (-t))]
  have h1 := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  have h2 := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (-t)
  simp only [mgf, id, zero_mul, zero_add, NNReal.coe_one, one_mul] at h1 h2
  rw [h1, h2]
  ring_nf

/-- The two halves of `∫ exp (-x) dN(0,1)` on `{x > -1}` and `{x ≤ -1}` are equal: the density
`exp (-x) φ(x)` is that of `N(-1, 1)` up to the constant `exp (1/2)`, and `N(-1, 1)` is
symmetric about `-1`. -/
lemma integral_exp_neg_halves :
    ∫ x in Ioi (-1 : ℝ), Real.exp (-x) ∂(gaussianReal 0 1) =
      ∫ x in Iic (-1 : ℝ), Real.exp (-x) ∂(gaussianReal 0 1) := by
  -- the tilt of `N(0,1)` by `-x` is `N(-1,1)`
  have htilt : (gaussianReal 0 1).tilted (fun x => (-1 : ℝ) * x) = gaussianReal (-1) 1 := by
    rw [Novel.MGFUniqueness.gaussianReal_tilted]
    congr 1
    simp
  have hint : Integrable (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal (-1)
  have hpos : 0 < ∫ x, Real.exp ((-1 : ℝ) * x) ∂(gaussianReal 0 1) := integral_exp_pos hint
  -- set integrals of `exp (-x)` through the tilted measure
  have hset : ∀ s : Set ℝ, MeasurableSet s →
      ∫ x in s, Real.exp (-x) ∂(gaussianReal 0 1) =
        (∫ x, Real.exp ((-1 : ℝ) * x) ∂(gaussianReal 0 1)) * (gaussianReal (-1) 1).real s := by
    intro s hs
    rw [← htilt, measureReal_def, tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal
      ((hint.div_const _).integrableOn)
      (Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hpos.le),
      ENNReal.toReal_ofReal (integral_nonneg fun x => div_nonneg (Real.exp_pos _).le hpos.le),
      integral_div, mul_div_cancel₀ _ hpos.ne']
    refine setIntegral_congr_fun hs fun x _ => ?_
    simp
  rw [hset _ measurableSet_Ioi, hset _ measurableSet_Iic]
  congr 1
  -- `N(-1,1)(Ioi (-1)) = N(-1,1)(Iic (-1))`: translate to `N(0,1)` and reflect
  have hmap : gaussianReal (-1) 1 = (gaussianReal 0 1).map (fun x => x + -1) := by
    rw [gaussianReal_map_add_const]
    simp
  have hneg : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]
    simp
  have hIoi : (gaussianReal (-1) 1).real (Ioi (-1)) = (gaussianReal 0 1).real (Ioi 0) := by
    rw [hmap, measureReal_def, measureReal_def,
      Measure.map_apply (f := fun x : ℝ => x + -1) (by fun_prop) measurableSet_Ioi]
    congr 2
    ext x
    simp
  have hIic : (gaussianReal (-1) 1).real (Iic (-1)) = (gaussianReal 0 1).real (Iic 0) := by
    rw [hmap, measureReal_def, measureReal_def,
      Measure.map_apply (f := fun x : ℝ => x + -1) (by fun_prop) measurableSet_Iic]
    congr 2
    ext x
    simp
  have hrefl : (gaussianReal 0 1).real (Iic 0) = (gaussianReal 0 1).real (Ici 0) := by
    conv_lhs => rw [← hneg]
    rw [measureReal_def, measureReal_def, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 2
    ext x
    simp
  have hatom : (gaussianReal 0 1).real ({0} : Set ℝ) = 0 := by
    rw [measureReal_def, gaussianReal_of_var_ne_zero _ one_ne_zero,
      withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hsplit : (gaussianReal 0 1).real (Ici 0) =
      (gaussianReal 0 1).real ({0} : Set ℝ) + (gaussianReal 0 1).real (Ioi 0) := by
    rw [← measureReal_union (disjoint_singleton_left.2 (by simp)) measurableSet_Ioi]
    congr 1
    ext x
    simp [le_iff_lt_or_eq, eq_comm]
  rw [hIoi, hIic, hrefl, hsplit, hatom, zero_add]

/-- `∫ exp (-x) dN(0,1) = exp (1/2)`. -/
lemma integral_exp_neg : ∫ x, Real.exp (-x) ∂(gaussianReal 0 1) = Real.exp (1 / 2) := by
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (-1)
  simp only [mgf, id, zero_mul, zero_add, NNReal.coe_one, one_mul] at this
  rw [show (fun x : ℝ => Real.exp (-x)) = fun x => Real.exp (-1 * x) by funext x; ring_nf, this]
  norm_num

/-- Each half of `∫ exp (-x) dN(0,1)` is `exp (1/2) / 2`. -/
lemma integral_exp_neg_Ioi :
    ∫ x in Ioi (-1 : ℝ), Real.exp (-x) ∂(gaussianReal 0 1) = Real.exp (1 / 2) / 2 := by
  have hsum : ∫ x in Ioi (-1 : ℝ), Real.exp (-x) ∂(gaussianReal 0 1) +
      ∫ x in Iic (-1 : ℝ), Real.exp (-x) ∂(gaussianReal 0 1) = Real.exp (1 / 2) := by
    rw [← integral_exp_neg, ← setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by
      simp only [mem_Ioi] at hx; simp only [mem_Iic] at hx'; linarith) measurableSet_Iic
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1) |>.congr (Filter.Eventually.of_forall
        fun x => by simp) |>.integrableOn)
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1) |>.congr (Filter.Eventually.of_forall
        fun x => by simp) |>.integrableOn)]
    rw [Ioi_union_Iic]
    simp
  linarith [integral_exp_neg_halves]

/-- The Fubini computation behind (H) on the second interval:
`E[exp (-X₁) exp (-t X₂)] = exp (1/2) exp (t²/2)`. -/
lemma integral_exp_X1_X2 (t : ℝ) :
    ∫ ω, Real.exp (-X1 ω) * Real.exp (-t * X2 ω) ∂P = Real.exp (1 / 2) * Real.exp (t ^ 2 / 2) := by
  have hdecomp : (fun ω : ℝ × ℝ => Real.exp (-X1 ω) * Real.exp (-t * X2 ω)) =
      fun ω => (Ioi (-1 : ℝ)).indicator (fun x => Real.exp (-x)) ω.1 * Real.exp (-t * |ω.2|) +
        (Iic (-1 : ℝ)).indicator (fun x => Real.exp (-x)) ω.1 * Real.exp (t * |ω.2|) := by
    funext ω
    simp only [X1, X2]
    by_cases h : -1 < ω.1
    · simp only [h, ↓reduceIte, indicator_of_mem (mem_Ioi.2 h), indicator_of_notMem (by simp [h] :
        ω.1 ∉ Iic (-1 : ℝ))]
      ring
    · simp only [h, ↓reduceIte, indicator_of_notMem (by simpa using h : ω.1 ∉ Ioi (-1 : ℝ)),
        indicator_of_mem (mem_Iic.2 (not_lt.1 h))]
      ring_nf
  have hexp : Integrable (fun x : ℝ => Real.exp (-x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1)).congr
      (Filter.Eventually.of_forall fun x => by simp)
  have hi1 : Integrable (fun ω : ℝ × ℝ =>
      (Ioi (-1 : ℝ)).indicator (fun x => Real.exp (-x)) ω.1 * Real.exp (-t * |ω.2|)) P :=
    (hexp.indicator measurableSet_Ioi).mul_prod (integrable_exp_abs (-t))
  have hi2 : Integrable (fun ω : ℝ × ℝ =>
      (Iic (-1 : ℝ)).indicator (fun x => Real.exp (-x)) ω.1 * Real.exp (t * |ω.2|)) P :=
    (hexp.indicator measurableSet_Iic).mul_prod (integrable_exp_abs t)
  rw [hdecomp, integral_add hi1 hi2]
  show ∫ ω, _ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) +
    ∫ ω, _ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  have e1 := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x => (Ioi (-1 : ℝ)).indicator (fun x => Real.exp (-x)) x) (fun y => Real.exp (-t * |y|))
  have e2 := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x => (Iic (-1 : ℝ)).indicator (fun x => Real.exp (-x)) x) (fun y => Real.exp (t * |y|))
  beta_reduce at e1 e2
  rw [e1, e2, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Iic, ← integral_exp_neg_halves, integral_exp_neg_Ioi,
    ← mul_add, add_comm, integral_exp_abs_add]
  ring

/-- The dates of the example: `T_0 = 0`, `T_1 = 1`, `T_2 = 2`. -/
def τ (k : ℕ) : ℝ := k

/-- The jump `ξ` of the example: `X₁ + (u - 1)` on `[1, 2)`, `X₂ + (u - 2)` on `[2, ∞)`, `0`
before `1`. -/
noncomputable def ξ (u : ℝ) (ω : ℝ × ℝ) : ℝ :=
  if u < 1 then 0 else if u < 2 then X1 ω + (u - 1) else X2 ω + (u - 2)

lemma integral_ξ_of_le_two {T : ℝ} (h1 : 1 ≤ T) (h2 : T ≤ 2) (ω : ℝ × ℝ) :
    ∫ u in (1 : ℝ)..T, ξ u ω = X1 ω * (T - 1) + (T - 1) ^ 2 / 2 := by
  rw [intervalIntegral.integral_congr_Ioo_of_le h1 (g := fun u => X1 ω + (u - 1) • (1 : ℝ))
    (fun u hu => by
      have h1 : ¬ u < 1 := not_lt.2 (by linarith [hu.1])
      have h2 : u < 2 := by linarith [hu.2]
      simp only [ξ, smul_eq_mul, mul_one, h1, h2, ↓reduceIte]),
    Novel.PiecewiseAffineIntegralProof.integral_affine]
  simp only [smul_eq_mul, mul_one]
  ring

lemma intervalIntegrable_ξ_one_two (ω : ℝ × ℝ) : IntervalIntegrable (ξ · ω) volume 1 2 := by
  refine ((by fun_prop : Continuous fun u : ℝ => X1 ω + (u - 1)).intervalIntegrable 1 2).congr_uIoo ?_
  rw [uIoo_of_le (by norm_num)]
  intro u hu
  have h1 : ¬ u < 1 := not_lt.2 (by linarith [hu.1])
  simp only [ξ, h1, hu.2, ↓reduceIte]

lemma intervalIntegrable_ξ_two {T : ℝ} (hT : 2 ≤ T) (ω : ℝ × ℝ) :
    IntervalIntegrable (ξ · ω) volume 2 T := by
  refine ((by fun_prop : Continuous fun u : ℝ => X2 ω + (u - 2)).intervalIntegrable 2 T).congr_uIoo ?_
  rw [uIoo_of_le hT]
  intro u hu
  have h1 : ¬ u < 1 := not_lt.2 (by linarith [hu.1])
  have h2 : ¬ u < 2 := not_lt.2 (by linarith [hu.1])
  simp only [ξ, h1, h2, ↓reduceIte]

lemma integral_ξ_of_two_le {T : ℝ} (hT : 2 ≤ T) (ω : ℝ × ℝ) :
    ∫ u in (1 : ℝ)..T, ξ u ω = X1 ω + 1 / 2 + X2 ω * (T - 2) + (T - 2) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_ξ_one_two ω)
    (intervalIntegrable_ξ_two hT ω), integral_ξ_of_le_two (by norm_num) le_rfl,
    intervalIntegral.integral_congr_Ioo_of_le hT (g := fun u => X2 ω + (u - 2) • (1 : ℝ))
    (fun u hu => by
      have h1 : ¬ u < 1 := not_lt.2 (by linarith [hu.1])
      have h2 : ¬ u < 2 := not_lt.2 (by linarith [hu.1])
      simp only [ξ, smul_eq_mul, mul_one, h1, h2, ↓reduceIte]),
    Novel.PiecewiseAffineIntegralProof.integral_affine]
  simp only [smul_eq_mul, mul_one]
  ring

/-- (H) for the example, with `G = ⊥`. -/
lemma H_example : ∀ T : ℝ, τ 1 ≤ T →
    P[fun ω => Real.exp (-(∫ u in τ 1..T, ξ u ω)) | ⊥] =ᵐ[P] 1 := by
  intro T hT
  simp only [τ, Nat.cast_one] at hT ⊢
  rw [condExp_bot]
  refine Filter.Eventually.of_forall fun _ => ?_
  show ∫ ω, Real.exp (-(∫ u in (1 : ℝ)..T, ξ u ω)) ∂P = 1
  rcases le_or_gt T 2 with h2 | h2
  · simp_rw [integral_ξ_of_le_two hT h2]
    have : (fun ω => Real.exp (-(X1 ω * (T - 1) + (T - 1) ^ 2 / 2))) =
        fun ω => Real.exp (-((T - 1) ^ 2 / 2)) * Real.exp (-(T - 1) * X1 ω) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this, integral_const_mul, integral_exp_X1, ← Real.exp_add]
    simp
  · simp_rw [integral_ξ_of_two_le h2.le]
    have : (fun ω => Real.exp (-(X1 ω + 1 / 2 + X2 ω * (T - 2) + (T - 2) ^ 2 / 2))) =
        fun ω => Real.exp (-(1 / 2 + (T - 2) ^ 2 / 2)) *
          (Real.exp (-X1 ω) * Real.exp (-(T - 2) * X2 ω)) := by
      funext ω
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [this, integral_const_mul, integral_exp_X1_X2, ← Real.exp_add, ← Real.exp_add]
    simp

/-- The moment generating function of `X₂`: `E[exp (u X₂)] = p h(u) + (1 - p) h(-u)` with
`p = N(0,1)(-1, ∞)` and `h(u) = E[exp (u |Z|)]`. -/
lemma mgf_X2 (u : ℝ) :
    mgf X2 P u = (gaussianReal 0 1).real (Ioi (-1)) * ∫ z, Real.exp (u * |z|) ∂(gaussianReal 0 1) +
      (gaussianReal 0 1).real (Iic (-1)) * ∫ z, Real.exp (-u * |z|) ∂(gaussianReal 0 1) := by
  have hdecomp : (fun ω : ℝ × ℝ => Real.exp (u * X2 ω)) =
      fun ω => (Ioi (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.1 * Real.exp (u * |ω.2|) +
        (Iic (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.1 * Real.exp (-u * |ω.2|) := by
    funext ω
    simp only [X2]
    by_cases h : -1 < ω.1
    · simp only [h, ↓reduceIte, indicator_of_mem (mem_Ioi.2 h), indicator_of_notMem (by simp [h] :
        ω.1 ∉ Iic (-1 : ℝ))]
      ring
    · simp only [h, ↓reduceIte, indicator_of_notMem (by simpa using h : ω.1 ∉ Ioi (-1 : ℝ)),
        indicator_of_mem (mem_Iic.2 (not_lt.1 h))]
      ring_nf
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const 1
  have hi1 : Integrable (fun ω : ℝ × ℝ =>
      (Ioi (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.1 * Real.exp (u * |ω.2|)) P :=
    (hone.indicator measurableSet_Ioi).mul_prod (integrable_exp_abs u)
  have hi2 : Integrable (fun ω : ℝ × ℝ =>
      (Iic (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.1 * Real.exp (-u * |ω.2|)) P :=
    (hone.indicator measurableSet_Iic).mul_prod (integrable_exp_abs (-u))
  simp only [mgf]
  rw [hdecomp, integral_add hi1 hi2]
  show ∫ ω, _ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) +
    ∫ ω, _ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  have e1 := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x => (Ioi (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) x) (fun y => Real.exp (u * |y|))
  have e2 := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x => (Iic (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) x) (fun y => Real.exp (-u * |y|))
  beta_reduce at e1 e2
  rw [e1, e2, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iic,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/-- `N(0,1)(-1, ∞) + N(0,1)(-∞, -1] = 1`. -/
lemma real_Ioi_add_Iic :
    (gaussianReal 0 1).real (Ioi (-1)) + (gaussianReal 0 1).real (Iic (-1)) = 1 := by
  rw [← measureReal_union (Set.disjoint_left.2 fun x hx hx' => by
    simp only [mem_Ioi] at hx; simp only [mem_Iic] at hx'; linarith) measurableSet_Iic,
    Ioi_union_Iic]
  simp

/-- The symmetrized identity `mgf X₂ (u) + mgf X₂ (-u) = 2 exp (u²/2)`. -/
lemma mgf_X2_add_neg (u : ℝ) : mgf X2 P u + mgf X2 P (-u) = 2 * Real.exp (u ^ 2 / 2) := by
  rw [mgf_X2, mgf_X2, neg_neg]
  have h := integral_exp_abs_add u
  have hsum := real_Ioi_add_Iic
  set a := (gaussianReal 0 1).real (Ioi (-1))
  set b := (gaussianReal 0 1).real (Iic (-1))
  set I₁ := ∫ z, Real.exp (u * |z|) ∂(gaussianReal 0 1)
  set I₂ := ∫ z, Real.exp (-u * |z|) ∂(gaussianReal 0 1)
  have : a * I₁ + b * I₂ + (a * I₂ + b * I₁) = (a + b) * (I₁ + I₂) := by ring
  rw [this, hsum, one_mul, h]

/-- `N(0,1)((-1, 0]) > 0`: the density is positive. -/
lemma gaussian_Ioc_pos : 0 < gaussianReal 0 1 (Ioc (-1 : ℝ) 0) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ measurableSet_Ioc,
    setLIntegral_pos_iff (measurable_gaussianPDF _ _)]
  have : Function.support (gaussianPDF 0 1) = univ := by
    ext x
    simp
  rw [this, univ_inter, Real.volume_Ioc]
  norm_num

/-- `P(X₂ > 0) = N(0,1)(-1, ∞)`. -/
lemma P_X2_pos : P.real {ω | 0 < X2 ω} = (gaussianReal 0 1).real (Ioi (-1)) := by
  have hset : {ω : ℝ × ℝ | 0 < X2 ω} = Ioi (-1 : ℝ) ×ˢ {z : ℝ | z ≠ 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, X2, mem_prod, mem_Ioi]
    by_cases h : -1 < ω.1
    · simp [h, abs_pos]
    · simp only [h, ↓reduceIte, false_and, iff_false, not_lt]
      exact neg_nonpos.2 (abs_nonneg _)
  have hz : gaussianReal 0 1 {z : ℝ | z ≠ 0} = 1 := by
    have h0 : gaussianReal 0 1 ({0} : Set ℝ) = 0 := by
      rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (measurableSet_singleton 0)]
      simp
    have : {z : ℝ | z ≠ 0} = ({0} : Set ℝ)ᶜ := by ext; simp
    rw [this, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), h0, measure_univ,
      tsub_zero]
  rw [hset, measureReal_def, measureReal_def]
  show (((gaussianReal 0 1).prod (gaussianReal 0 1)) _).toReal = _
  rw [Measure.prod_prod, hz, mul_one]

/-- `N(0,1)(0, ∞) = 1/2`. -/
lemma gaussian_Ioi_zero_half : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
  have hneg : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]
    simp
  have hrefl : (gaussianReal 0 1).real (Iic 0) = (gaussianReal 0 1).real (Ici 0) := by
    conv_lhs => rw [← hneg]
    rw [measureReal_def, measureReal_def, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 2
    ext x
    simp
  have hatom : (gaussianReal 0 1).real ({0} : Set ℝ) = 0 := by
    rw [measureReal_def, gaussianReal_of_var_ne_zero _ one_ne_zero,
      withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hsplit : (gaussianReal 0 1).real (Ici 0) =
      (gaussianReal 0 1).real ({0} : Set ℝ) + (gaussianReal 0 1).real (Ioi 0) := by
    rw [← measureReal_union (disjoint_singleton_left.2 (by simp)) measurableSet_Ioi]
    congr 1
    ext x
    simp [le_iff_lt_or_eq, eq_comm]
  have htot : (gaussianReal 0 1).real (Iic 0) + (gaussianReal 0 1).real (Ioi 0) = 1 := by
    rw [← measureReal_union (Set.disjoint_left.2 fun x hx hx' => by
      simp only [mem_Iic] at hx; simp only [mem_Ioi] at hx'; linarith) measurableSet_Ioi,
      Iic_union_Ioi]
    simp
  rw [hrefl, hsplit, hatom, zero_add] at htot
  linarith

/-- `X₂` is not Gaussian under `P`. -/
lemma not_gaussian_X2 : ¬ ∃ (m : ℝ) (v : NNReal), HasLaw X2 (gaussianReal m v) P := by
  rintro ⟨m, v, hlaw⟩
  -- the symmetrized moment generating function identity forces `m = 0` and `v = 1`
  have hmgf : ∀ u : ℝ, Real.exp (m * u + v * u ^ 2 / 2) + Real.exp (m * -u + v * (-u) ^ 2 / 2) =
      2 * Real.exp (u ^ 2 / 2) := fun u => by
    rw [← mgf_gaussianReal hlaw u, ← mgf_gaussianReal hlaw (-u)]
    exact mgf_X2_add_neg u
  set c : ℝ := Real.exp m + Real.exp (-m) with hc
  have hcpos : 0 < c := by positivity
  have h1 : Real.exp ((v : ℝ) / 2) * c = 2 * Real.exp (1 / 2) := by
    have := hmgf 1
    rw [hc, mul_add, ← Real.exp_add, ← Real.exp_add]
    convert this using 3 <;> ring_nf
  have h2 : Real.exp (2 * (v : ℝ)) * (c ^ 2 - 2) = 2 * Real.exp 2 := by
    have := hmgf 2
    have hsq : c ^ 2 - 2 = Real.exp (2 * m) + Real.exp (-(2 * m)) := by
      rw [hc]
      have e1 : Real.exp (2 * m) = Real.exp m * Real.exp m := by rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (-(2 * m)) = Real.exp (-m) * Real.exp (-m) := by
        rw [← Real.exp_add]; ring_nf
      have e3 : Real.exp m * Real.exp (-m) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [e1, e2, e3]
    rw [hsq, mul_add, ← Real.exp_add, ← Real.exp_add]
    convert this using 3 <;> ring_nf
  -- eliminate the exponentials: `c ^ 2 - 2 = c ^ 4 / 8` hence `c = 2`
  have hE : Real.exp ((v : ℝ) / 2) ^ 4 = Real.exp (2 * v) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE2 : Real.exp (1 / 2 : ℝ) ^ 4 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc2 : c = 2 := by
    have h1' : Real.exp ((v : ℝ) / 2) = 2 * Real.exp (1 / 2) / c := by
      rw [eq_div_iff hcpos.ne']
      exact h1
    have hEv : Real.exp (2 * (v : ℝ)) = 16 * Real.exp 2 / c ^ 4 := by
      rw [← hE, h1', div_pow, mul_pow, hE2]
      norm_num
    rw [hEv] at h2
    have hc4 : c ^ 4 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, div_eq_iff hc4] at h2
    -- `16 e² (c² - 2) = 2 e² c⁴`, hence `8 (c² - 2) = c⁴`, hence `(c² - 4)² = 0`
    have h3 : Real.exp 2 * (8 * (c ^ 2 - 2) - c ^ 4) = 0 := by linear_combination h2 / 2
    have h4 : 8 * (c ^ 2 - 2) - c ^ 4 = 0 :=
      (mul_eq_zero.1 h3).resolve_left (Real.exp_pos 2).ne'
    have h5 : (c ^ 2 - 4) ^ 2 = 0 := by nlinarith
    have h6 : c ^ 2 = 4 := by
      have := pow_eq_zero_iff (n := 2) (a := c ^ 2 - 4) two_ne_zero |>.1 h5
      linarith
    nlinarith
  have hm : m = 0 := by
    have : Real.exp m * Real.exp (-m) = 1 := by rw [← Real.exp_add]; simp
    have h3 : (Real.exp m - 1) ^ 2 = 0 := by
      have : Real.exp m + Real.exp (-m) = 2 := hc2
      nlinarith [Real.exp_pos m]
    have : Real.exp m = 1 := by nlinarith [pow_eq_zero_iff (n := 2) (a := Real.exp m - 1) two_ne_zero |>.1 h3]
    exact Real.exp_eq_one_iff m |>.1 this
  have hv : (v : ℝ) = 1 := by
    rw [hc2] at h1
    have := Real.exp_injective (by linarith : Real.exp ((v : ℝ) / 2) = Real.exp (1 / 2))
    linarith
  -- so `X₂ ~ N(0, 1)` and `P(X₂ > 0) = 1/2`, but `P(X₂ > 0) = N(0,1)(-1, ∞) > 1/2`
  have hv' : v = 1 := by exact_mod_cast hv
  rw [hm, hv'] at hlaw
  have hP : P.real {ω | 0 < X2 ω} = (gaussianReal 0 1).real (Ioi 0) := by
    rw [← hlaw.map_eq, measureReal_def, measureReal_def,
      Measure.map_apply measurable_X2 measurableSet_Ioi]
    rfl
  rw [P_X2_pos, gaussian_Ioi_zero_half] at hP
  have hsplit : (gaussianReal 0 1).real (Ioi (-1)) =
      (gaussianReal 0 1).real (Ioc (-1) 0) + (gaussianReal 0 1).real (Ioi 0) := by
    rw [← measureReal_union (Set.disjoint_left.2 fun x hx hx' => by
      simp only [mem_Ioc] at hx; simp only [mem_Ioi] at hx'; linarith) measurableSet_Ioi,
      Ioc_union_Ioi_eq_Ioi (by norm_num)]
  rw [hsplit, gaussian_Ioi_zero_half] at hP
  have : (gaussianReal 0 1).real (Ioc (-1) 0) = 0 := by linarith
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at this
  rcases this with h | h
  · exact gaussian_Ioc_pos.ne' h
  · exact (measure_ne_top _ _) h

/-- The law of `X₁`, with the cast used in the statement. -/
lemma hasLaw_X1' : HasLaw X1 (gaussianReal 0 (1 : ℝ).toNNReal) P := by
  rw [Real.toNNReal_one]
  exact hasLaw_X1

end Novel.JumpLawExample

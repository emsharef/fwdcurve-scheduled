import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Tilted
import Novel.MGF

/-!
# Law uniqueness from the moment generating function near zero

Supporting lemma for Claim 008 (its Step 6, the "uniqueness theorem for moment generating
functions" listed under Not shown, `[curtiss1942note]`) and, per Red's review of that claim,
for D3: two real random variables whose moment generating functions are finite and equal on
an open interval `(-ε, ε)` around `0` have the same law (`map_eq_of_mgf_eqOn`); in particular
a random variable whose moment generating function agrees near `0` with that of `N(m, v)` has
law `N(m, v)` (`map_eq_gaussianReal_of_mgf_eqOn`).

Route: on the vertical strip over `(-ε, ε)` both complex moment generating functions are
analytic (`ProbabilityTheory.analyticOnNhd_complexMGF`) and agree on a real sequence
converging to `0`, so they agree on the strip by the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`); on the imaginary axis they are the
characteristic functions (`complexMGF_mul_I`), which determine the laws
(`Measure.ext_of_charFun`).
-/

open MeasureTheory ProbabilityTheory Complex Set Filter Topology

namespace Novel.MGFUniqueness

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

/-- The open vertical strip over `(-ε, ε)` is preconnected (it is convex). -/
lemma isPreconnected_strip (ε : ℝ) : IsPreconnected {z : ℂ | z.re ∈ Ioo (-ε) ε} :=
  ((convex_Ioo (-ε) ε).linear_preimage Complex.reLm).isPreconnected

/-- A real sequence `ε / 2 / (n + 1)` tending to `0` within `ℂ \ {0}`. -/
lemma tendsto_seq {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((ε / 2 * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h1 : Tendsto (fun n : ℕ => ε / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ε / 2 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (ε / 2)
    rw [mul_zero] at h1
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at h2
    exact h2
  · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity

/-- Two real random variables whose moment generating functions are finite and equal on an
open interval `(-ε, ε)` around `0` have the same law. -/
theorem map_eq_of_mgf_eqOn [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ') {ε : ℝ} (hε : 0 < ε)
    (hintX : ∀ t ∈ Ioo (-ε) ε, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hintY : ∀ t ∈ Ioo (-ε) ε, Integrable (fun ω => Real.exp (t * Y ω)) μ')
    (h : ∀ t ∈ Ioo (-ε) ε, mgf X μ t = mgf Y μ' t) :
    μ.map X = μ'.map Y := by
  set U : Set ℂ := {z | z.re ∈ Ioo (-ε) ε} with hU
  have hsubX : Ioo (-ε) ε ⊆ integrableExpSet X μ := fun t ht => hintX t ht
  have hsubY : Ioo (-ε) ε ⊆ integrableExpSet Y μ' := fun t ht => hintY t ht
  have hfX : AnalyticOnNhd ℂ (complexMGF X μ) U :=
    analyticOnNhd_complexMGF.mono fun z hz => interior_maximal hsubX isOpen_Ioo hz
  have hfY : AnalyticOnNhd ℂ (complexMGF Y μ') U :=
    analyticOnNhd_complexMGF.mono fun z hz => interior_maximal hsubY isOpen_Ioo hz
  have h0 : (0 : ℂ) ∈ U := by
    show (0 : ℂ).re ∈ Ioo (-ε) ε
    rw [Complex.zero_re]
    exact ⟨by linarith, hε⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF X μ z = complexMGF Y μ' z := by
    refine (tendsto_seq hε).frequently (Eventually.of_forall fun n => ?_).frequently
    have hn : ε / 2 * (1 / ((n : ℝ) + 1)) ∈ Ioo (-ε) ε := by
      have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      constructor <;> nlinarith
    rw [complexMGF_ofReal, complexMGF_ofReal, h _ hn]
  have hEq : EqOn (complexMGF X μ) (complexMGF Y μ') U :=
    hfX.eqOn_of_preconnected_of_frequently_eq hfY (isPreconnected_strip ε) h0 hfreq
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  refine hEq ?_
  show ((t : ℂ) * I).re ∈ Ioo (-ε) ε
  simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  exact ⟨by linarith, hε⟩

/-- A real random variable whose moment generating function is finite on `(-ε, ε)` and agrees
there with that of `N(m, v)` has law `N(m, v)`. -/
theorem map_eq_gaussianReal_of_mgf_eqOn [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    {ε : ℝ} (hε : 0 < ε) {m : ℝ} {v : NNReal}
    (hint : ∀ t ∈ Ioo (-ε) ε, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (h : ∀ t ∈ Ioo (-ε) ε, mgf X μ t = Real.exp (m * t + v * t ^ 2 / 2)) :
    μ.map X = gaussianReal m v := by
  have := map_eq_of_mgf_eqOn (Y := id) (μ' := gaussianReal m v) hX aemeasurable_id hε hint
    (fun t _ => integrable_exp_mul_gaussianReal t)
    (fun t ht => by rw [h t ht, mgf_id_gaussianReal])
  simpa using this

/-- The law of `X` under the tilt of `μ` by `g ∘ X` is the tilt of the law of `X` by `g`. -/
lemma map_tilted (hX : Measurable X) {g : ℝ → ℝ} (hg : Measurable g) :
    (μ.tilted (fun ω => g (X ω))).map X = (μ.map X).tilted g := by
  ext s hs
  rw [Measure.map_apply hX hs, tilted_apply' _ _ (hX hs), tilted_apply' _ _ hs,
    setLIntegral_map (f := fun x => ENNReal.ofReal (Real.exp (g x) / ∫ x, Real.exp (g x) ∂(μ.map X)))
      hs ((Real.measurable_exp.comp hg).div_const _).ennreal_ofReal hX,
    integral_map (f := fun x => Real.exp (g x)) hX.aemeasurable
      (Real.measurable_exp.comp hg).aestronglyMeasurable]

/-- Tilting `N(m, v)` by `x ↦ c x` gives `N(m + c v, v)`. -/
lemma gaussianReal_tilted (m : ℝ) (v : NNReal) (c : ℝ) :
    (gaussianReal m v).tilted (fun x => c * x) = gaussianReal (m + c * v) v := by
  have hint : Integrable (fun x => Real.exp (c * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal c
  have : IsProbabilityMeasure ((gaussianReal m v).tilted (fun x => c * x)) :=
    isProbabilityMeasure_tilted hint
  have hG : ∀ t, ∫ x, Real.exp (t * x) ∂(gaussianReal m v) =
      Real.exp (m * t + v * t ^ 2 / 2) := fun t => by
    have := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) t
    simpa only [mgf, id] using this
  have hmgf : ∀ t, mgf id ((gaussianReal m v).tilted (fun x => c * x)) t =
      Real.exp ((m + c * v) * t + v * t ^ 2 / 2) := by
    intro t
    simp only [mgf, id]
    rw [integral_tilted]
    simp_rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add]
    rw [integral_div, hG c]
    have : ∫ x, Real.exp (c * x + t * x) ∂(gaussianReal m v) =
        Real.exp (m * (c + t) + v * (c + t) ^ 2 / 2) := by
      rw [← hG (c + t)]
      congr 1
      funext x
      ring_nf
    rw [this, ← Real.exp_sub]
    congr 1
    ring
  have := map_eq_gaussianReal_of_mgf_eqOn (μ := (gaussianReal m v).tilted (fun x => c * x))
    (X := id) aemeasurable_id one_pos (fun t _ => ?_) (fun t _ => hmgf t)
  · simpa using this
  · rw [integrable_tilted_iff hint]
    refine (integrable_exp_mul_gaussianReal (c + t)).congr (Filter.Eventually.of_forall
      fun x => ?_)
    simp only [id, smul_eq_mul, ← Real.exp_add]
    ring_nf

/-- The moment generating function of `X` under the tilt of `μ` by `exp (-τ₀ X)`. -/
lemma mgf_tilted_neg (X : Ω → ℝ) (μ : Measure Ω) (τ₀ s : ℝ) :
    mgf X (μ.tilted (fun ω => -τ₀ * X ω)) s = mgf X μ (s - τ₀) / mgf X μ (-τ₀) := by
  simp only [mgf]
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add]
  rw [integral_div]
  congr 2
  funext ω
  ring_nf

/-- Integrability of `exp (s X)` under the tilt by `exp (-τ₀ X)`. -/
lemma integrable_exp_tilted_neg {τ₀ s : ℝ}
    (hf : Integrable (fun ω => Real.exp (-τ₀ * X ω)) μ)
    (h : Integrable (fun ω => Real.exp ((s - τ₀) * X ω)) μ) :
    Integrable (fun ω => Real.exp (s * X ω)) (μ.tilted (fun ω => -τ₀ * X ω)) := by
  rw [integrable_tilted_iff hf]
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [smul_eq_mul, ← Real.exp_add]
  ring_nf

/-- The untilt: the law of `X` is the tilt by `x ↦ τ₀ x` of its law under the tilt of `μ` by
`exp (-τ₀ X)`. -/
lemma map_eq_tilted_untilt [IsProbabilityMeasure μ] (hX : Measurable X) {τ₀ : ℝ}
    (hf : Integrable (fun ω => Real.exp (-τ₀ * X ω)) μ) :
    μ.map X = ((μ.tilted (fun ω => -τ₀ * X ω)).map X).tilted (fun x => τ₀ * x) := by
  rw [← map_tilted (g := fun x => τ₀ * x) hX (by fun_prop), tilted_tilted hf]
  have : (fun ω => -τ₀ * X ω) + (fun ω => τ₀ * X ω) = 0 := by
    funext ω
    simp only [Pi.add_apply, Pi.zero_apply]
    ring
  rw [this, tilted_zero]

/-- One-sided uniqueness: two real random variables whose moment generating functions are
finite and equal at `-τ` for `τ ∈ [0, L)` have the same law. Route (Claim 008, Step 6): tilt
both by `exp (-τ₀ ·)` with `τ₀ = L / 2`, where the moment generating functions are finite and
equal on `(-τ₀, τ₀)`, apply `map_eq_of_mgf_eqOn`, and untilt. -/
theorem map_eq_of_mgf_eqOn_Ico [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) {L : ℝ} (hL : 0 < L)
    (hintX : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun ω => Real.exp (-τ * X ω)) μ)
    (hintY : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun ω => Real.exp (-τ * Y ω)) μ')
    (h : ∀ τ ∈ Ico (0 : ℝ) L, mgf X μ (-τ) = mgf Y μ' (-τ)) :
    μ.map X = μ'.map Y := by
  set τ₀ : ℝ := L / 2 with hτ₀
  have hτ₀L : τ₀ ∈ Ico (0 : ℝ) L := ⟨by linarith, by linarith⟩
  have hτ₀pos : 0 < τ₀ := by linarith
  have hfX := hintX τ₀ hτ₀L
  have hfY := hintY τ₀ hτ₀L
  have : IsProbabilityMeasure (μ.tilted (fun ω => -τ₀ * X ω)) := isProbabilityMeasure_tilted hfX
  have : IsProbabilityMeasure (μ'.tilted (fun ω => -τ₀ * Y ω)) :=
    isProbabilityMeasure_tilted hfY
  have hsub : ∀ s ∈ Ioo (-τ₀) τ₀, τ₀ - s ∈ Ico (0 : ℝ) L := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hkey := map_eq_of_mgf_eqOn (μ := μ.tilted (fun ω => -τ₀ * X ω))
    (μ' := μ'.tilted (fun ω => -τ₀ * Y ω))
    (hX.aemeasurable.mono_ac (tilted_absolutelyContinuous _ _))
    (hY.aemeasurable.mono_ac (tilted_absolutelyContinuous _ _)) hτ₀pos
    (fun s hs => integrable_exp_tilted_neg hfX (by simpa [neg_sub] using hintX _ (hsub s hs)))
    (fun s hs => integrable_exp_tilted_neg hfY (by simpa [neg_sub] using hintY _ (hsub s hs)))
    (fun s hs => by
      rw [mgf_tilted_neg, mgf_tilted_neg, h _ hτ₀L]
      have := h _ (hsub s hs)
      rw [neg_sub] at this
      rw [this])
  rw [map_eq_tilted_untilt hX hfX, map_eq_tilted_untilt hY hfY, hkey]

/-- Claim 008, Step 6 with (8.4): if the moment generating function of `X` is finite on
`(-L, 0]` and equals `exp (½ y τ²)` at `-τ` for `τ ∈ [0, L)`, then `y ≥ 0` and `X ~ N(0, y)`.
`y ≥ 0` is Claim 001's inequality `mgf (t/2)² ≤ mgf t`; the law is `map_eq_of_mgf_eqOn_Ico`
against `N(0, y)`. -/
theorem map_eq_gaussianReal_of_mgf_eqOn_Ico [IsProbabilityMeasure μ] (hX : Measurable X)
    {L y : ℝ} (hL : 0 < L)
    (hint : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun ω => Real.exp (-τ * X ω)) μ)
    (h : ∀ τ ∈ Ico (0 : ℝ) L, mgf X μ (-τ) = Real.exp (y * τ ^ 2 / 2)) :
    0 ≤ y ∧ μ.map X = gaussianReal 0 y.toNNReal := by
  -- (8.4): `y ≥ 0`.
  have hy : 0 ≤ y := by
    have hτ : L / 2 ∈ Ico (0 : ℝ) L := ⟨by linarith, by linarith⟩
    have hτ' : L / 2 / 2 ∈ Ico (0 : ℝ) L := ⟨by linarith, by linarith⟩
    have hsq := Novel.MGF.mgf_half_sq_le (μ := μ) (X := X) (t := -(L / 2)) (hint _ hτ)
    rw [h _ hτ, neg_div, h _ hτ', sq, ← Real.exp_add] at hsq
    have hle := Real.exp_le_exp.1 hsq
    have hL2 : 0 < L ^ 2 := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hL2
    nlinarith
  refine ⟨hy, ?_⟩
  have := map_eq_of_mgf_eqOn_Ico (μ' := gaussianReal 0 y.toNNReal) (Y := id) hX measurable_id
    hL hint (fun τ _ => integrable_exp_mul_gaussianReal (-τ)) (fun τ hτ => by
      rw [h τ hτ, mgf_id_gaussianReal]
      simp only [Real.coe_toNNReal y hy]
      congr 1
      ring)
  simpa using this

/-- `v ↦ N(m, v)` is a measurable family of measures (the Gaussian kernel in its variance). -/
lemma measurable_gaussianReal (m : ℝ) : Measurable (fun v : NNReal => gaussianReal m v) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hjoint : Measurable (fun p : NNReal × ℝ => gaussianPDF m p.1 p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have h1 : Measurable (fun v : NNReal => volume.withDensity (gaussianPDF m v) s) := by
    simp_rw [withDensity_apply _ hs]
    exact hjoint.lintegral_prod_right' (ν := volume.restrict s)
  have : (fun v : NNReal => gaussianReal m v s) =
      fun v => if v = 0 then Measure.dirac m s else volume.withDensity (gaussianPDF m v) s := by
    funext v
    simp only [gaussianReal]
    split_ifs <;> rfl
  rw [this]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const h1

/-- One-sided uniqueness in lower-integral form: a random variable `X` under `μ` and a
probability measure `μ'` on `ℝ` with equal, finite `∫⁻ exp (-τ ·)` for `τ ∈ [0, L)` satisfy
`μ.map X = μ'`. -/
theorem map_eq_of_lintegral_exp_eqOn_Ico {μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hX : Measurable X) {L : ℝ} (hL : 0 < L)
    (h : ∀ τ ∈ Ico (0 : ℝ) L, ∫⁻ ω, ENNReal.ofReal (Real.exp (-τ * X ω)) ∂μ =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂μ')
    (hfin : ∀ τ ∈ Ico (0 : ℝ) L, ∫⁻ x, ENNReal.ofReal (Real.exp (-τ * x)) ∂μ' < ⊤) :
    μ.map X = μ' := by
  have hintX : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun ω => Real.exp (-τ * X ω)) μ := by
    intro τ hτ
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul hX)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le),
      h τ hτ]
    exact hfin τ hτ
  have hintY : ∀ τ ∈ Ico (0 : ℝ) L, Integrable (fun x => Real.exp (-τ * x)) μ' := by
    intro τ hτ
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact hfin τ hτ
  have := map_eq_of_mgf_eqOn_Ico (μ' := μ') (Y := id) hX measurable_id hL hintX hintY
    (fun τ hτ => by
      simp only [mgf, id]
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
        (Real.exp_pos _).le) (hintX τ hτ).1,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
        (Real.exp_pos _).le) (hintY τ hτ).1, h τ hτ])
  simpa using this

end Novel.MGFUniqueness

import Standalone.JumpShapeKernel
import Novel.MGFUniqueness

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel
namespace Novel.JumpShapeKernelProof

/-- A real strictly between `τ` and `L`. -/
lemma exists_between {L : ℝ≥0∞} {τ : ℝ} (hτ : 0 ≤ τ) (h : ENNReal.ofReal τ < L) :
    ∃ r, τ < r ∧ ENNReal.ofReal r < L := by
  obtain ⟨r, hr0, hτr, hrL⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
  exact ⟨r, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hτ).1 hτr, hrL⟩

lemma inI_of_lt {L : ℝ≥0∞} {r s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : ENNReal.ofReal r < L) :
    InI L s := ⟨hs, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsr) hr⟩

variable {ν : Measure ℝ} {L : ℝ≥0∞}

lemma Mlap_eq (τ : ℝ) : Mlap ν τ = mgf id ν (-τ) := rfl

lemma Klap_eq : Klap ν = fun τ => cgf id ν (-τ) := rfl

/-- For `τ ∈ (0, L)`, `−τ` is interior to the integrability set. -/
lemma mem_interior (h : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ) :
    -τ ∈ interior (integrableExpSet id ν) := by
  obtain ⟨r, hτr, hrL⟩ := exists_between hτ.1.le hτ.2
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Ioo_mem_nhds (a := -r) (b := 0)
    (by linarith) (by linarith [hτ.1])) fun t ht => ?_)
  have := h (-t) (inI_of_lt (by linarith [ht.2]) (by linarith [ht.1]) hrL)
  simpa [integrableExpSet] using this

/-- `(0, L)` is open. -/
lemma isOpen_Io : IsOpen {τ : ℝ | InIo L τ} := by
  refine isOpen_iff_mem_nhds.2 fun τ hτ => ?_
  obtain ⟨r, hτr, hrL⟩ := exists_between hτ.1.le hτ.2
  refine Filter.mem_of_superset (Ioo_mem_nhds (a := 0) (b := r) hτ.1 hτr) fun s hs =>
    ⟨hs.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2.le) hrL⟩

lemma tiltMean_eq (h : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ) :
    tiltMean ν τ = deriv (cgf id ν) (-τ) := by
  rw [deriv_cgf (mem_interior h hτ)]
  rfl

lemma tiltVar_eq (h : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ) :
    tiltVar ν τ = iteratedDeriv 2 (cgf id ν) (-τ) := by
  rw [iteratedDeriv_two_cgf_eq_integral (mem_interior h hτ), ← tiltMean_eq h hτ]
  rfl

lemma deriv_hasDerivAt (h : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ) :
    HasDerivAt (deriv (cgf id ν)) (iteratedDeriv 2 (cgf id ν) (-τ)) (-τ) := by
  have ha := (analyticAt_cgf (mem_interior h hτ)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ha.differentiableAt.hasDerivAt

lemma deriv_part [IsProbabilityMeasure ν] (h : LapFinite ν L) :
    AnalyticOnNhd ℝ (Klap ν) {τ | InIo L τ} ∧
    ∀ τ, InIo L τ → HasDerivAt (Klap ν) (-tiltMean ν τ) τ ∧
      HasDerivAt (tiltMean ν) (-tiltVar ν τ) τ := by
  refine ⟨fun τ hτ => ?_, fun τ hτ => ⟨?_, ?_⟩⟩
  · rw [Klap_eq]
    exact (analyticAt_cgf (mem_interior h hτ)).comp analyticAt_id.neg
  · have hd := (analyticAt_cgf (mem_interior h hτ)).differentiableAt.hasDerivAt.comp τ
      (hasDerivAt_neg τ)
    rw [Klap_eq, tiltMean_eq h hτ]
    convert hd using 1 <;> first | rfl | ring
  · have hd := (deriv_hasDerivAt h hτ).comp τ (hasDerivAt_neg τ)
    have hev : (fun s => deriv (cgf id ν) (-s)) =ᶠ[𝓝 τ] tiltMean ν := by
      filter_upwards [isOpen_Io.mem_nhds hτ] with s hs using (tiltMean_eq h hs).symm
    rw [tiltVar_eq h hτ]
    convert (hd.congr_of_eventuallyEq hev.symm) using 1
    ring

lemma tiltVar_nonneg [IsProbabilityMeasure ν] (τ : ℝ) : 0 ≤ tiltVar ν τ :=
  div_nonneg (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg fun _ => (Real.exp_pos _).le)

/-- A probability measure almost surely equal to `a` is `δ_a`. -/
lemma eq_dirac_of_ae [IsProbabilityMeasure ν] {a : ℝ} (h : ∀ᵐ x ∂ν, x = a) :
    ν = Measure.dirac a := by
  have hnull : ν {x | x ≠ a} = 0 := ae_iff.1 h
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, Pi.one_apply]
    have : ν sᶜ = 0 := measure_mono_null (fun x (hx : x ∈ sᶜ) (hxa : x = a) => hx (hxa ▸ ha)) hnull
    rw [← prob_compl_eq_zero_iff hs]
    exact this
  · rw [Set.indicator_of_notMem ha]
    exact measure_mono_null (fun x (hx : x ∈ s) (hxa : x = a) => ha (hxa ▸ hx)) hnull

lemma tiltVar_eq_zero_iff [IsProbabilityMeasure ν] (h : LapFinite ν L) {τ : ℝ}
    (hτ : InIo L τ) : tiltVar ν τ = 0 ↔ ∃ a : ℝ, ν = Measure.dirac a := by
  have hmem := mem_interior h hτ
  have hint : Integrable (fun x => Real.exp (-τ * x)) ν := h τ ⟨hτ.1.le, hτ.2⟩
  have hM : 0 < Mlap ν τ := mgf_pos (X := id) hint
  constructor
  · intro h0
    set m := tiltMean ν τ
    have hI : Integrable (fun x => (x - m) ^ 2 * Real.exp (-τ * x)) ν := by
      have h2 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 2
      have h1 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1
      have h0' := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 0
      have := (h2.sub (h1.const_mul (2 * m))).add (h0'.const_mul (m ^ 2))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [id, Pi.add_apply, Pi.sub_apply]
      ring
    have hz : ∫ x, (x - m) ^ 2 * Real.exp (-τ * x) ∂ν = 0 := by
      have := h0
      unfold tiltVar at this
      rcases div_eq_zero_iff.1 this with h' | h'
      · exact h'
      · exact absurd h' hM.ne'
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hI).1 hz
    refine ⟨m, eq_dirac_of_ae ?_⟩
    filter_upwards [hae] with x hx
    have := (mul_eq_zero.1 hx).resolve_right (Real.exp_pos _).ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro ⟨a, rfl⟩
    have hM' : Mlap (Measure.dirac a) τ = Real.exp (-τ * a) := by simp [Mlap]
    have hm : tiltMean (Measure.dirac a) τ = a := by
      simp only [tiltMean, hM', integral_dirac]
      field_simp
    simp [tiltVar, hm]

lemma derivS : Standalone.JumpShapeKernel.derivStatement := by
  intro ν _ L h
  obtain ⟨ha, hd⟩ := deriv_part h
  exact ⟨ha, fun τ hτ => ⟨(hd τ hτ).1, (hd τ hτ).2, tiltVar_nonneg τ,
    tiltVar_eq_zero_iff h hτ⟩⟩

lemma uniqueS : Standalone.JumpShapeKernel.uniqueStatement := by
  intro ν ν' _ _ L hL h h' heq
  obtain ⟨r, hr0, hr⟩ := exists_between le_rfl (by simpa using hL)
  have hsub : ∀ τ ∈ Ico (0 : ℝ) r, InI L τ := fun τ hτ => inI_of_lt hτ.1 hτ.2.le hr
  have := Novel.MGFUniqueness.map_eq_of_mgf_eqOn_Ico (X := id) (Y := id) (μ := ν) (μ' := ν')
    measurable_id measurable_id hr0 (fun τ hτ => h τ (hsub τ hτ)) (fun τ hτ => h' τ (hsub τ hτ))
    (fun τ hτ => heq τ (hsub τ hτ))
  simpa using this

theorem jumpShapeKernel : Standalone.JumpShapeKernel.statement := ⟨derivS, uniqueS⟩

end Novel.JumpShapeKernelProof

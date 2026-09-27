import Standalone.JumpShapeProfile
import Novel.JumpShapeKernelProof

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile
namespace Novel.JumpShapeProfileProof
open Novel.JumpShapeKernelProof

variable {ν : Measure ℝ} {L : ℝ≥0∞}

lemma Klap_zero [IsProbabilityMeasure ν] : Klap ν 0 = 0 := by simp [Klap, Mlap]

/-- `M` is continuous on `[0, r]`, `r < L`: `e^{−sx} ≤ 1 + e^{−rx}` for `s ∈ [0, r]`. -/
lemma Mlap_continuousOn [IsProbabilityMeasure ν] (h : LapFinite ν L) {r : ℝ} (hr0 : 0 ≤ r) (hr : ENNReal.ofReal r < L) :
    ContinuousOn (Mlap ν) (Icc 0 r) := by
  have hb : Integrable (fun x => 1 + Real.exp (-r * x)) ν :=
    (integrable_const 1).add (h r ⟨hr0, hr⟩)
  refine continuousOn_of_dominated (bound := fun x => 1 + Real.exp (-r * x))
    (fun s _ => (by fun_prop : Continuous fun x : ℝ => Real.exp (-s * x)).aestronglyMeasurable)
    (fun s hs => Eventually.of_forall fun x => ?_) hb
    (Eventually.of_forall fun x => by fun_prop)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 x with hx | hx
  · have : Real.exp (-s * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hs.1])
    linarith [Real.exp_pos (-r * x)]
  · have : Real.exp (-s * x) ≤ Real.exp (-r * x) := Real.exp_le_exp.2 (by nlinarith [hs.2])
    linarith

lemma Mlap_pos [IsProbabilityMeasure ν] (h : LapFinite ν L) {τ : ℝ} (hτ : InI L τ) :
    0 < Mlap ν τ := mgf_pos (X := id) (h τ hτ)

lemma Klap_continuousOn [IsProbabilityMeasure ν] (h : LapFinite ν L) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ENNReal.ofReal r < L) : ContinuousOn (Klap ν) (Icc 0 r) :=
  (Mlap_continuousOn h hr0 hr).log fun _ hs =>
    (Mlap_pos h (inI_of_lt hs.1 hs.2 hr)).ne'

/-- `(0, L)` is order-connected. -/
lemma ordConnected_Io : OrdConnected {τ : ℝ | InIo L τ} :=
  ⟨fun _ ha _ hb _ hx => ⟨lt_of_lt_of_le ha.1 hx.1,
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hx.2) hb.2⟩⟩

lemma monotone_part [IsProbabilityMeasure ν] (h : LapFinite ν L) :
    MonotoneOn (fun τ => -tiltMean ν τ) {τ | InIo L τ} ∧
    ((¬ ∃ a : ℝ, ν = Measure.dirac a) →
      StrictMonoOn (fun τ => -tiltMean ν τ) {τ | InIo L τ}) := by
  have hd : ∀ τ, InIo L τ → HasDerivAt (fun τ => -tiltMean ν τ) (- -tiltVar ν τ) τ :=
    fun τ hτ => ((deriv_part h).2 τ hτ).2.neg
  have hconv : Convex ℝ {τ : ℝ | InIo L τ} := ordConnected_Io.convex
  have hint : interior {τ : ℝ | InIo L τ} = {τ | InIo L τ} := isOpen_Io.interior_eq
  have hcont : ContinuousOn (fun τ => -tiltMean ν τ) {τ | InIo L τ} := fun τ hτ =>
    (hd τ hτ).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun τ => -tiltMean ν τ) (interior {τ | InIo L τ}) := by
    rw [hint]
    exact fun τ hτ => (hd τ hτ).differentiableAt.differentiableWithinAt
  refine ⟨monotoneOn_of_deriv_nonneg hconv hcont hdiff fun τ hτ => ?_, fun hnd =>
    strictMonoOn_of_deriv_pos hconv hcont fun τ hτ => ?_⟩
  · rw [hint] at hτ
    rw [(hd τ hτ).deriv, neg_neg]
    exact tiltVar_nonneg τ
  · rw [hint] at hτ
    rw [(hd τ hτ).deriv, neg_neg]
    refine lt_of_le_of_ne (tiltVar_nonneg τ) fun h0 => hnd ?_
    exact (tiltVar_eq_zero_iff h hτ).1 h0.symm

/-- On `[0, q]`, `q < L`, `∫_0^· h = K` gives `K′ = h` at almost every point of `(0, q)`. -/
lemma ae_on [IsProbabilityMeasure ν] {h : ℝ → ℝ} (hf : LapFinite ν L) (hl : LocInt h L)
    (hs : ShapeEq ν h L) {q : ℝ} (hq0 : 0 < q) (hq : ENNReal.ofReal q < L) :
    ∀ᵐ τ ∂volume, τ ∈ Ioo 0 q → h τ = -tiltMean ν τ := by
  have hI : IntegrableOn h (Icc 0 q) := (intervalIntegrable_iff_integrableOn_Icc_of_le hq0.le).1
    (hl q ⟨hq0.le, hq⟩)
  set g := (Icc 0 q).indicator h
  have hg : LocallyIntegrable g volume :=
    ((integrable_indicator_iff measurableSet_Icc).2 hI).locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with τ hτ hmem
  have hgh : ∀ y ∈ Icc (0:ℝ) q, ∫ u in (0:ℝ)..y, g u = Klap ν y := fun y hy => by
    rw [← hs y (inI_of_lt hy.1 hy.2 hq)]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hy.1] at hu
    exact indicator_of_mem (show u ∈ Icc (0:ℝ) q from ⟨hu.1, hu.2.trans hy.2⟩) h
  have hK : HasDerivAt (Klap ν) (g τ) τ := by
    refine (hτ 0).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
    exact (hgh y ⟨hy.1.le, hy.2.le⟩).symm
  have hIo : InIo L τ := ⟨hmem.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmem.2.le) hq⟩
  have := hK.unique ((deriv_part hf).2 τ hIo).1
  rwa [show g τ = h τ from indicator_of_mem (show τ ∈ Icc (0:ℝ) q from ⟨hmem.1.le, hmem.2.le⟩) h] at this

lemma shapeS : Standalone.JumpShapeProfile.shapeStatement := by
  intro ν _ L h hf hl hs
  refine ⟨?_, fun τ hτ hc => ?_, (monotone_part hf).1, (monotone_part hf).2⟩
  · have hall : ∀ q : ℚ, ∀ᵐ τ ∂volume, (0 < (q : ℝ) ∧ ENNReal.ofReal q < L) →
        τ ∈ Ioo 0 (q : ℝ) → h τ = -tiltMean ν τ := fun q => by
      by_cases hq : 0 < (q : ℝ) ∧ ENNReal.ofReal q < L
      · filter_upwards [ae_on hf hl hs hq.1 hq.2] with τ hτ _ using hτ
      · exact Eventually.of_forall fun τ h' => absurd h' hq
    filter_upwards [ae_all_iff.2 hall] with τ hτ hIo
    obtain ⟨r, hτr, hrL⟩ := exists_between hIo.1.le hIo.2
    obtain ⟨q, hτq, hqr⟩ := exists_rat_btwn hτr
    exact hτ q ⟨hIo.1.trans hτq, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hqr.le) hrL⟩
      ⟨hIo.1, hτq⟩
  · obtain ⟨r, hτr, hrL⟩ := exists_between hτ.1.le hτ.2
    have hI : IntervalIntegrable h volume 0 r := hl r (inI_of_lt (hτ.1.le.trans hτr.le) le_rfl hrL)
    have hmeas : StronglyMeasurableAtFilter h (𝓝[Ioi τ] τ) volume :=
      ⟨Icc τ r, Icc_mem_nhdsGT hτr, ((intervalIntegrable_iff_integrableOn_Icc_of_le
        (hτ.1.le.trans hτr.le)).1 hI).mono_set (Icc_subset_Icc hτ.1.le le_rfl) |>.aestronglyMeasurable⟩
    have hF := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici τ) (t := Ioi τ) (hI.mono_set (by
      rw [uIcc_of_le hτ.1.le, uIcc_of_le (hτ.1.le.trans hτr.le)]
      exact Icc_subset_Icc le_rfl hτr.le)) hmeas (hc.mono Ioi_subset_Ici_self)
    have hK : HasDerivWithinAt (Klap ν) (h τ) (Ici τ) τ := by
      refine hF.congr_of_eventuallyEq ?_ (hs τ ⟨hτ.1.le, hτ.2⟩).symm
      filter_upwards [Icc_mem_nhdsGE hτr] with y hy
      exact (hs y (inI_of_lt (hτ.1.le.trans hy.1) hy.2 hrL)).symm
    exact (uniqueDiffWithinAt_Ici τ).eq_deriv _ hK ((deriv_part hf).2 τ hτ).1.hasDerivWithinAt

lemma converseS : Standalone.JumpShapeProfile.converseStatement := by
  intro ν _ L h hf hl hae τ hτ
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    simp [Klap_zero]
  have hIo : ∀ u ∈ Ioo 0 τ, InIo L u := fun u hu =>
    ⟨hu.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2.le) hτ.2⟩
  have hae' : ∀ᵐ u ∂volume, u ∈ uIoc 0 τ → h u = -tiltMean ν u := by
    filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le hpos.le] at hmem
    exact hu ⟨hmem.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmem.2) hτ.2⟩
  have hI : IntervalIntegrable h volume 0 τ := hl τ hτ
  have hI' : IntervalIntegrable (fun u => -tiltMean ν u) volume 0 τ :=
    hI.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hae')
  rw [intervalIntegral.integral_congr_ae hae',
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpos.le
      (Klap_continuousOn hf hpos.le hτ.2) (fun u hu => ((deriv_part hf).2 u (hIo u hu)).1) hI',
    Klap_zero, sub_zero]

theorem jumpShapeProfile : Standalone.JumpShapeProfile.statement := ⟨shapeS, converseS⟩

end Novel.JumpShapeProfileProof

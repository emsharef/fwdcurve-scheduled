import Standalone.JumpShapeGeneral
import Novel.JumpShapeCondBProof

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB Standalone.JumpShapeGeneral
namespace Novel.JumpShapeGeneralProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof Novel.JumpShapeCondBProof

variable {ν : Measure ℝ} {L : ℝ≥0∞}

lemma int_xexp (h : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ) :
    Integrable (fun x => x * Real.exp (-τ * x)) ν := by
  have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (mem_interior h hτ) 1
  simpa using this

/-- `Ê_τ[r_{T_n + τ}] = f(t, T_n + τ) + h(τ) + Ẽ_τ[X]`: the `G`-measurable factor cancels. -/
lemma tiltRate_eq [IsProbabilityMeasure ν] (hf : LapFinite ν L) {f h : ℝ → ℝ} {Tn τ : ℝ}
    (hτ : InIo L τ) (hfi : IntervalIntegrable (fun u => f (Tn + u)) volume 0 τ)
    (hhi : IntervalIntegrable h volume 0 τ) :
    tiltRate ν f h Tn τ = f (Tn + τ) + h τ + tiltMean ν τ := by
  set A := ∫ u in (0:ℝ)..τ, (f (Tn + u) + h u)
  have hA : ∀ x, Real.exp (-∫ u in (0:ℝ)..τ, (f (Tn + u) + x + h u)) =
      Real.exp (-A) * Real.exp (-τ * x) := fun x => by
    rw [← Real.exp_add]
    congr 1
    rw [intervalIntegral.integral_add (hfi.add intervalIntegrable_const) hhi,
      intervalIntegral.integral_add hfi intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    simp only [A]
    rw [intervalIntegral.integral_add hfi hhi]
    ring
  have hM : 0 < Mlap ν τ := Mlap_pos hf ⟨hτ.1.le, hτ.2⟩
  have hi := hf τ ⟨hτ.1.le, hτ.2⟩
  have hxi := int_xexp hf hτ
  unfold tiltRate
  simp_rw [hA]
  have e1 : ∫ x, (f (Tn + τ) + x + h τ) * (Real.exp (-A) * Real.exp (-τ * x)) ∂ν =
      Real.exp (-A) * ((f (Tn + τ) + h τ) * Mlap ν τ + ∫ x, x * Real.exp (-τ * x) ∂ν) := by
    rw [Mlap, ← integral_const_mul, ← integral_add (hi.const_mul _) hxi, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [e1, integral_const_mul, tiltMean]
  change _ / (Real.exp (-A) * Mlap ν τ) = _
  field_simp

lemma forwardMeasureS : Standalone.JumpShapeGeneral.forwardMeasureStatement := by
  intro Ω m₀ P G X h fT Tn L κ hS hfT hH
  have hκ := hS.2.2.2.2.2.1
  obtain ⟨N, -, hN0, hN⟩ := shapeCondS Ω m₀ P G X h L κ hS hH
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  obtain ⟨hf, -, -, hae, -⟩ := hN ω hω
  filter_upwards [hae] with τ hτ hIo
  have hfi : IntervalIntegrable (fun u => fT (Tn + u) ω) volume 0 τ := by
    have := (hfT ω τ ⟨hIo.1.le, hIo.2⟩).comp_add_left Tn
    simpa using this
  rw [tiltRate_eq hf hIo hfi (hS.2.2.2.2.1 ω τ ⟨hIo.1.le, hIo.2⟩), hτ hIo]
  ring

/-- `Ẽ_τ[X + c] = Ẽ_τ[X] + c`. -/
lemma tiltMean_shift [IsProbabilityMeasure ν] (hf : LapFinite ν L) {τ : ℝ} (hτ : InIo L τ)
    (c : ℝ) : tiltMean (ν.map fun x => x + c) τ = tiltMean ν τ + c := by
  have hmeas : Measurable fun x : ℝ => x + c := measurable_id.add_const c
  have hM : 0 < Mlap ν τ := Mlap_pos hf ⟨hτ.1.le, hτ.2⟩
  have hi := hf τ ⟨hτ.1.le, hτ.2⟩
  have hxi := int_xexp hf hτ
  have eM : Mlap (ν.map fun x => x + c) τ = Real.exp (-τ * c) * Mlap ν τ := by
    rw [Mlap, integral_map hmeas.aemeasurable (by fun_prop), Mlap, ← integral_const_mul]
    congr 1
    funext x
    rw [← Real.exp_add]
    ring_nf
  have eN : ∫ x, x * Real.exp (-τ * x) ∂(ν.map fun x => x + c) =
      Real.exp (-τ * c) * ((∫ x, x * Real.exp (-τ * x) ∂ν) + c * Mlap ν τ) := by
    rw [integral_map hmeas.aemeasurable (by fun_prop), Mlap, ← integral_const_mul,
      ← integral_add hxi (hi.const_mul c), ← integral_const_mul]
    congr 1
    funext x
    rw [show -τ * (x + c) = -τ * c + -τ * x by ring, Real.exp_add]
    ring
  rw [tiltMean, eM, eN, tiltMean]
  field_simp

lemma onlyCaseS : Standalone.JumpShapeGeneral.onlyCaseStatement := by
  intro Ω m₀ P G X h fT Tn L κ rt rl hL hS hH hlim hfc hhc
  have hκ := hS.2.2.2.2.2.1
  obtain ⟨N, -, hN0, hN⟩ := shapeCondS Ω m₀ P G X h L κ hS hH
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  obtain ⟨hf, -, -, -, hrc, -⟩ := hN ω hω
  have hh : ∀ τ, InIo L τ → h τ ω = -tiltMean (κ ω) τ := fun τ hτ =>
    hrc τ hτ (hhc ω τ ⟨hτ.1.le, hτ.2⟩)
  set D : ℝ → ℝ := fun τ => fT (Tn + τ) ω + h τ ω - (fT Tn ω + h 0 ω)
  have hiff : ∀ τ, InIo L τ → (fT (Tn + τ) ω = rt ω +
      tiltMean ((κ ω).map fun x => x + (fT Tn ω + h 0 ω - rl ω)) τ ↔ D τ = rt ω - rl ω) :=
    fun τ hτ => by
      rw [tiltMean_shift hf hτ, ← neg_neg (tiltMean (κ ω) τ), ← hh τ hτ]
      simp only [D]
      constructor <;> intro e <;> linarith
  -- `D` is right-continuous at `0`, with `D(0) = 0`
  have hD : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    have h1 : ContinuousWithinAt (fun u : ℝ => Tn + u) (Ici 0) 0 :=
      (continuous_const.add continuous_id).continuousWithinAt
    have hf0 : ContinuousWithinAt (fun u => fT (Tn + u) ω) (Ici 0) 0 :=
      (hfc ω 0 ⟨le_rfl, by simpa using hL⟩).comp_of_eq h1 (fun u hu => by
        simp only [mem_Ici] at hu ⊢
        linarith) (by simp)
    have := ((hf0.add (hhc ω 0 ⟨le_rfl, by simpa using hL⟩)).sub
      (continuousWithinAt_const (b := fT Tn ω + h 0 ω))).mono Ioi_subset_Ici_self
    convert this.tendsto using 2
    simp
  obtain ⟨r, hr0, hr⟩ := exists_between le_rfl (by simpa using hL)
  have hIo : ∀ τ ∈ Ioo 0 r, InIo L τ := fun τ hτ =>
    ⟨hτ.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hτ.2.le) hr⟩
  constructor
  · intro h51
    have hconst : ∀ τ ∈ Ioo 0 r, D τ = rt ω - rl ω := fun τ hτ => (hiff τ (hIo τ hτ)).1
      (h51 τ (hIo τ hτ))
    have hlim' : Tendsto D (𝓝[>] 0) (𝓝 (rt ω - rl ω)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsGT hr0] with τ hτ using (hconst τ hτ).symm)
    have e0 := tendsto_nhds_unique hlim' hD
    refine ⟨by linarith, fun τ hτ => ?_⟩
    rcases hτ.1.eq_or_lt with h0 | hpos
    · subst h0; simp
    · have := (hiff τ ⟨hpos, hτ.2⟩).1 (h51 τ ⟨hpos, hτ.2⟩)
      simp only [D] at this
      linarith
  · rintro ⟨hrl, hcst⟩ τ hτ
    refine (hiff τ hτ).2 ?_
    have := hcst τ ⟨hτ.1.le, hτ.2⟩
    simp only [D]
    linarith

theorem jumpShapeGeneral : Standalone.JumpShapeGeneral.statement :=
  ⟨forwardMeasureS, onlyCaseS⟩

end Novel.JumpShapeGeneralProof

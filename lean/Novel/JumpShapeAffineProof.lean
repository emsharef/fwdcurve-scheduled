import Standalone.JumpShapeAffine
import Novel.JumpShapeProfileProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeAffine
namespace Novel.JumpShapeAffineProof
open Novel.JumpShapeKernelProof

lemma int_affine (c y τ : ℝ) : ∫ u in (0:ℝ)..τ, (c + y * u) = c * τ + y * τ ^ 2 / 2 := by
  rw [intervalIntegral.integral_add (f := fun _ => c) (g := fun u => y * u) intervalIntegrable_const
    ((continuous_const.mul continuous_id : Continuous fun u : ℝ => y * u).intervalIntegrable _ _),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

lemma affineS : Standalone.JumpShapeAffine.affineStatement := by
  intro ν _ L c y hL
  constructor
  · rintro ⟨hf, hs⟩
    have hM : ∀ τ, InI L τ → Mlap ν τ = Real.exp (c * τ + y * τ ^ 2 / 2) := fun τ hτ => by
      have hpos : 0 < Mlap ν τ := mgf_pos (X := id) (hf τ hτ)
      have := hs τ hτ
      rw [int_affine] at this
      rw [this, Klap, Real.exp_log hpos]
    obtain ⟨r, hr0, hr⟩ := exists_between le_rfl (by simpa using hL)
    have hsub : ∀ τ ∈ Ico (0 : ℝ) r, InI L τ := fun τ hτ => inI_of_lt hτ.1 hτ.2.le hr
    have hint : ∀ τ ∈ Ico (0 : ℝ) r, Integrable (fun x => Real.exp (-τ * (x + c))) ν :=
      fun τ hτ => ((hf τ (hsub τ hτ)).const_mul (Real.exp (-τ * c))).congr
        (Filter.Eventually.of_forall fun x => by
          simp only
          rw [← Real.exp_add]
          ring_nf)
    obtain ⟨hy, hmap⟩ := Novel.MGFUniqueness.map_eq_gaussianReal_of_mgf_eqOn_Ico (μ := ν)
      (X := fun x => x + c) (y := y) (measurable_id.add_const c) hr0 hint fun τ hτ => by
        have e : mgf (fun x => x + c) ν (-τ) = Real.exp (-τ * c) * Mlap ν τ := by
          simp only [mgf, Mlap]
          rw [← integral_const_mul]
          congr 1
          funext x
          rw [← Real.exp_add]
          ring_nf
        rw [e, hM τ (hsub τ hτ), ← Real.exp_add]
        ring_nf
    refine ⟨hy, ?_⟩
    have : ν = (ν.map (fun x => x + c)).map (· + (-c)) := by
      rw [Measure.map_map (by fun_prop : Measurable fun x : ℝ => x + -c)
        (by fun_prop : Measurable fun x : ℝ => x + c)]
      have : ((· + (-c)) ∘ fun x : ℝ => x + c) = id := by
        funext x
        simp
      rw [this, Measure.map_id]
    rw [this, hmap, gaussianReal_map_add_const, zero_add]
  · rintro ⟨hy, rfl⟩
    refine ⟨fun τ _ => integrable_exp_mul_gaussianReal (-τ), fun τ _ => ?_⟩
    rw [int_affine, Klap, Mlap_eq, mgf_id_gaussianReal, Real.coe_toNNReal _ hy, Real.log_exp]
    ring

theorem jumpShapeAffine : Standalone.JumpShapeAffine.statement := affineS

end Novel.JumpShapeAffineProof

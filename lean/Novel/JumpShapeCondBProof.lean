import Standalone.JumpShapeCondB
import Novel.JumpShapeCondProof
import Novel.JumpShapeAffineProof

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB
namespace Novel.JumpShapeCondBProof
open Novel.JumpShapeKernelProof Novel.JumpShapeProfileProof Novel.JumpShapeCondProof

/-- (a)'s "if", from an almost-everywhere statement. -/
lemma hyp_of_ae {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω} {G : MeasurableSpace Ω}
    {X : Ω → ℝ} {h : ℝ → Ω → ℝ} {L : ℝ≥0∞} {κ : @Kernel Ω ℝ G _} (hS : Setting P G X h L κ)
    (hae : ∀ᵐ ω ∂P, LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L) : HypH P G X h L := by
  obtain ⟨hP, hG, -, hh, hloc, hκ, hR⟩ := hS
  intro τ hτ
  refine (key hG hh hloc hR hτ).2 ?_
  filter_upwards [hae] with ω hω
  obtain ⟨hf, hs⟩ := hω
  rw [Ml_eq (hf τ hτ), hs τ hτ, Klap, Real.exp_log (Mlap_pos hf hτ)]

/-- (a)'s "only if". -/
lemma null_of_hyp {Ω : Type} {m₀ : MeasurableSpace Ω} {P : Measure Ω} {G : MeasurableSpace Ω}
    {X : Ω → ℝ} {h : ℝ → Ω → ℝ} {L : ℝ≥0∞} {κ : @Kernel Ω ℝ G _} (hS : Setting P G X h L κ)
    (hH : HypH P G X h L) : ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
      ∀ ω ∉ N, LapFinite (κ ω) L ∧ ShapeEq (κ ω) (fun u => h u ω) L := by
  obtain ⟨hP, hG, hX, hh, hloc, hκ, hR⟩ := hS
  exact (@charS Ω m₀ P hP G hG X hX h hh L hloc κ hκ hR).1 hH

lemma shapeCondS : Standalone.JumpShapeCondB.shapeCondStatement := by
  intro Ω m₀ P G X h L κ hS hH
  obtain ⟨N, hNm, hN0, hN⟩ := null_of_hyp hS hH
  have hκ := hS.2.2.2.2.2.1
  refine ⟨N, hNm, hN0, fun ω hω => ?_⟩
  obtain ⟨hf, hs⟩ := hN ω hω
  have hd := (derivS (κ ω) L hf).2
  obtain ⟨h1, h2, h3, -⟩ := shapeS (κ ω) L (fun u => h u ω) hf (fun τ hτ => hS.2.2.2.2.1 ω τ hτ) hs
  exact ⟨hf, hs, fun τ hτ => ⟨(hd τ hτ).1, (hd τ hτ).2.1, (hd τ hτ).2.2.1⟩, h1, h2, h3⟩

lemma converseCondS : Standalone.JumpShapeCondB.converseCondStatement := by
  intro Ω m₀ P G X h L κ hS hae
  have hκ := hS.2.2.2.2.2.1
  refine hyp_of_ae hS ?_
  filter_upwards [hae] with ω hω
  exact ⟨hω.1, converseS (κ ω) L (fun u => h u ω) hω.1 (fun τ hτ => hS.2.2.2.2.1 ω τ hτ) hω.2⟩

lemma uniqueCondS : Standalone.JumpShapeCondB.uniqueCondStatement := by
  intro Ω m₀ P G X X' h L κ κ' hL hS hS' hH hH'
  obtain ⟨N, -, hN0, hN⟩ := null_of_hyp hS hH
  obtain ⟨N', -, hN0', hN'⟩ := null_of_hyp hS' hH'
  have hκ := hS.2.2.2.2.2.1
  have hκ' := hS'.2.2.2.2.2.1
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, measure_eq_zero_iff_ae_notMem.1 hN0']
    with ω hω hω'
  obtain ⟨hf, hs⟩ := hN ω hω
  obtain ⟨hf', hs'⟩ := hN' ω hω'
  refine uniqueS (κ ω) (κ' ω) L hL hf hf' fun τ hτ => ?_
  rw [← Real.exp_log (Mlap_pos hf hτ), ← Real.exp_log (Mlap_pos hf' hτ)]
  change Real.exp (Klap (κ ω) τ) = Real.exp (Klap (κ' ω) τ)
  rw [← hs τ hτ, ← hs' τ hτ]

lemma affineCondS : Standalone.JumpShapeCondB.affineCondStatement := by
  intro Ω m₀ P G X c y L κ hL hS
  have hκ := hS.2.2.2.2.2.1
  constructor
  · intro hH
    obtain ⟨N, -, hN0, hN⟩ := null_of_hyp hS hH
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact (Novel.JumpShapeAffineProof.affineS (κ ω) L (c ω) (y ω) hL).1 (hN ω hω)
  · intro hae
    refine hyp_of_ae hS ?_
    filter_upwards [hae] with ω hω
    exact (Novel.JumpShapeAffineProof.affineS (κ ω) L (c ω) (y ω) hL).2 hω

theorem jumpShapeCondB : Standalone.JumpShapeCondB.statement :=
  ⟨shapeCondS, converseCondS, uniqueCondS, affineCondS⟩

end Novel.JumpShapeCondBProof

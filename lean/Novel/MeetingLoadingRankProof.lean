import Standalone.MeetingLoadingRank
import Novel.MeetingLoadingDimensionProof
import Novel.MeetingLoadingLawProof
import Mathlib.LinearAlgebra.Basis.VectorSpace

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open Standalone.MeetingLoadingHankel Standalone.MeetingLoadingRank
namespace Novel.MeetingLoadingRankProof

lemma rank_le : Standalone.MeetingLoadingRank.statement := by
  intro Ω mΩ μ hμ a R n δ hδm hδ f c hf q Y Z Ψ hΨ hreal
  classical
  set H := hankel029 a R n
  set L := H.mulVecLin
  set V := LinearMap.range L
  set ρ := H.rank
  have hρ : Module.finrank ℝ V = Module.finrank ℝ (Fin ρ → ℝ) := by
    rw [Module.finrank_fin_fun]; rfl
  let e : V ≃ₗ[ℝ] (Fin ρ → ℝ) := LinearEquiv.ofFinrankEq V (Fin ρ → ℝ) hρ
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (e : V →ₗ[ℝ] (Fin ρ → ℝ))
  have hπL : Function.Surjective (π.comp L) := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := hv
    refine ⟨x, ?_⟩
    have := congrArg (fun g => g ⟨L x, LinearMap.mem_range_self L x⟩) hπ
    simpa using this
  -- the projected vector and its law
  have hlaw := Novel.MeetingLoadingLawProof.affine (n+1) ρ (μ.map δ) (π.comp L) (π c) hδ hπL
  have hcontA : Continuous fun x : Fin (n+1) → ℝ => π c + (π.comp L) x :=
    continuous_const.add (π.comp L).continuous_of_finiteDimensional
  have hVm : AEMeasurable (fun ω => π c + (π.comp L) (δ ω)) μ := hcontA.measurable.comp_aemeasurable hδm
  have hmapV : μ.map (fun ω => π c + (π.comp L) (δ ω)) =
      (μ.map δ).map (fun x => π c + (π.comp L) x) :=
    (AEMeasurable.map_map_of_aemeasurable hcontA.aemeasurable hδm).symm
  -- the projected curve map
  have hπc : Continuous π := π.continuous_of_finiteDimensional
  set Φ : (Fin q → ℝ) → Fin ρ → ℝ := fun y => π (Ψ y)
  have hΦ : ∀ j, LocallyLipschitzOn Z fun y => Φ y j := by
    intro j x hx
    obtain ⟨C, t, ht, hL⟩ := Novel.MeetingLoadingDimensionProof.locallyLipschitzOn_pi Ψ Z hΨ x hx
    have hπL' : LipschitzWith ‖π.toContinuousLinearMap‖₊ π := π.toContinuousLinearMap.lipschitzWith
    refine ⟨‖π.toContinuousLinearMap‖₊ * C, t, ht, fun u hu v hv => ?_⟩
    calc edist (Φ u j) (Φ v j) ≤ edist (Φ u) (Φ v) := edist_le_pi_edist _ _ j
      _ ≤ ‖π.toContinuousLinearMap‖₊ * edist (Ψ u) (Ψ v) := hπL' _ _
      _ ≤ ‖π.toContinuousLinearMap‖₊ * (C * edist u v) := by gcongr; exact hL hu hv
      _ = (‖π.toContinuousLinearMap‖₊ * C : ℝ≥0) * edist u v := by
          push_cast; ring
  refine Novel.MeetingLoadingDimensionProof.dimension Ω mΩ μ hμ q ρ
    (fun ω => π c + (π.comp L) (δ ω)) Y Φ Z hVm (hmapV ▸ hlaw) hΦ ?_
  filter_upwards [hf, hreal] with ω h1 h2
  refine ⟨h2.1, ?_⟩
  show _ = π (Ψ (Y ω))
  rw [← h2.2, h1, map_add]
  rfl

theorem meetingLoadingRank : Standalone.MeetingLoadingRank.statement := rank_le

end Novel.MeetingLoadingRankProof

import Standalone.SpliceCrossTermOpen
import Novel.SpliceCrossTermNecessityProof

open MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermOpen
namespace Novel.SpliceCrossTermOpenProof

lemma open_times : openStatement := by
  intro Tm s hs C hC a b ρ ha hb m τ τl τr H hl hr hH hidxl hidxr hne
  set Δ : ℝ → ℝ := fun u => ρ * b * (s (m + 1) u - s m u)
  have hloc : LocallyIntegrable Δ volume := by
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
    refine (locallyIntegrable_const (|ρ * b| * (C + C))).mono
      (((hs (m + 1)).sub (hs m)).const_mul _).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (by linarith) : 0 ≤ |ρ * b| * (C + C))]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hC _ _) (hC _ _)))
      (abs_nonneg _)
  have hne' : ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ → Δ u = 0) := by
    intro h
    apply hne
    filter_upwards [h] with u hu hmem
    have := hu hmem
    have : ρ * (s (m + 1) u - s m u) * b = 0 := by simp only [Δ] at this; linear_combination this
    exact (mul_eq_zero.1 this).resolve_right hb
  obtain ⟨hO, hOne⟩ := Novel.SpliceCrossTermAnalyticProof.open_set a τ Δ hloc hne'
  refine ⟨_, hO, hOne, fun t ht => ht.1, fun t ht hform => ht.2 ?_⟩
  have hβ := Novel.SpliceCrossTermNecessityProof.beta_eq_at Tm s hs C hC a b ρ ha m τ τl τr H
    hl hr hH hidxl hidxr t ⟨ht.1.1.le, ht.1.2⟩ hform
  have hj := Novel.SpliceCrossTermDriftProof.jump s hs C hC a b ρ m t
  rw [← hβ, sub_self] at hj
  rw [show (fun u => Real.exp (a * u) * Δ u) =
    fun u => ρ * b * (Real.exp (a * u) * (s (m + 1) u - s m u)) from by funext u; simp only [Δ]; ring,
    intervalIntegral.integral_const_mul]
  exact hj.symm

theorem spliceCrossTermOpen : Standalone.SpliceCrossTermOpen.statement := open_times

end Novel.SpliceCrossTermOpenProof

import Standalone.SpliceRandomScalesPath
import Novel.SpliceQuasiExponentialCrossProof
import Novel.SpliceQuasiExponentialKeyProof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceQuasiExponentialKey Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceRandomScalesPath
namespace Novel.SpliceRandomScalesPathProof

variable {r : ℕ}

lemma cross : Standalone.SpliceRandomScalesPath.crossStatement := by
  intro ρ ψ s Tm r c A b u T
  have hsig : sigS033 (wS ρ ψ s) Tm u T = ρ u * ψ u * sigS033 s Tm u T := rfl
  have hSS : SS033 (wS ρ ψ s) Tm u T = ρ u * ψ u * SS033 s Tm u T := by
    unfold SS033
    rw [← intervalIntegral.integral_const_mul]
    rfl
  rw [cross039, cross035, hsig, hSS]
  ring

/-- The weighted scales are measurable and bounded. -/
lemma wS_bounded {ρ ψ : ℝ → ℝ} {s : ℕ → ℝ → ℝ} (h : PathScales ρ ψ s) :
    (∀ i, Measurable (wS ρ ψ s i)) ∧ ∃ C : ℝ, ∀ i u, |wS ρ ψ s i u| ≤ C := by
  obtain ⟨hs, hρ, hψ, C, hsC, hρC, hψC⟩ := h
  refine ⟨fun i => (hρ.mul hψ).mul (hs i), C * C * C, fun i u => ?_⟩
  simp only [wS, abs_mul]
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hρC 0)
  gcongr
  · exact hρC u
  · exact hψC u
  · exact hsC i u

lemma explicit : Standalone.SpliceRandomScalesPath.explicitStatement := by
  intro ρ ψ s h Tm r A hA b c j t T0 ht hj htT0 T hT htT
  obtain ⟨hm, C, hC⟩ := wS_bounded h
  have e := Novel.SpliceQuasiExponentialCrossProof.explicit Tm (wS ρ ψ s) hm C hC r A hA b c 1 j
    t T0 ht hj htT0 T hT htT
  rw [show (fun u => cross039 ρ ψ s Tm c A b u T) = fun u => cross035 1 (wS ρ ψ s) Tm c A b u T
    from funext fun u => cross ρ ψ s Tm r c A b u T, e, one_mul]
  rfl

lemma jump : Standalone.SpliceRandomScalesPath.jumpStatement := by
  intro ρ ψ s h Tm r A b m τ τl τr T0 T1 t h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨hm, C, hC⟩ := wS_bounded h
  have e := Novel.SpliceQuasiExponentialCrossProof.jump Tm (wS ρ ψ s) hm C hC r A b 1 m τ τl τr
    T0 T1 t h1 h2 h3 h4 h5 h6 h7 h8
  have hΔ : (fun u => wS ρ ψ s (m + 1) u - wS ρ ψ s m u) =
      fun u => ρ u * ψ u * (s (m + 1) u - s m u) := funext fun u => by simp only [wS]; ring
  rw [hΔ, one_smul, one_smul] at e
  exact e

lemma key : Standalone.SpliceRandomScalesPath.keyStatement := by
  intro ρ ψ s h r A hA b c hc hctrl m L Tm d₁ d₂ hd hK
  obtain ⟨hs, hρ, hψ, C, hsC, hρC, hψC⟩ := h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hρC 0)
  have hloc : LocallyIntegrable (fun u => ρ u * ψ u * (s (m + 1) u - s m u)) volume := by
    refine (locallyIntegrable_const (C * C * (C + C))).mono
      ((hρ.mul hψ).mul ((hs (m + 1)).sub (hs m))).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    rw [abs_mul, abs_mul]
    gcongr
    · exact hρC u
    · exact hψC u
    · exact (abs_sub _ _).trans (add_le_add (hsC _ _) (hsC _ _))
  exact Novel.SpliceQuasiExponentialKeyProof.key r A hA b c hc hctrl L Tm d₁ d₂ _ hd hloc hK

theorem spliceRandomScalesPath : Standalone.SpliceRandomScalesPath.statement :=
  ⟨cross, explicit, jump, key⟩

end Novel.SpliceRandomScalesPathProof

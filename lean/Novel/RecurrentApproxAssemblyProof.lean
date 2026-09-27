import Standalone.RecurrentApproxAssembly
import Novel.RecurrentApproxEstimatesProof
import Novel.RecurrentApproxMeanSquareProof
import Novel.RecurrentApproxPriceBoundsProof
import Novel.RecurrentApproxBondProof
import Novel.RecurrentApproxRealizationProof

open MeasureTheory Set
open scoped NNReal
open Standalone.RecurrentApproxEstimates Standalone.RecurrentApproxAssembly
namespace Novel.RecurrentApproxAssemblyProof

lemma sharpMS : Standalone.RecurrentApproxAssembly.sharpStatement := by
  intro Ω _ S k hc Tm lam f0 H Λ ε Abar hlm hlam hΛ hε hεA t T htT hTH
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have hA : 0 ≤ Abar := by linarith
  have h : Hyp048 Tm (fun _ => Abar) (fun _ => Abar - ε) lam H Λ ε Abar :=
    ⟨hlm, fun x hx => by rw [hlam x hx, abs_of_nonneg hΛ], fun _ _ =>
      ⟨by rw [sub_sub_cancel, abs_of_nonneg hε], (abs_of_nonneg hA).le,
        abs_le.2 ⟨by linarith, by linarith⟩⟩⟩
  obtain ⟨-, heq, -, -⟩ := Novel.RecurrentApproxMeanSquareProof.meanSquareS Ω S k hc Tm _ _ lam f0
    H Λ ε Abar h t T htT hTH
  obtain ⟨hs1, hs2⟩ := Novel.RecurrentApproxEstimatesProof.sharpS Tm lam H Λ ε Abar hlam t T ht htT hTH
  rw [heq, hs2, intervalIntegral.integral_congr (g := fun _ => (ε * Λ) ^ 2) fun s hs => by
    rw [uIcc_of_le ht] at hs
    simp only [hs1 s ⟨hs.1, hs.2.trans htT⟩]]
  simp
  ring

theorem recurrentApproxAssembly : Standalone.RecurrentApproxAssembly.statement := ⟨Novel.RecurrentApproxEstimatesProof.recurrentApproxEstimates, Novel.RecurrentApproxMeanSquareProof.recurrentApproxMeanSquare, Novel.RecurrentApproxPriceBoundsProof.recurrentApproxPriceBounds, Novel.RecurrentApproxBondProof.recurrentApproxBond, Novel.RecurrentApproxRealizationProof.recurrentApproxRealization, sharpMS⟩

end Novel.RecurrentApproxAssemblyProof

import Standalone.DiffusionMeetingInversion
import Novel.DiffusionMeetingRankProof
import Novel.SpliceCrossTermDriftProof

open Standalone.DiffusionMeetingRank Standalone.DiffusionMeetingInversion
open Novel.DiffusionMeetingRankProof
namespace Novel.DiffusionMeetingInversionProof

lemma Qp_eq {N P L : ℕ} (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (n : Fin (L + 1)) : Qp T c S θ n = Qf T c S θ n := by
  simp only [Qp, Qf, ite_mul, one_mul, zero_mul]

lemma inversionS : inversionStatement := by
  intro N P L T c S hS hS0 hT θ
  have hrow : ∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ},
      (lamE T c S).mulVec (fun p => θ (Sum.inr p)) ℓ =
        Qp T c S θ ℓ.1.succ - Qp T c S θ ℓ.1.castSucc := fun ℓ => by
    rw [← meetingFree_row, Df_eq T c S hS hS0, Qp_eq, Qp_eq]
  refine ⟨by rw [Qp_eq, Qf_zero T c S hS0 hT], fun ℓ => by rw [panel_apply, Qp_eq], hrow,
    fun hinj u hu => hinj (funext fun ℓ => by rw [hu, hrow]), fun ℓ i h1 h2 h3 => ?_⟩
  have := single_row (c := c) ⟨h1, h2⟩ h3 θ
  rw [Df_eq T c S hS hS0, ← Qp_eq, ← Qp_eq] at this
  linarith

lemma bondS : bondStatement := by
  intro Ω N M a b hf ⟨C, hC⟩
  have ii := Novel.SpliceCrossTermDriftProof.ii_bdd hf C hC
  rw [Standalone.DiffusionMeetingPricing.P0, Standalone.DiffusionMeetingPricing.P0,
    ← Real.exp_sub, Real.log_exp, Standalone.DiffusionMeetingGauss.Aint,
    Standalone.DiffusionMeetingGauss.Aint, Standalone.DiffusionMeetingGauss.Aint,
    ← intervalIntegral.integral_interval_sub_left (ii 0 b) (ii 0 a)]
  ring

theorem diffusionMeetingInversion : Standalone.DiffusionMeetingInversion.statement :=
  ⟨inversionS, bondS⟩

end Novel.DiffusionMeetingInversionProof

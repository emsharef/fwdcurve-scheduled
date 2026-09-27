import Standalone.MeetingLoadingObstruction
import Novel.MeetingLoadingCurveProof
import Novel.MeetingLoadingRankProof
import Novel.MeetingLoadingHankelProof
import Novel.MeetingLoadingLawProof

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve Standalone.MeetingLoadingObstruction
namespace Novel.MeetingLoadingObstructionProof

/-- The piece endpoints `0 < 1 < ... < n < n + 1/2`, in increasing order. -/
noncomputable def tau029 (n : ℕ) : Fin (n+2) → ℝ≥0 :=
  fun j => if (j:ℕ) = n+1 then time029 n else ((j:ℕ) : ℝ≥0)

lemma tau_strictMono (n : ℕ) : StrictMono (tau029 n) := by
  intro j j' h
  have h' : (j:ℕ) < j' := h
  have hj : (j:ℕ) ≠ n+1 := by omega
  simp only [tau029, hj, ite_false]
  split_ifs with hj'
  · rw [← NNReal.coe_lt_coe, Novel.MeetingLoadingCurveProof.time_coe, NNReal.coe_natCast]
    have : ((j:ℕ):ℝ) ≤ n := by exact_mod_cast (by omega : (j:ℕ) ≤ n)
    linarith
  · exact_mod_cast h'

lemma rank_bound : rankStatement := by
  intro Ω mΩ S k hB a f0 R n q hreal
  obtain ⟨Y, Z, Ψ, hΨ, hYZ⟩ := hreal
  have hB' := hB.toIsPreBrownianReal
  -- the increments counted backwards from t
  set δ : Ω → Fin (n+1) → ℝ := fun ω l => S.B k (upper029 n l) ω - S.B k (lower029 n l) ω
  let A : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) := LinearMap.funLeft ℝ ℝ Fin.rev
  have hA : Function.Surjective A := LinearMap.funLeft_surjective_of_injective _ _ _ Fin.rev_injective
  have hδeq : (fun ω => (0 : Fin (n+1) → ℝ) +
      A (fun l => S.B k (tau029 n l.succ) ω - S.B k (tau029 n l.castSucc) ω)) = δ := by
    funext ω l
    simp only [zero_add, A, LinearMap.funLeft_apply, δ, tau029, upper029, lower029,
      Fin.val_succ, Fin.coe_castSucc, Fin.val_rev]
    by_cases hl : (l:ℕ) = 0
    · simp [hl]
    · have h1 : n + 1 - (l + 1) + 1 ≠ n + 1 := by omega
      have h2 : n + 1 - (l + 1) ≠ n + 1 := by omega
      simp only [h1, h2, hl, ite_false]
      congr 3 <;> omega
  have hlaw := Novel.MeetingLoadingLawProof.law Ω mΩ S.μ (S.B k) hB' (n+1) (n+1) (tau029 n)
    (tau_strictMono n) A 0 hA
  rw [hδeq] at hlaw
  have hδm : AEMeasurable δ S.μ :=
    AEMeasurable.of_eval fun l => (hB'.aemeasurable _).sub (hB'.aemeasurable _)
  have hcurve := (Novel.MeetingLoadingCurveProof.curve Ω mΩ S k a n R).2
  let c : Fin (R+1) → ℝ := fun i =>
    f0 (mat029 n i) + ∫ s in (0:ℝ)..(time029 n : ℝ), alpha029 a n R s (mat029 n i)
  refine Novel.MeetingLoadingRankProof.rank_le Ω mΩ S.μ inferInstance a R n δ hδm hlaw
    (fun ω i => curve029 S k a f0 n R i ω) c ?_ q Y Z Ψ hΨ ?_
  · filter_upwards [hcurve] with ω hω
    funext i
    simp only [curve029, Pi.add_apply, Matrix.mulVec, dotProduct, c, hω i]
    rfl
  · filter_upwards [hYZ] with ω hω
    exact ⟨hω.1, funext hω.2⟩

lemma recurrence : Standalone.MeetingLoadingObstruction.recurrenceStatement := by
  intro Ω mΩ S k hB a f0 q hall
  exact Novel.MeetingLoadingHankelProof.recurrence a q fun R n =>
    rank_bound Ω mΩ S k hB a f0 R n q (hall R n)

lemma harmonic : Standalone.MeetingLoadingObstruction.harmonicStatement := by
  intro Ω mΩ S k hB f0 q hall
  obtain ⟨L, -, c, hrec⟩ := recurrence Ω mΩ S k hB harmonic029 f0 q hall
  exact Novel.MeetingLoadingHankelProof.harmonic L c hrec

theorem meetingLoadingObstruction : Standalone.MeetingLoadingObstruction.statement :=
  ⟨rank_bound, recurrence, harmonic⟩

end Novel.MeetingLoadingObstructionProof

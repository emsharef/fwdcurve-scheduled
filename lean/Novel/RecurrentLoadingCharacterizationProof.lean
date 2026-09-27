import Standalone.RecurrentLoadingCharacterization
import Novel.MeetingLoadingObstructionProof
import Novel.RecurrentLoadingDiffusionProof
import Novel.RecurrentLoadingAlgebraProof
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory ProbabilityTheory Matrix NormedSpace
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve Standalone.MeetingLoadingObstruction
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDiffusion
namespace Novel.RecurrentLoadingCharacterizationProof

/-- Claim 029's schedule `T_m = m`, `1 ≤ m ≤ n + R`, as a finite set of dates. -/
noncomputable def sched (n R : ℕ) : Finset ℝ :=
  (Finset.range (n+R)).image fun j : ℕ => (j:ℝ) + 1

lemma count_eq (n R : ℕ) (s T : ℝ) : count030 (sched n R) s T = count029 n R s T := by
  rw [count030, count029, sched, Finset.filter_image, Finset.card_image_of_injective]
  intro i j hij
  simpa using hij

/-- `λ ≡ 1` as a quasi-exponential shape. -/
lemma shape_one (x : ℝ) :
    shape030 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (0 : Matrix (Fin 1) (Fin 1) ℝ) x = 1 := by
  simp [shape030, dotProduct]

lemma sufficiency : Standalone.RecurrentLoadingCharacterization.sufficiencyStatement := by
  intro Ω mΩ S k a f0 L c hrec R n
  classical
  obtain ⟨u, v, M, ha⟩ := Novel.RecurrentLoadingAlgebraProof.companion a L c hrec
  let Tm := sched n R
  let cc : Fin 1 → ℝ := fun _ => 1
  let A : Matrix (Fin 1) (Fin 1) ℝ := 0
  let h : ℝ≥0 → Ω → ℝ := fun _ _ => 1
  have hP : IsStronglyPredictable S.ℱ h := stronglyMeasurable_const
  have hC : ∀ s ω, |h s ω| ≤ 1 := fun _ _ => by simp [h]
  have hD := Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP 1 hC L 1 Tm u v M
    cc cc A (time029 n)
  -- Claim 029's volatility is Claim 030's with these data
  have hsig : ∀ T, sigma029 (Ω := Ω) a n R T = sigmaInt Tm u v M cc cc A h T := by
    intro T
    funext s ω
    simp only [sigma029, sigmaInt, sigma030, h, one_mul, cc, A, shape_one, mul_one, Tm,
      count_eq, ha]
  let x : Fin (R+1) → ℝ := fun i => ((i : ℕ) : ℝ) + 1/4
  have hx : ∀ i : Fin (R+1), mat029 n i = (time029 n : ℝ) + x i := fun i => by
    simp only [mat029, time029, x, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    ring
  let κ : Fin (R+1) → Fin L → ℝ := fun i j =>
    k030 u M cc A (x i) (dist030 Tm (time029 n)) (j, 0)
  let Y : Ω → Fin L → ℝ := fun ω j =>
    S.I k (xiInt Tm v M cc A h (time029 n) (j, 0)) (time029 n) ω
  let Ψ : (Fin L → ℝ) → Fin (R+1) → ℝ := fun y i => f0 (mat029 n i) +
    (∫ s in (0:ℝ)..(time029 n : ℝ), alpha029 a n R s (mat029 n i)) + ∑ j, κ i j * y j
  refine ⟨Y, Set.univ, Ψ, fun i => ?_, ?_⟩
  · have : ContDiff ℝ 1 fun y : Fin L → ℝ => Ψ y i := by
      simp only [Ψ]
      fun_prop
    exact this.contDiffOn.locallyLipschitzOn convex_univ
  · have hall := ae_all_iff.2 fun i : Fin (R+1) => hD.2.2 (x i) (by positivity)
    filter_upwards [hall] with ω hω
    refine ⟨Set.mem_univ _, fun i => ?_⟩
    simp only [curve029, Ψ]
    rw [hsig, hx i, hω i]
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl

lemma characterization :
    Standalone.RecurrentLoadingCharacterization.characterizationStatement := by
  intro Ω mΩ S k hB a f0
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨L, -, c, hc⟩ := Novel.MeetingLoadingObstructionProof.recurrence Ω mΩ S k hB a f0 q hq
    exact ⟨L, c, hc⟩
  · rintro ⟨L, c, hc⟩
    exact ⟨L, sufficiency Ω mΩ S k a f0 L c hc⟩

theorem recurrentLoadingCharacterization : Standalone.RecurrentLoadingCharacterization.statement := ⟨sufficiency, characterization⟩

end Novel.RecurrentLoadingCharacterizationProof

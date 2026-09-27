import Standalone.RecurrenceNecessityAssembly
import Novel.RecurrenceNecessityRankProof
import Novel.RecurrenceNecessityAlgebraProof
import Novel.RecurrentLoadingCharacterizationProof

open MeasureTheory ProbabilityTheory Matrix NormedSpace
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve Standalone.RecurrenceNecessityCurve
open Standalone.RecurrenceNecessityRank Standalone.RecurrenceNecessityAssembly
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDiffusion
namespace Novel.RecurrenceNecessityAssemblyProof

lemma necessity : necessityStatement := by
  intro Ω mΩ S k hB a r c b A f0 q hlne hreal
  obtain ⟨C, b', c', hlam, hΓ, hc⟩ := Novel.RecurrenceNecessityReductionProof.reduction r A b c
  have hc' : c' ≠ 0 := hc hlne
  have hrank : ∀ R n, (Standalone.RecurrenceNecessityAlgebra.blockHankel032 a c' (exp C) R n).rank
      ≤ q := fun R n =>
    Novel.RecurrenceNecessityRankProof.rank_bound Ω mΩ S k hB a r c b A f0 n R q (hreal R n)
      C b' c' hlam hΓ
  have hdet : IsUnit (exp C).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  exact Novel.RecurrenceNecessityAlgebraProof.recurrence r a c' (exp C) hc' hdet q hrank

/-- Claim 030's construction realizes recurrent loadings, for any quasi-exponential shape. -/
lemma sufficiency (Ω : Type) [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (a : ℕ → ℝ) (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (f0 : ℝ → ℝ) (L : ℕ)
    (coef : Fin L → ℝ) (hrec : Recurrence029 a L coef) (R n : ℕ) :
    Realized032 S k a c A b f0 n R (L * r) := by
  classical
  obtain ⟨u, v, M, ha⟩ := Novel.RecurrentLoadingAlgebraProof.companion a L coef hrec
  let Tm := Novel.RecurrentLoadingCharacterizationProof.sched n R
  let h : ℝ≥0 → Ω → ℝ := fun _ _ => 1
  have hP : IsStronglyPredictable S.ℱ h := stronglyMeasurable_const
  have hC : ∀ s ω, |h s ω| ≤ 1 := fun _ _ => by simp [h]
  have hD := Novel.RecurrentLoadingDiffusionProof.diffusion Ω mΩ S k h hP 1 hC L r Tm u v M
    c b A (time029 n)
  have hsig : ∀ T, sigma032 (Ω := Ω) a c A b n R T = sigmaInt Tm u v M c b A h T := by
    intro T
    funext s ω
    simp only [sigma032, sigmaInt, sigma030, h, one_mul, Tm,
      Novel.RecurrentLoadingCharacterizationProof.count_eq, ← ha]
    rfl
  let x : Fin (R+1) → ℝ := fun i => ((i : ℕ) : ℝ) + 1/4
  have hx : ∀ i : Fin (R+1), mat029 n i = (time029 n : ℝ) + x i := fun i => by
    simp only [mat029, time029, x, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    ring
  let e := (finProdFinEquiv : Fin L × Fin r ≃ Fin (L * r))
  let κ : Fin (R+1) → Fin (L * r) → ℝ := fun i j =>
    k030 u M c A (x i) (dist030 Tm (time029 n)) (e.symm j)
  let Y : Ω → Fin (L * r) → ℝ := fun ω j =>
    S.I k (xiInt Tm v M b A h (time029 n) (e.symm j)) (time029 n) ω
  let Ψ : (Fin (L * r) → ℝ) → Fin (R+1) → ℝ := fun y i => f0 (mat029 n i) +
    (∫ s in (0:ℝ)..(time029 n : ℝ), alpha032 a c A b n R s (mat029 n i)) + ∑ j, κ i j * y j
  refine ⟨Y, Set.univ, Ψ, fun i => ?_, ?_⟩
  · have : ContDiff ℝ 1 fun y : Fin (L * r) → ℝ => Ψ y i := by
      simp only [Ψ]
      fun_prop
    exact this.contDiffOn.locallyLipschitzOn convex_univ
  · have hall := ae_all_iff.2 fun i : Fin (R+1) => hD.2.2 (x i) (by positivity)
    filter_upwards [hall] with ω hω
    refine ⟨Set.mem_univ _, fun i => ?_⟩
    simp only [curve032, Ψ]
    rw [hsig, hx i, hω i]
    congr 1
    simp only [dotProduct, κ, Y]
    exact Fintype.sum_equiv e _ _ fun ab => by simp

lemma characterization : characterizationStatement := by
  intro Ω mΩ S k hB a r c b A hlne
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨L, -, coef, hc⟩ := necessity Ω mΩ S k hB a r c b A (fun _ => 0) q hlne hq
    exact ⟨L, coef, hc⟩
  · rintro ⟨L, coef, hc⟩
    exact ⟨L * r, fun R n => sufficiency Ω S k a r c b A (fun _ => 0) L coef hc R n⟩

theorem recurrenceNecessityAssembly : Standalone.RecurrenceNecessityAssembly.statement := ⟨Novel.RecurrenceNecessityAlgebraProof.recurrenceNecessityAlgebra, Novel.RecurrenceNecessityGaussianProof.recurrenceNecessityGaussian, Novel.RecurrenceNecessityReductionProof.recurrenceNecessityReduction, Novel.RecurrenceNecessityCurveProof.recurrenceNecessityCurve, Novel.RecurrenceNecessityRankProof.recurrenceNecessityRank, necessity, characterization⟩

end Novel.RecurrenceNecessityAssemblyProof

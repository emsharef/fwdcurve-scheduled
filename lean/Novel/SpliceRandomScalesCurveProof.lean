import Standalone.SpliceRandomScalesCurve
import Novel.SpliceQuasiExponentialCurveProof
import Novel.RecurrentLoadingDiffusionProof

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceRandomScalesCurve
namespace Novel.SpliceRandomScalesCurveProof

variable {r : ℕ}

section U4
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- `√(1 − ρ²)` of a predictable process is predictable. -/
lemma sqrt_pred (ρ : ℝ → Ω → ℝ) (hρ : IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => ρ u ω)) :
    IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => Real.sqrt (1 - ρ u ω ^ 2)) :=
  (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).comp_stronglyMeasurable hρ

lemma sqrt_le (x : ℝ) : |Real.sqrt (1 - x ^ 2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (by nlinarith)

/-- A bounded predictable process times a bounded continuous function of time. -/
lemma U4_mul (h : ℝ → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => h u ω))
    (C : ℝ) (hC : ∀ u ω, |h u ω| ≤ C) (g : ℝ≥0 → ℝ) (hg : Continuous g) :
    U4 S.ℱ S.μ (fun (u : ℝ≥0) ω => h u ω * g u) :=
  Novel.RecurrentLoadingDiffusionProof.U4_scaled S (fun u ω => h u ω) hP C (fun u ω => hC u ω) g
    hg.measurable (Novel.RecurrenceNecessityCurveProof.bdd_of_cont _ hg)

lemma U4_proc (h : ℝ → Ω → ℝ) (hP : IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => h u ω))
    (C : ℝ) (hC : ∀ u ω, |h u ω| ≤ C) : U4 S.ℱ S.μ (fun (u : ℝ≥0) ω => h u ω) := by
  have := U4_mul S h hP C hC (fun _ => 1) continuous_const
  simpa using this

end U4

lemma gcont (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (i : Fin r) :
    Continuous fun u : ℝ≥0 => (exp ((u : ℝ) • (-A)) *ᵥ b) i :=
  (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i).comp NNReal.continuous_coe

lemma random : randomStatement := by
  intro Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c T t
  obtain ⟨hsP, hρP, hψP, -, -, -, hsC, hρC, hψC⟩ := hsc
  set w := c ᵥ* exp (T • A)
  set g : Fin r → ℝ≥0 → ℝ := fun i u => (exp ((u : ℝ) • (-A)) *ᵥ b) i
  -- the two weights `ρψ` and `√(1 − ρ²) ψ`
  have hw1P : IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => ρ u ω * ψ u ω) := hρP.mul hψP
  have hw1C : ∀ u ω, |ρ u ω * ψ u ω| ≤ 1 * C := fun u ω => by
    rw [abs_mul]; exact mul_le_mul (hρC u ω) (hψC u ω) (abs_nonneg _) zero_le_one
  have hw2P : IsStronglyPredictable S.ℱ
      (fun (u : ℝ≥0) ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω) := (sqrt_pred S ρ hρP).mul hψP
  have hw2C : ∀ u ω, |Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω| ≤ 1 * C := fun u ω => by
    rw [abs_mul]; exact mul_le_mul (sqrt_le _) (hψC u ω) (abs_nonneg _) zero_le_one
  let G1 : Fin r → ℝ≥0 → Ω → ℝ := fun i u ω => ρ u ω * ψ u ω * g i u
  let G2 : Fin r → ℝ≥0 → Ω → ℝ := fun i u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * g i u
  have hG1 : ∀ i, U4 S.ℱ S.μ (G1 i) := fun i =>
    U4_mul S (fun u ω => ρ u ω * ψ u ω) hw1P _ hw1C (g i) (gcont A b i)
  have hG2 : ∀ i, U4 S.ℱ S.μ (G2 i) := fun i =>
    U4_mul S (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω) hw2P _ hw2C (g i) (gcont A b i)
  have hlam : ∀ u : ℝ, lam035 c A b (T - u) = ∑ i, w i * (exp (u • (-A)) *ᵥ b) i := fun u => by
    rw [Novel.SpliceQuasiExponentialCrossProof.lam_eq]; rfl
  have hstep := U4_proc S (s (idx033 Tm T)) (hsP _) C (hsC _)
  have hK := Novel.SeparableMeetingRepresentationProof.domain_sum S G1 w hG1 Finset.univ
  have h1 := S.int_linear k₁ (fun (u : ℝ≥0) ω => s (idx033 Tm T) u ω)
    (fun u ω => ∑ i ∈ Finset.univ, w i * G1 i u ω) 1 1 hstep hK t
  have hs1 := Novel.SeparableMeetingRepresentationProof.integral_sum S k₁ G1 w hG1 Finset.univ t
  have hs2 := Novel.SeparableMeetingRepresentationProof.integral_sum S k₂ G2 w hG2 Finset.univ t
  have e1 : ((1:ℝ) • (fun (u : ℝ≥0) ω => s (idx033 Tm T) u ω) +
      (1:ℝ) • fun u ω => ∑ i ∈ Finset.univ, w i * G1 i u ω) =
      fun (u : ℝ≥0) ω => s (idx033 Tm T) u ω + ρ u ω * ψ u ω * lam035 c A b (T - u) := by
    funext u ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, hlam, G1, g, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (fun u ω => ∑ i ∈ Finset.univ, w i * G2 i u ω) =
      fun (u : ℝ≥0) ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * lam035 c A b (T - u) := by
    funext u ω
    simp only [hlam, G2, g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at h1
  rw [e2] at hs2
  filter_upwards [h1, hs1, hs2] with ω hω1 hω2 hω3
  rw [hω1, hω3]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [hω2, dotProduct_mulVec]
  simp only [dotProduct, Yv039, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [G1, G2, g, w]
  ring
theorem spliceRandomScalesCurve : Standalone.SpliceRandomScalesCurve.statement := random

end Novel.SpliceRandomScalesCurveProof

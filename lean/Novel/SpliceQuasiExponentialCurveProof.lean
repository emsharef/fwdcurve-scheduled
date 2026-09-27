import Standalone.SpliceQuasiExponentialCurve
import Novel.SpliceQuasiExponentialCrossProof
import Novel.SeparableMeetingRepresentationProof

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceQuasiExponentialCurve
namespace Novel.SpliceQuasiExponentialCurveProof

variable {r : ℕ}

section Random
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma g_U4 (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (i : Fin r) :
    U4 S.ℱ S.μ (fun (u : ℝ≥0) (_ : Ω) => (exp ((u : ℝ) • (-A)) *ᵥ b) i) :=
  have hc : Continuous fun u : ℝ≥0 => (exp ((u : ℝ) • (-A)) *ᵥ b) i :=
    (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i).comp NNReal.continuous_coe
  Novel.RecurrenceNecessityCurveProof.U4_det S _ hc.measurable
    (Novel.RecurrenceNecessityCurveProof.bdd_of_cont _ hc)

end Random

lemma random : randomStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC r A b c ρ T t
  set w := c ᵥ* exp (T • A)
  set σ := Real.sqrt (1 - ρ ^ 2)
  let G : Fin r → ℝ≥0 → Ω → ℝ := fun i u _ => (exp ((u : ℝ) • (-A)) *ᵥ b) i
  have hG : ∀ i, U4 S.ℱ S.μ (G i) := fun i => g_U4 S A b i
  have hlam : ∀ u : ℝ, lam035 c A b (T - u) = ∑ i, w i * (exp (u • (-A)) *ᵥ b) i := fun u => by
    rw [Novel.SpliceQuasiExponentialCrossProof.lam_eq]; rfl
  have hK := Novel.SeparableMeetingRepresentationProof.domain_sum S G (fun i => ρ * w i) hG
    Finset.univ
  have h1 := S.int_linear k₁ (fun (u : ℝ≥0) (_ : Ω) => s (idx033 Tm T) u)
    (fun u ω => ∑ i ∈ Finset.univ, (ρ * w i) * G i u ω) 1 1
    (Novel.SpliceCrossTermCurveProof.step_U4 S s hs C hC _) hK t
  have hs1 := Novel.SeparableMeetingRepresentationProof.integral_sum S k₁ G (fun i => ρ * w i)
    hG Finset.univ t
  have hs2 := Novel.SeparableMeetingRepresentationProof.integral_sum S k₂ G (fun i => σ * w i)
    hG Finset.univ t
  have e1 : ((1:ℝ) • (fun (u : ℝ≥0) (_ : Ω) => s (idx033 Tm T) u) +
      (1:ℝ) • fun u ω => ∑ i ∈ Finset.univ, (ρ * w i) * G i u ω) =
      fun (u : ℝ≥0) (_ : Ω) => sigS033 s Tm u T + ρ * lam035 c A b (T - u) := by
    funext u ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, sigS033, hlam, G,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (fun u ω => ∑ i ∈ Finset.univ, (σ * w i) * G i u ω) =
      fun (u : ℝ≥0) (_ : Ω) => σ * lam035 c A b (T - u) := by
    funext u ω
    simp only [hlam, G, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at h1
  rw [e2] at hs2
  filter_upwards [h1, hs1, hs2] with ω hω1 hω2 hω3
  rw [hω1, hω3]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at hω1 ⊢
  rw [hω2, dotProduct_mulVec]
  simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  simp only [G, w]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem spliceQuasiExponentialCurve : Standalone.SpliceQuasiExponentialCurve.statement := random

end Novel.SpliceQuasiExponentialCurveProof

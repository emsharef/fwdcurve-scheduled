import Standalone.SeparableMeetingMarkovProperty
import Novel.SeparableMeetingMarkovSolutionProof
import Mathlib.MeasureTheory.Function.FactorsThrough
import Upstream.LipschitzMarkovTime
import Upstream.Predictability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization Standalone.SeparableMeetingMarkovSolution
open Standalone.SeparableMeetingMarkovProperty
namespace Novel.SeparableMeetingMarkovPropertyProof

section Initial
variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) {n : ℕ}
  (b : ℝ≥0 × (Fin n → ℝ) → Fin n → ℝ) (σ : ℝ≥0 × (Fin n → ℝ) → Fin n → Fin S.m → ℝ)

/-- A solution from a deterministic initial value takes that value at time 0 a.s. -/
lemma initial_ae (x0 : Fin n → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (hX : Solution6 S b σ (fun _ => x0) X) : X 0 =ᵐ[S.μ] fun _ => x0 := by
  obtain ⟨-, -, hU4, -, heq⟩ := hX
  have hz : ∀ᵐ ω ∂S.μ, ∀ (i : Fin n) (k : Fin S.m),
      S.I k (fun s ω => σ (s, X s ω) i k) 0 ω = 0 := by
    simp only [ae_all_iff]
    exact fun i k => S.int_zero k _ (hU4 i k)
  filter_upwards [heq, hz] with ω he hz0
  funext i
  rw [he 0 i]
  simp [hz0 i]

/-- The solution class does not see the initial random vector off a null set. -/
lemma solution_congr (ξ ξ' : Ω → Fin n → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (hX : Solution6 S b σ ξ X) (hξ : ξ =ᵐ[S.μ] ξ') : Solution6 S b σ ξ' X := by
  obtain ⟨h1, h2, h3, h4, heq⟩ := hX
  refine ⟨h1, h2, h3, h4, ?_⟩
  filter_upwards [heq, hξ] with ω he hx t i
  rw [he t i, hx]

end Initial

lemma markov : markovStatement := by
  intro Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z hset s t hst F hF
  obtain ⟨hTd, hlast, hcoef, hψc, ⟨Kψ, hψ⟩, ⟨Lψ, hψL⟩, hg, hZc, hZsol⟩ := hset
  set XH := XH028 S drv Td Hor psi g Z with hXH
  have hsol := Novel.SeparableMeetingMarkovSolutionProof.solution Ω mΩ S P p d N drv Td Hor
    hTd hlast beta Sigma psi g Kψ Lψ z0 Z hcoef hψc hψ hψL hg hZc hZsol
  have hc := Novel.SeparableMeetingMarkovSolutionProof.coefficients p d N S.m Td Hor beta
    Sigma psi g drv Kψ Lψ hcoef hψc hψ hψL hg
  have h0 := initial_ae S _ _ _ XH hsol
  have hsol' := solution_congr S _ _ _ (XH 0) XH hsol h0.symm
  have hL2 : MemLp (XH 0) 2 S.μ := (memLp_const _).ae_eq h0.symm
  have h1 := M.markov_property hB _ _ _ hc XH hsol' hL2 s t hst F hF
  refine ⟨h1, ?_⟩
  obtain ⟨gts, hgts, heq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap (XH s) inferInstance)
      (f := F ∘ XH t) (μ := S.μ)).exists_eq_measurable_comp
  exact ⟨gts, hgts.measurable, h1.trans (EventuallyEq.of_eq heq)⟩

lemma curve : Standalone.SeparableMeetingMarkovProperty.curveStatement := by
  intro Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z f0 hset s t T hst F hF hFb
  have hΛ := (Novel.SeparableMeetingMarkovRealizationProof.lambda p d N f0 g
    (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k))).2 T
  obtain ⟨C, hC⟩ := hFb
  have hB13 : BoundedBorel13 (fun x : Fin (dim028 p d N) → ℝ =>
      F (Lambda028 f0 g (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k)) x T)) :=
    ⟨hF.comp hΛ.measurable, C, fun x => hC _⟩
  exact (markov Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z hset s t hst _ hB13).2

/-- The audited AX-13 structure gives the standalone restatement. -/
lemma markovTime_ofUpstream {Ω : Type} [MeasurableSpace Ω] (h : Upstream.ItoCalculus Ω)
    (M : Upstream.LipschitzMarkovTime h) :
    MarkovTime (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream h) :=
  ⟨M.markov_property⟩

/-- The audited AX-09 structure gives the standalone restatement. -/
lemma predictability_ofUpstream {Ω : Type} [MeasurableSpace Ω] (h : Upstream.ItoCalculus Ω)
    (P : Upstream.Predictability h.ℱ) :
    Predictability (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream h).ℱ :=
  ⟨P.continuous_predictable⟩

theorem separableMeetingMarkovProperty : Standalone.SeparableMeetingMarkovProperty.statement :=
  ⟨markov, curve⟩

end Novel.SeparableMeetingMarkovPropertyProof

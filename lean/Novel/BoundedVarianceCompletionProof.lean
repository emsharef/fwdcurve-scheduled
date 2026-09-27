import Standalone.BoundedVarianceCompletion
import Novel.BoundedVarianceBondProof
import Novel.BoundedVarianceItoProof
import Novel.BoundedVarianceUniquenessProof

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIndependence Standalone.BoundedVarianceCompletion
namespace Novel.BoundedVarianceCompletionProof

lemma coordinates {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i : Fin S.m) (lam : ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hY : ∀ ω, Continuous fun t => Y t ω) (hzero : ∀ ω, Y 0 ω = 0) :
    ∀ᵐ ω ∂S.μ, (∀ j : Fin 3, Continuous fun s : ℝ => z025 S i lam Y (Real.toNNReal s) ω j) ∧
      z025 S i lam Y 0 ω = 0 := by
  filter_upwards [S.B_continuous i,S.B_zero i] with ω hB hB0
  constructor
  · intro j
    have hy := (hY ω).comp continuous_real_toNNReal
    have hv : Continuous fun s : ℝ => v025 (Y (Real.toNNReal s) ω)/(2*lam) :=
      (continuous_const.add (Novel.BoundedVarianceItoProof.tanh_smooth.continuous.comp hy)).div_const _
    have hprim := (intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ)) hv).continuous
    have ht : Continuous fun s : ℝ => ((Real.toNNReal s : ℝ≥0):ℝ) :=
      NNReal.continuous_coe.comp continuous_real_toNNReal
    fin_cases j
    · exact (ht.div_const lam).add (hB.comp continuous_real_toNNReal)
    · exact hy
    · exact (hprim.comp ht).neg
  · ext j
    fin_cases j <;> simp [z025,hzero,hB0]

lemma construction : constructionStatement := by
  intro Ω mΩ S R E ES A D P Q M hB hBS i k l hik hs hμ hdriver hRS hc hWi hInd hFil lam hl
  obtain ⟨Y,hR,hS,hY,hzero,hjump⟩ := Novel.BoundedVarianceIndependenceProof.jump
    Ω mΩ S R E A D P Q hB i k l hs hμ hdriver hRS hWi hInd hFil lam hl
  have hIto := Novel.BoundedVarianceItoProof.transfer Ω mΩ S R A D P Q k l hs hμ hdriver hRS
    (fun t => by simpa using hB.2.2.2 l l t) lam hl Y hR hY
  have hstop := fun tau => Novel.BoundedVarianceUniquenessProof.stopped Ω mΩ S P k lam hl tau Y hS hY
  refine ⟨Y,hR,hS,hY,hzero,hIto.1,hIto.2,?_,?_,hstop,?_,hjump,coordinates S i lam Y hY hzero⟩
  · intro tau T htau
    exact Novel.BoundedVarianceBondProof.martingale Ω mΩ S A P M i k hik hc lam hl Y hS hY tau T htau
  · intro tau
    exact Novel.BoundedVarianceItoProof.covariation Ω mΩ S P k
      (fun t => by simp [hc]) Y hS.1 hY tau

  · intro tau X hX
    exact Novel.BoundedVarianceUniquenessProof.uniqueness Ω mΩ S ES hBS k lam hl tau
      X (fun t ω _ => Y (min t tau) ω) hX (hstop tau)

/-- The construction uses the actual audited Upstream interfaces. All conclusions
refer to the same coordinate; none is supplied as an additional field. -/
theorem upstream_construction {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S R : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE R)
    (ES : Upstream.LipschitzSDE S)
    (A : Upstream.IntegralApproximation S) (D : Upstream.IntegralApproximation R)
    (P : Upstream.Predictability S.ℱ) (Q : Upstream.Predictability R.ℱ)
    (M : Upstream.ExponentialMartingale S) (hB : Upstream.BrownianDrivers6 R)
    (hBS : Upstream.BrownianDrivers6 S)
    (i k : Fin S.m) (l : Fin R.m) (hik : i ≠ k) (hs : ∀ j, j = l)
    (hμ : R.μ = S.μ) (hdriver : S.B k = R.B l) (hRS : ∀ t, R.ℱ t ≤ S.ℱ t)
    (hc : ∀ j j' t, S.c j j' t = if j = j' then 1 else 0)
    (hWi : IsBrownianReal (S.B i) S.μ)
    (hInd : IndepFun (fun ω t => S.B i t ω) (fun ω t => R.B l t ω) S.μ)
    (hFil : ∀ t, R.ℱ t ≤ m025 S.μ (R.B l)) (lam : ℝ) (hl : 0 < lam) :
    ∃ Y, C025 (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
      (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R) i k l lam Y :=
  construction Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R)
    (Novel.BoundedVarianceExistenceProof.ofUpstream R E)
    (Novel.BoundedVarianceExistenceProof.ofUpstream S ES)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream S A)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream R D)
    ⟨P.continuous_predictable⟩ ⟨Q.continuous_predictable⟩
    (Novel.BoundedVarianceMartingaleProof.ofUpstream S M)
    hB hBS i k l hik hs hμ hdriver hRS hc hWi hInd hFil lam hl

theorem boundedVarianceCompletion : Standalone.BoundedVarianceCompletion.statement :=
  ⟨Novel.BoundedVarianceStateProof.boundedVarianceState,
    Novel.BoundedVarianceBondProof.boundedVarianceBond,
    Novel.BoundedVarianceItoProof.boundedVarianceIto,
    Novel.BoundedVarianceUniquenessProof.boundedVarianceUniqueness,construction⟩

end Novel.BoundedVarianceCompletionProof

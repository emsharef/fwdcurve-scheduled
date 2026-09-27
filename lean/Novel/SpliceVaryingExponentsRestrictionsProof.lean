import Standalone.SpliceVaryingExponentsRestrictions
import Novel.SpliceVaryingExponentsProof
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Upstream.ExpPolyConsistency

open MeasureTheory ProbabilityTheory Set Polynomial
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.SpliceVaryingExponents Standalone.SpliceVaryingExponentsRestrictions
namespace Novel.SpliceVaryingExponentsRestrictionsProof

lemma restrictions : Standalone.SpliceVaryingExponentsRestrictions.restrictionsStatement := by
  intro Ω _ S E hB K n Z b σ hIto hH1 hP hAX
  -- (H2) from (a), almost everywhere
  have hH2 : aeTP S fun t ω => Eq3 (Z t ω) (aMat σ t ω) (fun j => b j t ω) := by
    have := Novel.SpliceVaryingExponentsProof.transfer K n (ℝ × Ω) inferInstance
      (((volume : Measure ℝ).restrict (Set.Ici 0)).prod S.μ)
      (fun p => Z (Real.toNNReal p.1) p.2) (fun p => aMat σ (Real.toNNReal p.1) p.2)
      (fun p j => b j (Real.toNNReal p.1) p.2) hP hAX
    filter_upwards [this] with p hp x _ using hp x
  have hPre : Premises16 S Z b σ := ⟨hIto, hH1, hH2⟩
  exact ⟨hPre, E.exponent_diffusion_zero hB K n Z b σ hPre,
    E.exponent_drift_zero hB K n Z b σ hPre, E.exponent_constant hB K n Z b σ hPre,
    E.dynamics_after_stopping hB K n Z b σ hPre, E.dynamics_regular hB K n Z b σ hPre,
    E.corollary_3_4 hB K n Z b σ hPre, E.corollary_3_5 hB K n Z b σ hPre⟩

/-- The audited AX-16 structure gives the standalone restatement. -/
lemma expPoly_ofUpstream {Ω : Type} [MeasurableSpace Ω] (h : Upstream.ItoCalculus Ω)
    (E : Upstream.ExpPolyConsistency h) :
    ExpPolyConsistency (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream h) :=
  ⟨E.exponent_diffusion_zero, E.exponent_drift_zero, E.exponent_constant,
    E.dynamics_after_stopping, E.dynamics_regular, E.corollary_3_4, E.corollary_3_5⟩

theorem spliceVaryingExponentsRestrictions : Standalone.SpliceVaryingExponentsRestrictions.statement :=
  restrictions

end Novel.SpliceVaryingExponentsRestrictionsProof

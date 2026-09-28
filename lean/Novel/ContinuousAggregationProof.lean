import Standalone.ContinuousAggregation
import Novel.ContinuousAggregationCurveProof
import Novel.ContinuousAggregationLevelProof
import Novel.ContinuousAggregationEuropeanProof
import Novel.ContinuousAggregationRegressionProof
import Novel.ContinuousAggregationSectioningProof
import Novel.ContinuousAggregationAmericanLowerProof
import Novel.ContinuousAggregationAmericanProof

/-! # Claim 054, assembled (proof) -/

namespace Novel.ContinuousAggregationProof

theorem continuousAggregation : Standalone.ContinuousAggregation.statement :=
  ⟨Novel.ContinuousAggregationCurveProof.continuousAggregationCurve,
    Novel.ContinuousAggregationLevelProof.continuousAggregationLevel,
    Novel.ContinuousAggregationEuropeanProof.continuousAggregationEuropean,
    Novel.ContinuousAggregationRegressionProof.continuousAggregationRegression,
    Novel.ContinuousAggregationSectioningProof.continuousAggregationSectioning,
    Novel.ContinuousAggregationAmericanLowerProof.continuousAggregationAmericanLower,
    Novel.ContinuousAggregationAmericanProof.continuousAggregationAmerican⟩

end Novel.ContinuousAggregationProof

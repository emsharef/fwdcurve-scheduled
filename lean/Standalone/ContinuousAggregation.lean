import Standalone.ContinuousAggregationCurve
import Standalone.ContinuousAggregationLevel
import Standalone.ContinuousAggregationEuropean
import Standalone.ContinuousAggregationSectioning
import Standalone.ContinuousAggregationAmericanLower
import Standalone.ContinuousAggregationRegression
import Standalone.ContinuousAggregationAmerican

/-! # Claim 054, assembled

Claim 046's model. **Everything probabilistic is conditional on `GaussLaw`**, as in Claim 046.
(54-S) and the deterministic parts of (b) and (d) are unconditional.

* (a), the law of `y_A` under `Q^A` and its independence from the future driving increments:
  `ContinuousAggregationLevel`.
* (b), the curve at `A` and the split of `p` at `A` (54.2): `ContinuousAggregationCurve`; `Λ_V`:
  `ContinuousAggregationEuropean`, and its joint measurability: `ContinuousAggregationAmericanLower`.
* (c), European post-cutoff cash claims (54.3), with the law of `(y_A, Ξ)` under `Q^A`:
  `ContinuousAggregationEuropean`.
* (d), later futures quotes (54.4): `ContinuousAggregationCurve`.
* (54-R), the regression and product representation, with the filtration identity in the
  corrected form (54.7): `ContinuousAggregationRegression`.
* (54-S), sectioning on a product with a right-continuous filtration:
  `ContinuousAggregationSectioning`.
* (e), American post-cutoff cash claims (54.6): the definitions and the lower bound in
  `ContinuousAggregationAmericanLower`, the equality in `ContinuousAggregationAmerican`.
-/

namespace Standalone.ContinuousAggregation

def statement : Prop :=
  Standalone.ContinuousAggregationCurve.statement ∧
    Standalone.ContinuousAggregationLevel.statement ∧
    Standalone.ContinuousAggregationEuropean.statement ∧
    Standalone.ContinuousAggregationRegression.statement ∧
    Standalone.ContinuousAggregationSectioning.statement ∧
    Standalone.ContinuousAggregationAmericanLower.statement ∧
    Standalone.ContinuousAggregationAmerican.statement

end Standalone.ContinuousAggregation

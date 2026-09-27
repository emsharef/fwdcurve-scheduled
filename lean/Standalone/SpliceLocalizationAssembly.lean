import Standalone.SpliceLocalization
import Standalone.SpliceLocalizationConverse
import Standalone.SpliceLocalizationRegularity

/-! # Claim 050: assembly

`statement` gathers Claim 050:
* `SpliceLocalization`: (a), (b), the carry-over of Claim 049's statements to the class (L), and
  (d)'s facts. These are the product counterexample, the bounded factor, products of `L²` rows,
  the shift invariance of (49.1) and the frozen curve.
* `SpliceLocalizationConverse`: (c), the conditional converse's drifts written out, AX-01 with
  them, and their local integrability under (L).
* `SpliceLocalizationRegularity`: (c), the Section 2 regularity of the converse's curve, as
  maturity-uniform envelopes, integrable in time.
-/

namespace Standalone.SpliceLocalizationAssembly

def statement : Prop :=
  Standalone.SpliceLocalization.statement ∧ Standalone.SpliceLocalizationConverse.statement ∧
  Standalone.SpliceLocalizationRegularity.statement

end Standalone.SpliceLocalizationAssembly

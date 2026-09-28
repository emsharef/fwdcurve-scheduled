import Standalone.FrontEndConstructionMatching
import Standalone.FrontEndConstructionProcess
import Standalone.FrontEndConstructionRepresentation

/-! # Claim 055, assembled

The splice's front end at process level. **(a)–(c) are conditional on the cited calculus**
AX-03 to AX-05 (`Upstream.ItoCalculus`, restated verbatim in
`Standalone.ZeroMeanReversionUpstreamBridge`), whose only instance is degenerate. (d)–(f) use
AX-01 in the ledger's form. The block `Z` is given, not constructed.

* (a) `driftStatement`: the matching drifts `ℓ_m`, `c_m` are progressively measurable and, truncated to
  `[0, H]`, in the (U6) class: `FrontEndConstructionProcess`.
* (b) `processStatement`: `L_m`, `C_m` as driver-form processes, predictable and almost surely
  continuous, with `C_m` an integral of its drift: `FrontEndConstructionProcess`.
* (c) `representationStatement`, `regularityStatement`: (2.2) for (`eq:splice`) with the
  coefficients of Claims 049–050, and the regularity of Section 2:
  `FrontEndConstructionRepresentation`.
* (d) `driftConditionStatement`, (e) `matchingStatement`, (f) `theoremStatement`, at the coefficient
  level: `FrontEndConstructionMatching`.
-/

namespace Standalone.FrontEndConstruction

def statement : Prop :=
  Standalone.FrontEndConstructionProcess.driftStatement ∧
    Standalone.FrontEndConstructionProcess.processStatement ∧
    Standalone.FrontEndConstructionRepresentation.representationStatement ∧
    Standalone.FrontEndConstructionRepresentation.regularityStatement ∧
    Standalone.FrontEndConstructionMatching.driftConditionStatement ∧
    Standalone.FrontEndConstructionMatching.matchingStatement ∧
    Standalone.FrontEndConstructionMatching.theoremStatement

end Standalone.FrontEndConstruction

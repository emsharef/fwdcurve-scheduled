import Standalone.SpliceCrossTermAnalytic
import Standalone.SpliceCrossTermAlpha
import Standalone.SpliceCrossTermCurve
import Standalone.SpliceCrossTermNecessity
import Standalone.SpliceCrossTermOpen
import Standalone.SpliceCrossTermUncorrelated
import Standalone.SpliceCrossTermSufficiency

/-! # Claim 033: the deterministic-volatility splice, assembled

* (a): the cross term (33.2) with `β_m` and its jump (`SpliceCrossTermDrift`), `α_m` with `κ_m` and
  its jump (`SpliceCrossTermAlpha`), the step and block parts and the version of the random part
  (`SpliceCrossTermCurve`).
* (b) and (d) at the claim level, with consistency in the version form
  (`SpliceCrossTermConsistency`), from their pathwise forms (`SpliceCrossTermNecessity`,
  `SpliceCrossTermOpen`) and the analytic steps (`SpliceCrossTermAnalytic`).
* (c): `E_0` is a block, (c)(i) and (c)(ii) (`SpliceCrossTermSufficiency`), from the
  deterministic core of (c)(i) (`SpliceCrossTermUncorrelated`).
-/

namespace Standalone.SpliceCrossTermAssembly

def statement : Prop :=
  Standalone.SpliceCrossTermAnalytic.statement ∧ Standalone.SpliceCrossTermDrift.statement ∧
  Standalone.SpliceCrossTermAlpha.statement ∧ Standalone.SpliceCrossTermCurve.statement ∧
  Standalone.SpliceCrossTermNecessity.statement ∧ Standalone.SpliceCrossTermOpen.statement ∧
  Standalone.SpliceCrossTermUncorrelated.statement ∧
  Standalone.SpliceCrossTermConsistency.statement ∧
  Standalone.SpliceCrossTermSufficiency.statement

end Standalone.SpliceCrossTermAssembly

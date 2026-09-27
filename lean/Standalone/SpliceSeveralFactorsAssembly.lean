import Standalone.SpliceSeveralFactorsSufficiency
import Standalone.SpliceSeveralFactorsMinimal

/-! # Claim 041, assembled

* (a): the argument for a sum of cross terms (`SpliceSeveralFactorsCore`), its necessity from AX-01
  with several step factors (`SpliceSeveralFactorsAX01.necessityStatement`), and its converse
  (`SpliceSeveralFactorsSufficiency`).
* (b): `SpliceSeveralFactorsBlocks`.
* (c): `SpliceSeveralFactorsMinimal`.
* (d): `SpliceSeveralFactorsAX01.noThirdWayStatement`.
-/

namespace Standalone.SpliceSeveralFactorsAssembly

def statement : Prop :=
  Standalone.SpliceSeveralFactorsCore.statement ∧ Standalone.SpliceSeveralFactorsAX01.statement ∧
  Standalone.SpliceSeveralFactorsSufficiency.statement ∧
  Standalone.SpliceSeveralFactorsBlocks.statement ∧ Standalone.SpliceSeveralFactorsMinimal.statement

end Standalone.SpliceSeveralFactorsAssembly

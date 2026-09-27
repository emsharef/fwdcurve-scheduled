import Standalone.SpliceStateBlockAX01
import Standalone.SpliceStateBlockObservability

/-! # Claim 040, assembled

* Lemma 040-A: `SpliceStateBlockObservability`.
* (a)'s cross term, its jump and the argument on one path: `SpliceStateBlockCross`.
* (a)–(c) from AX-01 for (40.2) in driver form, on one path: `SpliceStateBlockAX01`.
-/

namespace Standalone.SpliceStateBlockAssembly

def statement : Prop :=
  Standalone.SpliceStateBlockObservability.statement ∧ Standalone.SpliceStateBlockCross.statement ∧
  Standalone.SpliceStateBlockAX01.statement

end Standalone.SpliceStateBlockAssembly

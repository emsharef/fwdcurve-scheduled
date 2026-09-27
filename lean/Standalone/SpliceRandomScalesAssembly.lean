import Standalone.SpliceRandomScalesSufficiency

/-! # Claim 039, assembled

* (a): the jump (39.2) and the explicit cross term, path by path (`SpliceRandomScalesPath`), and
  the version of the random part (`SpliceRandomScalesCurve`).
* (b) and (d): `SpliceRandomScalesNecessity`, with (b)'s last step on the path in
  `SpliceRandomScalesPath.keyStatement`.
* (c)(i) and (c)(ii): `SpliceRandomScalesSufficiency`.
-/

namespace Standalone.SpliceRandomScalesAssembly

def statement : Prop :=
  Standalone.SpliceRandomScalesPath.statement ∧ Standalone.SpliceRandomScalesCurve.statement ∧
  Standalone.SpliceRandomScalesNecessity.statement ∧
  Standalone.SpliceRandomScalesSufficiency.statement

end Standalone.SpliceRandomScalesAssembly

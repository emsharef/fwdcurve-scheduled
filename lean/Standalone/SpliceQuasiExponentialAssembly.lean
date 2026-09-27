import Standalone.SpliceQuasiExponentialAlgebra
import Standalone.SpliceQuasiExponentialConsistency
import Standalone.SpliceCrossTermCurve

/-! # Claim 035: the splice with a quasi-exponential block factor, assembled

* (a): the cross term `X_{t,m}` in explicit, entire form and its jump (35.2)
  (`SpliceQuasiExponentialCross`); the step part is Claim 033's
  (`SpliceCrossTermCurve.stepStatement`); the block part lies in every block
  (`SpliceQuasiExponentialBlock.blockPartStatement`); the version of the random part
  (`SpliceQuasiExponentialCurve`).
* `E_1` is the smallest block containing `λ`, `x λ(x)` and `λΛ` (`SpliceQuasiExponentialBlock`).
* (b)'s analytic steps: the affine step and the last step (`SpliceQuasiExponentialAlgebra`), and
  the subspace step with controllability (`SpliceQuasiExponentialKey`).
* (b), (c)(i), (c)(ii) and (d), with consistency in the version form
  (`SpliceQuasiExponentialConsistency`).
-/

namespace Standalone.SpliceQuasiExponentialAssembly

def statement : Prop :=
  Standalone.SpliceQuasiExponentialAlgebra.statement ∧
  Standalone.SpliceQuasiExponentialKey.statement ∧
  Standalone.SpliceQuasiExponentialCross.statement ∧
  Standalone.SpliceCrossTermCurve.stepStatement ∧
  Standalone.SpliceQuasiExponentialBlock.statement ∧
  Standalone.SpliceQuasiExponentialCurve.statement ∧
  Standalone.SpliceQuasiExponentialConsistency.statement

end Standalone.SpliceQuasiExponentialAssembly

import Standalone.JumpShapeTwoPoint
import Standalone.JumpShapeLater
import Standalone.JumpShapeOrigin
import Standalone.JumpShapeGeneral
import Standalone.JumpShapeExist

/-! # Claim 045, assembled

* (45.5) and the pointwise uniqueness step, for one conditional law: `JumpShapeKernel`.
* (45.6) and (b)'s converse, for one conditional law: `JumpShapeProfile`.
* (45.8) for one conditional law: `JumpShapeAffine`.
* (a), the characterization with one null set: `JumpShapeCond`.
* (b) over `ω` (with uniqueness of the law) and (c1): `JumpShapeCondB`.
* (45.7), and (d)(ii) at `τ = 0`: `JumpShapeOrigin`.
* (b)'s existence: `JumpShapeExist`.
* (c2), the two-point level jump: `JumpShapeTwoPoint`.
* (d), the pre-meeting forward rate (5.1): `JumpShapeForward`.
* (d′), without a flat short rate: `JumpShapeGeneral`.
* (e), later intervals: `JumpShapeLater`.
-/

namespace Standalone.JumpShapeAssembly

def statement : Prop :=
  Standalone.JumpShapeKernel.statement ∧ Standalone.JumpShapeProfile.statement ∧
  Standalone.JumpShapeAffine.statement ∧ Standalone.JumpShapeCond.statement ∧
  Standalone.JumpShapeCondB.statement ∧ Standalone.JumpShapeOrigin.statement ∧
  Standalone.JumpShapeExist.statement ∧ Standalone.JumpShapeTwoPoint.statement ∧
  Standalone.JumpShapeForward.statement ∧ Standalone.JumpShapeGeneral.statement ∧
  Standalone.JumpShapeLater.statement

end Standalone.JumpShapeAssembly

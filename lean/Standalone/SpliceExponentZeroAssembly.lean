import Standalone.SpliceExponentZeroQuasiPoly
import Standalone.SpliceExponentZeroCross
import Standalone.SpliceExponentZeroAX01
import Standalone.SpliceExponentZeroResidual

/-! # Claim 044, assembled

* Quasi-exponentials with nonzero exponents are independent of the polynomials:
  `SpliceExponentZeroQuasiPoly`.
* (a)'s cross terms, their jumps and the argument on one path: `SpliceExponentZeroCross`.
* (a)–(c) from AX-01 for the block (44.1) in driver form, on one path: `SpliceExponentZeroAX01`.
* (b)'s point that Claim 043's bound and admissible covariances carry over with the extra cross
  terms: `SpliceExponentZeroResidual`.
-/

namespace Standalone.SpliceExponentZeroAssembly

def statement : Prop :=
  Standalone.SpliceExponentZeroQuasiPoly.statement ∧ Standalone.SpliceExponentZeroCross.statement ∧
    Standalone.SpliceExponentZeroAX01.statement ∧ Standalone.SpliceExponentZeroResidual.statement

end Standalone.SpliceExponentZeroAssembly

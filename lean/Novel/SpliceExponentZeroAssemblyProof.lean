import Standalone.SpliceExponentZeroAssembly
import Novel.SpliceExponentZeroAX01Proof
import Novel.SpliceExponentZeroResidualProof

namespace Novel.SpliceExponentZeroAssemblyProof

theorem spliceExponentZeroAssembly : Standalone.SpliceExponentZeroAssembly.statement :=
  ⟨Novel.SpliceExponentZeroQuasiPolyProof.spliceExponentZeroQuasiPoly,
    Novel.SpliceExponentZeroCrossProof.spliceExponentZeroCross,
    Novel.SpliceExponentZeroAX01Proof.spliceExponentZeroAX01,
    Novel.SpliceExponentZeroResidualProof.spliceExponentZeroResidual⟩

end Novel.SpliceExponentZeroAssemblyProof

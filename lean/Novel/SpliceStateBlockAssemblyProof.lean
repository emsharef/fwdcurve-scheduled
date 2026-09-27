import Standalone.SpliceStateBlockAssembly
import Novel.SpliceStateBlockAX01Proof

namespace Novel.SpliceStateBlockAssemblyProof

theorem spliceStateBlockAssembly : Standalone.SpliceStateBlockAssembly.statement :=
  ⟨Novel.SpliceStateBlockObservabilityProof.spliceStateBlockObservability,
    Novel.SpliceStateBlockCrossProof.spliceStateBlockCross,
    Novel.SpliceStateBlockAX01Proof.spliceStateBlockAX01⟩

end Novel.SpliceStateBlockAssemblyProof

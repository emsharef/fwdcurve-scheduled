import Standalone.SpliceRandomScalesAssembly
import Novel.SpliceRandomScalesSufficiencyProof

namespace Novel.SpliceRandomScalesAssemblyProof

theorem spliceRandomScalesAssembly : Standalone.SpliceRandomScalesAssembly.statement :=
  ⟨Novel.SpliceRandomScalesPathProof.spliceRandomScalesPath,
    Novel.SpliceRandomScalesCurveProof.spliceRandomScalesCurve,
    Novel.SpliceRandomScalesNecessityProof.spliceRandomScalesNecessity,
    Novel.SpliceRandomScalesSufficiencyProof.spliceRandomScalesSufficiency⟩

end Novel.SpliceRandomScalesAssemblyProof

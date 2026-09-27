import Standalone.CorrelatedFactorsAssembly
import Novel.CorrelatedFactorsAlwaysProof
import Novel.CorrelatedFactorsSignProof
import Novel.CorrelatedFactorsSmallProof
import Novel.CorrelatedFactorsProcessProof
import Novel.CorrelatedFactorsGramProof
import Novel.NonnegPolySOSProof

namespace Novel.CorrelatedFactorsAssemblyProof

theorem correlatedFactorsAssembly : Standalone.CorrelatedFactorsAssembly.statement :=
  ⟨Novel.CorrelatedFactorsReductionProof.correlatedFactorsReduction,
    Novel.NonnegPolySOSProof.nonnegPolySOS, Novel.CorrelatedFactorsGramProof.correlatedFactorsGram,
    Novel.CorrelatedFactorsExistsProof.correlatedFactorsExists,
    Novel.CorrelatedFactorsHankelProof.correlatedFactorsHankel,
    Novel.CorrelatedFactorsAlwaysProof.correlatedFactorsAlways,
    Novel.CorrelatedFactorsSignProof.correlatedFactorsSign,
    Novel.CorrelatedFactorsSmallProof.correlatedFactorsSmall,
    Novel.CorrelatedFactorsProcessProof.correlatedFactorsProcess⟩

end Novel.CorrelatedFactorsAssemblyProof

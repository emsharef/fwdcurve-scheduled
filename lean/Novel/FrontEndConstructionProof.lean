import Standalone.FrontEndConstruction
import Novel.FrontEndConstructionMatchingProof
import Novel.FrontEndConstructionProcessProof
import Novel.FrontEndConstructionRepresentationProof

/-! # Claim 055, assembled (proof) -/

namespace Novel.FrontEndConstructionProof

theorem frontEndConstruction : Standalone.FrontEndConstruction.statement :=
  ⟨Novel.FrontEndConstructionProcessProof.driftS, Novel.FrontEndConstructionProcessProof.processS,
    Novel.FrontEndConstructionRepresentationProof.representationS,
    Novel.FrontEndConstructionRepresentationProof.regularityS,
    Novel.FrontEndConstructionMatchingProof.driftS, Novel.FrontEndConstructionMatchingProof.matchingS,
    Novel.FrontEndConstructionMatchingProof.theoremS⟩

end Novel.FrontEndConstructionProof

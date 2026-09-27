import Standalone.MaturityShapeAssembly
import Novel.MaturityShapeConsistencyProof
import Novel.MaturityShapeInstanceProof
import Novel.MaturityShapeListingProof
import Novel.MaturityShapeS1Proof
import Novel.MaturityShapeS2Proof
import Novel.DiffusionMeetingPricingProof

namespace Novel.MaturityShapeAssemblyProof

theorem maturityShapeAssembly : Standalone.MaturityShapeAssembly.statement :=
  ⟨Novel.MaturityShapeConsistencyProof.maturityShapeConsistency,
    Novel.MaturityShapeIdentitiesProof.maturityShapeIdentities,
    Novel.MaturityShapeGaussProof.maturityShapeGauss,
    Novel.MaturityShapePricingProof.maturityShapePricing,
    Novel.DiffusionMeetingPricingProof.surfaceS,
    Novel.MaturityShapeRankProof.maturityShapeRank,
    Novel.MaturityShapeCalendarProof.maturityShapeCalendar,
    Novel.MaturityShapeS2Proof.maturityShapeS2,
    Novel.MaturityShapeS1Proof.maturityShapeS1,
    Novel.MaturityShapeInstanceProof.maturityShapeInstance,
    Novel.MaturityShapeListingProof.maturityShapeListing⟩

end Novel.MaturityShapeAssemblyProof

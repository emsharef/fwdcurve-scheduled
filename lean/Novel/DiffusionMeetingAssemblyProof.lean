import Standalone.DiffusionMeetingAssembly
import Novel.DiffusionMeetingConsistencyProof
import Novel.DiffusionMeetingInversionProof
import Novel.DiffusionMeetingRankValueProof
import Novel.DiffusionMeetingCalendarProof
import Novel.DiffusionMeetingFuturesProof
import Novel.DiffusionMeetingPrecisionProof
import Novel.DiffusionMeetingInstanceProof

namespace Novel.DiffusionMeetingAssemblyProof

theorem diffusionMeetingAssembly : Standalone.DiffusionMeetingAssembly.statement :=
  ⟨Novel.DiffusionMeetingConsistencyProof.diffusionMeetingConsistency,
    Novel.DiffusionMeetingIdentitiesProof.diffusionMeetingIdentities,
    Novel.DiffusionMeetingGaussProof.diffusionMeetingGauss,
    Novel.DiffusionMeetingPricingProof.diffusionMeetingPricing,
    Novel.DiffusionMeetingInversionProof.diffusionMeetingInversion,
    Novel.DiffusionMeetingRankProof.diffusionMeetingRank,
    Novel.DiffusionMeetingRankValueProof.diffusionMeetingRankValue,
    Novel.DiffusionMeetingCalendarProof.diffusionMeetingCalendar,
    Novel.DiffusionMeetingFuturesProof.diffusionMeetingFutures,
    Novel.DiffusionMeetingPrecisionProof.diffusionMeetingPrecision,
    Novel.DiffusionMeetingInstanceProof.diffusionMeetingInstance⟩

end Novel.DiffusionMeetingAssemblyProof

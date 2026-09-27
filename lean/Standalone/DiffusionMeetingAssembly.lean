import Standalone.DiffusionMeetingRank
import Standalone.DiffusionMeetingPrecision
import Standalone.DiffusionMeetingCalendar
import Standalone.DiffusionMeetingRankValue
import Standalone.DiffusionMeetingIdentities
import Standalone.DiffusionMeetingFutures
import Standalone.DiffusionMeetingGauss
import Standalone.DiffusionMeetingPricing
import Standalone.DiffusionMeetingConsistency
import Standalone.DiffusionMeetingInversion
import Standalone.DiffusionMeetingInstance

/-! # Claim 046, assembled

**(a) and (b)'s probabilistic parts are conditional on the hypothesis `GaussLaw`** (the joint
Gaussian law of the diffusion's Wiener integrals, their independence from the meeting jumps and
of the filtration's future, and stochastic Fubini), stated in `DiffusionMeetingGauss`. It is not
derived in Lean, and it is neither an `Upstream` field nor a ledger entry (PM's scope decision,
2026-09-25). `DiffusionMeetingInstance` shows that it is satisfiable, by Claim 011's model with
Gaussian meeting jumps and no diffusion.

* (a), consistency (regularity, Assumptions 2.1 and 2.2, (46.1) is (2.2)) and the true martingale
  with its factorization through Claim 011's discounted bond: `DiffusionMeetingConsistency`,
  under `GaussLaw`; the bracket identity: `DiffusionMeetingIdentities`.
* (b), the futures quote `G_0 = exp(A + p)`: `DiffusionMeetingGauss`; the martingale `G`,
  `E[B_S⁻¹] = P(0, S)`, the law of `log G_S` under `Q^S` and the call: `DiffusionMeetingPricing`,
  under `GaussLaw`. The Black form (46.5), the recovery of `(P(0, S), m, q)` and (46.6):
  `DiffusionMeetingPricing`, without it. `A = log(P(0, a)/P(0, b))`: `DiffusionMeetingInversion`.
  The drift and accumulation integrals: `DiffusionMeetingIdentities`.
* (c), identification iff full rank, positive non-identified pairs, and (46.8):
  `DiffusionMeetingRank`; `rank 𝒜 = N + rank Λ_E`: `DiffusionMeetingRankValue`; the inversion
  formulas: `DiffusionMeetingInversion`.
* (d1)–(d3): `DiffusionMeetingCalendar`; the rank values: `DiffusionMeetingRankValue`; (d4):
  `DiffusionMeetingFutures`.
* (e), (46.9) and (46.10): `DiffusionMeetingPrecision`.
-/

namespace Standalone.DiffusionMeetingAssembly

def statement : Prop :=
  Standalone.DiffusionMeetingConsistency.statement ∧ Standalone.DiffusionMeetingIdentities.statement ∧
  Standalone.DiffusionMeetingGauss.statement ∧ Standalone.DiffusionMeetingPricing.statement ∧
  Standalone.DiffusionMeetingInversion.statement ∧ Standalone.DiffusionMeetingRank.statement ∧
  Standalone.DiffusionMeetingRankValue.statement ∧ Standalone.DiffusionMeetingCalendar.statement ∧
  Standalone.DiffusionMeetingFutures.statement ∧ Standalone.DiffusionMeetingPrecision.statement ∧
  Standalone.DiffusionMeetingInstance.statement

end Standalone.DiffusionMeetingAssembly

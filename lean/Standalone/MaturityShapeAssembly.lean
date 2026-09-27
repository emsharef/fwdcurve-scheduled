import Standalone.MaturityShapeRank
import Standalone.MaturityShapeCalendar
import Standalone.MaturityShapeS2
import Standalone.MaturityShapeS1
import Standalone.MaturityShapeIdentities
import Standalone.MaturityShapeGauss
import Standalone.MaturityShapePricing
import Standalone.MaturityShapeConsistency
import Standalone.MaturityShapeInstance
import Standalone.MaturityShapeListing
import Standalone.DiffusionMeetingPricing

/-! # Claim 047, assembled

**(a) and (b)'s probabilistic parts are conditional on the hypothesis `ShapeGaussLaw`**
(`MaturityShapeGauss`): Claim 046's `GaussLaw`, with the process `X t x = ∫_0^t σ(s) φ(s, x) dW_s`
and its two stochastic-Fubini forms in place of `Y`. It is not derived in Lean, and it is neither
an `Upstream` field nor a ledger entry (PM's scope decision of 2026-09-25 for Claim 046).
`MaturityShapeInstance` shows that it is satisfiable, by Claim 011's model with Gaussian meeting
jumps and no diffusion, for every bounded Borel shape.

* (a): `MaturityShapeConsistency` (regularity, Assumptions 2.1 and 2.2, (47.1) is (2.2), the true
  martingale and its factorization), under `ShapeGaussLaw`; the identities
  (Assumption 2.1, the bracket): `MaturityShapeIdentities`.
* (b): the futures quote, `MaturityShapeGauss`; `G`, `E[B_S⁻¹] = P(0, S)`, the law under `Q^S`
  and the call, `MaturityShapePricing`, under `ShapeGaussLaw`; (47.4) and `z̃ = log G_0 − log m`,
  `MaturityShapePricing`, without it; the recovery of `(P(0, S), m, q)` from a surface, Claim 046's
  `surfaceStatement` about `C0177`, unchanged.
* (c): `MaturityShapeRank` ((47.5) for any diffusion columns, identification iff full rank, the
  positive perturbation, the inversion formulas, `P ≤ |E|`); the (S1) sign remark,
  `MaturityShapeS1.windowStatement`.
* (d1)–(d2): `MaturityShapeCalendar`; (d3), (S2): `MaturityShapeS2`; (d4), (S1): `MaturityShapeS1`;
  (d5), the listing of 2 January 2026: `MaturityShapeListing`.
-/

namespace Standalone.MaturityShapeAssembly

def statement : Prop :=
  Standalone.MaturityShapeConsistency.statement ∧ Standalone.MaturityShapeIdentities.statement ∧
  Standalone.MaturityShapeGauss.statement ∧ Standalone.MaturityShapePricing.statement ∧
  Standalone.DiffusionMeetingPricing.surfaceStatement ∧ Standalone.MaturityShapeRank.statement ∧
  Standalone.MaturityShapeCalendar.statement ∧ Standalone.MaturityShapeS2.statement ∧
  Standalone.MaturityShapeS1.statement ∧ Standalone.MaturityShapeInstance.statement ∧
  Standalone.MaturityShapeListing.statement

end Standalone.MaturityShapeAssembly

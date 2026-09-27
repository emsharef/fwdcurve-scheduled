import Standalone.SharefFilipovicIto
import Standalone.SharefFilipovicPartB

/-! # Claim 034: the Sharef–Filipović restrictions inside the block, assembled

AX-01 is taken for the drift and volatility that Itô's formula gives for the representation
(34.2): the front end's own, plus those of `F(T − t, Z_t)`.

* The block's Itô drift `D^B` and volatility `σ^B` (`SharefFilipovicIto`, by AX-05).
* (a) and (c), at a fixed time and path: AX-01 for the whole curve on a piece of a maturity
  interval gives the block's equation (34.3) for every `x`, and the front end's own AX-01
  (`SharefFilipovicPartA`). It uses the splitting of AX-01 (`SharefFilipovicSplit`), the
  vanishing of the residual (`SharefFilipovicResidual`) and the independence of `x^k e^{−iβx}`
  from the polynomials (`SharefFilipovicIndependence`).
* (b): the bound on nontrivial factors, by the lab's AX-14 lemma (`SharefFilipovicMaxFactors`),
  and the converse, so the splice is consistent iff `(Z, a, b)` solves (34.3)
  (`SharefFilipovicPartB`).
-/

namespace Standalone.SharefFilipovicAssembly

def statement : Prop :=
  Standalone.SharefFilipovicIndependence.statement ∧ Standalone.SharefFilipovicResidual.statement ∧
  Standalone.SharefFilipovicSplit.statement ∧ Standalone.SharefFilipovicIto.statement ∧
  Standalone.SharefFilipovicPartA.statement ∧ Standalone.SharefFilipovicMaxFactors.statement ∧
  Standalone.SharefFilipovicPartB.statement

end Standalone.SharefFilipovicAssembly

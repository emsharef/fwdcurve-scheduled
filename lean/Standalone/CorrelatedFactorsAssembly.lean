import Standalone.CorrelatedFactorsAlways
import Standalone.CorrelatedFactorsSign
import Standalone.CorrelatedFactorsSmall
import Standalone.CorrelatedFactorsProcess
import Standalone.NonnegPolySOS

/-! # Claim 036, assembled

* (a) is `CorrelatedFactorsReduction`.
* (b): its Gram step is `CorrelatedFactorsGram`, which uses the lab's lemma `NonnegPolySOS`. Its
  first form is `CorrelatedFactorsExists`, and its second (Hankel) form is
  `CorrelatedFactorsHankel`.
* (c) is `CorrelatedFactorsAlways`.
* (d): its necessary sign is `CorrelatedFactorsSign.signStatement`, and its exact conditions for
  `n = 0` and `n = 1` are `CorrelatedFactorsSmall`.
* (e): the point is `CorrelatedFactorsSign.counterexampleStatement`, and the path-level step is
  `CorrelatedFactorsProcess`.
-/

namespace Standalone.CorrelatedFactorsAssembly

def statement : Prop :=
  Standalone.CorrelatedFactorsReduction.statement ∧ Standalone.NonnegPolySOS.statement ∧
  Standalone.CorrelatedFactorsGram.statement ∧ Standalone.CorrelatedFactorsExists.statement ∧
  Standalone.CorrelatedFactorsHankel.statement ∧ Standalone.CorrelatedFactorsAlways.statement ∧
  Standalone.CorrelatedFactorsSign.statement ∧ Standalone.CorrelatedFactorsSmall.statement ∧
  Standalone.CorrelatedFactorsProcess.statement

end Standalone.CorrelatedFactorsAssembly

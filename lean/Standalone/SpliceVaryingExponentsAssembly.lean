import Standalone.SpliceVaryingExponentsRestrictions

/-! # Claim 042, assembled

* (a): the pointwise reduction, with the parameter derivatives certified, and its almost-everywhere
  form (`SpliceVaryingExponents`).
* (b): AX-16's conclusions for `Z` in the splice (`SpliceVaryingExponentsRestrictions`).
-/

namespace Standalone.SpliceVaryingExponentsAssembly

def statement : Prop :=
  Standalone.SpliceVaryingExponents.statement ∧ Standalone.SpliceVaryingExponentsRestrictions.statement

end Standalone.SpliceVaryingExponentsAssembly

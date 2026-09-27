import Standalone.UnifiedSpliceAlgebra
import Standalone.UnifiedSpliceNecessity
import Standalone.UnifiedSpliceConverse
import Standalone.UnifiedSpliceStep0
import Standalone.UnifiedSpliceQuantifiers
import Standalone.UnifiedSpliceExpPoly
import Standalone.UnifiedSpliceDiag
import Standalone.UnifiedSpliceSpecial
import Standalone.UnifiedSpliceConverseAX01

/-! # Claim 049: assembly

`statement` gathers Claim 049:
* `UnifiedSpliceAlgebra`: the pointwise algebra. It covers the effective level (49.5), the general
  jump (b)(i), and the non-level cross part `K` (49.4) of (b)(ii).
* `UnifiedSpliceNecessity`: (a) at a point, and the level jump (49.3).
* `UnifiedSpliceConverse`: (b)(iv) at a point. Consistency on every interval holds iff (49.2)
  holds and `R♯` is affine.
* `UnifiedSpliceStep0`: Step 0, from AX-01 to the pointwise identity, `(Q ⊗ dt)`-a.e.
* `UnifiedSpliceQuantifiers`: (a) and (b)(iv) "only if" with the claim's quantifiers: almost surely,
  for almost every `u`.
* `UnifiedSpliceConverseAX01`: (b)(iv) "if", back to AX-01, with the front-end drifts of Claim
  037(a)'s converse.
* `UnifiedSpliceExpPoly` and `UnifiedSpliceDiag`: (b2) for a diagonalizable exponential part,
  which is (49.6).
* `UnifiedSpliceSpecial`: (c) aggregation, cancellation and the shared-exponent reduction; the
  "orthogonality alone" counterexample; and (d)'s specializations.
-/

namespace Standalone.UnifiedSpliceAssembly

def statement : Prop :=
  Standalone.UnifiedSpliceAlgebra.statement ∧ Standalone.UnifiedSpliceNecessity.statement ∧
  Standalone.UnifiedSpliceConverse.statement ∧ Standalone.UnifiedSpliceStep0.statement ∧
  Standalone.UnifiedSpliceQuantifiers.statement ∧ Standalone.UnifiedSpliceExpPoly.statement ∧
  Standalone.UnifiedSpliceDiag.statement ∧ Standalone.UnifiedSpliceSpecial.statement ∧
  Standalone.UnifiedSpliceConverseAX01.statement

end Standalone.UnifiedSpliceAssembly

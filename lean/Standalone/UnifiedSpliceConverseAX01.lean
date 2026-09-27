import Standalone.UnifiedSpliceStep0

/-! # Claim 049 (b)(iv), "if", back to AX-01

The Setting of Step 0 (`UnifiedSpliceStep0`), at one time `u` on one path. The data `p` fixes the
block and the front end's noise. The front end's drifts `dL_m`, `dC_m` are free: they are the only
coefficients (b)(iv) chooses.

`converseAX01Statement`: suppose (49.2) holds at every meeting `τ ∈ (u, H)`, and `R♯` (with the
effective level `H^{0,0} + V_{n(u)}`) is affine on `ℝ`. Then there are front-end drifts, one
affine function `dL_m + dC_m T` per interval, for which AX-01 holds at `(u, ω)` for every maturity
`T ∈ [u, H]`: `∫_u^T α = ½|∫_u^T σ|²`. This is Claim 037(a)'s converse. The drifts absorb the
affine function that `R♯` differs by, the level's cross terms on each interval (including the
jumps (49.3)), and `σ^S · ∫σ^S`.

The proof:
* by (49.2), every non-level row `h` has `h · V_{n(v)}` constant on `[u, H)`, so
  `h · P(u, T) = (T − u) h · V_{n(u)}`;
* so the non-level cross part is `K` (49.4), and by (49.5) the pointwise identity of Step 0 reads
  `R♯ + (affine) = −D^S` on each interval, where the front-end primitive is `T V_m + κ_m`;
* that fixes affine drifts, and the fundamental theorem of calculus, with finitely many
  exceptional maturities, integrates `α = σ · ∫σ` back to AX-01.
-/

open Matrix NormedSpace Set

namespace Standalone.UnifiedSpliceConverseAX01
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0

def converseAX01Statement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
  IsUnit A.det → ∀ (S : Finset ℝ) (H u : ℝ) (p : Pt049 k r), 0 ≤ u → u < H → u ∉ S →
  (∀ τ ∈ S, u < τ → τ < H →
    (∀ μ, 1 ≤ μ → μ ≤ d → p.Hp μ ⬝ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
    p.Hz *ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) →
  (∃ α β : ℝ, ∀ x, resid (sharp p.Hp (p.V (nS S u))) p.Hz c A d p.bP p.zP p.bZ p.z x =
    α + β * x) →
  ∃ dL dC : ℕ → ℝ, ∀ T ∈ Icc u H, ax01At c A d S { p with dL := dL, dC := dC } u T

def statement : Prop := converseAX01Statement

end Standalone.UnifiedSpliceConverseAX01

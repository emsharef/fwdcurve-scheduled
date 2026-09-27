import Standalone.UnifiedSpliceStep0

/-! # Claim 049 (a) and (b)(iv) with the claim's quantifiers

The Setting of `UnifiedSpliceStep0`. AX-01 holds, in the ledger's form, for the drift and
volatility that Itô's formula gives for the representation, and `A` is invertible with `(A, c)`
observable. The meetings are the finite set `S`, and `n(T)` is the interval of `T`. At a meeting
`τ`, the front end's noise steps from `V_{n(τ)−1}` to `V_{n(τ)}`, so the aggregate maturity-step
integrand is `G = V_{n(τ)} − V_{n(τ)−1}`. The current noise at time `u` is `V_{n(u)}`.

`quantifierStatement`: almost surely, for almost every `u ∈ [0, H]`:
* (a), (49.2): at every meeting `τ ∈ (u, H)`, `H^{0,μ}(u) G = 0` for `μ = 1, …, d`, and
  `H^ζ(u) G = 0`;
* (b)(iv), "only if": `x ↦ R♯(u, x)` is affine on `ℝ`, where `R♯` is the residual with the
  effective level `H^{0,0}(u) + V_{n(u)}(u)`.

The proof combines Step 0 (`UnifiedSpliceStep0`) with the pointwise results. Next to each meeting
`τ`, the front end's primitive is `T V + κ` on either side, with `κ` continuous across `τ`. Step 0's
identity makes the cross part's jump affine, and stage 2's (a) gives (49.2). Just after `u`, the
primitive is `(T − u) V_{n(u)}`, and stage 3's (b)(iv) gives `R♯` affine. Fubini turns
`(Q ⊗ dt)`-a.e. into "almost surely, for almost every `u`".
-/

open Matrix NormedSpace MeasureTheory Set

namespace Standalone.UnifiedSpliceQuantifiers
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0

def quantifierStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r),
  (∀ T, 0 < T → T ≤ H →
    ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 T))), ax01At c A d S (D q.2 q.1) q.2 T) →
  ∀ᵐ ω ∂μ, ∀ᵐ u ∂(volume.restrict (Icc 0 H)),
    (∀ τ ∈ S, u < τ → τ < H →
      (∀ μ', 1 ≤ μ' → μ' ≤ d →
        (D u ω).Hp μ' ⬝ᵥ ((D u ω).V (nS S τ) - (D u ω).V (nS S τ - 1)) = 0) ∧
      (D u ω).Hz *ᵥ ((D u ω).V (nS S τ) - (D u ω).V (nS S τ - 1)) = 0) ∧
    ∃ α β : ℝ, ∀ x, resid (sharp (D u ω).Hp ((D u ω).V (nS S u))) (D u ω).Hz c A d (D u ω).bP
      (D u ω).zP (D u ω).bZ (D u ω).z x = α + β * x

def statement : Prop := quantifierStatement

end Standalone.UnifiedSpliceQuantifiers

import Standalone.UnifiedSpliceAlgebra

/-! # Claim 049 (a) and (b)(i), pointwise

At one time `u` on one path. Across the meeting `T_m`, the front end's noise steps from `V_{m−1}`
to `V_m`, with `G_m = V_m − V_{m−1}` the aggregate maturity-step integrand. The primitive
`T V_m + κ_m` is continuous at `T_m`: `κ_m − κ_{m−1} = −T_m G_m`. The jump of the cross part is
`c_m − c_{m−1}` (`cross`, `UnifiedSpliceAlgebra`). The block's exponential part is invertible
(`A` invertible) and observable.

`necessityStatement`, (a) at a point: if the jump is affine in `T` on an open interval (as Step 0
gives on `I_m ∩ [u, H]`), then (49.2) holds: `H^{0,μ} G_m = 0` for `μ = 1, …, d` and
`H^ζ G_m = 0`. No condition falls on `H^{0,0} G_m`. The proof is the claim's:
* the part with nonzero exponents is `c e^{TA}(y + T z)` with `z = e^{−uA} H^ζ G_m`, and it equals
  a polynomial on the interval. Claim 044's lemma (`SpliceExponentZeroQuasiPoly`) makes it vanish
  identically, and Lemma 040-A (`SpliceStateBlockObservability`) gives `H^ζ G_m = 0`;
* the polynomial part, in `x = T − u`, is `∑_μ (H^{0,μ} G_m)((μ+2)/(μ+1) x^{μ+1} + (u − T_m) x^μ)`.
  It is affine on an interval, hence as a polynomial, and the coefficients of `x^{d+1}, …, x²`
  vanish in turn.

`levelJumpStatement`, (b)(i) (49.3): under (49.2) the jump is
`T ↦ (H^{0,0} G_m)(2T − u − T_m)`, affine.
-/

open Matrix NormedSpace Set

namespace Standalone.UnifiedSpliceNecessity
open Standalone.UnifiedSpliceAlgebra

def necessityStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (V₀ V₁ κ₀ κ₁ : Fin k → ℝ) (Tm u d₁ d₂ α β : ℝ), d₁ < d₂ → κ₁ - κ₀ = -Tm • (V₁ - V₀) →
  (∀ T ∈ Ioo d₁ d₂, cross Hp Hz c A d V₁ κ₁ u T - cross Hp Hz c A d V₀ κ₀ u T = α + β * T) →
  (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V₁ - V₀) = 0) ∧ Hz *ᵥ (V₁ - V₀) = 0

def levelJumpStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (V₀ V₁ κ₀ κ₁ : Fin k → ℝ) (Tm u : ℝ), κ₁ - κ₀ = -Tm • (V₁ - V₀) →
  (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V₁ - V₀) = 0) → Hz *ᵥ (V₁ - V₀) = 0 →
  ∀ T, cross Hp Hz c A d V₁ κ₁ u T - cross Hp Hz c A d V₀ κ₀ u T =
    (Hp 0 ⬝ᵥ (V₁ - V₀)) * (2 * T - u - Tm)

def statement : Prop := necessityStatement ∧ levelJumpStatement

end Standalone.UnifiedSpliceNecessity

import Standalone.RecurrentApproxBond
import Standalone.RecurrentLoadingAssembly

/-! # Claim 048 (c): the approximating model is realized by Claim 030's construction

Assume (H1), `λ(x) = c e^{xA} b`, and (H2) for the approximating loadings:
`ã_i = u M^i v` (`loading030 u v M`). The initial curve is zero. The driver is a Brownian motion,
as in (b).

`realizationStatement`:
* (i) Claim 030's volatility and drift (`sigma030`, `alpha030`) are those of the approximating
  model (48.1) with `ã`, `σ̃` and its own drift `α̃ = σ̃ ∫σ̃`. For `t + x ≤ H`, the approximating
  curve (48.2) satisfies, almost surely, `f̃(t, t + x) = G(Y_t, D(t))(x)`. Here `G(Y_t, D(t))` is the
  realized curve `curve031` at the state `Y_t = (Ξ_t, P_t, Q_t)` (`state030`), of dimension
  `m + m(m+1)/2 + m`, `m = pr` (Claim 030). The realized bond price
  `exp(−∫_t^T G(Y_t, D(t))(y − t) dy)` (`Preal048`) equals `P̃(t, T)` of (b) almost surely.
* (ii) Against the original loadings `a`, for `0 ≤ t ≤ T ≤ H`, with `ε` and `Ā` over the indices
  that occur:
  `E|f(t, T) − G(Y_t, D(t))(T − t)|² ≤ ε²(Λ²H + Ā²Λ⁴H⁴)`, which is (48.5), and
  `E|P(t, T) − exp(−∫_t^T G(Y_t, D(t))(y − t) dy)|² ≤ 2√3 e^{5Ā²Λ²H³} ε²(Λ²H³ + ¼Ā²Λ⁴H⁶)`,
  which is (48.7) with `F_0 = 0`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace Standalone.RecurrentApproxRealization
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
  Standalone.RecurrentLoadingAssembly Standalone.ExternalScaleConditions
  Standalone.RecurrentApproxEstimates Standalone.RecurrentApproxMeanSquare
  Standalone.RecurrentApproxBond Standalone.ZeroMeanReversionUpstreamBridge

/-- The realized bond price `exp(−∫_t^T G(Y_t, D(t))(y − t) dy)`. -/
noncomputable def Preal048 {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (S : ItoCalculus Ω)
    (k : Fin S.m) (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-∫ y in (t:ℝ)..T,
    curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) (y - t))

def realizationStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω)
  (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (p r : ℕ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (a : ℕ → ℝ) (H Λ ε Abar : ℝ),
  Hyp048 Tm a (loading030 u v M) (shape030 c b A) H Λ ε Abar →
    (∀ s T, sigma030 Tm u v M c b A s T = sig048 Tm (loading030 u v M) (shape030 c b A) s T ∧
      alpha030 Tm u v M c b A s T = alpha048 Tm (loading030 u v M) (shape030 c b A) s T) ∧
    ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
      (∀ x, 0 ≤ x → (t:ℝ) + x ≤ H →
        fwd048 S k (fun _ => 0) Tm (loading030 u v M) (shape030 c b A) t (t + x) =ᵐ[S.μ]
          fun ω => curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) x) ∧
      (Preal048 S k Tm u v M c b A t T =ᵐ[S.μ]
        P048 S k (fun _ => 0) Tm (loading030 u v M) c b A t T) ∧
      ∫ ω, (fwd048 S k (fun _ => 0) Tm a (shape030 c b A) t T ω -
          curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) (T - t)) ^ 2 ∂S.μ ≤
        ε ^ 2 * (Λ ^ 2 * H + Abar ^ 2 * Λ ^ 4 * H ^ 4) ∧
      ∫ ω, (P048 S k (fun _ => 0) Tm a c b A t T ω - Preal048 S k Tm u v M c b A t T ω) ^ 2 ∂S.μ ≤
        2 * Real.sqrt 3 * Real.exp (5 * Abar ^ 2 * Λ ^ 2 * H ^ 3) *
          (ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4))

def statement : Prop := realizationStatement

end Standalone.RecurrentApproxRealization

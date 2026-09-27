import Standalone.RecurrentApproxEstimates
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 048 (a): the probabilistic comparison of the forward curves

The driver and its integrals are the restated calculus `ItoCalculus` (AX-03), with a standard
Brownian driver `k` (`c_kk ≡ 1`). For a maturity `T`, the volatility integrand is
`sigT a T s = σ(s, T) 1{s ≤ T}` (48.1), deterministic, so no stochastic input beyond AX-03 is
used. The curves (48.2) share the bounded Borel initial curve `f_0` and the driver:
`f(t, T) = f_0(T) + ∫_0^t α(s, T) ds + ∫_0^t σ(s, T) dW_s`, and likewise `f̃` with `ã`.

`meanSquareStatement`, (a): for `0 ≤ t ≤ T ≤ H`,
* `f − f̃ = m(t, T) + ∫_0^t (σ − σ̃)(s, T) dW_s` almost surely (`f_0` cancels);
* `E|f − f̃|² = m(t, T)² + ∫_0^t (σ − σ̃)(s, T)² ds`, the equality in (48.4);
* hence (48.4), `E|f − f̃|² ≤ ε²[Λ² t + 4Ā²Λ⁴(tT − t²/2)²]`, and (48.5), `E|f − f̃|² ≤ ε²(Λ² H + Ā²Λ⁴ H⁴)`,
  by `RecurrentApproxEstimates`.
-/

open MeasureTheory
open scoped NNReal

namespace Standalone.RecurrentApproxMeanSquare
open Standalone.RecurrentApproxEstimates Standalone.ZeroMeanReversionUpstreamBridge

/-- The integrand `σ(s, T) 1{s ≤ T}`. -/
noncomputable def sigT (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (T : ℝ) (s : ℝ≥0) : ℝ :=
  if (s : ℝ) ≤ T then sig048 Tm a lam s T else 0

/-- The forward curve (48.2) at `(t, T)`. -/
noncomputable def fwd048 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (f0 : ℝ → ℝ) (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  f0 T + (∫ s in (0:ℝ)..t, alpha048 Tm a lam s T) + S.I k (fun s _ => sigT Tm a lam T s) t ω

def meanSquareStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω)
  (k : Fin S.m), (∀ s, S.c k k s = 1) →
  ∀ (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam f0 : ℝ → ℝ) (H Λ ε Abar : ℝ),
    Hyp048 Tm a a' lam H Λ ε Abar → ∀ (t : ℝ≥0) (T : ℝ), (t : ℝ) ≤ T → T ≤ H →
    (fun ω => fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) =ᵐ[S.μ]
      (fun ω => m048 Tm a a' lam t T +
        S.I k (fun s _ => sigT Tm a lam T s - sigT Tm a' lam T s) t ω) ∧
    ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ =
      m048 Tm a a' lam t T ^ 2 +
        ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 ∧
    ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ ≤
      ε ^ 2 * (Λ ^ 2 * t + 4 * Abar ^ 2 * Λ ^ 4 * (t * T - (t:ℝ) ^ 2 / 2) ^ 2) ∧
    ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ ≤
      ε ^ 2 * (Λ ^ 2 * H + Abar ^ 2 * Λ ^ 4 * H ^ 4)

def statement : Prop := meanSquareStatement

end Standalone.RecurrentApproxMeanSquare

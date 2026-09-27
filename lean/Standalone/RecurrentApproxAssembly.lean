import Standalone.RecurrentApproxEstimates
import Standalone.RecurrentApproxMeanSquare
import Standalone.RecurrentApproxPriceBounds
import Standalone.RecurrentApproxBond
import Standalone.RecurrentApproxRealization

/-! # Claim 048: assembly

`statement` gathers Claim 048:
* (a): the deterministic estimates (48.3), and the deterministic parts of (48.4)–(48.5) with the
  sharpness identities (`RecurrentApproxEstimates`). Then the probabilistic comparison
  `E|f − f̃|² = m² + ∫(σ − σ̃)²` and (48.4)–(48.5) (`RecurrentApproxMeanSquare`);
* (b): its deterministic bounds, the Gaussian fourth moment and the price inequality
  (`RecurrentApproxPriceBounds`), then the version and (48.6)–(48.7) (`RecurrentApproxBond`);
* (c): Claim 030's realization of the approximating model, and (48.5), (48.7) against it
  (`RecurrentApproxRealization`);
* `sharpStatement`, the sharpness of (48.4). For `a ≡ Ā`, `ã ≡ Ā − ε` (`0 ≤ ε ≤ 2Ā`) and
  `λ ≡ Λ ≥ 0` on `[0, H]`, `E|f(t, T) − f̃(t, T)|² = ε²[Λ²t + (2Ā − ε)²Λ⁴(tT − t²/2)²]`. At
  `t = T = H` this is at least `ε²Λ²H`, and its ratio to the bound of (48.4) tends to 1 as
  `ε/Ā → 0`.
-/

open MeasureTheory
open scoped NNReal

namespace Standalone.RecurrentApproxAssembly
open Standalone.RecurrentApproxEstimates Standalone.RecurrentApproxMeanSquare
  Standalone.ZeroMeanReversionUpstreamBridge

def sharpStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω)
  (k : Fin S.m), (∀ s, S.c k k s = 1) →
  ∀ (Tm : Finset ℝ) (lam f0 : ℝ → ℝ) (H Λ ε Abar : ℝ), Measurable lam →
    (∀ x ∈ Set.Icc 0 H, lam x = Λ) → 0 ≤ Λ → 0 ≤ ε → ε ≤ 2 * Abar →
    ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
      ∫ ω, (fwd048 S k f0 Tm (fun _ => Abar) lam t T ω -
          fwd048 S k f0 Tm (fun _ => Abar - ε) lam t T ω) ^ 2 ∂S.μ =
        ε ^ 2 * (Λ ^ 2 * t + (2 * Abar - ε) ^ 2 * Λ ^ 4 * (t * T - (t:ℝ) ^ 2 / 2) ^ 2)

def statement : Prop :=
  Standalone.RecurrentApproxEstimates.statement ∧ Standalone.RecurrentApproxMeanSquare.statement ∧
  Standalone.RecurrentApproxPriceBounds.statement ∧ Standalone.RecurrentApproxBond.statement ∧
  Standalone.RecurrentApproxRealization.statement ∧ sharpStatement

end Standalone.RecurrentApproxAssembly

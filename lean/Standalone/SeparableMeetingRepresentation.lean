import Standalone.SeparableMeetingCoefficients

/-! # Claim 026: the HJM representation for finitely many time pieces

For one Brownian driver, the H_k are its masked scales. The statement pulls
out every deterministic maturity loading from the stochastic and ordinary
integrals, on one event for all times at the fixed maturity. There is no
stochastic Fubini assumption and no finite expected-energy premise.
-/
open MeasureTheory ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingCoefficients
open scoped NNReal
namespace Standalone.SeparableMeetingRepresentation

def statement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (n : ℕ) (H : Fin n → ℝ≥0 → Ω → ℝ)
  (g B : Fin n → ℝ) (G : Fin n → ℝ → ℝ),
  (∀ i, U4 S.ℱ S.μ (H i)) → (∀ i, Continuous (G i)) →
  U4 S.ℱ S.μ (fun s ω => ∑ i, g i * H i s ω) ∧
  (∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    S.I k (fun s ω => ∑ i, g i * H i s ω) t ω +
      (∫ s in (0:ℝ)..t, ∑ i, g i * H i (Real.toNNReal s) ω ^ 2 * (B i - G i s)) =
    ∑ i, (g i * (S.I k (H i) t ω - D026 (H i) (G i) t ω) +
      g i * B i * D026 (H i) (fun _ => 1) t ω))

end Standalone.SeparableMeetingRepresentation

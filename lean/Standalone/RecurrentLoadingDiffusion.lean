import Standalone.RecurrentLoadingAlgebra
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claims 030 and 031: the diffusion part of the realization

The scale is a bounded predictable process `h` (Claim 030: `h ≡ 1`; Claim 031:
`h_s = ψ(Z_s)`, predictable by AX-09). The volatility integrand for the maturity
`T` is `h_s σ̃(s,T)`, with `σ̃` Claim 030's (30.1). For a time `t`, `Ξ_t` is the
vector of driver integrals up to `t` of the coordinates of `h_s w(s,t)` stopped
at `t`, with `w` Claim 030's (30.6).

`diffusionStatement`: all these integrands are in (U4), and for every `x ≥ 0`,
almost surely, the driver integral of `h σ̃(·, t+x)` up to `t` is
`k(x, D(t)) · Ξ_t`. The right side is one random vector for all `x`, so it is a
version of the driver integrals, simultaneous in `x` on every path (the version form
of (30.5) and (31.4)); the literal identity simultaneously in `x` is not asserted. The state
equations of `Ξ` between and at meetings are not in this target.
-/

open MeasureTheory Matrix
open scoped NNReal
namespace Standalone.RecurrentLoadingDiffusion
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra

/-- The volatility integrand `h_s σ̃(s,T)`. -/
noncomputable def sigmaInt {Ω : Type*} {p r : ℕ} (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (h : ℝ≥0 → Ω → ℝ) (T : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => h s ω * sigma030 Tm u v M c b A s T

/-- The coordinate `a` of `h_s w(s,t)`, stopped at `t`. -/
noncomputable def xiInt {Ω : Type*} {p r : ℕ} (Tm : Finset ℝ) (v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (h : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Fin p × Fin r) : ℝ≥0 → Ω → ℝ :=
  fun s ω => Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * (h s ω * w030 Tm v M b A s t a)

def diffusionStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ), IsStronglyPredictable S.ℱ h → ∀ C : ℝ, (∀ s ω, |h s ω| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0),
  (∀ T : ℝ, U4 S.ℱ S.μ (sigmaInt Tm u v M c b A h T)) ∧
  (∀ a, U4 S.ℱ S.μ (xiInt Tm v M b A h t a)) ∧
  ∀ x : ℝ, 0 ≤ x → ∀ᵐ ω ∂S.μ,
    S.I k (sigmaInt Tm u v M c b A h ((t:ℝ) + x)) t ω =
      k030 u M c A x (dist030 Tm t) ⬝ᵥ fun a => S.I k (xiInt Tm v M b A h t a) t ω

def statement : Prop := diffusionStatement

end Standalone.RecurrentLoadingDiffusion

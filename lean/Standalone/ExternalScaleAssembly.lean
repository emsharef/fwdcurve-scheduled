import Standalone.ExternalScaleDrift
import Standalone.ExternalScaleStateP
import Standalone.ExternalScaleStateQ
import Standalone.ExternalScaleConditions
import Standalone.RecurrentLoadingXiEquation
import Standalone.BoundedVarianceMartingale

/-! # Claim 031: assembly of the realization with a stochastic scale

The scale is `h_s = ψ(Z_s)` with `ψ` continuous and bounded by `C` and `Z` an `ℝⁿ`-valued
adapted process whose every path is continuous (the everywhere-continuous `Solution6` solution
of Claim 028(a0)); AX-09 (`Predictability`) makes `h` predictable. The HJM curve at time `t`
and time to maturity `x` is `hjm031`: the drift integral of `α` (with the path's scale) plus the
driver integral of `h σ(·, t+x)` up to `t`. The state `Y_t = (Z_t, Ξ_t, P^h_t, Q^h_t)` is
`state031`, with `Ξ_t` the vector of driver integrals of `h_s w(s,t)` up to `t` and `P^h, Q^h`
the pathwise integrals of (31.5).

`curveStatement` is (31.4): the volatility integrands are in (U4), and for every `t` and
`x ≥ 0`, almost surely, `f(t, t+x) = G(Y_t, D(t))(x)` with `G` Claim 030's curve map
`curve031`. This is (31.4) in its version form: the right side uses one random state `Y_t` for
all `x`, so `x ↦ G(Y_t, D(t))(x)` is a version of the curve at time `t`, simultaneous in `x` on
every path. The literal identity for the HJM integral simultaneously in `x` is not asserted: the
cited calculus fixes each driver integral only up to its own null set.
`symmetryStatement`: `P^h_t` is symmetric, so it has `m(m+1)/2` free coordinates, which gives
the state dimension `q = n + m + m(m+1)/2 + m` of (b), independent of the schedule.

`statement` gathers Claim 031: (H2) and (30.7) (`RecurrentLoadingAlgebra`); (a) and (31.5)
(`ExternalScaleDrift`); the diffusion part (`RecurrentLoadingDiffusion`); the equations
(31.2) between meetings and the restarts (31.3) of `P^h` (`ExternalScaleStateP`), `Q^h`
(`ExternalScaleStateQ`) and `Ξ` (`RecurrentLoadingXi`, `RecurrentLoadingXiEquation`, for a
bounded predictable scale); the conditions of (R3)–(R5) (`ExternalScaleConditions`); and (31.4)
with the symmetry above. (c) restates (b) for every scale in (R2).
-/

open MeasureTheory Matrix
open scoped NNReal
namespace Standalone.ExternalScaleAssembly
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingDrift Standalone.RecurrentLoadingDiffusion
open Standalone.ExternalScaleDrift Standalone.ExternalScaleConditions
open Standalone.BoundedVarianceMartingale

variable {Ω : Type*} [MeasurableSpace Ω] {n p r : ℕ}

/-- The HJM curve `f(t, t+x)` with the scale `ψ(Z)`, from the zero initial curve. -/
noncomputable def hjm031 (S : ItoCalculus Ω) (k : Fin S.m) (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (ψ : (Fin n → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (x : ℝ) (ω : Ω) : ℝ :=
  (∫ s in (0:ℝ)..t, alpha031 Tm u v M c b A (fun s => ψ (Z (Real.toNNReal s) ω)) s (t + x)) +
    S.I k (sigmaInt Tm u v M c b A (fun s ω => ψ (Z s ω)) ((t:ℝ) + x)) t ω

/-- The state `Y_t = (Z_t, Ξ_t, P^h_t, Q^h_t)`. -/
noncomputable def state031 (S : ItoCalculus Ω) (k : Fin S.m) (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (ψ : (Fin n → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω) : State031 n p r :=
  (Z t ω, fun a => S.I k (xiInt Tm v M b A (fun s ω => ψ (Z s ω)) t a) t ω,
    P031 Tm v M b A (fun s => ψ (Z (Real.toNNReal s) ω)) t,
    Q031 Tm u v M c b A (fun s => ψ (Z (Real.toNNReal s) ω)) t)

def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), Predictability S.ℱ →
  ∀ (n : ℕ) (Z : ℝ≥0 → Ω → Fin n → ℝ), (∀ t, Measurable[S.ℱ t] (Z t)) →
  (∀ ω, Continuous fun t => Z t ω) →
  ∀ (ψ : (Fin n → ℝ) → ℝ) (C : ℝ), Continuous ψ → (∀ z, |ψ z| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
  (∀ T : ℝ, U4 S.ℱ S.μ (sigmaInt Tm u v M c b A (fun s ω => ψ (Z s ω)) T)) ∧
  ∀ (t : ℝ≥0) (x : ℝ), 0 ≤ x → ∀ᵐ ω ∂S.μ,
    hjm031 S k Tm u v M c b A ψ Z t x ω =
      curve031 u M c A (state031 S k Tm u v M c b A ψ Z t ω) (dist030 Tm t) x

def symmetryStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ)
  (t : ℝ), (P031 Tm v M b A h t)ᵀ = P031 Tm v M b A h t

def statement : Prop :=
  Standalone.RecurrentLoadingAlgebra.statement ∧ Standalone.ExternalScaleDrift.statement ∧
  Standalone.RecurrentLoadingDiffusion.statement ∧ Standalone.ExternalScaleStateP.statement ∧
  Standalone.ExternalScaleStateQ.statement ∧ Standalone.RecurrentLoadingXi.statement ∧
  Standalone.RecurrentLoadingXiEquation.statement ∧ Standalone.ExternalScaleConditions.statement ∧
  curveStatement ∧ symmetryStatement

end Standalone.ExternalScaleAssembly

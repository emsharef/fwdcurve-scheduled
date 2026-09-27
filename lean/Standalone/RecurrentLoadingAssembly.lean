import Standalone.RecurrentLoadingAlgebra
import Standalone.RecurrentLoadingDrift
import Standalone.RecurrentLoadingDiffusion
import Standalone.RecurrentLoadingStateP
import Standalone.RecurrentLoadingRestartP
import Standalone.RecurrentLoadingStateQ
import Standalone.RecurrentLoadingRestartQ
import Standalone.RecurrentLoadingXi
import Standalone.RecurrentLoadingXiEquation
import Standalone.RecurrentLoadingCharacterization
import Standalone.ExternalScaleConditions

/-! # Claim 030: assembly of the realization with constant scale

The HJM curve at time `t` and time to maturity `x`, from the zero initial curve, is `hjm030`:
the drift integral of `α(s, t+x)` plus the driver integral of `σ(·, t+x)` up to `t`. The state
`Y_t = (Ξ_t, P_t, Q_t)` is `state030`, written in Claim 031's `State031` with no scale
coordinate (`n = 0`): `Ξ_t` is the vector of driver integrals of `w(s,t)` up to `t`, and `P_t`,
`Q_t` are the integrals of (30.8).

`curveStatement` is (30.5): the volatility integrands are in (U4), and for every `t` and
`x ≥ 0`, almost surely, `f(t, t+x) = G(Y_t, D(t))(x)`, with `G` the curve map `curve031`,
`k(x, D) · (Ξ + P K(x, D) + Q)`. This is (30.5) in its version form: the right side uses one random
state `Y_t` for all `x`, so `x ↦ G(Y_t, D(t))(x)` is a version of the curve at time `t`,
simultaneous in `x` on every path. The literal identity for the HJM integral simultaneously in `x`
is not asserted: the cited calculus fixes each driver integral only up to its own null set.
`symmetryStatement`: `P_t` is symmetric, so it has `m(m+1)/2` free coordinates, which gives the
state dimension `q = m + m(m+1)/2 + m`, independent of the schedule.

`statement` gathers Claim 030: (H2) and (30.7) (`RecurrentLoadingAlgebra`); (a) and (30.8)
(`RecurrentLoadingDrift`); the diffusion part (`RecurrentLoadingDiffusion`); the equations
(30.3) between meetings and the restarts (30.4) of `P` (`RecurrentLoadingStateP`,
`RecurrentLoadingRestartP`), `Q` (`RecurrentLoadingStateQ`, `RecurrentLoadingRestartQ`) and `Ξ`
(`RecurrentLoadingXi`, `RecurrentLoadingXiEquation`, with `h ≡ 1`); the conditions of (R3)–(R5)
(`ExternalScaleConditions`, with no scale coordinate and `ψ ≡ 1`); (c)
(`RecurrentLoadingCharacterization`); and (30.5) with the symmetry above.
-/

open MeasureTheory Matrix
open scoped NNReal
namespace Standalone.RecurrentLoadingAssembly
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingDrift Standalone.RecurrentLoadingDiffusion
open Standalone.ExternalScaleConditions

variable {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}

/-- The HJM curve `f(t, t+x)` with constant scale, from the zero initial curve. -/
noncomputable def hjm030 (S : ItoCalculus Ω) (k : Fin S.m) (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t : ℝ≥0) (x : ℝ) (ω : Ω) : ℝ :=
  (∫ s in (0:ℝ)..t, alpha030 Tm u v M c b A s (t + x)) +
    S.I k (fun s _ => sigma030 Tm u v M c b A s ((t:ℝ) + x)) t ω

/-- The state `Y_t = (Ξ_t, P_t, Q_t)`, with no scale coordinate. -/
noncomputable def state030 (S : ItoCalculus Ω) (k : Fin S.m) (Tm : Finset ℝ) (u v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t : ℝ≥0) (ω : Ω) : State031 0 p r :=
  (0, fun a => S.I k (xiInt Tm v M b A (fun _ _ => 1) t a) t ω,
    P030 Tm v M b A t, Q030 Tm u v M c b A t)

def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
  (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
  (∀ T : ℝ, U4 S.ℱ S.μ (fun s _ => sigma030 Tm u v M c b A s T)) ∧
  ∀ (t : ℝ≥0) (x : ℝ), 0 ≤ x → ∀ᵐ ω ∂S.μ,
    hjm030 S k Tm u v M c b A t x ω =
      curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) x

def symmetryStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ),
  (P030 Tm v M b A t)ᵀ = P030 Tm v M b A t

def statement : Prop :=
  Standalone.RecurrentLoadingAlgebra.statement ∧ Standalone.RecurrentLoadingDrift.statement ∧
  Standalone.RecurrentLoadingDiffusion.statement ∧ Standalone.RecurrentLoadingStateP.statement ∧
  Standalone.RecurrentLoadingRestartP.statement ∧ Standalone.RecurrentLoadingStateQ.statement ∧
  Standalone.RecurrentLoadingRestartQ.statement ∧ Standalone.RecurrentLoadingXi.statement ∧
  Standalone.RecurrentLoadingXiEquation.statement ∧
  Standalone.ExternalScaleConditions.statement ∧
  Standalone.RecurrentLoadingCharacterization.statement ∧ curveStatement ∧ symmetryStatement

end Standalone.RecurrentLoadingAssembly

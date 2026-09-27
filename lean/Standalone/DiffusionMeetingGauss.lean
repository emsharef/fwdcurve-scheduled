import Standalone.DiffusionMeetingIdentities
import Standalone.CompoundedFuturesIdentification

/-! # Claim 046 (a)–(b): the model, conditional on the Gaussian law of the diffusion's integrals

`DiffModel` is the model (46.1) on a probability space `(Ω, m₀, Q)`: meeting dates `T i > 0` and
variances `v i ≥ 0`, the diffusion's `σ² = g` (bounded, measurable, nonnegative), the initial curve
`f0` (bounded, measurable), the meeting jumps `Z i`, the Wiener integrals `I f = ∫ f σ dW` of
deterministic integrands `f`, the process `Y t = ∫_0^t σ dW`, and the filtration `F`.
`rate` is the short rate `r_u = f(u, u)` of (46.1).

**The Gaussian law is a hypothesis, not derived in Lean** (PM's scope decision, 2026-09-25).
`GaussLaw` states it, as Claims 013–015 take given solutions:
* `I` is linear (almost surely), and every combination `Σ β_i Z_i + I f`, `f` bounded measurable with support in `[0, H]`, has law
  `N(0, Σ β_i² v_i + ∫ f² σ²)`: the integrals are jointly Gaussian with covariance `∫ f g σ²` and
  independent of the `Z_n`;
* `Y t = I 1_{[0, t]}`, with continuous paths, and stochastic Fubini
  `∫_a^b Y_u du = I w_{a,b}` with `w_{a,b}(s) = (b − s)^+ − (a − s)^+` (46.3);
* measurability, for a filtration `F`: `Z i` is `F t`-measurable for `T i ≤ t`, and `I f` for `f` supported in `[0, t]`;
  and independent increments: a combination of the `Z i` with `T i > t` and an `I f` with `f`
  supported in `(t, H]` is independent of `F t`.

* `futuresStatement` is (b)'s futures quote: `E_Q[exp ∫_a^b r] = exp(A + p)`, `A = ∫_a^b f(0, u) du`,
  `p = Σ_i h_i v_i + ∫_0^b σ² h` (46.4), for `0 ≤ a ≤ b ≤ H`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.DiffusionMeetingGauss
open Standalone.CompoundedFuturesIdentification Standalone.DiffusionMeetingIdentities

/-- The model (46.1). -/
structure DiffModel (Ω : Type*) (N : ℕ) where
  T : Fin N → ℝ
  v : Fin N → ℝ
  g : ℝ → ℝ
  f0 : ℝ → ℝ
  Z : Fin N → Ω → ℝ
  I : (ℝ → ℝ) → Ω → ℝ
  Y : ℝ → Ω → ℝ
  F : ℝ → MeasurableSpace Ω

variable {Ω : Type*} {N : ℕ}

/-- The short rate `r_u = f(0, u) + Σ_{T_n ≤ u} [Z_n + v_n (u − T_n)] + Y_u + ∫_0^u σ²(u − s) ds`. -/
noncomputable def rate (M : DiffModel Ω N) (u : ℝ) (ω : Ω) : ℝ :=
  M.f0 u + ∑ n, (if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n) else 0) + M.Y u ω +
    ∫ s in (0:ℝ)..u, M.g s * (u - s)

/-- A deterministic integrand: bounded, measurable, supported in `[lo, hi]`. -/
def Integrand (f : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  Measurable f ∧ (∃ C, ∀ s, |f s| ≤ C) ∧ ∀ s, f s ≠ 0 → lo ≤ s ∧ s ≤ hi

/-- The hypothesis on the diffusion's integrals, up to the horizon `H`. -/
def GaussLaw [m₀ : MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (H : ℝ) : Prop :=
  (∀ i, 0 < M.T i) ∧ (∀ i, 0 ≤ M.v i) ∧ Measurable M.g ∧ (∃ C, ∀ s, |M.g s| ≤ C) ∧
  (∀ s, 0 ≤ M.g s) ∧ Measurable M.f0 ∧ (∃ C, ∀ s, |M.f0 s| ≤ C) ∧
  -- the joint Gaussian law
  (∀ (β : Fin N → ℝ) (f : ℝ → ℝ), Integrand f 0 H →
    Q.map (fun ω => ∑ i, β i * M.Z i ω + M.I f ω) =
      gaussianReal 0 (∑ i, β i ^ 2 * M.v i + ∫ s in (0:ℝ)..H, f s ^ 2 * M.g s).toNNReal) ∧
  -- linearity of the integral, and measurability
  (∀ f g c, Integrand f 0 H → Integrand g 0 H →
    M.I (fun s => f s + c * g s) =ᵐ[Q] fun ω => M.I f ω + c * M.I g ω) ∧
  (∀ i, Measurable (M.Z i)) ∧ (∀ f, Integrand f 0 H → Measurable (M.I f)) ∧
  -- `Y`, its paths and stochastic Fubini
  (∀ ω, Continuous fun u => M.Y u ω) ∧
  (∀ t, 0 ≤ t → t ≤ H → M.Y t =ᵐ[Q] M.I ((Set.Icc 0 t).indicator 1)) ∧
  (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → (fun ω => ∫ u in a..b, M.Y u ω) =ᵐ[Q]
    M.I ((Set.Icc 0 b).indicator fun s => max (b - s) 0 - max (a - s) 0)) ∧
  -- the filtration and independent increments
  Monotone M.F ∧ (∀ t, M.F t ≤ m₀) ∧ (∀ i t, M.T i ≤ t → Measurable[M.F t] (M.Z i)) ∧
  (∀ f t, Integrand f 0 t → Measurable[M.F t] (M.I f)) ∧
  (∀ (t : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ), (∀ i, β i ≠ 0 → t < M.T i) → Integrand f 0 H →
    (∀ s, f s ≠ 0 → t < s) →
    Indep (MeasurableSpace.comap (fun ω => ∑ i, β i * M.Z i ω + M.I f ω) inferInstance) (M.F t) Q)

/-- `A = ∫_a^b f(0, u) du`. -/
noncomputable def Aint (M : DiffModel Ω N) (a b : ℝ) : ℝ := ∫ u in a..b, M.f0 u

/-- `p = Σ_i h_i v_i + ∫_0^b σ² h` (46.4). -/
noncomputable def pdiff (M : DiffModel Ω N) (a b : ℝ) : ℝ :=
  ∑ i, h a b (M.T i) * M.v i + ∫ s in (0:ℝ)..b, M.g s * h a b s

def futuresStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
    ∫ ω, Real.exp (∫ u in a..b, rate M u ω) ∂Q = Real.exp (Aint M a b + pdiff M a b)

def statement : Prop := futuresStatement

end Standalone.DiffusionMeetingGauss

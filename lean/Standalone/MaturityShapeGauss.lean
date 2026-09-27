import Standalone.MaturityShapeIdentities
import Standalone.DiffusionMeetingGauss

/-! # Claim 047 (b): the model with a shape, and the futures quote, conditional on `ShapeGaussLaw`

`ShapeModel` is the model (47.1) on a probability space `(Ω, m₀, Q)`, for a known shape `φ`: the
meeting dates `T i`, variances `v i`, `σ² = g`, the initial curve `f0`, the jumps `Z i`, the Wiener
integrals `I f = ∫ f σ dW` of deterministic integrands, the process
`X t x = ∫_0^t σ(s) φ(s, x) dW_s` (in a jointly measurable version), and the filtration `F`.
`rate M φ u = f(u, u)` and `fwd M φ t T = f(t, T)` are (47.1).

**The Gaussian law is a hypothesis, not derived in Lean**, as for Claim 046 (PM's scope decision of
2026-09-25). `ShapeGaussLaw` is Claim 046's `GaussLaw` with its statements about `Y` replaced by
statements about `X`:
* `X t x = I(1_{[0,t]} φ(·, x))` almost surely, with `u ↦ X u u` and `x ↦ X t x` integrable on
  bounded intervals (the claim's jointly measurable version);
* the stochastic Fubini theorem for bounded deterministic integrands, in the two forms the proof
  uses: `∫_a^b X u u du = I W̃` with `W̃(s) = 1_{[0,b]}(s) ∫_{a∨s}^b φ(s, x) dx` (47.2), and
  `∫_c^d X t x dx = I(1_{[0,t]} ∫_c^d φ(·, x) dx)`.
With `φ ≡ 1` and `X t x = Y_t` it is `GaussLaw`.

* `futuresStatement`: `E_Q[exp ∫_a^b r] = exp(A + p̃)`, `p̃ = Σ_i h_i v_i + ∫_0^b σ² h̃` (47.3),
  `h̃ = d̃ + W̃²/2`, for `0 ≤ a ≤ b ≤ H`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.MaturityShapeGauss
open Standalone.CompoundedFuturesIdentification Standalone.MaturityShapeIdentities
open Standalone.DiffusionMeetingGauss (Integrand)

/-- The model (47.1). -/
structure ShapeModel (Ω : Type*) (N : ℕ) where
  T : Fin N → ℝ
  v : Fin N → ℝ
  g : ℝ → ℝ
  f0 : ℝ → ℝ
  Z : Fin N → Ω → ℝ
  I : (ℝ → ℝ) → Ω → ℝ
  X : ℝ → ℝ → Ω → ℝ
  F : ℝ → MeasurableSpace Ω

variable {Ω : Type*} {N : ℕ}

/-- The short rate `r_u = f(u, u)`. -/
noncomputable def rate (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  M.f0 u + ∑ n, (if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n) else 0) + M.X u u ω +
    ∫ s in (0:ℝ)..u, M.g s * φ s u * Phi φ s u

/-- The forward curve (47.1). -/
noncomputable def fwd (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  M.f0 T + ∑ n, (if M.T n ≤ t then M.Z n ω + M.v n * (T - M.T n) else 0) + M.X t T ω +
    ∫ s in (0:ℝ)..t, M.g s * φ s T * Phi φ s T

/-- `W̃(s) = 1_{[0,b]}(s) ∫_{a∨s}^b φ(s, x) dx` (47.2). -/
noncomputable def Wt (φ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  (Set.Icc 0 b).indicator fun s => ∫ x in max a s..b, φ s x

/-- The hypothesis on the diffusion's integrals, up to the horizon `H`. -/
def ShapeGaussLaw [m₀ : MeasurableSpace Ω] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (Q : Measure Ω)
    (H : ℝ) : Prop :=
  (∀ i, 0 < M.T i) ∧ (∀ i, 0 ≤ M.v i) ∧ Measurable M.g ∧ (∃ C, ∀ s, |M.g s| ≤ C) ∧
  (∀ s, 0 ≤ M.g s) ∧ Measurable M.f0 ∧ (∃ C, ∀ s, |M.f0 s| ≤ C) ∧
  Measurable (Function.uncurry φ) ∧ (∃ C, ∀ s x, |φ s x| ≤ C) ∧
  -- the joint Gaussian law
  (∀ (β : Fin N → ℝ) (f : ℝ → ℝ), Integrand f 0 H →
    Q.map (fun ω => ∑ i, β i * M.Z i ω + M.I f ω) =
      gaussianReal 0 (∑ i, β i ^ 2 * M.v i + ∫ s in (0:ℝ)..H, f s ^ 2 * M.g s).toNNReal) ∧
  -- linearity of the integral, and measurability
  (∀ f g c, Integrand f 0 H → Integrand g 0 H →
    M.I (fun s => f s + c * g s) =ᵐ[Q] fun ω => M.I f ω + c * M.I g ω) ∧
  (∀ i, Measurable (M.Z i)) ∧ (∀ f, Integrand f 0 H → Measurable (M.I f)) ∧
  -- `X`, its version and stochastic Fubini
  (∀ ω a b, IntervalIntegrable (fun u => M.X u u ω) volume a b) ∧
  (∀ ω t a b, IntervalIntegrable (fun x => M.X t x ω) volume a b) ∧
  (∀ t x, 0 ≤ t → t ≤ H → M.X t x =ᵐ[Q] M.I ((Set.Icc 0 t).indicator fun s => φ s x)) ∧
  (∀ a b, 0 ≤ a → a ≤ b → b ≤ H →
    (fun ω => ∫ u in a..b, M.X u u ω) =ᵐ[Q] M.I (Wt φ a b)) ∧
  (∀ t c d, 0 ≤ t → t ≤ H → (fun ω => ∫ x in c..d, M.X t x ω) =ᵐ[Q]
    M.I ((Set.Icc 0 t).indicator fun s => ∫ x in c..d, φ s x)) ∧
  -- the filtration and independent increments
  Monotone M.F ∧ (∀ t, M.F t ≤ m₀) ∧ (∀ i t, M.T i ≤ t → Measurable[M.F t] (M.Z i)) ∧
  (∀ f t, Integrand f 0 t → Measurable[M.F t] (M.I f)) ∧
  (∀ (t : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ), (∀ i, β i ≠ 0 → t < M.T i) → Integrand f 0 H →
    (∀ s, f s ≠ 0 → t < s) →
    Indep (MeasurableSpace.comap (fun ω => ∑ i, β i * M.Z i ω + M.I f ω) inferInstance) (M.F t) Q)

/-- `A = ∫_a^b f(0, u) du`. -/
noncomputable def Aint (M : ShapeModel Ω N) (a b : ℝ) : ℝ := ∫ u in a..b, M.f0 u

/-- `p̃ = Σ_i h_i v_i + ∫_0^b σ² h̃`, `h̃ = d̃ + W̃²/2` (47.3). -/
noncomputable def ptil (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, h a b (M.T i) * M.v i + ∫ s in (0:ℝ)..b, M.g s * (dtil φ a b s + Wt φ a b s ^ 2 / 2)

def futuresStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (H : ℝ), ShapeGaussLaw M φ Q H →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
    ∫ ω, Real.exp (∫ u in a..b, rate M φ u ω) ∂Q = Real.exp (Aint M a b + ptil M φ a b)

def statement : Prop := futuresStatement

end Standalone.MaturityShapeGauss

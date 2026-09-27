import Standalone.DiffusionMeetingPricing
import Standalone.D3EventVariances

/-! # Claim 046 (a): consistency and the true martingale, conditional on `GaussLaw`

In the model of `Standalone.DiffusionMeetingGauss`, **under the hypothesis `GaussLaw` (not derived
in Lean)**, with the coefficients (46.2):
* `alpha M t T = σ(t)²(T − t)` and `sigma M t T = σ(t) = √(σ²(t))` for `T ≥ t`, both `0` for
  `T < t`; `xi M n u = 1{u ≥ T_n}[Z_n + v_n (u − T_n)]`;
* `consistencyStatement`: the coefficients are Borel in `(t, T)` (deterministic, hence
  progressively measurable for any filtration) and vanish for `T < t`; `ξ_n` is
  `ℬ ⊗ F_{T_n}`-measurable and vanishes before `T_n`; Assumption 2.1 holds at every `t ≤ T`:
  `∫_t^T α(t, u) du = ½ (∫_t^T σ(t, u) du)²`; Assumption 2.2 holds:
  `E[exp(−∫_{T_n}^T ξ_n) | F_{T_n−}] = 1` with `F_{t−} = ⨆_{s < t} F_s`; and the curve (46.1)
  is (2.2): `f(t, T) = f(0, T) + ∫_0^t α(s, T) ds + ∫_0^t σ(s, T) dW_s + Σ_{T_n ≤ t} ξ_n(T)`,
  almost surely, where `∫_0^t σ(s, T) dW_s = I 1_{[0, t]}` since `σ(s, T) = σ(s)` for
  `s ≤ t ≤ T` (`I f` is `∫ f σ dW`);
* `martingaleStatement`: for `0 ≤ T ≤ H`, `P(t, T)/B_t = exp(−∫_0^t r − ∫_t^T f(t, u) du)`,
  `0 ≤ t ≤ T`, is an integrable `Q`-martingale, and almost surely
  `P(t, T)/B_t = P(0, T) · exp(−∫_0^t σ(s)(T − s) dW_s − ½ ∫_0^t σ(s)²(T − s)² ds) · Π^{011}_t(T)`,
  with `Π^{011}_t(T)` Claim 011's `discounted` evaluated at the jumps `Z` (its dates
  `τ (n + 1) = T_n`, variances `v`; zero initial curve, no diffusion).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.DiffusionMeetingConsistency
open Standalone.DiffusionMeetingGauss Standalone.DiffusionMeetingPricing

variable {Ω : Type*} {N : ℕ}

/-- The drift `α(t, T) = σ(t)²(T − t)` for `T ≥ t`, and `0` for `T < t` (46.2). -/
noncomputable def alpha (M : DiffModel Ω N) (t T : ℝ) : ℝ := if t ≤ T then M.g t * (T - t) else 0

/-- The volatility `σ(t, T) = σ(t)` for `T ≥ t`, and `0` for `T < t` (46.2). -/
noncomputable def sigma (M : DiffModel Ω N) (t T : ℝ) : ℝ := if t ≤ T then Real.sqrt (M.g t) else 0

/-- The curve jump `ξ_n(u) = 1{u ≥ T_n}[Z_n + v_n (u − T_n)]` (46.2). -/
noncomputable def xi (M : DiffModel Ω N) (n : Fin N) (u : ℝ) (ω : Ω) : ℝ :=
  if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n) else 0

/-- The forward curve (46.1). -/
noncomputable def fwd (M : DiffModel Ω N) (t T : ℝ) (ω : Ω) : ℝ :=
  M.f0 T + ∑ n, (if M.T n ≤ t then M.Z n ω + M.v n * (T - M.T n) else 0) + M.Y t ω +
    ∫ s in (0:ℝ)..t, M.g s * (T - s)

/-- The discounted bond `P(t, T)/B_t = exp(−∫_0^t r − ∫_t^T f(t, u) du)`. -/
noncomputable def discBond (M : DiffModel Ω N) (t T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(∫ u in (0:ℝ)..t, rate M u ω) - ∫ u in t..T, fwd M t u ω)

set_option warn.classDefReducibility false in
/-- `F_{t−} = ⨆_{s < t} F_s`. -/
def leftLim (M : DiffModel Ω N) (t : ℝ) : MeasurableSpace Ω := ⨆ s < t, M.F s

/-- `exp(−∫_0^t σ(s)(T − s) dW_s − ½ ∫_0^t σ(s)²(T − s)² ds)`. -/
noncomputable def Dfac (M : DiffModel Ω N) (t T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-M.I ((Set.Icc 0 t).indicator fun s => T - s) ω -
    (1 / 2) * ∫ s in (0:ℝ)..t, M.g s * (T - s) ^ 2)

/-- Claim 011's dates: `τ 0 = 0`, `τ (n + 1) = T_n`. -/
noncomputable def tau (M : DiffModel Ω N) (n : ℕ) : ℝ :=
  if h : n ≠ 0 ∧ n - 1 < N then M.T ⟨n - 1, h.2⟩ else 0

/-- Claim 011's variances. -/
noncomputable def vN (M : DiffModel Ω N) (i : Fin N) : NNReal := (M.v i).toNNReal

def consistencyStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
    -- regularity
    Measurable (Function.uncurry (alpha M)) ∧ Measurable (Function.uncurry (sigma M)) ∧
    (∀ t T, T < t → alpha M t T = 0 ∧ sigma M t T = 0) ∧
    (∀ n, Measurable[MeasurableSpace.prod inferInstance (M.F (M.T n))]
      fun p : ℝ × Ω => xi M n p.1 p.2) ∧
    (∀ n u ω, u < M.T n → xi M n u ω = 0) ∧
    -- Assumption 2.1
    (∀ t T, t ≤ T → ∫ u in t..T, alpha M t u = (1 / 2) * (∫ u in t..T, sigma M t u) ^ 2) ∧
    -- Assumption 2.2
    (∀ n T, M.T n ≤ T →
      Q[fun ω => Real.exp (-∫ u in M.T n..T, xi M n u ω) | leftLim M (M.T n)] =ᵐ[Q] 1) ∧
    -- the curve (46.1) is (2.2)
    (∀ t T, 0 ≤ t → t ≤ T → t ≤ H →
      fwd M t T =ᵐ[Q] fun ω => M.f0 T + (∫ s in (0:ℝ)..t, alpha M s T) +
        M.I ((Set.Icc 0 t).indicator 1) ω + ∑ n, (if M.T n ≤ t then xi M n T ω else 0))

def martingaleStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ T, 0 ≤ T → T ≤ H →
    (∀ t, 0 ≤ t → t ≤ T → Integrable (discBond M t T) Q) ∧
    (∀ s t, 0 ≤ s → s ≤ t → t ≤ T → Q[discBond M t T | M.F s] =ᵐ[Q] discBond M s T) ∧
    (∀ t, 0 ≤ t → t ≤ T → discBond M t T =ᵐ[Q] fun ω => P0 M T * Dfac M t T ω *
      Standalone.D3EventVariances.discounted (tau M) (vN M) T t fun i => M.Z i ω)

def statement : Prop := consistencyStatement ∧ martingaleStatement

end Standalone.DiffusionMeetingConsistency

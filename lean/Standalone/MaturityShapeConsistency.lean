import Standalone.MaturityShapePricing
import Standalone.D3EventVariances

/-! # Claim 047 (a): consistency and the true martingale with a shape, conditional on `ShapeGaussLaw`

In the model of `MaturityShapeGauss`, **under the hypothesis `ShapeGaussLaw` (not derived in Lean)**,
with the coefficients `α(t, T) = σ(t)² φ(t, T) Φ(t, T)` and `σ(t, T) = σ(t) φ(t, T)` for `T ≥ t`
(both `0` for `T < t`), and the parallel jumps `ξ_n(u) = 1{u ≥ T_n}[Z_n + v_n (u − T_n)]`:
* `consistencyStatement`: the coefficients are Borel in `(t, T)` (deterministic, hence
  progressively measurable for any filtration) and vanish for `T < t`; `ξ_n` is
  `ℬ ⊗ F_{T_n}`-measurable and vanishes before `T_n`; Assumption 2.1 holds at every `t ≤ T`;
  Assumption 2.2 holds, `E[exp(−∫_{T_n}^T ξ_n) | F_{T_n−}] = 1`; and the curve (47.1) is (2.2),
  almost surely, with `∫_0^t σ(s, T) dW_s = I(1_{[0,t]} φ(·, T))`.
* `martingaleStatement`: for `0 ≤ T ≤ H`, `P(t, T)/B_t`, `0 ≤ t ≤ T`, is an integrable martingale,
  and almost surely `P(t, T)/B_t = P(0, T) · exp(−∫_0^t σ(s) Φ(s, T) dW_s −
  ½ ∫_0^t σ(s)² Φ(s, T)² ds) · Π^{011}_t(T)`, with `Π^{011}` Claim 011's `discounted` at the jumps.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.MaturityShapeConsistency
open Standalone.MaturityShapeIdentities Standalone.MaturityShapeGauss Standalone.MaturityShapePricing

variable {Ω : Type*} {N : ℕ}

/-- The drift `α(t, T) = σ(t)² φ(t, T) Φ(t, T)` for `T ≥ t`, and `0` for `T < t`. -/
noncomputable def alpha (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (t T : ℝ) : ℝ :=
  if t ≤ T then M.g t * φ t T * Phi φ t T else 0

/-- The volatility `σ(t, T) = σ(t) φ(t, T)` for `T ≥ t`, and `0` for `T < t`. -/
noncomputable def sigma (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (t T : ℝ) : ℝ :=
  if t ≤ T then Real.sqrt (M.g t) * φ t T else 0

/-- The curve jump `ξ_n(u) = 1{u ≥ T_n}[Z_n + v_n (u − T_n)]`. -/
noncomputable def xi (M : ShapeModel Ω N) (n : Fin N) (u : ℝ) (ω : Ω) : ℝ :=
  if M.T n ≤ u then M.Z n ω + M.v n * (u - M.T n) else 0

/-- The discounted bond `P(t, T)/B_t = exp(−∫_0^t r − ∫_t^T f(t, u) du)`. -/
noncomputable def discBond (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(∫ u in (0:ℝ)..t, rate M φ u ω) - ∫ u in t..T, fwd M φ t u ω)

set_option warn.classDefReducibility false in
/-- `F_{t−} = ⨆_{s < t} F_s`. -/
def leftLim (M : ShapeModel Ω N) (t : ℝ) : MeasurableSpace Ω := ⨆ s < t, M.F s

/-- `exp(−∫_0^t σ(s) Φ(s, T) dW_s − ½ ∫_0^t σ(s)² Φ(s, T)² ds)`. -/
noncomputable def Dfac (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-M.I ((Set.Icc 0 t).indicator fun s => Phi φ s T) ω -
    (1 / 2) * ∫ s in (0:ℝ)..t, M.g s * Phi φ s T ^ 2)

/-- Claim 011's dates: `τ 0 = 0`, `τ (n + 1) = T_n`. -/
noncomputable def tau (M : ShapeModel Ω N) (n : ℕ) : ℝ :=
  if h : n ≠ 0 ∧ n - 1 < N then M.T ⟨n - 1, h.2⟩ else 0

/-- Claim 011's variances. -/
noncomputable def vN (M : ShapeModel Ω N) (i : Fin N) : NNReal := (M.v i).toNNReal

def consistencyStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (H : ℝ), ShapeGaussLaw M φ Q H →
    -- regularity
    Measurable (Function.uncurry (alpha M φ)) ∧ Measurable (Function.uncurry (sigma M φ)) ∧
    (∀ t T, T < t → alpha M φ t T = 0 ∧ sigma M φ t T = 0) ∧
    (∀ n, Measurable[MeasurableSpace.prod inferInstance (M.F (M.T n))]
      fun p : ℝ × Ω => xi M n p.1 p.2) ∧
    (∀ n u ω, u < M.T n → xi M n u ω = 0) ∧
    -- Assumption 2.1
    (∀ t T, t ≤ T → ∫ u in t..T, alpha M φ t u = (1 / 2) * (∫ u in t..T, sigma M φ t u) ^ 2) ∧
    -- Assumption 2.2
    (∀ n T, M.T n ≤ T →
      Q[fun ω => Real.exp (-∫ u in M.T n..T, xi M n u ω) | leftLim M (M.T n)] =ᵐ[Q] 1) ∧
    -- the curve (47.1) is (2.2)
    (∀ t T, 0 ≤ t → t ≤ T → t ≤ H →
      fwd M φ t T =ᵐ[Q] fun ω => M.f0 T + (∫ s in (0:ℝ)..t, alpha M φ s T) +
        M.I ((Set.Icc 0 t).indicator fun s => φ s T) ω +
          ∑ n, (if M.T n ≤ t then xi M n T ω else 0))

def martingaleStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (H : ℝ), ShapeGaussLaw M φ Q H →
  ∀ T, 0 ≤ T → T ≤ H →
    (∀ t, 0 ≤ t → t ≤ T → Integrable (discBond M φ t T) Q) ∧
    (∀ s t, 0 ≤ s → s ≤ t → t ≤ T → Q[discBond M φ t T | M.F s] =ᵐ[Q] discBond M φ s T) ∧
    (∀ t, 0 ≤ t → t ≤ T → discBond M φ t T =ᵐ[Q] fun ω => P0 M T * Dfac M φ t T ω *
      Standalone.D3EventVariances.discounted (tau M) (vN M) T t fun i => M.Z i ω)

def statement : Prop := consistencyStatement ∧ martingaleStatement

end Standalone.MaturityShapeConsistency

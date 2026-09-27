import Standalone.RecurrentApproxEstimates
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-! # Claim 048 (b), the deterministic and Gaussian ingredients of the bond-price estimate

Fix `0 ≤ t ≤ T ≤ H`. For the log-price `X = ∫_t^T (V(t, u) − f_0(u)) du = μ + ∫_0^t U dW`, the
proof of (b) uses two deterministic functions of the model, and one fact about Gaussian laws.
* `U048 … t T s = U(s) = ∫_t^T σ(s, u) du`, the integrand of `X`;
* `mu048 … t T = μ = ∫_t^T ∫_0^t α(s, u) ds du`, the mean of `X`.

`boundStatement`, the deterministic bounds of (b), under the hypotheses of (a):
* `|U| ≤ ĀΛ(T − t)` and `|U − Ũ| ≤ εΛ(T − t)` on `[0, t]`;
* `∫_0^t U² ≤ Ā²Λ²H³` and `|μ| ≤ ½Ā²Λ²H³`, and the same for `ã`;
* `|μ − μ̃| ≤ ½εĀΛ²H³` and `∫_0^t (U − Ũ)² ≤ ε²Λ²H³`, so
  `(μ − μ̃)² + ∫_0^t (U − Ũ)² ≤ ε²(Λ²H³ + ¼Ā²Λ⁴H⁶)`, the right side of (48.6).

`fourthMomentStatement`: `∫ x⁴ dN(m, v) = m⁴ + 6m²v + 3v²` (so `E D⁴ ≤ 3(E D²)²`).

`priceStatement`, the passage from log-prices to prices: if `X`, `X̃` and `X − X̃` are Gaussian,
with `|E X|, |E X̃| ≤ B/2` and `Var X, Var X̃ ≤ B`, then
`E|e^{−X} − e^{−X̃}|² ≤ 2√3 e^{5B} E(X − X̃)²`. This is the step from (48.6) to (48.7), with
`B = Ā²Λ²H³`: by the mean value theorem, Cauchy–Schwarz, the fourth moment and
`E e^{−4X} = e^{−4E X + 8 Var X}`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Standalone.RecurrentApproxPriceBounds
open Standalone.RecurrentApproxEstimates

/-- `U(s) = ∫_t^T σ(s, u) du`. -/
noncomputable def U048 (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (t T s : ℝ) : ℝ :=
  ∫ u in t..T, sig048 Tm a lam s u

/-- `μ = ∫_t^T ∫_0^t α(s, u) ds du`. -/
noncomputable def mu048 (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (t T : ℝ) : ℝ :=
  ∫ u in t..T, ∫ s in (0:ℝ)..t, alpha048 Tm a lam s u

def boundStatement : Prop := ∀ (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam : ℝ → ℝ) (H Λ ε Abar : ℝ),
  Hyp048 Tm a a' lam H Λ ε Abar → ∀ t T, 0 ≤ t → t ≤ T → T ≤ H →
    (∀ s ∈ Set.Icc 0 t, |U048 Tm a lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a' lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a lam t T s - U048 Tm a' lam t T s| ≤ ε * Λ * (T - t)) ∧
    ∫ s in (0:ℝ)..t, U048 Tm a lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 ∧
    ∫ s in (0:ℝ)..t, U048 Tm a' lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 ∧
    |mu048 Tm a lam t T| ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 / 2 ∧
    |mu048 Tm a' lam t T| ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 / 2 ∧
    |mu048 Tm a lam t T - mu048 Tm a' lam t T| ≤ ε * Abar * Λ ^ 2 * H ^ 3 / 2 ∧
    ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2 ≤ ε ^ 2 * Λ ^ 2 * H ^ 3 ∧
    (mu048 Tm a lam t T - mu048 Tm a' lam t T) ^ 2 +
        ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2 ≤
      ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4)

def fourthMomentStatement : Prop := ∀ (m : ℝ) (v : ℝ≥0),
  ∫ x, x ^ 4 ∂gaussianReal m v = m ^ 4 + 6 * m ^ 2 * v + 3 * v ^ 2

def priceStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (X X' : Ω → ℝ), Measurable X → Measurable X' →
  ∀ (μ μ' m B : ℝ) (v v' w : ℝ≥0), HasLaw X (gaussianReal μ v) P →
    HasLaw X' (gaussianReal μ' v') P → HasLaw (fun ω => X ω - X' ω) (gaussianReal m w) P →
    |μ| ≤ B / 2 → |μ'| ≤ B / 2 → (v:ℝ) ≤ B → (v':ℝ) ≤ B →
    ∫ ω, (Real.exp (-X ω) - Real.exp (-X' ω)) ^ 2 ∂P ≤
      2 * Real.sqrt 3 * Real.exp (5 * B) * (m ^ 2 + w)

def statement : Prop := boundStatement ∧ fourthMomentStatement ∧ priceStatement

end Standalone.RecurrentApproxPriceBounds

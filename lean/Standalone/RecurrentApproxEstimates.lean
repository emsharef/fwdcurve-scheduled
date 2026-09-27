import Standalone.RecurrentLoadingAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 048 (a): the deterministic volatility and drift estimates

A schedule `Tm` (a finite set of meeting dates), a shape `λ` and loadings `a`. As in Claim 030,
`count030 Tm s T` is the number of meetings in `(s, T]`. The volatility (48.1) is
`σ(s, T) = a_{i(s,T)} λ(T − s)`, with `S(s, T) = ∫_s^T σ(s, u) du` and the differentiated HJM drift
`α(s, T) = σ(s, T) S(s, T)`. The approximating model uses loadings `ã`.

The hypotheses are those of (a). `λ` is Borel with `|λ| ≤ Λ` on `[0, H]`. The loading error `ε`
and the loading bound `Ā` hold at the indices `0, …, |Tm|` that occur, `|a_i − ã_i| ≤ ε` and
`|a_i|, |ã_i| ≤ Ā`. These are the deterministic half of (a), kept apart from the probabilistic
comparison:
* `volStatement`, (48.3): `|σ − σ̃| ≤ εΛ` and `|α − α̃| ≤ 2εĀΛ²(T − s)` for `0 ≤ s ≤ T ≤ H`.
* `meanStatement`: the deterministic part of (48.4) and (48.5) for `0 ≤ t ≤ T ≤ H`. It bounds
  `m(t, T) = ∫_0^t (α − α̃)(s, T) ds` by `|m| ≤ 2εĀΛ²(tT − t²/2)`, and `∫_0^t (σ − σ̃)(s, T)² ds`
  by `ε²Λ² t`. Hence
  `m² + ∫_0^t (σ − σ̃)² ≤ ε²[Λ² t + 4Ā²Λ⁴(tT − t²/2)²] ≤ ε²(Λ² H + Ā²Λ⁴ H⁴)`.
  The constant involves only `Λ`, `Ā` and `H`; the schedule enters only through `ε` and `Ā`.
* `sharpStatement`, sharpness: for `a ≡ Ā`, `ã ≡ Ā − ε` and `λ ≡ Λ` on `[0, H]`,
  `σ − σ̃ = εΛ` and `m(t, T) = (2Ā − ε)εΛ²(tT − t²/2)`.
-/

open MeasureTheory

namespace Standalone.RecurrentApproxEstimates
open Standalone.RecurrentLoadingAlgebra

/-- `σ(s, T) = a_{i(s,T)} λ(T − s)` (48.1). -/
noncomputable def sig048 (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (s T : ℝ) : ℝ :=
  a (count030 Tm s T) * lam (T - s)

/-- `S(s, T) = ∫_s^T σ(s, u) du`. -/
noncomputable def S048 (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (s T : ℝ) : ℝ :=
  ∫ u in s..T, sig048 Tm a lam s u

/-- `α(s, T) = σ(s, T) S(s, T)`, the differentiated HJM drift. -/
noncomputable def alpha048 (Tm : Finset ℝ) (a : ℕ → ℝ) (lam : ℝ → ℝ) (s T : ℝ) : ℝ :=
  sig048 Tm a lam s T * S048 Tm a lam s T

/-- `m(t, T) = ∫_0^t (α − α̃)(s, T) ds`. -/
noncomputable def m048 (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam : ℝ → ℝ) (t T : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, (alpha048 Tm a lam s T - alpha048 Tm a' lam s T)

/-- The hypotheses of (a): a Borel shape bounded by `Λ` on `[0, H]`, and the loading error and
bound at the indices that occur. -/
def Hyp048 (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam : ℝ → ℝ) (H Λ ε Abar : ℝ) : Prop :=
  Measurable lam ∧ (∀ x ∈ Set.Icc 0 H, |lam x| ≤ Λ) ∧
  ∀ i ≤ Tm.card, |a i - a' i| ≤ ε ∧ |a i| ≤ Abar ∧ |a' i| ≤ Abar

def volStatement : Prop := ∀ (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam : ℝ → ℝ) (H Λ ε Abar : ℝ),
  Hyp048 Tm a a' lam H Λ ε Abar → ∀ s T, 0 ≤ s → s ≤ T → T ≤ H →
    |sig048 Tm a lam s T - sig048 Tm a' lam s T| ≤ ε * Λ ∧
    |alpha048 Tm a lam s T - alpha048 Tm a' lam s T| ≤ 2 * ε * Abar * Λ ^ 2 * (T - s)

def meanStatement : Prop := ∀ (Tm : Finset ℝ) (a a' : ℕ → ℝ) (lam : ℝ → ℝ) (H Λ ε Abar : ℝ),
  Hyp048 Tm a a' lam H Λ ε Abar → ∀ t T, 0 ≤ t → t ≤ T → T ≤ H →
    |m048 Tm a a' lam t T| ≤ 2 * ε * Abar * Λ ^ 2 * (t * T - t ^ 2 / 2) ∧
    ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 ≤ ε ^ 2 * Λ ^ 2 * t ∧
    m048 Tm a a' lam t T ^ 2 + ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 ≤
      ε ^ 2 * (Λ ^ 2 * t + 4 * Abar ^ 2 * Λ ^ 4 * (t * T - t ^ 2 / 2) ^ 2) ∧
    ε ^ 2 * (Λ ^ 2 * t + 4 * Abar ^ 2 * Λ ^ 4 * (t * T - t ^ 2 / 2) ^ 2) ≤
      ε ^ 2 * (Λ ^ 2 * H + Abar ^ 2 * Λ ^ 4 * H ^ 4)

def sharpStatement : Prop := ∀ (Tm : Finset ℝ) (lam : ℝ → ℝ) (H Λ ε Abar : ℝ),
  (∀ x ∈ Set.Icc 0 H, lam x = Λ) → ∀ t T, 0 ≤ t → t ≤ T → T ≤ H →
    (∀ s ∈ Set.Icc 0 T, sig048 Tm (fun _ => Abar) lam s T - sig048 Tm (fun _ => Abar - ε) lam s T =
      ε * Λ) ∧
    m048 Tm (fun _ => Abar) (fun _ => Abar - ε) lam t T =
      (2 * Abar - ε) * ε * Λ ^ 2 * (t * T - t ^ 2 / 2)

def statement : Prop := volStatement ∧ meanStatement ∧ sharpStatement

end Standalone.RecurrentApproxEstimates

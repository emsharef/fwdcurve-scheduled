import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Claim 033 (a): the cross term

Meetings are a finite set `Tm` of dates; `idx033 Tm v` is the number of meetings at or before `v`,
so `v` lies in the maturity interval `I_j` exactly when `idx033 Tm v = j`. The step volatility is
`σ^S(u, v) = s_j(u)` for `v` in `I_j` (`sigS033`), with bounded Borel `s_j`, and
`S^S(u, T) = ∫_u^T σ^S(u, v) dv` (`SS033`). The block volatility is `σ^B(u, v) = b e^{−a(v−u)}`, with
`S^B(u, T) = b (1 − e^{−a(T−u)}) / a`. The cross part of the drift (33.1) is
`ρ [σ^S S^B + σ^B S^S]` (`cross033`).

`crossStatement` is (33.2) for the cross term. For `t ≥ 0` and each interval `I_j`, there are
constants `c_0` and `α` such that for every `T` in `I_j` with `T ≥ t`,
`∫_0^t ρ [σ^S S^B + σ^B S^S](u, T) du = c_0 + e^{−aT} (α + β_j(t) T)`, with
`β_j(t) = ρ b ∫_0^t e^{au} s_j(u) du` (`beta033`). The jumps of the coefficients across a meeting
`T_m` are then, for `β`, `β_m − β_{m−1} = ρ b ∫_0^t e^{au} Δ_m(u) du` with `Δ_m = s_m − s_{m−1}`
(`jumpStatement`).
-/

open MeasureTheory
namespace Standalone.SpliceCrossTermDrift

/-- The number of meetings at or before `v`: `v ∈ I_j` iff this is `j`. -/
noncomputable def idx033 (Tm : Finset ℝ) (v : ℝ) : ℕ := (Tm.filter fun τ => τ ≤ v).card

/-- The step volatility `σ^S(u, v) = s_j(u)` for `v ∈ I_j`. -/
noncomputable def sigS033 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (u v : ℝ) : ℝ := s (idx033 Tm v) u

/-- `S^S(u, T) = ∫_u^T σ^S(u, v) dv`. -/
noncomputable def SS033 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  ∫ v in u..T, sigS033 s Tm u v

/-- The cross part `ρ [σ^S S^B + σ^B S^S]` of the drift (33.1). -/
noncomputable def cross033 (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  ρ * (sigS033 s Tm u T * (b * (1 - Real.exp (-a * (T - u))) / a) +
    b * Real.exp (-a * (T - u)) * SS033 s Tm u T)

/-- `β_j(t) = ρ b ∫_0^t e^{au} s_j(u) du`. -/
noncomputable def beta033 (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ρ * b * ∫ u in (0:ℝ)..t, Real.exp (a * u) * s j u

def crossStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ), a ≠ 0 → ∀ (j : ℕ) (t : ℝ), 0 ≤ t →
  ∃ c₀ α : ℝ, ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T =
      c₀ + Real.exp (-a * T) * (α + beta033 a b ρ s j t * T)

def jumpStatement : Prop := ∀ (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ) (m : ℕ) (t : ℝ),
  beta033 a b ρ s (m + 1) t - beta033 a b ρ s m t =
    ρ * b * ∫ u in (0:ℝ)..t, Real.exp (a * u) * (s (m + 1) u - s m u)

def statement : Prop := crossStatement ∧ jumpStatement

end Standalone.SpliceCrossTermDrift

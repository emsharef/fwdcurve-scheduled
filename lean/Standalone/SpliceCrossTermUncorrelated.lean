import Standalone.SpliceCrossTermDrift

/-! # Claim 033 (c)(i): without a correlated jump the cross term is one function

The setting is `SpliceCrossTermDrift`'s. `uncorrelatedStatement` is the deterministic core of
(c)(i). Fix `t ≥ 0`, and suppose either `ρ = 0`, or for almost every `u ∈ [0, t]` the step
volatility `s_{j}(u)` is the same on every maturity interval `I_j` that meets `[t, ∞)`. When
`ρ ≠ 0`, `ρ Δ_m = 0` almost everywhere on `[0, T_m)` for every `m` gives this: every `Δ_m` with
`T_m > t` vanishes at almost every `u ≤ t`. Then the cross term is one function
`c₀ + e^{−aT}(α + β T)` for every `T ≥ t`, across all later meetings, so it lies in
`span{e^{−aT}, T e^{−aT}} + ℝ`, which is `span{e^{−a(T−t)}, (T−t) e^{−a(T−t)}} + ℝ`, inside
`S⁺ + E_0(· − t)`. By `crossStatement`, for every `ρ` the cross term is `c₀ + e^{−aT}(α_j + β_j T)`
on each maturity interval, which lies in the indicator span of (c)(ii).
-/

open MeasureTheory Set
namespace Standalone.SpliceCrossTermUncorrelated
open Standalone.SpliceCrossTermDrift

def uncorrelatedStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ), a ≠ 0 → ∀ t : ℝ, 0 ≤ t →
  (ρ = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 t → ∀ v, t ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u) →
  ∃ c₀ α β : ℝ, ∀ T : ℝ, t ≤ T →
    ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T = c₀ + Real.exp (-a * T) * (α + β * T)

def statement : Prop := uncorrelatedStatement

end Standalone.SpliceCrossTermUncorrelated

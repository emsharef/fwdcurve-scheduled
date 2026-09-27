import Standalone.SpliceCrossTermDrift
import Standalone.SpliceCrossTermAnalytic

/-! # Claim 033 (b): necessity, pathwise

The setting is `SpliceCrossTermDrift`'s. `τ = T_m` is a meeting before the horizon `H`, with
the step index `m − 1` just before it and `m` from it on: there are `τl < τ < τr` with
`idx033 Tm v = m − 1` on `(τl, τ)` and `idx033 Tm v = m` on `[τ, τr)`.

`necessityStatement` is (b) for the cross term. Suppose that for every `t ∈ [0, τ)`, on `(t, H)`,
the cross term `X_t(T) = ∫_0^t ρ[σ^S S^B + σ^B S^S](u, T) du` is `p(T) + g(T − t)` with `g`
real-analytic on `ℝ` (an element of a block) and `p` affine on each maturity interval (an
element of `S⁺`). Then `ρ Δ_m(u) = 0` for almost every `u ∈ [0, τ)`, `Δ_m = s_m − s_{m−1}`, provided
`a ≠ 0` and `b ≠ 0`. That the cross term has this form when the curve is consistent is the
remaining step of (b), since the curve's other parts lie in `S⁺ + E(· − t)`.
-/

open MeasureTheory Set
namespace Standalone.SpliceCrossTermNecessity
open Standalone.SpliceCrossTermDrift

def necessityStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ), a ≠ 0 → b ≠ 0 →
  ∀ (m : ℕ) (τ τl τr H : ℝ), 0 ≤ τ → τl < τ → τ < τr → τ < H →
  (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) →
  (∀ t ∈ Ico 0 τ, ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
    (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T = p T + g (T - t)) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * (s (m + 1) u - s m u) = 0

def statement : Prop := necessityStatement

end Standalone.SpliceCrossTermNecessity

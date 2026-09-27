import Standalone.SpliceCrossTermNecessity

/-! # Claim 033 (d): no third way, pathwise

The setting is `SpliceCrossTermNecessity`'s. `openStatement` is (d) for the cross term: if
`ρ Δ_m` is not almost everywhere zero on `[0, τ)`, `τ = T_m`, with `a ≠ 0` and `b ≠ 0`, then there
is a nonempty open set of times `t ∈ (0, τ)` at which the cross term `X_t` on `(t, H)` is not of the
form `p + g(· − t)` with `g` real-analytic and `p` affine on each maturity interval. At such `t`
the coefficient `β` of `T e^{−aT}` jumps across `T_m`, and the analytic matching step forbids it.
-/

open MeasureTheory Set
namespace Standalone.SpliceCrossTermOpen
open Standalone.SpliceCrossTermDrift

def openStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ), a ≠ 0 → b ≠ 0 →
  ∀ (m : ℕ) (τ τl τr H : ℝ), τl < τ → τ < τr → τ < H →
  (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) →
  ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * (s (m + 1) u - s m u) = 0) →
  ∃ O : Set ℝ, IsOpen O ∧ O.Nonempty ∧ O ⊆ Ioo 0 τ ∧ ∀ t ∈ O,
    ¬ ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
      (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
      ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T = p T + g (T - t)

def statement : Prop := openStatement

end Standalone.SpliceCrossTermOpen

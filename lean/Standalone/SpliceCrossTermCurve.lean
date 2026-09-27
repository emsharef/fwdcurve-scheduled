import Standalone.SpliceCrossTermDrift
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 033 (a): the other parts of the curve

The setting is `SpliceCrossTermDrift`'s. With the independent drivers written out, the AX-01
drift (33.1) is `σ^S S^S + σ^B S^B + ρ (σ^S S^B + σ^B S^S)`, and the random part of `f(t, T)` is
`I_1(σ_1(·, T))(t) + I_2(σ_2(·, T))(t)`, with `σ_1 = σ^S + ρ σ^B` and `σ_2 = √(1 − ρ²) σ^B`.

* `stepStatement`: `∫_0^t σ^S S^S(u, T) du` is affine in `T` on each maturity interval
  `I_j ∩ [t, ∞)`, so it lies in `S⁺`.
* `blockStatement`: `∫_0^t σ^B S^B(u, T) du = γ_1 e^{−aT} + γ_2 e^{−2aT}` for all `T`.
* `randomStatement`: for every `T` and `t`, almost surely,
  `I_1(σ_1(·, T))(t) + I_2(σ_2(·, T))(t) = I_1(s_j)(t) + e^{−aT} (ρ b I_1(e^{a·})(t) + √(1 − ρ²) b I_2(e^{a·})(t))`
  with `j` the maturity interval of `T`. The right side is built from finitely many random
  variables, one per interval plus two, the same for every `T`. It is a version of the random part
  in `S⁺ + span{e^{−aT}}`, simultaneously in `T` on every path, as for Claims 030 and 031.
-/

open MeasureTheory
open scoped NNReal
namespace Standalone.SpliceCrossTermCurve
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift

def stepStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (j : ℕ) (t : ℝ), 0 ≤ t →
  ∃ c₀ c₁ : ℝ, ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, sigS033 s Tm u T * SS033 s Tm u T = c₀ + c₁ * T

def blockStatement : Prop := ∀ (a b t : ℝ), a ≠ 0 → ∃ γ₁ γ₂ : ℝ, ∀ T : ℝ,
  ∫ u in (0:ℝ)..t, b * Real.exp (-a * (T - u)) * (b * (1 - Real.exp (-a * (T - u))) / a) =
    γ₁ * Real.exp (-a * T) + γ₂ * Real.exp (-2 * a * T)

def randomStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ T : ℝ) (t : ℝ≥0), ∀ᵐ ω ∂S.μ,
    S.I k₁ (fun u _ => sigS033 s Tm u T + ρ * (b * Real.exp (-a * (T - u)))) t ω +
      S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * (b * Real.exp (-a * (T - u)))) t ω =
    S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω + Real.exp (-a * T) *
      (ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
        Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω)

def statement : Prop := stepStatement ∧ blockStatement ∧ randomStatement

end Standalone.SpliceCrossTermCurve

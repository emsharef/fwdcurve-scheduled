import Standalone.SpliceCrossTermDrift

/-! # Claim 033 (a): the coefficient `α_m(t)` and its jump

The setting is `SpliceCrossTermDrift`'s. On the maturity interval `I_j`,
`S^S(u, T) = s_j(u) T + κ_j(u)` for `u ≤ T`. `kappa033 s Tm j T₀ u` is `κ_j(u)`, read off at an
anchor `T₀ ∈ I_j`; `alphaCoef033` is `α_j(t) = ρ b ∫_0^t e^{au} (κ_j(u) − s_j(u)/a) du`.

* `kappaStatement`: `κ_j(u)` does not depend on the anchor `T₀ ∈ I_j` with `u ≤ T₀`.
* `explicitStatement`: (33.2) for the cross term with its coefficients. For `T ∈ I_j`, `T ≥ t`,
  `∫_0^t ρ[σ^S S^B + σ^B S^S](u, T) du = c₀ + e^{−aT} (α_j(t) + β_j(t) T)`.
* `alphaJumpStatement`: at a meeting `τ` that ends `I_m` and begins `I_{m+1}`, for `t < τ`,
  `α_{m+1}(t) − α_m(t) = −ρ b ∫_0^t e^{au} (τ + 1/a) Δ(u) du`, `Δ = s_{m+1} − s_m`.
  The jump of `β` is `SpliceCrossTermDrift.jumpStatement`.
-/

open MeasureTheory Set
namespace Standalone.SpliceCrossTermAlpha
open Standalone.SpliceCrossTermDrift

/-- `κ_j(u) = S^S(u, T₀) − s_j(u) T₀` for an anchor `T₀ ∈ I_j`. -/
noncomputable def kappa033 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (j : ℕ) (T0 u : ℝ) : ℝ :=
  SS033 s Tm u T0 - s j u * T0

/-- `α_j(t) = ρ b ∫_0^t e^{au} (κ_j(u) − s_j(u)/a) du`. -/
noncomputable def alphaCoef033 (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (j : ℕ)
    (T0 t : ℝ) : ℝ :=
  ρ * b * ∫ u in (0:ℝ)..t, Real.exp (a * u) * (kappa033 s Tm j T0 u - s j u / a)

def kappaStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (j : ℕ) (T0 T1 u : ℝ), idx033 Tm T0 = j →
  idx033 Tm T1 = j → u ≤ T0 → u ≤ T1 → kappa033 s Tm j T0 u = kappa033 s Tm j T1 u

def explicitStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ), a ≠ 0 → ∀ (j : ℕ) (t T0 : ℝ), 0 ≤ t →
  idx033 Tm T0 = j → t ≤ T0 → ∃ c₀ : ℝ, ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T =
      c₀ + Real.exp (-a * T) * (alphaCoef033 a b ρ s Tm j T0 t + beta033 a b ρ s j t * T)

def alphaJumpStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ : ℝ) (m : ℕ) (τ τl τr T0 T1 t : ℝ),
  τl < τ → τ < τr → (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) →
  T0 ∈ Ioo τl τ → T1 ∈ Ico τ τr → 0 ≤ t → t ≤ T0 →
  alphaCoef033 a b ρ s Tm (m + 1) T1 t - alphaCoef033 a b ρ s Tm m T0 t =
    -(ρ * b * ∫ u in (0:ℝ)..t, Real.exp (a * u) * (τ + 1 / a) * (s (m + 1) u - s m u))

def statement : Prop := kappaStatement ∧ explicitStatement ∧ alphaJumpStatement

end Standalone.SpliceCrossTermAlpha

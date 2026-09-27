import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Claim 033 (b), (d): the deterministic core

`affineStatement`: for `a ≠ 0`, if `e^{−aT}(α + βT)` agrees with an affine function on an open
interval, then `α = β = 0`; the functions `1, T, e^{−aT}, T e^{−aT}` are linearly independent on
every interval.

`matchStatement` is the matching step of (b). Let `g` be real-analytic on `ℝ` (an element of a
block, shifted). If on one open interval `g = e^{−aT}(α₁ + β₁T) + p₁` and on another
`g = e^{−aT}(α₂ + β₂T) + p₂`, with `p₁`, `p₂` affine, then `α₁ = α₂` and `β₁ = β₂`. The first
identity extends from its interval to all of `ℝ` by analyticity.

`lebesgueStatement` is the last step of (b): if `∫_0^t e^{au} Δ(u) du = 0` for every
`t ∈ [0, L)`, with `Δ` locally integrable, then `Δ = 0` almost everywhere on `[0, L)`.
`openStatement` is (d)'s: otherwise the times `t ∈ (0, L)` with `∫_0^t e^{au} Δ(u) du ≠ 0`
form a nonempty open set.
-/

open MeasureTheory Set
namespace Standalone.SpliceCrossTermAnalytic

def affineStatement : Prop := ∀ (a : ℝ), a ≠ 0 → ∀ (c d : ℝ), c < d →
  ∀ (α β k₀ k₁ : ℝ), (∀ T ∈ Ioo c d, Real.exp (-a * T) * (α + β * T) = k₀ + k₁ * T) →
  α = 0 ∧ β = 0

def matchStatement : Prop := ∀ (a : ℝ), a ≠ 0 → ∀ (g : ℝ → ℝ), AnalyticOnNhd ℝ g univ →
  ∀ (c₁ d₁ c₂ d₂ : ℝ), c₁ < d₁ → c₂ < d₂ →
  ∀ (α₁ β₁ α₂ β₂ k₀ k₁ l₀ l₁ : ℝ),
  (∀ T ∈ Ioo c₁ d₁, g T = Real.exp (-a * T) * (α₁ + β₁ * T) + (k₀ + k₁ * T)) →
  (∀ T ∈ Ioo c₂ d₂, g T = Real.exp (-a * T) * (α₂ + β₂ * T) + (l₀ + l₁ * T)) →
  α₁ = α₂ ∧ β₁ = β₂

def lebesgueStatement : Prop := ∀ (a L : ℝ) (Δ : ℝ → ℝ), LocallyIntegrable Δ volume →
  (∀ t ∈ Ico 0 L, ∫ u in (0:ℝ)..t, Real.exp (a * u) * Δ u = 0) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 L → Δ u = 0

def openStatement : Prop := ∀ (a L : ℝ) (Δ : ℝ → ℝ), LocallyIntegrable Δ volume →
  ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 L → Δ u = 0) →
  IsOpen {t ∈ Ioo 0 L | ∫ u in (0:ℝ)..t, Real.exp (a * u) * Δ u ≠ 0} ∧
  {t ∈ Ioo 0 L | ∫ u in (0:ℝ)..t, Real.exp (a * u) * Δ u ≠ 0}.Nonempty

def statement : Prop := affineStatement ∧ matchStatement ∧ lebesgueStatement ∧ openStatement

end Standalone.SpliceCrossTermAnalytic

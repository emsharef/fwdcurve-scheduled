import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 047 (a)–(b): the deterministic identities with a shape

For a shape `φ(s, T)`, bounded and Borel, `Phi φ s T = Φ(s, T) = ∫_s^T φ(s, x) dx`; `σ² = g`, bounded
measurable and nonnegative.

* `squareStatement`: for bounded measurable `ψ` and `Ψ(x) = ∫_c^x ψ`,
  `∫_a^b ψ Ψ = (Ψ(b)² − Ψ(a)²)/2` (the proof's `∂_x Φ²/2 = φΦ` a.e., in integrated form).
* `assumption21Statement`, Assumption 2.1 at every `t ≤ T`: `∫_t^T α(t, x) dx = ½(∫_t^T σ(t, x) dx)²`
  with `α(t, x) = σ(t)² φ(t, x) Φ(t, x)` and `σ(t, x) = σ(t) φ(t, x)`.
* `driftStatement`, (b): `∫_a^b ∫_0^u σ(s)² φ(s, u) Φ(s, u) ds du = ∫_0^b σ(s)² d̃(s) ds`, with
  `d̃(s) = (Φ(s, b)² − Φ(s, a∨s)²)/2` of (47.2), for `0 ≤ a ≤ b`.
* `bracketStatement`, (a): `∫_0^t ∫_0^u σ²φΦ(s, u) ds du + ∫_t^T ∫_0^t σ²φΦ(s, x) ds dx
  = ½ ∫_0^t σ(s)² Φ(s, T)² ds` for `0 ≤ t ≤ T`.
-/

namespace Standalone.MaturityShapeIdentities

/-- `Φ(s, T) = ∫_s^T φ(s, x) dx`. -/
noncomputable def Phi (φ : ℝ → ℝ → ℝ) (s T : ℝ) : ℝ := ∫ x in s..T, φ s x

/-- `d̃(s) = (Φ(s, b)² − Φ(s, a∨s)²)/2` (47.2). -/
noncomputable def dtil (φ : ℝ → ℝ → ℝ) (a b s : ℝ) : ℝ :=
  (Phi φ s b ^ 2 - Phi φ s (max a s) ^ 2) / 2

def squareStatement : Prop := ∀ ψ : ℝ → ℝ, Measurable ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
  ∀ c a b : ℝ, ∫ x in a..b, ψ x * ∫ y in c..x, ψ y =
    ((∫ y in c..b, ψ y) ^ 2 - (∫ y in c..a, ψ y) ^ 2) / 2

def assumption21Statement : Prop := ∀ φ : ℝ → ℝ → ℝ, (∀ s, Measurable (φ s)) →
  (∃ C, ∀ s T, |φ s T| ≤ C) → ∀ (g : ℝ → ℝ), (∀ s, 0 ≤ g s) → ∀ t T : ℝ,
    ∫ x in t..T, g t * φ t x * Phi φ t x = (1 / 2) * (∫ x in t..T, Real.sqrt (g t) * φ t x) ^ 2

def driftStatement : Prop := ∀ φ : ℝ → ℝ → ℝ, Measurable (Function.uncurry φ) →
  (∃ C, ∀ s T, |φ s T| ≤ C) → ∀ g : ℝ → ℝ, Measurable g → (∃ B, ∀ s, |g s| ≤ B) →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∫ u in a..b, ∫ s in (0:ℝ)..u, g s * φ s u * Phi φ s u = ∫ s in (0:ℝ)..b, g s * dtil φ a b s

def bracketStatement : Prop := ∀ φ : ℝ → ℝ → ℝ, Measurable (Function.uncurry φ) →
  (∃ C, ∀ s T, |φ s T| ≤ C) → ∀ g : ℝ → ℝ, Measurable g → (∃ B, ∀ s, |g s| ≤ B) →
  ∀ t T : ℝ, 0 ≤ t → t ≤ T →
    (∫ u in (0:ℝ)..t, ∫ s in (0:ℝ)..u, g s * φ s u * Phi φ s u) +
      (∫ x in t..T, ∫ s in (0:ℝ)..t, g s * φ s x * Phi φ s x) =
      ∫ s in (0:ℝ)..t, g s * Phi φ s T ^ 2 / 2

def statement : Prop :=
  squareStatement ∧ assumption21Statement ∧ driftStatement ∧ bracketStatement

end Standalone.MaturityShapeIdentities

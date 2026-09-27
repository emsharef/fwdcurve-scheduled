import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 046 (a)–(b): the deterministic identities

`g` is `σ²`, bounded and measurable (for the model, piecewise constant on the cells).

* `bracketStatement` is (a)'s bracket: for `0 ≤ t ≤ T`,
  `∫_t^T ∫_0^t σ(v)²(u − v) dv du + ∫_0^t ∫_0^s σ(v)²(s − v) dv ds = ½ ∫_0^t σ(v)²(T − v)² dv`.
* `driftStatement` is (b)'s drift integral: for `0 ≤ a ≤ b`,
  `∫_a^b ∫_0^u σ(s)²(u − s) ds du = ∫_0^b σ(s)² d(s) ds`, with
  `d(s) = ((b − s)^{+2} − (a − s)^{+2})/2` (46.3).
* `accumulatedStatement` is the diffusion part of `z = δ ∫_0^S Q` (46.6):
  `∫_0^S ∫_0^x σ(s)² ds dx = ∫_0^S σ(s)²(S − s) ds`.
-/

namespace Standalone.DiffusionMeetingIdentities

/-- `d(s) = ((b − s)^{+2} − (a − s)^{+2})/2`. -/
noncomputable def dfun (a b s : ℝ) : ℝ := (max (b - s) 0 ^ 2 - max (a - s) 0 ^ 2) / 2

def bracketStatement : Prop := ∀ (g : ℝ → ℝ), Measurable g → (∃ B, ∀ s, |g s| ≤ B) →
  ∀ t T : ℝ, 0 ≤ t → t ≤ T →
  (∫ u in t..T, ∫ v in (0:ℝ)..t, g v * (u - v)) +
    (∫ s in (0:ℝ)..t, ∫ v in (0:ℝ)..s, g v * (s - v)) =
      ∫ v in (0:ℝ)..t, g v * (T - v) ^ 2 / 2

def driftStatement : Prop := ∀ (g : ℝ → ℝ), Measurable g → (∃ B, ∀ s, |g s| ≤ B) →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
  ∫ u in a..b, ∫ s in (0:ℝ)..u, g s * (u - s) = ∫ s in (0:ℝ)..b, g s * dfun a b s

def accumulatedStatement : Prop := ∀ (g : ℝ → ℝ), Measurable g → (∃ B, ∀ s, |g s| ≤ B) →
  ∀ S : ℝ, 0 ≤ S → ∫ x in (0:ℝ)..S, ∫ s in (0:ℝ)..x, g s = ∫ s in (0:ℝ)..S, g s * (S - s)

def statement : Prop := bracketStatement ∧ driftStatement ∧ accumulatedStatement

end Standalone.DiffusionMeetingIdentities

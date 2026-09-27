import Standalone.SharefFilipovicSplit

/-! # Claim 034 (a) and (c): the splice has no cross terms

Fix a time `t` and a path, as in `SharefFilipovicSplit`, now with one list of `m` drivers shared
by the front end and the block. The front end's volatility is `σ^S(T) ∈ ℝ^m` and the block's is
`σ^B(T) = ∑_i φ_i(T − t) σ_Z^{i,·}`. The two groups of drivers are separate: for each driver `k`,
either the front end has no volatility on it, or no component of the block does.

`partAStatement`: suppose AX-01 holds for the whole curve on an open piece `J` of a maturity
interval, on which `D^S` and `σ^S` are affine. The whole curve's volatility is `σ^S + σ^B` on every
driver: `∫_t^T (D^S + D^B) = ½ ∑_k (∫_t^T (σ^S_k + σ^B_k))²`. Then:
* the block's consistency equation (34.3), with `a = σ_Z σ_Zᵀ`, holds for every `x`, which is (a);
* the front end satisfies its own AX-01 on `J` in differentiated form,
  `D^S(T) = σ^S(T) · ∫_t^T σ^S`.
There is no cross term because the driver groups are disjoint, which is (c)'s second point.
-/

open Set
namespace Standalone.SharefFilipovicPartA
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicSplit

def partAStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ m : ℕ)
  (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin m → ℝ)
  (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t p q : ℝ), t ≤ p → p < q →
  IntervalIntegrable DS MeasureTheory.volume t q →
  (∀ k, IntervalIntegrable (fun u => sS u k) MeasureTheory.volume t q) →
  (∃ d₀ d₁ : ℝ, ∀ T ∈ Ioo p q, DS T = d₀ + d₁ * T) →
  (∃ s₀ s₁ : Fin m → ℝ, ∀ T ∈ Ioo p q, ∀ k, sS T k = s₀ k + s₁ k * T) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  (∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DB034 β Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sB034 β sZ t u k)) ^ 2) →
  (∀ x : ℝ, residual034 β n₁ n₂ Z b (fun i j => ∑ k, sZ i k * sZ j k) x = 0) ∧
  (∀ T ∈ Ioo p q, DS T = ∑ k, sS T k * ∫ u in t..T, sS u k)

def statement : Prop := partAStatement

end Standalone.SharefFilipovicPartA

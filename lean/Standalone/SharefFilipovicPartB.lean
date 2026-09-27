import Standalone.SharefFilipovicPartA
import Standalone.SharefFilipovicMaxFactors

/-! # Claim 034 (b): the restrictions survive, and the splice imposes exactly the block's system

The setting is `SharefFilipovicPartA`'s: a fixed time `t` and a path, one list of `m` drivers
split into the front end's and the block's, the block's drift `D^B` and volatility
`σ^B(T) = ∑_i φ_i(T − t) σ_Z^{i,·}` as Itô's formula gives them (`SharefFilipovicIto`), and
`a = σ_Z σ_Zᵀ`.

* `boundStatement` is (b)'s first bullet. Under `partAStatement`'s hypotheses (AX-01 for the
  whole curve on an open piece of a maturity interval), every nonzero entry `a_{(i,μ),(j,ν)}` has
  `i = j = 1` and `μ, ν ≤ ⌊n₂/2⌋`. So at most `min(n₁, ⌊n₂/2⌋) + 1` components of `Z` are
  nontrivial, namely `Z^{1,k}` for `k ≤ min(n₁, ⌊n₂/2⌋)`. The proof is (a) followed by the lab's
  lemma `SharefFilipovicMaxFactors` (AX-14, proved under rule 6 as amended by Q-08), whose
  docstring cites [sharef2004conditions] §4.2 as prior art.
* `converseStatement` is the converse used in (b)'s second bullet. If `(Z, a, b)` solves the
  block's equation (34.3) for every `x ≥ 0`, the groups of drivers are separate, and the front end
  satisfies its own AX-01 up to a maturity `T ≥ t`, then the whole curve satisfies AX-01 up to `T`:
  `∫_t^T (D^S + D^B) = ½ ∑_k (∫_t^T (σ^S_k + σ^B_k))²`. With `partAStatement`, the splice is
  consistent iff `(Z, a, b)` solves (34.3), given the front end's own AX-01. So the splice
  imposes exactly the system (34.3) of the block alone, and any sufficiency result for the block
  alone carries over. The central proposition of [sharef2004conditions] §4.2 is not used.
-/

open Set
namespace Standalone.SharefFilipovicPartB
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicSplit

def boundStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ m : ℕ)
  (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin m → ℝ)
  (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t p q : ℝ), t ≤ p → p < q →
  IntervalIntegrable DS MeasureTheory.volume t q →
  (∀ k, IntervalIntegrable (fun u => sS u k) MeasureTheory.volume t q) →
  (∃ d₀ d₁ : ℝ, ∀ T ∈ Ioo p q, DS T = d₀ + d₁ * T) →
  (∃ s₀ s₁ : Fin m → ℝ, ∀ T ∈ Ioo p q, ∀ k, sS T k = s₀ k + s₁ k * T) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  (∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DB034 β Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sB034 β sZ t u k)) ^ 2) →
  ∀ i j, (∑ k, sZ i k * sZ j k) ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
    (μ : ℕ) ≤ n₂ / 2 ∧ (ν : ℕ) ≤ n₂ / 2

def converseStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ m : ℕ)
  (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin m → ℝ)
  (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t : ℝ),
  (∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ Z b (fun i j => ∑ k, sZ i k * sZ j k) x = 0) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  ∀ T : ℝ, t ≤ T → IntervalIntegrable DS MeasureTheory.volume t T →
  (∀ k, IntervalIntegrable (fun u => sS u k) MeasureTheory.volume t T) →
  ∫ u in t..T, DS u = (1/2 : ℝ) * ∑ k, (∫ u in t..T, sS u k) ^ 2 →
  ∫ u in t..T, (DS u + DB034 β Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sB034 β sZ t u k)) ^ 2

def statement : Prop := boundStatement ∧ converseStatement

end Standalone.SharefFilipovicPartB

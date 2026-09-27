import Standalone.SpliceAffineOverlapAbsorb
import Standalone.SpliceAffineOverlapNS
import Standalone.AnalyticPrimitive

/-! # Claim 037: blocks with constant or linear terms, assembled

* (a), with no extra hypothesis: `absorbFullStatement` is `SpliceAffineOverlapAbsorb.absorbStatement`
  without the hypothesis that the primitives of the `φ_i` are real-analytic, which
  `AnalyticPrimitive` proves; the converse is `SpliceAffineOverlapAbsorb.converseStatement`.
* (b) is `SpliceAffineOverlapNS`.
* (c), the interpretation, as two facts about the Nelson–Siegel block. `levelStatement`: if
  `a = σ_Z σ_Zᵀ` is supported on the level's entry `a^{11}` (as (b) forces), then `σ_Z` has no
  loading on `z_2` or `z_3`, so they carry no nontrivial factor. `shiftStatement`: moving the level
  `z_1` by `c` moves the curve `F(·, z)` by the constant `c`, a parallel shift, which lies in `S⁺`
  and is what adding `c` to every `L_m` does.
-/

open Set MeasureTheory
namespace Standalone.SpliceAffineOverlapAssembly
open Standalone.SpliceAffineOverlapAbsorb Standalone.SpliceAffineOverlapNS

def absorbFullStatement : Prop := ∀ (N m : ℕ) (φ : Fin N → ℝ → ℝ),
  (∀ i, AnalyticOnNhd ℝ (φ i) univ) →
  ∀ (Z b : Fin N → ℝ) (sZ : Fin N → Fin m → ℝ) (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t p q : ℝ),
  t ≤ p → p < q → IntervalIntegrable DS volume t q →
  (∀ k, IntervalIntegrable (fun u => sS u k) volume t q) →
  (∃ d₀ d₁ : ℝ, ∀ T ∈ Ioo p q, DS T = d₀ + d₁ * T) →
  (∃ s₀ : Fin m → ℝ, ∀ T ∈ Ioo p q, sS T = s₀) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  (∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DBlin φ Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2) →
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, Rlin φ Z b (fun i j => ∑ k, sZ i k * sZ j k) x = c₀ + c₁ * x

def levelStatement : Prop := ∀ (m : ℕ) (sZ : Fin 3 → Fin m → ℝ),
  (∀ i j, (∑ k, sZ i k * sZ j k) ≠ 0 → i = 0 ∧ j = 0) → ∀ i : Fin 3, i ≠ 0 → ∀ k, sZ i k = 0

def shiftStatement : Prop := ∀ (β c : ℝ) (z : Fin 3 → ℝ) (x : ℝ),
  FNS β (z + c • Pi.single 0 1) x = FNS β z x + c

def statement : Prop :=
  Standalone.AnalyticPrimitive.statement ∧ absorbFullStatement ∧ converseStatement ∧
  Standalone.SpliceAffineOverlapNS.statement ∧ levelStatement ∧ shiftStatement

end Standalone.SpliceAffineOverlapAssembly

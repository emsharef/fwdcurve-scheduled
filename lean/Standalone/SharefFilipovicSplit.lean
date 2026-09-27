import Standalone.SharefFilipovicResidual

/-! # Claim 034 (a): AX-01 splits and gives the block's equation

Fix a time `t` and a path. On the curve (34.2), `D^S` and `σ^S ∈ ℝ^{d_S}` are the front end's drift
and volatility at maturity `T`, and the block part `F(T − t, Z_t)` has drift
`D^B(T) = −∂_x F(T − t, Z) + ∑_i b_i φ_i(T − t)` and volatility
`σ^B(T) = ∑_i φ_i(T − t) σ_Z^{i,·} ∈ ℝ^{d_B}`, as Itô's formula gives for `F` linear in `z`.
`splitStatement`: let `J = (p, q)`, with `t ≤ p < q`, be an open piece of a maturity interval on
which `D^S` and `σ^S` are affine in `T`. The front-end terms are interval integrable on `[t, q]`,
and AX-01 holds for the whole curve on `J`:
`∫_t^T (D^S + D^B) = ½ (|∫_t^T σ^S|² + |∫_t^T σ^B|²)` for `T ∈ J`. Then the residual of the block's
consistency equation (34.3), with `a = σ_Z σ_Zᵀ`, vanishes for every `x`. This is (a): the
right side of (34.5) is a polynomial on `J`, and the residual step applies.
-/

open Set Polynomial
namespace Standalone.SharefFilipovicSplit
open Standalone.SharefFilipovicResidual

variable {n₁ n₂ : ℕ}

/-- The block's drift `−∂_x F(T − t, Z) + ∑ b_i φ_i(T − t)`. -/
noncomputable def DB034 (β : ℝ) (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (t T : ℝ) : ℝ :=
  -deriv (F034 β n₁ n₂ Z) (T - t) + ∑ i, b i * phi034 β n₁ n₂ i (T - t)

/-- The block's volatility `∑_i φ_i(T − t) σ_Z^{i,l}`. -/
noncomputable def sB034 {dB : ℕ} (β : ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin dB → ℝ)
    (t T : ℝ) (l : Fin dB) : ℝ :=
  ∑ i, phi034 β n₁ n₂ i (T - t) * sZ i l

def splitStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ dS dB : ℕ)
  (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin dB → ℝ)
  (DS : ℝ → ℝ) (sS : ℝ → Fin dS → ℝ) (t p q : ℝ), t ≤ p → p < q →
  IntervalIntegrable DS MeasureTheory.volume t q →
  (∀ k, IntervalIntegrable (fun u => sS u k) MeasureTheory.volume t q) →
  (∃ d₀ d₁ : ℝ, ∀ T ∈ Ioo p q, DS T = d₀ + d₁ * T) →
  (∃ s₀ s₁ : Fin dS → ℝ, ∀ T ∈ Ioo p q, ∀ k, sS T k = s₀ k + s₁ k * T) →
  (∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DB034 β Z b t u) =
    (1/2 : ℝ) * (∑ k, (∫ u in t..T, sS u k) ^ 2 + ∑ l, (∫ u in t..T, sB034 β sZ t u l) ^ 2)) →
  ∀ x : ℝ, residual034 β n₁ n₂ Z b (fun i j => ∑ l, sZ i l * sZ j l) x = 0

def statement : Prop := splitStatement

end Standalone.SharefFilipovicSplit

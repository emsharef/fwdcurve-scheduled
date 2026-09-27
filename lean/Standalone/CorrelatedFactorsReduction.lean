import Standalone.SharefFilipovicResidual
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Claim 036 (a): the reduction to `t_k(S_A) = r_k`

The family is Claim 034's (34.1), `F(x, z) = p_1(x) e^{−βx} + p_2(x) e^{−2βx}`, and (34.3) at a
parameter point `(z, a, b)` for all `x ≥ 0` is `residual034 β n₁ n₂ z b a x = 0` for `x ≥ 0`
(`SharefFilipovicResidual`). Put `n = ⌊n₂/2⌋`. `z1 z k`, `z2 z k` are `z_{1,k}`, `z_{2,k}` (zero out
of range), and likewise for `b`.

* `Pnu β ν` is `P_ν(x) = ∑_{j=0}^{ν} (ν!/(ν−j)!) x^{ν−j} β^{−j−1}`, written by degree
  `d = ν − j`: `∑_{d=0}^{ν} (ν!/d!) β^{−(ν−d)−1} x^d`. So `P_ν(x) e^{−βx} = ∫_x^∞ η^ν e^{−βη} dη`.
* `SA β a` is `S_A = ∑_{μ,ν} a_{(1,μ),(1,ν)} P_μ P_ν`, over the whole `Z¹` block.
* `tk β S k` is `t_k(S) = [x^k](β S − S'/2) = β s_k − (k+1) s_{k+1}/2`.

`reductionStatement` is (a). Let `a` be nonnegative definite and let the coefficients `z_{2,k}` with
`k ≤ 2n` and `z_{2,k} = 0` be structurally absent, with drift `b_{2,k} = 0` (the set `K_0` of the
Statement). Then `(z, a, b)` satisfies (34.3) for all `x ≥ 0` if and only if
* `a` is supported on `A = (a_{(1,μ),(1,ν)})_{μ,ν ≤ n}` (AX-14, `SharefFilipovicMaxFactors`),
* the drifts are given by (36.3):
  `b_{1,k} = (k+1) z_{1,k+1} − β z_{1,k} + ∑_ν a_{(1,k),(1,ν)} ν!/β^{ν+1}` and, for `k ∉ K_0`,
  `b_{2,k} = (k+1) z_{2,k+1} − 2β z_{2,k} − t_k(S_A)`,
* and (36.1): `t_k(S_A) = r_k = (k+1) z_{2,k+1}` for every `k ∈ K_0`.
-/

open Polynomial
namespace Standalone.CorrelatedFactorsReduction
open Standalone.SharefFilipovicResidual

/-- `P_ν(x) = ∑_{d=0}^{ν} (ν!/d!) β^{−(ν−d)−1} x^d`. -/
noncomputable def Pnu (β : ℝ) (ν : ℕ) : ℝ[X] :=
  ∑ d ∈ Finset.range (ν + 1), C ((ν.factorial : ℝ) / (d.factorial : ℝ) / β ^ (ν - d + 1)) * X ^ d

/-- `S_A = ∑_{μ,ν} a_{(1,μ),(1,ν)} P_μ P_ν`. -/
noncomputable def SA (β : ℝ) {n₁ n₂ : ℕ}
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) : ℝ[X] :=
  ∑ μ : Fin (n₁ + 1), ∑ ν : Fin (n₁ + 1), C (a (Sum.inl μ) (Sum.inl ν)) * Pnu β μ * Pnu β ν

/-- `t_k(S) = β s_k − (k+1) s_{k+1}/2`. -/
noncomputable def tk (β : ℝ) (S : ℝ[X]) (k : ℕ) : ℝ :=
  β * S.coeff k - ((k : ℝ) + 1) * S.coeff (k + 1) / 2

/-- `z_{1,k}`, zero out of range. -/
noncomputable def c1 {n₁ n₂ : ℕ} (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n₁ + 1 then z (Sum.inl ⟨k, h⟩) else 0

/-- `z_{2,k}`, zero out of range. -/
noncomputable def c2 {n₁ n₂ : ℕ} (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n₂ + 1 then z (Sum.inr ⟨k, h⟩) else 0

def reductionStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ n₂ : ℕ)
  (z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
  (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ), a.PosSemidef →
  (∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 → b (Sum.inr k) = 0) →
  ((∀ x : ℝ, 0 ≤ x → residual034 β n₁ n₂ z b a x = 0) ↔
    ((∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
        (μ : ℕ) ≤ n₂ / 2 ∧ (ν : ℕ) ≤ n₂ / 2) ∧
      (∀ k : Fin (n₁ + 1), b (Sum.inl k) = ((k : ℝ) + 1) * c1 z (k + 1) - β * z (Sum.inl k) +
        ∑ ν : Fin (n₁ + 1), a (Sum.inl k) (Sum.inl ν) * ((ν : ℕ).factorial / β ^ ((ν : ℕ) + 1))) ∧
      (∀ k : Fin (n₂ + 1), (z (Sum.inr k) ≠ 0 ∨ 2 * (n₂ / 2) < (k : ℕ)) →
        b (Sum.inr k) = ((k : ℝ) + 1) * c2 z (k + 1) - 2 * β * z (Sum.inr k) - tk β (SA β a) k) ∧
      (∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 →
        tk β (SA β a) k = ((k : ℝ) + 1) * c2 z (k + 1))))

def statement : Prop := reductionStatement

end Standalone.CorrelatedFactorsReduction

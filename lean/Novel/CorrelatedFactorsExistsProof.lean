import Standalone.CorrelatedFactorsExists
import Novel.CorrelatedFactorsGramProof

open Polynomial Matrix
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsGram Standalone.CorrelatedFactorsExists
namespace Novel.CorrelatedFactorsExistsProof

variable {n₁ n₂ : ℕ}

/-- Reindex a sum over `Fin (n₁ + 1)` vanishing beyond `n` to a sum over `Fin (n + 1)`. -/
lemma sum_castLE {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : n ≤ n₁) (f : Fin (n₁ + 1) → M)
    (hf : ∀ μ : Fin (n₁ + 1), n < (μ : ℕ) → f μ = 0) :
    ∑ μ, f μ = ∑ μ : Fin (n + 1), f (Fin.castLE (by omega) μ) := by
  have e := Finset.sum_map Finset.univ (Fin.castLEEmb (by omega : n + 1 ≤ n₁ + 1)) f
  calc ∑ μ, f μ = ∑ x ∈ Finset.univ.map (Fin.castLEEmb (by omega : n + 1 ≤ n₁ + 1)), f x := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun μ _ hμ => hf μ ?_).symm
        by_contra h
        exact hμ (Finset.mem_map.2 ⟨⟨μ, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    _ = _ := e

/-- For `a` supported on `μ, ν ≤ n`, `S_a = S_A` with `A` its block. -/
lemma SA_eq (β : ℝ) (n : ℕ) (hn : n ≤ n₁)
    (a : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ)
    (hsupp : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
      (μ : ℕ) ≤ n ∧ (ν : ℕ) ≤ n) :
    SA β a = SAn β n (blockA n hn a) := by
  have hz : ∀ μ ν : Fin (n₁ + 1), (n < (μ : ℕ) ∨ n < (ν : ℕ)) →
      a (Sum.inl μ) (Sum.inl ν) = 0 := fun μ ν h => by
    by_contra hne
    obtain ⟨μ', ν', h1, h2, h3, h4⟩ := hsupp _ _ hne
    cases Sum.inl_injective h1; cases Sum.inl_injective h2
    omega
  unfold SA SAn blockA
  rw [sum_castLE n hn _ fun μ hμ => Finset.sum_eq_zero fun ν _ => by
    rw [hz μ ν (Or.inl hμ), C_0, zero_mul, zero_mul]]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_castLE n hn _ fun ν hν => by rw [hz _ ν (Or.inr hν), C_0, zero_mul, zero_mul]]
  rfl

/-- The inclusion of the first `n + 1` coordinates of the `Z¹` block. -/
def Pm (n : ℕ) (hn : n ≤ n₁) : Matrix (Fin (n + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ :=
  fun μ j => if j = Sum.inl (Fin.castLE (by omega) μ) then 1 else 0

/-- `a = Pᵀ A P`: `A` on the block, zero elsewhere. -/
def aOf (n : ℕ) (hn : n ≤ n₁) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) ℝ :=
  (Pm (n₂ := n₂) n hn)ᴴ * A * Pm n hn

lemma aOf_apply (n : ℕ) (hn : n ≤ n₁) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) :
    aOf n hn A i j = ∑ μ, ∑ ν, Pm n hn μ i * A μ ν * Pm n hn ν j := by
  simp only [aOf, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma aOf_block (n : ℕ) (hn : n ≤ n₁) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    blockA n hn (aOf (n₂ := n₂) n hn A) = A := by
  ext μ ν
  simp only [blockA, aOf_apply, Pm]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro ν' _ hν'
    rw [ite_eq_right (fun h => hν' (Fin.castLE_injective _ (Sum.inl_injective h).symm)), mul_zero]
  · simp
  · intro μ' _ hμ'
    refine Finset.sum_eq_zero fun ν' _ => ?_
    rw [ite_eq_right (fun h => hμ' (Fin.castLE_injective _ (Sum.inl_injective h).symm)),
      zero_mul, zero_mul]
  · simp

lemma aOf_supp (n : ℕ) (hn : n ≤ n₁) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (h : aOf n hn A i j ≠ 0) :
    ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧ (μ : ℕ) ≤ n ∧ (ν : ℕ) ≤ n := by
  rw [aOf_apply] at h
  obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨ν, -, hν⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  simp only [Pm] at hν
  by_cases hi : i = Sum.inl (Fin.castLE (by omega) μ)
  · by_cases hj : j = Sum.inl (Fin.castLE (by omega) ν)
    · exact ⟨_, _, hi, hj, by simp; omega, by simp; omega⟩
    · rw [ite_eq_right hj, mul_zero] at hν; exact absurd rfl hν
  · rw [ite_eq_right hi, zero_mul, zero_mul] at hν; exact absurd rfl hν

lemma exists_ : existsStatement := by
  intro β hβ n₁ n₂ hn z
  constructor
  · rintro ⟨a, b, ha, hA, hK0, hres⟩
    obtain ⟨hsupp, -, -, htk⟩ :=
      (Novel.CorrelatedFactorsReductionProof.reduction β hβ n₁ n₂ z b a ha hK0).1 hres
    have hSA := SA_eq β (n₂ / 2) hn a hsupp
    obtain ⟨h1, h2, h3⟩ := Novel.CorrelatedFactorsGramProof.forward β hβ _ hA
    exact ⟨SAn β (n₂ / 2) (blockA (n₂ / 2) hn a), h1, h2, h3, fun k hk hz => hSA ▸ htk k hk hz⟩
  · rintro ⟨S, h1, h2, h3, h4⟩
    obtain ⟨A, hA, hS⟩ := Novel.CorrelatedFactorsGramProof.backward β hβ S h1 h2 h3
    let a := aOf (n₂ := n₂) (n₂ / 2) hn A
    have ha : a.PosSemidef := hA.posSemidef.conjTranspose_mul_mul_same (Pm (n₂ / 2) hn)
    have hsupp := aOf_supp (n₂ := n₂) (n₂ / 2) hn A
    have hSA : SA β a = S := by rw [SA_eq β (n₂ / 2) hn a hsupp, aOf_block, hS]
    let b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ := Sum.elim
      (fun k => ((k : ℝ) + 1) * c1 z (k + 1) - β * z (Sum.inl k) +
        ∑ ν : Fin (n₁ + 1), a (Sum.inl k) (Sum.inl ν) * ((ν : ℕ).factorial / β ^ ((ν : ℕ) + 1)))
      (fun k => if (k : ℕ) ≤ 2 * (n₂ / 2) ∧ z (Sum.inr k) = 0 then 0 else
        ((k : ℝ) + 1) * c2 z (k + 1) - 2 * β * z (Sum.inr k) - tk β (SA β a) k)
    have hK0 : ∀ k : Fin (n₂ + 1), (k : ℕ) ≤ 2 * (n₂ / 2) → z (Sum.inr k) = 0 →
        b (Sum.inr k) = 0 := fun k hk hz => by simp [b, hk, hz]
    refine ⟨a, b, ha, by rw [aOf_block]; exact hA, hK0,
      (Novel.CorrelatedFactorsReductionProof.reduction β hβ n₁ n₂ z b a ha hK0).2
        ⟨hsupp, fun k => rfl, fun k hk => ?_, fun k hk hz => by rw [hSA]; exact h4 k hk hz⟩⟩
    simp only [b, Sum.elim_inr]
    rw [ite_eq_right fun h => by rcases hk with hk | hk; exact hk h.2; omega]

theorem correlatedFactorsExists : Standalone.CorrelatedFactorsExists.statement := exists_

end Novel.CorrelatedFactorsExistsProof

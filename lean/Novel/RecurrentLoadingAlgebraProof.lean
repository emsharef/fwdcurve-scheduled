import Standalone.RecurrentLoadingAlgebra

open Matrix NormedSpace Polynomial Standalone.RecurrentLoadingAlgebra
namespace Novel.RecurrentLoadingAlgebraProof

lemma count : countStatement := by
  intro Tm s t T x
  constructor
  · intro hst htT
    have hdisj : Disjoint (Tm.filter fun τ => s < τ ∧ τ ≤ t) (Tm.filter fun τ => t < τ ∧ τ ≤ T) :=
      Finset.disjoint_filter.2 fun τ _ h1 h2 => by linarith [h1.2, h2.1]
    rw [count030, count030, count030, ← Finset.card_union_of_disjoint hdisj, ← Finset.filter_or]
    congr 1
    apply Finset.filter_congr
    intro τ _
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : τ ≤ t
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.trans htT⟩
      · exact ⟨lt_of_le_of_lt hst h1, h2⟩
  · rw [idx030, dist030, Finset.filter_image,
      Finset.card_image_of_injective _ (sub_left_injective (b := t)), Finset.filter_filter,
      count030]
    congr 1
    apply Finset.filter_congr
    intro τ _
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

lemma factor : factorStatement := by
  intro p r Tm u v M c b A s t T hst htT
  have hcount := (count Tm s t T 0).1 hst htT
  have hidx := (count Tm t t T (T - t)).2
  simp only [add_sub_cancel] at hidx
  simp only [sigma030, loading030, shape030, k030, w030, dotProduct, Fintype.sum_prod_type]
  rw [hidx, hcount]
  -- separate the two factors
  have hsplit : ∀ (f1 g1 : Fin p → ℝ) (f2 g2 : Fin r → ℝ),
      (∑ i, ∑ j, f1 i * f2 j * (g1 i * g2 j)) = (∑ i, f1 i * g1 i) * (∑ j, f2 j * g2 j) := by
    intro f1 g1 f2 g2
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hsplit]
  congr 1
  · -- the loadings
    have h1 : (∑ i, (u ᵥ* M ^ count030 Tm t T) i * ((M ^ count030 Tm s t) *ᵥ v) i) =
        (u ᵥ* M ^ count030 Tm t T) ⬝ᵥ ((M ^ count030 Tm s t) *ᵥ v) := rfl
    rw [h1, ← dotProduct_mulVec, mulVec_mulVec, ← pow_add, add_comm]
    rfl
  · -- the shape
    have h2 : (∑ j, (c ᵥ* exp ((T - t) • A)) j * (exp ((t - s) • A) *ᵥ b) j) =
        (c ᵥ* exp ((T - t) • A)) ⬝ᵥ (exp ((t - s) • A) *ᵥ b) := rfl
    rw [h2, ← dotProduct_mulVec, mulVec_mulVec,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
    congr 3
    ring

lemma companion : companionStatement := by
  intro a L c hrec
  classical
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    refine ⟨0, 0, 0, fun i => ?_⟩
    have := hrec i
    simp only [add_zero, Finset.univ_eq_empty, Finset.sum_empty] at this
    simp [this, loading030]
  · -- the companion matrix
    let M : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j =>
      if (i : ℕ) + 1 < L then (if (j : ℕ) = i + 1 then 1 else 0) else c j
    let v : Fin L → ℝ := fun i => a i
    let u : Fin L → ℝ := Pi.single ⟨0, hL⟩ 1
    have hpow : ∀ k : ℕ, ∀ i : Fin L, ((M ^ k) *ᵥ v) i = a (k + i) := by
      intro k
      induction k with
      | zero => intro i; simp [v]
      | succ k ih =>
        intro i
        rw [pow_succ', ← mulVec_mulVec]
        have hw : (M ^ k) *ᵥ v = fun j : Fin L => a (k + j) := funext ih
        rw [hw]
        simp only [mulVec, dotProduct, M, Matrix.of_apply]
        by_cases hi : (i : ℕ) + 1 < L
        · simp only [hi, ite_true]
          rw [Finset.sum_eq_single ⟨i + 1, hi⟩]
          · simp only [ite_true, one_mul]
            congr 1
            ring
          · intro j _ hj
            have : (j : ℕ) ≠ i + 1 := fun h => hj (Fin.ext h)
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [hi, ite_false]
          have hiL : (i : ℕ) = L - 1 := by omega
          rw [← hrec k]
          congr 1
          omega
    refine ⟨u, v, M, fun i => ?_⟩
    simp only [loading030, u]
    rw [single_dotProduct, one_mul, hpow]
    simp

lemma cayley : cayleyStatement := by
  intro p u v M
  classical
  refine ⟨fun l => -M.charpoly.coeff l, fun i => ?_⟩
  have hCH := Matrix.aeval_self_charpoly M
  rw [aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin] at hCH
  -- apply to `M^i v` and pair with `u`
  have h0 : u ⬝ᵥ ((M ^ i * ∑ l ∈ Finset.range (p + 1), M.charpoly.coeff l • M ^ l) *ᵥ v) = 0 := by
    rw [hCH, mul_zero, zero_mulVec, dotProduct_zero]
  rw [Finset.mul_sum, sum_mulVec, dotProduct_sum, Finset.sum_range_succ] at h0
  have hlead : M.charpoly.coeff p = 1 := by
    have := (charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  have hterm : ∀ l, u ⬝ᵥ ((M ^ i * M.charpoly.coeff l • M ^ l) *ᵥ v) =
      M.charpoly.coeff l * loading030 u v M (i + l) := by
    intro l
    rw [mul_smul_comm, smul_mulVec, dotProduct_smul, ← pow_add, smul_eq_mul]
    rfl
  simp only [hterm] at h0
  rw [hlead, one_mul] at h0
  simp only [loading030] at h0 ⊢
  rw [← Fin.sum_univ_eq_sum_range (fun l => M.charpoly.coeff l * u ⬝ᵥ ((M ^ (i + l)) *ᵥ v))] at h0
  have : ∑ l : Fin p, -M.charpoly.coeff l * u ⬝ᵥ ((M ^ (i + l)) *ᵥ v) =
      -∑ l : Fin p, M.charpoly.coeff l * u ⬝ᵥ ((M ^ (i + l)) *ᵥ v) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [this]
  linarith

theorem recurrentLoadingAlgebra : Standalone.RecurrentLoadingAlgebra.statement :=
  ⟨companion, cayley, count, factor⟩

end Novel.RecurrentLoadingAlgebraProof

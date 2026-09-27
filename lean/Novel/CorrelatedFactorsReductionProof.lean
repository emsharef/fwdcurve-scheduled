import Standalone.CorrelatedFactorsReduction
import Novel.SharefFilipovicMaxFactorsProof

open Set Polynomial Filter
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
namespace Novel.CorrelatedFactorsReductionProof

lemma Pnu_coeff (β : ℝ) (ν d : ℕ) :
    (Pnu β ν).coeff d =
      if d ≤ ν then (ν.factorial : ℝ) / (d.factorial : ℝ) / β ^ (ν - d + 1) else 0 := by
  simp only [Pnu, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

lemma Pnu_eval0 (β : ℝ) (ν : ℕ) : (Pnu β ν).eval 0 = (ν.factorial : ℝ) / β ^ (ν + 1) := by
  rw [← coeff_zero_eq_eval_zero, Pnu_coeff, ite_eq_left (Nat.zero_le _)]
  simp

/-- `β P_ν − P_ν' = x^ν`. -/
lemma Pnu_anti (β : ℝ) (hβ : β ≠ 0) (ν : ℕ) : C β * Pnu β ν - derivative (Pnu β ν) = X ^ ν := by
  ext d
  rw [coeff_sub, coeff_C_mul, coeff_derivative, Pnu_coeff, Pnu_coeff, coeff_X_pow]
  rcases lt_trichotomy d ν with h | rfl | h
  · obtain ⟨e, rfl⟩ : ∃ e, ν = d + 1 + e := ⟨ν - (d + 1), by omega⟩
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
      show d + 1 + e - d + 1 = e + 2 by omega, show d + 1 + e - (d + 1) + 1 = e + 1 by omega,
      Nat.factorial_succ d]
    push_cast
    field_simp
    ring
  · rw [ite_eq_left le_rfl, ite_eq_right (by omega), ite_eq_left rfl, Nat.sub_self]
    field_simp
    ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    ring

/-- The polynomial with coefficient vector `f`. -/
noncomputable def poly1 {m : ℕ} (f : Fin (m + 1) → ℝ) : ℝ[X] := ∑ μ, C (f μ) * X ^ (μ : ℕ)

lemma coeff_poly1 {m : ℕ} (f : Fin (m + 1) → ℝ) (j : ℕ) :
    (poly1 f).coeff j = if h : j < m + 1 then f ⟨j, h⟩ else 0 := by
  simp only [poly1, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro μ _ hμ
      rw [ite_eq_right]
      intro hj
      exact hμ (Fin.ext hj.symm)
    · simp
  · refine Finset.sum_eq_zero fun μ _ => ?_
    rw [ite_eq_right]
    intro hj
    exact h (hj ▸ μ.2)

lemma eval_poly1 {m : ℕ} (f : Fin (m + 1) → ℝ) (x : ℝ) :
    (poly1 f).eval x = ∑ μ, f μ * x ^ (μ : ℕ) := by
  simp [poly1, eval_finsetSum]

variable {n₁ n₂ : ℕ}

/-- `∑_i w_i φ_i(x) = W_1(x) e^{−βx} + W_2(x) e^{−2βx}`. -/
lemma sum_phi (β : ℝ) (w : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (x : ℝ) :
    ∑ i, w i * phi034 β n₁ n₂ i x =
      (poly1 fun μ => w (Sum.inl μ)).eval x * Real.exp (-β * x) +
        (poly1 fun μ => w (Sum.inr μ)).eval x * Real.exp (-(2 * β) * x) := by
  rw [Fintype.sum_sum_type, eval_poly1, eval_poly1, Finset.sum_mul, Finset.sum_mul]
  simp only [phi034, Sum.elim_inl, Sum.elim_inr]
  congr 1 <;> exact Finset.sum_congr rfl fun μ _ => by ring

lemma deriv_F (β : ℝ) (z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (x : ℝ) :
    deriv (F034 β n₁ n₂ z) x =
      (derivative (poly1 fun μ => z (Sum.inl μ)) - C β * poly1 fun μ => z (Sum.inl μ)).eval x *
          Real.exp (-β * x) +
        (derivative (poly1 fun μ => z (Sum.inr μ)) - C (2 * β) * poly1 fun μ => z (Sum.inr μ)).eval
          x * Real.exp (-(2 * β) * x) := by
  have e : F034 β n₁ n₂ z = fun x =>
      (poly1 fun μ => z (Sum.inl μ)).eval x * Real.exp (-β * x) +
        (poly1 fun μ => z (Sum.inr μ)).eval x * Real.exp (-(2 * β) * x) := by
    funext x
    exact sum_phi β z x
  rw [e]
  exact ((Novel.SharefFilipovicResidualProof.hd_pe _ β x).add
    (Novel.SharefFilipovicResidualProof.hd_pe _ (2 * β) x)).deriv

/-- `M = ∑_{μ,ν} a_{μν} x^μ P_ν`. -/
noncomputable def Mp (β : ℝ) (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) :
    ℝ[X] :=
  ∑ μ : Fin (n₁ + 1), ∑ ν : Fin (n₁ + 1), C (a (Sum.inl μ) (Sum.inl ν)) * X ^ (μ : ℕ) * Pnu β ν

/-- `W_1 = ∑_μ (∑_ν a_{μν} P_ν(0)) x^μ`. -/
noncomputable def W1 (β : ℝ) (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) :
    ℝ[X] :=
  poly1 fun μ : Fin (n₁ + 1) => ∑ ν : Fin (n₁ + 1), a (Sum.inl μ) (Sum.inl ν) * (Pnu β ν).eval 0

/-- The `a`-term of (34.3) for `a` supported on the `Z¹` block, (36.2). -/
lemma asum (β : ℝ) (hβ : β ≠ 0)
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (hsupp : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν) (x : ℝ) :
    ∑ i, ∑ j, a i j * phi034 β n₁ n₂ i x * ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η =
      (W1 β a).eval x * Real.exp (-β * x) - (Mp β a).eval x * Real.exp (-(2 * β) * x) := by
  have hz : ∀ i j, (∀ μ, i ≠ Sum.inl μ) ∨ (∀ ν, j ≠ Sum.inl ν) → a i j = 0 := fun i j h => by
    by_contra hne
    obtain ⟨μ, ν, rfl, rfl⟩ := hsupp i j hne
    rcases h with h | h
    · exact h μ rfl
    · exact h ν rfl
  have hint : ∀ ν : Fin (n₁ + 1), ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ (Sum.inl ν) η =
      (Pnu β ν).eval 0 - (Pnu β ν).eval x * Real.exp (-β * x) := fun ν => by
    rw [← Novel.SharefFilipovicMaxFactorsProof.int_of_anti (X ^ (ν : ℕ)) (Pnu β ν) β
      (Pnu_anti β hβ ν) x]
    refine intervalIntegral.integral_congr fun η _ => ?_
    simp [phi034]
  have hee : Real.exp (-β * x) * Real.exp (-β * x) = Real.exp (-(2 * β) * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type]
  rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun μ : Fin (n₂ + 1) =>
      (∑ ν, a (Sum.inr μ) (Sum.inl ν) * phi034 β n₁ n₂ (Sum.inr μ) x *
        ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ (Sum.inl ν) η) +
      ∑ ν, a (Sum.inr μ) (Sum.inr ν) * phi034 β n₁ n₂ (Sum.inr μ) x *
        ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ (Sum.inr ν) η)
      (fun μ _ => by
        simp [hz (Sum.inr μ) _ (Or.inl fun _ h => Sum.inr_ne_inl h)])]
  simp only [hz (Sum.inl _) (Sum.inr _) (Or.inr fun _ h => Sum.inr_ne_inl h), zero_mul,
    Finset.sum_const_zero, add_zero, hint]
  rw [W1, Mp, eval_poly1, eval_finsetSum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [eval_finsetSum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [phi034, Sum.elim_inl, eval_mul, eval_C, eval_X_pow]
  rw [← hee]
  ring

/-- For symmetric `a`, `∑ a_{μν} x^μ P_ν = β S_A − S_A'/2`. -/
lemma Mp_eq (β : ℝ) (hβ : β ≠ 0)
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (hsym : ∀ μ ν : Fin (n₁ + 1), a (Sum.inl ν) (Sum.inl μ) = a (Sum.inl μ) (Sum.inl ν)) :
    Mp β a = C β * SA β a - C (1 / 2) * derivative (SA β a) := by
  set D1 : ℝ[X] := ∑ μ : Fin (n₁ + 1), ∑ ν : Fin (n₁ + 1),
    C (a (Sum.inl μ) (Sum.inl ν)) * derivative (Pnu β μ) * Pnu β ν
  have hM : Mp β a = C β * SA β a - D1 := by
    simp only [Mp, SA, D1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [← Pnu_anti β hβ μ]
    ring
  have h2 : ∑ μ : Fin (n₁ + 1), ∑ ν : Fin (n₁ + 1),
      C (a (Sum.inl μ) (Sum.inl ν)) * Pnu β μ * derivative (Pnu β ν) = D1 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hsym]
    ring
  have hD : derivative (SA β a) = D1 + D1 := by
    nth_rewrite 2 [← h2]
    simp only [SA, D1, derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add,
      ← Finset.sum_add_distrib]
  rw [hM, hD, mul_add, ← add_mul, ← C_add]
  norm_num

/-- The residual of (34.3) is `R_1(x) e^{−βx} + R_2(x) e^{−2βx}`. -/
lemma decomp (β : ℝ) (hβ : β ≠ 0) (z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (hsupp : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν) (x : ℝ) :
    residual034 β n₁ n₂ z b a x =
      (-(derivative (poly1 fun μ => z (Sum.inl μ)) - C β * poly1 fun μ => z (Sum.inl μ)) +
          (poly1 fun μ => b (Sum.inl μ)) - W1 β a).eval x * Real.exp (-β * x) +
        (-(derivative (poly1 fun μ => z (Sum.inr μ)) - C (2 * β) * poly1 fun μ => z (Sum.inr μ)) +
          (poly1 fun μ => b (Sum.inr μ)) + Mp β a).eval x * Real.exp (-(2 * β) * x) := by
  rw [residual034, deriv_F, sum_phi β b x, asum β hβ a hsupp x]
  simp only [eval_add, eval_sub, eval_neg]
  ring

lemma coeff_poly1_fin {m : ℕ} (f : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    (poly1 f).coeff k = f k := by
  simp [coeff_poly1, k.2]

lemma coeff_poly1_out {m : ℕ} (f : Fin (m + 1) → ℝ) (k : ℕ) (hk : ¬ k < m + 1) :
    (poly1 f).coeff k = 0 := by
  simp [coeff_poly1, hk]

lemma Pnu_natDegree (β : ℝ) (ν : ℕ) : (Pnu β ν).natDegree ≤ ν :=
  natDegree_le_iff_coeff_eq_zero.2 fun d hd => by
    rw [Pnu_coeff, ite_eq_right (not_le.2 (by exact_mod_cast hd))]

/-- With `a` supported on `μ, ν ≤ n`, `S_A` has degree at most `2n`. -/
lemma SA_coeff_zero (β : ℝ) (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (hsupp : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
      (μ : ℕ) ≤ n₂ / 2 ∧ (ν : ℕ) ≤ n₂ / 2) (d : ℕ) (hd : 2 * (n₂ / 2) < d) :
    (SA β a).coeff d = 0 := by
  simp only [SA, finsetSum_coeff]
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
  by_cases ha : a (Sum.inl μ) (Sum.inl ν) = 0
  · rw [ha, C_0, zero_mul, zero_mul, coeff_zero]
  obtain ⟨μ', ν', h1, h2, hμ, hν⟩ := hsupp _ _ ha
  cases Sum.inl_injective h1
  cases Sum.inl_injective h2
  rw [mul_assoc, coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
  exact lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (Pnu_natDegree β μ)
    (Pnu_natDegree β ν))) (by omega)

lemma reduction : reductionStatement := by
  intro β hβ n₁ n₂ z b a ha hK0
  have hβ0 : β ≠ 0 := hβ.ne'
  have hsym : ∀ μ ν : Fin (n₁ + 1), a (Sum.inl ν) (Sum.inl μ) = a (Sum.inl μ) (Sum.inl ν) :=
    fun μ ν => by
      have := congrFun (congrFun ha.1.eq (Sum.inl μ)) (Sum.inl ν)
      simpa [Matrix.conjTranspose_apply] using this
  let R1 : ℝ[X] := -(derivative (poly1 fun μ => z (Sum.inl μ)) - C β * poly1 fun μ => z (Sum.inl μ)) +
    (poly1 fun μ => b (Sum.inl μ)) - W1 β a
  let R2 : ℝ[X] := -(derivative (poly1 fun μ => z (Sum.inr μ)) -
    C (2 * β) * poly1 fun μ => z (Sum.inr μ)) + (poly1 fun μ => b (Sum.inr μ)) + Mp β a
  have hR1c : ∀ k : ℕ, R1.coeff k = -((poly1 fun μ => z (Sum.inl μ)).coeff (k + 1) * ((k : ℝ) + 1) -
      β * (poly1 fun μ => z (Sum.inl μ)).coeff k) + (poly1 fun μ => b (Sum.inl μ)).coeff k -
      (W1 β a).coeff k := fun k => by
    simp only [R1, coeff_add, coeff_sub, coeff_neg, coeff_derivative, coeff_C_mul]
  have hR2c : ∀ k : ℕ, R2.coeff k = -((poly1 fun μ => z (Sum.inr μ)).coeff (k + 1) * ((k : ℝ) + 1) -
      2 * β * (poly1 fun μ => z (Sum.inr μ)).coeff k) + (poly1 fun μ => b (Sum.inr μ)).coeff k +
      tk β (SA β a) k := fun k => by
    simp only [R2, Mp_eq β hβ0 a hsym, coeff_add, coeff_sub, coeff_neg, coeff_derivative,
      coeff_C_mul, tk]
    ring
  have hW : ∀ k : Fin (n₁ + 1), (W1 β a).coeff k =
      ∑ ν : Fin (n₁ + 1), a (Sum.inl k) (Sum.inl ν) * ((ν : ℕ).factorial / β ^ ((ν : ℕ) + 1)) :=
    fun k => by
      unfold W1
      rw [coeff_poly1_fin]
      simp only [Pnu_eval0]
  have hc1 : ∀ k : ℕ, (poly1 fun μ => z (Sum.inl μ)).coeff k = c1 z k := fun k => by
    rw [coeff_poly1]; rfl
  have hc2 : ∀ k : ℕ, (poly1 fun μ => z (Sum.inr μ)).coeff k = c2 z k := fun k => by
    rw [coeff_poly1]; rfl
  constructor
  · intro hres
    have hsupp := Novel.SharefFilipovicMaxFactorsProof.maxFactors β hβ n₁ n₂ z b a ha hres
    have hs' : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν :=
      fun i j h => let ⟨μ, ν, h1, h2, _, _⟩ := hsupp i j h; ⟨μ, ν, h1, h2⟩
    have hind := Novel.SharefFilipovicIndependenceProof.independence β hβ 2 ![R1, R2] 0 0 1
      one_pos fun x hx => by
        rw [eval_zero, ← hres x hx.1.le, decomp β hβ0 z b a hs' x]
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
          Fin.val_one, Nat.cast_zero, Nat.cast_one, R1, R2]
        ring_nf
    have hR1 : R1 = 0 := hind.1 0
    have hR2 : R2 = 0 := hind.1 1
    refine ⟨hsupp, fun k => ?_, fun k _ => ?_, fun k hk hz => ?_⟩
    · have := hR1c k
      rw [hR1, coeff_zero, hc1, hW, coeff_poly1_fin, coeff_poly1_fin] at this
      linarith
    · have := hR2c k
      rw [hR2, coeff_zero, hc2, coeff_poly1_fin, coeff_poly1_fin] at this
      linarith
    · have := hR2c k
      rw [hR2, coeff_zero, hc2, coeff_poly1_fin, coeff_poly1_fin, hz, hK0 k hk hz] at this
      linarith
  · rintro ⟨hsupp, hb1, hb2, htk⟩
    have hs' : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν :=
      fun i j h => let ⟨μ, ν, h1, h2, _, _⟩ := hsupp i j h; ⟨μ, ν, h1, h2⟩
    have hR1 : R1 = 0 := by
      ext k
      rw [hR1c, coeff_zero]
      by_cases hk : k < n₁ + 1
      · have := hb1 ⟨k, hk⟩
        have e1 := coeff_poly1_fin (fun μ => z (Sum.inl μ)) ⟨k, hk⟩
        have e2 := coeff_poly1_fin (fun μ => b (Sum.inl μ)) ⟨k, hk⟩
        have e3 := hW ⟨k, hk⟩
        simp only at e1 e2 e3 this
        rw [hc1 (k + 1), e1, e2, e3]
        linarith
      · unfold W1
        rw [coeff_poly1_out _ _ hk, coeff_poly1_out _ _ (by omega), coeff_poly1_out _ _ hk,
          coeff_poly1_out _ _ hk]
        ring
    have hR2 : R2 = 0 := by
      ext k
      rw [hR2c, coeff_zero]
      by_cases hk : k < n₂ + 1
      · have e1 := coeff_poly1_fin (fun μ => z (Sum.inr μ)) ⟨k, hk⟩
        have e2 := coeff_poly1_fin (fun μ => b (Sum.inr μ)) ⟨k, hk⟩
        simp only at e1 e2
        rw [hc2 (k + 1), e1, e2]
        by_cases hc : z (Sum.inr ⟨k, hk⟩) ≠ 0 ∨ 2 * (n₂ / 2) < k
        · have := hb2 ⟨k, hk⟩ hc
          simp only at this
          linarith
        · push Not at hc
          have h1 := hK0 ⟨k, hk⟩ hc.2 hc.1
          have h2 := htk ⟨k, hk⟩ hc.2 hc.1
          simp only at h1 h2
          rw [h1, hc.1]
          linarith
      · rw [coeff_poly1_out _ _ hk, coeff_poly1_out _ _ (by omega), coeff_poly1_out _ _ hk, tk,
          SA_coeff_zero β a hsupp k (by omega), SA_coeff_zero β a hsupp (k + 1) (by omega)]
        ring
    intro x _
    rw [decomp β hβ0 z b a hs' x]
    change R1.eval x * _ + R2.eval x * _ = 0
    rw [hR1, hR2]
    simp

theorem correlatedFactorsReduction : Standalone.CorrelatedFactorsReduction.statement := reduction

end Novel.CorrelatedFactorsReductionProof

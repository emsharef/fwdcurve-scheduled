import Standalone.CorrelatedFactorsHankel
import Novel.CorrelatedFactorsGramProof
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas

open Polynomial Matrix Filter Set
open Standalone.CorrelatedFactorsReduction Standalone.CorrelatedFactorsHankel
namespace Novel.CorrelatedFactorsHankelProof

/-- The pairing `ℓ(S) = ∑_{j ≤ 2n+1} ℓ_j s_j`. -/
noncomputable def pairing (n : ℕ) (ℓ : ℕ → ℝ) (S : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (2 * n + 2), ℓ j * S.coeff j

lemma pairing_add (n : ℕ) (ℓ : ℕ → ℝ) (S T : ℝ[X]) :
    pairing n ℓ (S + T) = pairing n ℓ S + pairing n ℓ T := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_smul (n : ℕ) (ℓ : ℕ → ℝ) (c : ℝ) (S : ℝ[X]) :
    pairing n ℓ (C c * S) = c * pairing n ℓ S := by
  simp [pairing, coeff_C_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

lemma pairing_sum {m : ℕ} (n : ℕ) (ℓ : ℕ → ℝ) (S : Fin m → ℝ[X]) :
    pairing n ℓ (∑ i, S i) = ∑ i, pairing n ℓ (S i) := by
  simp only [pairing, finsetSum_coeff, Finset.mul_sum]
  exact Finset.sum_comm

/-- `∑_{k ∈ K_0} λ_k t_k(S) = ℓ(S)`. -/
lemma pair_tk (β : ℝ) (n : ℕ) (K0 : Finset ℕ) (hK : ∀ k ∈ K0, k ≤ 2 * n) (lam : ℕ → ℝ)
    (S : ℝ[X]) : ∑ k ∈ K0, lam k * tk β S k = pairing n (ellOf β K0 lam) S := by
  have hsub : K0 ⊆ Finset.range (2 * n + 2) := fun k hk => by
    simp only [Finset.mem_range]; have := hK k hk; omega
  have h1 : ∑ j ∈ Finset.range (2 * n + 2), (if j ∈ K0 then β * lam j else 0) * S.coeff j =
      ∑ k ∈ K0, β * lam k * S.coeff k := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
  have h2 : ∑ j ∈ Finset.range (2 * n + 2),
      (if 0 < j ∧ j - 1 ∈ K0 then (j : ℝ) / 2 * lam (j - 1) else 0) * S.coeff j =
      ∑ k ∈ K0, ((k : ℝ) + 1) / 2 * lam k * S.coeff (k + 1) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hset : (Finset.range (2 * n + 2)).filter (fun j => 0 < j ∧ j - 1 ∈ K0) =
        K0.image (· + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨-, hj, hj1⟩; exact ⟨j - 1, hj1, by omega⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨by have := hK k hk; omega, by omega, by simpa using hk⟩
    rw [hset, Finset.sum_image fun a _ b _ h => by simpa using h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.add_sub_cancel]; push_cast; ring
  simp only [pairing, ellOf, sub_mul, Finset.sum_sub_distrib, h1, h2, tk, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · exact Finset.sum_congr rfl fun k _ => by ring

/-- `ℓ(q²) = wᵀ H w` for `q = ∑_{i ≤ n} w_i x^i`. -/
lemma pairing_sq (n : ℕ) (ℓ : ℕ → ℝ) (w : Fin (n + 1) → ℝ) :
    pairing n ℓ ((∑ i : Fin (n + 1), C (w i) * X ^ (i : ℕ)) ^ 2) =
      w ⬝ᵥ ((Matrix.of fun i j : Fin (n + 1) => ℓ (i + j)) *ᵥ w) := by
  have hsq : (∑ i : Fin (n + 1), C (w i) * X ^ (i : ℕ)) ^ 2 =
      ∑ i : Fin (n + 1), ∑ i' : Fin (n + 1), C (w i * w i') * X ^ ((i : ℕ) + i') := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [C_mul, pow_add]; ring
  rw [hsq, pairing]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  have hmem : (i : ℕ) + i' ∈ Finset.range (2 * n + 2) := by
    simp only [Finset.mem_range]; have := i.2; have := i'.2; omega
  rw [Finset.sum_ite_eq', ite_eq_left hmem]
  ring

/-- `ℓ ≠ 0` at the least `k ∈ K_0` with `λ_k ≠ 0`, so the Hankel matrix is not zero. -/
lemma hankel_ne_zero (β : ℝ) (hβ : β ≠ 0) (n : ℕ) (K0 : Finset ℕ) (hK : ∀ k ∈ K0, k ≤ 2 * n)
    (lam : ℕ → ℝ) (hlam : ∃ k ∈ K0, lam k ≠ 0) :
    ∃ i j : Fin (n + 1), ellOf β K0 lam (i + j) ≠ 0 := by
  classical
  have hne : (K0.filter fun k => lam k ≠ 0).Nonempty :=
    let ⟨k, hk, hl⟩ := hlam; ⟨k, Finset.mem_filter.2 ⟨hk, hl⟩⟩
  set k0 := (K0.filter fun k => lam k ≠ 0).min' hne
  obtain ⟨hk0, hl0⟩ := Finset.mem_filter.1 ((K0.filter fun k => lam k ≠ 0).min'_mem hne)
  have hmin : ∀ k ∈ K0, k < k0 → lam k = 0 := fun k hk hlt => by
    by_contra h
    exact absurd ((K0.filter fun k => lam k ≠ 0).min'_le k (Finset.mem_filter.2 ⟨hk, h⟩))
      (not_le.2 hlt)
  have hell : ellOf β K0 lam k0 = β * lam k0 := by
    unfold ellOf
    rw [ite_eq_left hk0]
    by_cases h : 0 < k0 ∧ k0 - 1 ∈ K0
    · rw [ite_eq_left h, hmin _ h.2 (by omega)]; ring
    · rw [ite_eq_right h]; ring
  have := hK k0 hk0
  refine ⟨⟨min k0 n, by omega⟩, ⟨k0 - min k0 n, by omega⟩, ?_⟩
  simp only
  rw [show min k0 n + (k0 - min k0 n) = k0 by omega, hell]
  exact mul_ne_zero hβ hl0

/-- A nonzero positive semidefinite matrix has positive trace. -/
lemma trace_pos {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosSemidef)
    (hne : ∃ i j, H i j ≠ 0) : 0 < ∑ i, H i i := by
  obtain ⟨i, j, hij⟩ := hne
  have hii : H i i ≠ 0 := fun h => hij (Novel.SharefFilipovicMaxFactorsProof.psd_zero hH i j h).1
  exact lt_of_lt_of_le (lt_of_le_of_ne hH.diag_nonneg (Ne.symm hii))
    (Finset.single_le_sum (f := fun k => H k k) (fun k _ => hH.diag_nonneg) (Finset.mem_univ i))

lemma X_pow_eq {n : ℕ} (i : Fin (n + 1)) :
    (X : ℝ[X]) ^ (i : ℕ) = ∑ i' : Fin (n + 1), C ((Pi.single i 1 : Fin (n + 1) → ℝ) i') * X ^ (i' : ℕ) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma poly_as_fin {n : ℕ} (q : ℝ[X]) (hq : q.natDegree ≤ n) :
    q = ∑ i : Fin (n + 1), C (q.coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [q.as_sum_range' (n + 1) (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i)]
  simp [C_mul_X_pow_eq_monomial]

/-- The forward direction: a solution `S ∈ U` rules out every such `λ`. -/
lemma forward_dir (β : ℝ) (hβ : 0 < β) (n : ℕ) (K0 : Finset ℕ) (r : ℕ → ℝ)
    (hK : ∀ k ∈ K0, k ≤ 2 * n) (S : ℝ[X]) (hdeg : S.natDegree ≤ 2 * n)
    (hpos : ∀ x : ℝ, 0 < S.eval x) (htop : 0 < S.coeff (2 * n)) (hS : ∀ k ∈ K0, tk β S k = r k)
    (lam : ℕ → ℝ) (hlam : ∃ k ∈ K0, lam k ≠ 0)
    (hH : (Matrix.of fun i j : Fin (n + 1) => ellOf β K0 lam (i + j)).PosSemidef)
    (hsum : ∑ k ∈ K0, lam k * r k ≤ 0) : False := by
  set ℓ := ellOf β K0 lam
  set H := Matrix.of fun i j : Fin (n + 1) => ℓ (i + j)
  let G : ℝ[X] := ∑ i : Fin (n + 1), (X ^ (i : ℕ)) ^ 2
  have hGc : ∀ j, G.coeff j = if Even j ∧ j ≤ 2 * n then 1 else 0 := fun j => by
    simp only [G, ← pow_mul, finsetSum_coeff, coeff_X_pow]
    by_cases h : Even j ∧ j ≤ 2 * n
    · rw [ite_eq_left h]
      obtain ⟨⟨k, hk⟩, hjn⟩ := h
      rw [Finset.sum_eq_single ⟨k, by omega⟩]
      · simp; omega
      · intro i _ hi; rw [ite_eq_right]; intro h2; exact hi (Fin.ext (by simp at h2 ⊢; omega))
      · simp
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      intro h2; exact h ⟨⟨i, by omega⟩, by have := i.2; omega⟩
  have hGd : G.natDegree = 2 * n := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_) ?_
    · rw [hGc, ite_eq_right]; intro h; exact absurd h.2 (by exact_mod_cast not_le.2 hj)
    · rw [hGc, ite_eq_left ⟨even_two_mul n, le_rfl⟩]; exact one_ne_zero
  have hGpos : ∀ x : ℝ, 0 < G.eval x := fun x => by
    simp only [G, eval_finsetSum, eval_pow, eval_X]
    exact lt_of_lt_of_le (by simp : (0:ℝ) < (x ^ ((0 : Fin (n + 1)) : ℕ)) ^ 2)
      (Finset.single_le_sum (f := fun i : Fin (n + 1) => (x ^ (i : ℕ)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ 0))
  have hS0 : S ≠ 0 := fun h => by rw [h, coeff_zero] at htop; exact lt_irrefl _ htop
  have hG0 : G ≠ 0 := fun h => by
    have := hGc (2 * n); rw [h, coeff_zero, ite_eq_left ⟨even_two_mul n, le_rfl⟩] at this
    exact zero_ne_one this
  have hSd : S.natDegree = 2 * n := natDegree_eq_of_le_of_coeff_ne_zero hdeg htop.ne'
  obtain ⟨ε, hε, hεb⟩ := Novel.CorrelatedFactorsGramProof.eps_bound S G hpos hGpos
    (by rw [degree_eq_natDegree hS0, degree_eq_natDegree hG0, hSd, hGd])
    (by rw [leadingCoeff, leadingCoeff, hSd, hGd, hGc, ite_eq_left ⟨even_two_mul n, le_rfl⟩];
        simpa using htop)
  set T := S - C ε * G
  have hT : ∀ x, 0 ≤ T.eval x := fun x => by
    simp only [T, eval_sub, eval_mul, eval_C]; linarith [hεb x]
  obtain ⟨m, q, hq⟩ := Novel.NonnegPolySOSProof.sos T hT
  have hTd : T.natDegree ≤ 2 * n :=
    (natDegree_sub_le _ _).trans (max_le hdeg ((natDegree_C_mul_le _ _).trans hGd.le))
  have hqd := Novel.CorrelatedFactorsGramProof.sos_deg q n (hq ▸ hTd)
  have hpT : 0 ≤ pairing n ℓ T := by
    rw [hq, pairing_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [poly_as_fin (q i) (hqd i), pairing_sq]
    exact hH.dotProduct_mulVec_nonneg _
  have hpG : 0 < pairing n ℓ G := by
    simp only [G]
    rw [pairing_sum]
    have e : ∀ i : Fin (n + 1), pairing n ℓ ((X ^ (i : ℕ)) ^ 2) = H i i := fun i => by
      rw [X_pow_eq i, pairing_sq]
      simp [dotProduct, mulVec, Pi.single_apply, H]
    simp only [e]
    obtain ⟨i, j, hij⟩ := hankel_ne_zero β hβ.ne' n K0 hK lam hlam
    exact trace_pos H hH ⟨i, j, hij⟩
  have hpS : pairing n ℓ S = pairing n ℓ T + ε * pairing n ℓ G := by
    rw [← pairing_smul, ← pairing_add]; simp [T]
  have hpS' : pairing n ℓ S = ∑ k ∈ K0, lam k * r k := by
    rw [← pair_tk β n K0 hK lam S]
    exact Finset.sum_congr rfl fun k hk => by rw [hS k hk]
  have : 0 < pairing n ℓ S := by rw [hpS]; nlinarith
  linarith

section Coeff
open Novel.CorrelatedFactorsReductionProof

variable (n : ℕ)

lemma poly1_add (v w : Fin (2 * n + 1) → ℝ) : poly1 (v + w) = poly1 v + poly1 w := by
  simp [poly1, C_add, add_mul, Finset.sum_add_distrib]

lemma poly1_smul (c : ℝ) (v : Fin (2 * n + 1) → ℝ) : poly1 (c • v) = C c * poly1 v := by
  simp [poly1, C_mul, Finset.mul_sum, mul_assoc]

lemma poly1_natDegree (v : Fin (2 * n + 1) → ℝ) : (poly1 v).natDegree ≤ 2 * n :=
  natDegree_sum_le_of_forall_le _ _ fun j _ =>
    (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; have := j.2; omega)

lemma poly1_last (v : Fin (2 * n + 1) → ℝ) : (poly1 v).coeff (2 * n) = v (Fin.last (2 * n)) := by
  rw [coeff_poly1]; simp [Fin.last]

/-- `t_k` as a linear functional on coefficient vectors. -/
noncomputable def tlin (β : ℝ) (k : ℕ) : (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun v := tk β (poly1 v) k
  map_add' v w := by simp only [tk, poly1_add, coeff_add]; ring
  map_smul' c v := by simp only [tk, poly1_smul, coeff_C_mul, smul_eq_mul, RingHom.id_apply]; ring

/-- `U`: positive on `ℝ` with positive top coefficient. -/
def Uset : Set (Fin (2 * n + 1) → ℝ) :=
  {v | (∀ x : ℝ, 0 < (poly1 v).eval x) ∧ 0 < v (Fin.last (2 * n))}

/-- `1 + x^{2n}` (or `1` when `n = 0`), as a coefficient vector. -/
def gvec : Fin (2 * n + 1) → ℝ := fun j => if (j : ℕ) = 0 ∨ (j : ℕ) = 2 * n then 1 else 0

lemma gvec_eval_ge (x : ℝ) : 1 ≤ (poly1 (gvec n)).eval x ∧ x ^ (2 * n) ≤ (poly1 (gvec n)).eval x := by
  rw [eval_poly1]
  have hnn : ∀ j : Fin (2 * n + 1), 0 ≤ gvec n j * x ^ (j : ℕ) := fun j => by
    unfold gvec
    split_ifs with h
    · rcases h with h | h
      · rw [h]; simp
      · rw [h, one_mul]; exact (even_two_mul n).pow_nonneg x
    · simp
  refine ⟨?_, ?_⟩
  · have := Finset.single_le_sum (f := fun j : Fin (2 * n + 1) => gvec n j * x ^ (j : ℕ))
      (fun j _ => hnn j) (Finset.mem_univ 0)
    simpa [gvec] using this
  · have := Finset.single_le_sum (f := fun j : Fin (2 * n + 1) => gvec n j * x ^ (j : ℕ))
      (fun j _ => hnn j) (Finset.mem_univ (Fin.last (2 * n)))
    simpa [gvec] using this

lemma gvec_mem : gvec n ∈ Uset n :=
  ⟨fun x => lt_of_lt_of_le one_pos (gvec_eval_ge n x).1, by simp [gvec]⟩

lemma pow_le_g (x : ℝ) (j : ℕ) (hj : j ≤ 2 * n) : |x| ^ j ≤ (poly1 (gvec n)).eval x := by
  obtain ⟨h1, h2⟩ := gvec_eval_ge n x
  rcases le_total |x| 1 with h | h
  · exact (pow_le_one₀ (abs_nonneg x) h).trans h1
  · calc |x| ^ j ≤ |x| ^ (2 * n) := pow_le_pow_right₀ h hj
      _ = x ^ (2 * n) := (even_two_mul n).pow_abs x
      _ ≤ _ := h2

lemma Uset_open : IsOpen (Uset n) := by
  rw [Metric.isOpen_iff]
  intro v hv
  set S := poly1 v
  set G := poly1 (gvec n)
  have hS0 : S ≠ 0 := fun h => by
    have h2 := hv.2
    rw [← poly1_last n v] at h2
    change 0 < S.coeff (2 * n) at h2
    rw [h, coeff_zero] at h2
    exact lt_irrefl _ h2
  have hSd : S.natDegree = 2 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero (poly1_natDegree n v) (by rw [poly1_last]; exact hv.2.ne')
  have hGl : G.coeff (2 * n) = 1 := by rw [poly1_last]; simp [gvec]
  have hGd : G.natDegree = 2 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero (poly1_natDegree n _) (by rw [hGl]; exact one_ne_zero)
  have hG0 : G ≠ 0 := fun h => by rw [h, coeff_zero] at hGl; exact zero_ne_one hGl
  obtain ⟨ε, hε, hεb⟩ := Novel.CorrelatedFactorsGramProof.eps_bound S G hv.1
    (fun x => lt_of_lt_of_le one_pos (gvec_eval_ge n x).1)
    (by rw [degree_eq_natDegree hS0, degree_eq_natDegree hG0, hSd, hGd])
    (by rw [leadingCoeff, leadingCoeff, hSd, hGd, hGl, poly1_last, div_one]; exact hv.2)
  set δ := min (ε / (2 * (2 * n + 1))) (v (Fin.last (2 * n)) / 2)
  have hδ : 0 < δ := lt_min (by positivity) (half_pos hv.2)
  refine ⟨δ, hδ, fun w hw => ⟨fun x => ?_, ?_⟩⟩
  · have hj : ∀ j, |w j - v j| < δ := fun j =>
      lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist w v j) hw
    have hdiff : (poly1 w).eval x = S.eval x + ∑ j, (w j - v j) * x ^ (j : ℕ) := by
      simp only [S, eval_poly1, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hbound : |∑ j, (w j - v j) * x ^ (j : ℕ)| ≤ (2 * n + 1) * δ * G.eval x := by
      calc |∑ j, (w j - v j) * x ^ (j : ℕ)| ≤ ∑ j : Fin (2 * n + 1), |(w j - v j) * x ^ (j : ℕ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin (2 * n + 1), δ * G.eval x := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_pow]
            exact mul_le_mul (hj j).le (pow_le_g n x j (by have := j.2; omega))
              (by positivity) hδ.le
        _ = (2 * n + 1) * δ * G.eval x := by simp; ring
    have hGp : 0 < G.eval x := lt_of_lt_of_le one_pos (gvec_eval_ge n x).1
    have hδε : (2 * n + 1) * δ ≤ ε / 2 := by
      have := min_le_left (ε / (2 * (2 * n + 1))) (v (Fin.last (2 * n)) / 2)
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (2 * n + 1))] at this
      nlinarith
    have := hεb x
    have hab := neg_abs_le (∑ j, (w j - v j) * x ^ (j : ℕ))
    rw [hdiff]
    nlinarith
  · have h1 : |w (Fin.last (2 * n)) - v (Fin.last (2 * n))| < δ :=
      lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist w v _) hw
    have h2 := min_le_right (ε / (2 * (2 * n + 1))) (v (Fin.last (2 * n)) / 2)
    have := neg_abs_le (w (Fin.last (2 * n)) - v (Fin.last (2 * n)))
    linarith

lemma Uset_convex : Convex ℝ (Uset n) := by
  intro v hv w hw a b ha hb hab
  refine ⟨fun x => ?_, ?_⟩
  · rw [poly1_add, poly1_smul, poly1_smul, eval_add, eval_mul, eval_mul, eval_C, eval_C]
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h, zero_add] at hab; rw [← h, hab]; simpa using hw.1 x
    · have := hv.1 x; have := hw.1 x; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h, zero_add] at hab; rw [← h, hab]; simpa using hw.2
    · have := hv.2; have := hw.2; positivity

lemma Uset_smul (c : ℝ) (hc : 0 < c) (v : Fin (2 * n + 1) → ℝ) (hv : v ∈ Uset n) :
    c • v ∈ Uset n :=
  ⟨fun x => by rw [poly1_smul, eval_mul, eval_C]; exact mul_pos hc (hv.1 x),
    by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hc hv.2⟩

end Coeff

section Backward
open Novel.CorrelatedFactorsReductionProof

/-- Every polynomial of degree at most `2n` is `poly1` of its coefficient vector. -/
lemma poly1_vec (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ 2 * n) :
    poly1 (fun j : Fin (2 * n + 1) => P.coeff j) = P :=
  (poly_as_fin P hP).symm

lemma q_natDegree (n : ℕ) (w : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), C (w i) * X ^ (i : ℕ)).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; have := i.2; omega)

/-- The backward direction: with no solution in `U`, separation gives `λ`. -/
lemma backward_dir (β : ℝ) (hβ : 0 < β) (n : ℕ) (K0 : Finset ℕ) (r : ℕ → ℝ)
    (hK : ∀ k ∈ K0, k ≤ 2 * n) (hcons : ∀ k ∈ K0, k + 1 ∉ K0)
    (hno : ¬ ∃ S : ℝ[X], S.natDegree ≤ 2 * n ∧ (∀ x : ℝ, 0 < S.eval x) ∧ 0 < S.coeff (2 * n) ∧
      ∀ k ∈ K0, tk β S k = r k) :
    ∃ lam : ℕ → ℝ, (∃ k ∈ K0, lam k ≠ 0) ∧
      (Matrix.of fun i j : Fin (n + 1) => ellOf β K0 lam (i + j)).PosSemidef ∧
      ∑ k ∈ K0, lam k * r k ≤ 0 := by
  classical
  set V : Set (Fin (2 * n + 1) → ℝ) := {v | ∀ k ∈ K0, tlin n β k v = r k}
  have hdisj : Disjoint (Uset n) V := Set.disjoint_left.2 fun v hU hV =>
    hno ⟨poly1 v, poly1_natDegree n v, hU.1, by rw [poly1_last]; exact hU.2, fun k hk => hV k hk⟩
  have hVc : Convex ℝ V := by
    intro v hv w hw a b _ _ hab k hk
    rw [map_add, map_smul, map_smul, hv k hk, hw k hk, smul_eq_mul, smul_eq_mul, ← add_mul, hab,
      one_mul]
  obtain ⟨f, u, hfU, hfV⟩ := geometric_hahn_banach_open (Uset_convex n) (Uset_open n) hVc hdisj
  let v0 : Fin (2 * n + 1) → ℝ := fun j => if (j : ℕ) ∈ K0 then r j / β else 0
  have hv0 : v0 ∈ V := fun k hk => by
    show tk β (poly1 v0) k = r k
    have hk2 := hK k hk
    have hk3 : k < 2 * n + 1 := by omega
    rw [tk, coeff_poly1, coeff_poly1]
    simp only [hk3, ↓reduceDIte]
    have h2 : (if h : k + 1 < 2 * n + 1 then v0 ⟨k + 1, h⟩ else 0) = 0 := by
      split_ifs <;> simp [v0, hcons k hk]
    rw [h2]
    simp only [v0, hk, ↓reduceIte]
    field_simp
    ring
  have hfle : ∀ a ∈ Uset n, f a ≤ 0 := fun a ha => by
    by_contra h
    push Not at h
    have := hfU _ (Uset_smul n ((|u| + 1) / f a) (by positivity) a ha)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne'] at this
    linarith [le_abs_self u]
  have hu : 0 ≤ u := by
    by_contra h
    push Not at h
    have hg := hfle _ (gvec_mem n)
    rcases eq_or_lt_of_le hg with h0 | h0
    · linarith [hfU _ (gvec_mem n)]
    · have := hfU _ (Uset_smul n (u / (2 * f (gvec n))) (div_pos_of_neg_of_neg h (by linarith))
        _ (gvec_mem n))
      rw [map_smul, smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc,
        div_mul_cancel_right₀ h0.ne] at this
      linarith
  have hW : ∀ w, (∀ k ∈ K0, tlin n β k w = 0) → f w = 0 := fun w hw => by
    by_contra h
    have hv : v0 + ((u - f v0 - 1) / f w) • w ∈ V := fun k hk => by
      rw [map_add, map_smul, hw k hk, smul_zero, add_zero]; exact hv0 k hk
    have := hfV _ hv
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ h] at this
    linarith
  let L : K0 → (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] ℝ := fun k => tlin n β k
  have hker : ⨅ k, LinearMap.ker (L k) ≤ LinearMap.ker (f : (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] ℝ) :=
    fun w hw => by
      rw [Submodule.mem_iInf] at hw
      exact hW w fun k hk => hw ⟨k, hk⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hker)
  let lam : ℕ → ℝ := fun k => if h : k ∈ K0 then -c ⟨k, h⟩ else 0
  have hφ : ∀ v, -f v = ∑ k ∈ K0, lam k * tlin n β k v := fun v => by
    have := congrArg (fun g : (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] ℝ => g v) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_coe] at this
    rw [← this, ← Finset.sum_neg_distrib,
      ← Finset.sum_coe_sort K0 (fun k => lam k * tlin n β k v)]
    exact Finset.sum_congr rfl fun k _ => by simp [lam, L, k.2]
  refine ⟨lam, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hf0 : ∀ v, f v = 0 := fun v => by
      have := hφ v
      rw [Finset.sum_eq_zero fun k hk => by rw [h k hk, zero_mul]] at this
      linarith
    have := hfU _ (gvec_mem n)
    have := hfV _ hv0
    rw [hf0] at *
    linarith
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
    · ext i j; simp [Matrix.conjTranspose_apply, add_comm]
    set q := ∑ i : Fin (n + 1), C (w i) * X ^ (i : ℕ)
    have hqd : q.natDegree ≤ n := q_natDegree n w
    have hq2d : (q ^ 2).natDegree ≤ 2 * n := natDegree_pow_le.trans (by omega)
    set vq : Fin (2 * n + 1) → ℝ := fun j => (q ^ 2).coeff j
    have hkey : star w ⬝ᵥ ((Matrix.of fun i j : Fin (n + 1) => ellOf β K0 lam (i + j)) *ᵥ w) =
        -f vq := by
      rw [star_trivial, ← pairing_sq, ← pair_tk β n K0 hK lam, hφ]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = lam k * tk β (poly1 vq) k
      rw [poly1_vec n _ hq2d]
    rw [hkey, neg_nonneg]
    by_contra h
    push Not at h
    have htop : 0 ≤ (q ^ 2).coeff (2 * n) := by
      rw [sq, show 2 * n = n + n by ring, coeff_mul_add_eq_of_natDegree_le hqd hqd]
      exact mul_self_nonneg _
    set ε := f vq / (2 * (|f (gvec n)| + 1))
    have hε : 0 < ε := by positivity
    have hmem : vq + ε • gvec n ∈ Uset n := by
      refine ⟨fun x => ?_, ?_⟩
      · rw [poly1_add, poly1_smul, poly1_vec n _ hq2d, eval_add, eval_mul, eval_C, eval_pow]
        have := lt_of_lt_of_le one_pos (gvec_eval_ge n x).1
        positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vq]
        have : gvec n (Fin.last (2 * n)) = 1 := by simp [gvec]
        rw [this, mul_one]
        simp only [Fin.val_last]
        linarith
    have := hfle _ hmem
    rw [map_add, map_smul, smul_eq_mul] at this
    have hb : ε * |f (gvec n)| < f vq := by
      have : ε * (2 * (|f (gvec n)| + 1)) = f vq := div_mul_cancel₀ _ (by positivity)
      nlinarith [abs_nonneg (f (gvec n))]
    nlinarith [neg_abs_le (f (gvec n))]
  · have := hφ v0
    rw [show ∑ k ∈ K0, lam k * tlin n β k v0 = ∑ k ∈ K0, lam k * r k from
      Finset.sum_congr rfl fun k hk => by rw [hv0 k hk]] at this
    linarith [hfV _ hv0]

end Backward

lemma hankel : hankelStatement := by
  intro β hβ n K0 r hK hcons
  constructor
  · rintro ⟨S, h1, h2, h3, h4⟩ ⟨lam, hlam, hH, hsum⟩
    exact forward_dir β hβ n K0 r hK S h1 h2 h3 h4 lam hlam hH hsum
  · intro hno
    by_contra hS
    exact hno (backward_dir β hβ n K0 r hK hcons hS)

theorem correlatedFactorsHankel : Standalone.CorrelatedFactorsHankel.statement := hankel

end Novel.CorrelatedFactorsHankelProof

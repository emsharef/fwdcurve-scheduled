import Standalone.SharefFilipovicMaxFactors
import Novel.SharefFilipovicResidualProof
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef

open Set Polynomial Filter Matrix
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicMaxFactors
namespace Novel.SharefFilipovicMaxFactorsProof
open Novel.SharefFilipovicResidualProof

/-- The antiderivative data of `X^ν e^{−lx}`: `λ q − q' = X^ν` forces `deg q = ν`, leading `1/λ`. -/
lemma anti_deg (l : ℝ) (hl : l ≠ 0) (ν : ℕ) (q : ℝ[X]) (hq : C l * q - derivative q = X ^ ν) :
    q.natDegree = ν ∧ q.leadingCoeff = l⁻¹ := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp only [mul_zero, derivative_zero, sub_zero] at hq
    exact pow_ne_zero ν X_ne_zero hq.symm
  have hlc : ∀ p : ℝ[X], p = C l * q → p.natDegree = ν → p.leadingCoeff = 1 →
      q.natDegree = ν ∧ q.leadingCoeff = l⁻¹ := by
    intro p hp hd hc
    rw [hp, natDegree_C_mul hl] at hd
    rw [hp, leadingCoeff_mul, leadingCoeff_C] at hc
    exact ⟨hd, by field_simp; linarith⟩
  by_cases hd : q.natDegree = 0
  · have hder : derivative q = 0 := derivative_of_natDegree_zero hd
    rw [hder, sub_zero] at hq
    exact hlc _ rfl (by rw [hq, natDegree_X_pow]) (by rw [hq, leadingCoeff_X_pow])
  · have hlt : (derivative q).natDegree < (C l * q).natDegree := by
      rw [natDegree_C_mul hl]; exact natDegree_derivative_lt hd
    have e1 := natDegree_sub_eq_left_of_natDegree_lt hlt
    have e2 : (C l * q - derivative q).leadingCoeff = (C l * q).leadingCoeff :=
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hlt)
    rw [hq] at e1 e2
    exact hlc _ rfl (by rw [← e1, natDegree_X_pow]) (by rw [← e2, leadingCoeff_X_pow])

/-- `∫_0^x p(η) e^{−lη} dη = q(0) − q(x) e^{−lx}` when `λ q − q' = p`. -/
lemma int_of_anti (p q : ℝ[X]) (l : ℝ) (hq : C l * q - derivative q = p) (x : ℝ) :
    ∫ η in (0:ℝ)..x, p.eval η * Real.exp (-l * η) = q.eval 0 - q.eval x * Real.exp (-l * x) := by
  have hH : ∀ y, HasDerivAt (fun y => -(q.eval y * Real.exp (-l * y)))
      (p.eval y * Real.exp (-l * y)) y := fun y => by
    have := (hd_pe q l y).neg
    convert this using 1
    rw [← hq]
    simp only [eval_sub, eval_mul, eval_C]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hH y)
    ((p.continuous.mul (by fun_prop)).intervalIntegrable _ _)]
  simp
  ring

/-- A zero diagonal entry of a positive semidefinite matrix empties its row and column. -/
lemma psd_zero {ι : Type*} [Fintype ι] {a : Matrix ι ι ℝ} (ha : a.PosSemidef) (i j : ι)
    (hi : a i i = 0) : a i j = 0 ∧ a j i = 0 := by
  have hs : a j i = a i j := by
    have := congrFun (congrFun ha.1.eq i) j
    simpa [conjTranspose_apply] using this
  have hq : ∀ t : ℝ, 0 ≤ 2 * a i j * t + a j j := fun t => by
    have := (ha.submatrix ![i, j]).dotProduct_mulVec_nonneg ![t, 1]
    simp [dotProduct, mulVec, Fin.sum_univ_two, submatrix, hi, hs] at this
    linarith
  suffices a i j = 0 from ⟨this, hs ▸ this⟩
  by_contra h
  have := hq (-(a j j + 1) / (2 * a i j))
  field_simp at this
  linarith

/-- The top coefficient: if `∑_{s,t} a_{st} X^{d_s} q_t + E = 0` with `deg q_t = d_t`, a common
leading coefficient `c ≠ 0`, `d` injective and zero diagonal entries emptying rows and columns,
then at the largest `d_{t₀}` with `a_{t₀t₀} ≠ 0`, `E` has a nonzero coefficient at `X^{2d_{t₀}}`. -/
lemma key {T : Type*} [Fintype T] [DecidableEq T] (d : T → ℕ) (hd : Function.Injective d)
    (a : T → T → ℝ) (hz : ∀ s t, a s s = 0 → a s t = 0 ∧ a t s = 0) (q : T → ℝ[X]) (c : ℝ)
    (hc : c ≠ 0) (hq : ∀ t, (q t).natDegree = d t ∧ (q t).leadingCoeff = c) (E : ℝ[X])
    (h : ∑ s, ∑ t, C (a s t) * X ^ d s * q t + E = 0) (t0 : T) (h0 : a t0 t0 ≠ 0)
    (hmax : ∀ t, a t t ≠ 0 → d t ≤ d t0) : E.coeff (2 * d t0) ≠ 0 := by
  have hterm : ∀ s t, (C (a s t) * X ^ d s * q t).coeff (2 * d t0) =
      if s = t0 ∧ t = t0 then a t0 t0 * c else 0 := by
    intro s t
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases hst : s = t0 ∧ t = t0
    · obtain ⟨hs, ht⟩ := hst
      rw [hs, ht, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩),
        show 2 * d t0 - d t0 = (q t0).natDegree by rw [(hq t0).1]; omega, ← leadingCoeff, (hq t0).2]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hst)]
    by_cases hzero : a s t = 0
    · rw [hzero, zero_mul]
    have hs : d s ≤ d t0 := hmax s fun h => hzero (hz s t h).1
    have ht : d t ≤ d t0 := hmax t fun h => hzero (hz t s h).2
    have hlt : d s + d t < 2 * d t0 := by
      rcases lt_or_eq_of_le hs with h1 | h1
      · omega
      rcases lt_or_eq_of_le ht with h2 | h2
      · omega
      exact absurd ⟨hd h1, hd h2⟩ hst
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), coeff_eq_zero_of_natDegree_lt (by rw [(hq t).1]; omega), mul_zero]
  have hcoef := congrArg (fun p => p.coeff (2 * d t0)) h
  simp only [coeff_add, finsetSum_coeff, coeff_zero, hterm, ite_and] at hcoef
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero] at hcoef
  intro hE
  rw [hE, add_zero] at hcoef
  exact mul_ne_zero h0 hc hcoef

/-- The top coefficient at the largest index with a nonzero diagonal entry. -/
lemma key' {T : Type*} [Fintype T] [DecidableEq T] (d : T → ℕ) (hd : Function.Injective d)
    (a : T → T → ℝ) (hz : ∀ s t, a s s = 0 → a s t = 0 ∧ a t s = 0) (q : T → ℝ[X]) (c : ℝ)
    (hc : c ≠ 0) (hq : ∀ t, (q t).natDegree = d t ∧ (q t).leadingCoeff = c) (E : ℝ[X])
    (h : ∑ s, ∑ t, C (a s t) * X ^ d s * q t + E = 0) (t : T) (ht : a t t ≠ 0) :
    ∃ t0, d t ≤ d t0 ∧ E.coeff (2 * d t0) ≠ 0 := by
  obtain ⟨t0, ht0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun t => a t t ≠ 0) d
    ⟨t, by simpa using ht⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht0 hmax
  exact ⟨t0, hmax t ht, key d hd a hz q c hc hq E h t0 ht0 hmax⟩

lemma maxFactors : maxFactorsStatement := by
  intro β hβ n₁ n₂ z b a ha hres
  classical
  have hall : ∀ x, residual034 β n₁ n₂ z b a x = 0 :=
    residual β hβ n₁ n₂ z b a 0 0 1 one_pos fun x hx => by rw [eval_zero]; exact hres x hx.1.le
  -- the rate `λ_j = (k_j + 1) β` of each basis function, and the antiderivative polynomials
  let l : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ := fun j => (((kIdx j : ℕ) : ℝ) + 1) * β
  have hl : ∀ j, l j ≠ 0 := fun j => by simp only [l]; positivity
  choose q hq using fun j => anti (l j) (hl j) _ (pIdx j) le_rfl
  have hphi : ∀ j x, phi034 β n₁ n₂ j x = (pIdx j).eval x * Real.exp (-l j * x) := fun j x => by
    rw [phi_eq]; congr 2; simp only [l]; ring
  have hint : ∀ j x, ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η =
      (q j).eval 0 - (q j).eval x * Real.exp (-l j * x) := fun j x => by
    rw [← int_of_anti (pIdx j) (q j) (l j) (hq j) x]
    exact intervalIntegral.integral_congr fun η _ => hphi j η
  have hder : ∀ x, deriv (F034 β n₁ n₂ z) x = ∑ i, z i *
      ((derivative (pIdx i) - C (l i) * pIdx i).eval x * Real.exp (-l i * x)) := fun x => by
    have := HasDerivAt.sum (u := Finset.univ) fun i _ => (hd_pe (pIdx i) (l i) x).const_mul (z i)
    rw [show F034 β n₁ n₂ z = ∑ i ∈ Finset.univ,
        fun y => z i * ((pIdx i).eval y * Real.exp (-l i * y)) from by
      funext y; simp [F034, Finset.sum_apply, hphi]]
    exact this.deriv
  -- the explicit decomposition `R(x) = ∑_k Q_k(x) e^{−(k+1)βx}`
  let A : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ[X] := fun i =>
    C (z i * l i + b i - ∑ j, a i j * (q j).eval 0) * pIdx i - C (z i) * derivative (pIdx i)
  let Q : Fin 4 → ℝ[X] := fun k => ∑ i, (if (k : ℕ) = kIdx i then A i else 0) +
    ∑ i, ∑ j, (if (k : ℕ) = kIdx i + kIdx j + 1 then C (a i j) * pIdx i * q j else 0)
  have hsum1 : ∀ (m : ℕ) (hm : m < 4) (x : ℝ) (p : ℝ[X]),
      ∑ k : Fin 4, (if (k : ℕ) = m then p else 0).eval x * Real.exp (-(((k : ℕ) : ℝ) + 1) * β * x) =
        p.eval x * Real.exp (-((m : ℝ) + 1) * β * x) := by
    intro m hm x p
    rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro k _ hk
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hk (Fin.ext h))]
      simp
    · simp
  have hEi : ∀ i x, Real.exp (-(((kIdx i : ℕ) : ℝ) + 1) * β * x) = Real.exp (-l i * x) :=
    fun i x => by congr 1; simp only [l]; ring
  have hEij : ∀ i j x, Real.exp (-(((kIdx i + kIdx j + 1 : ℕ) : ℝ) + 1) * β * x) =
      Real.exp (-l i * x) * Real.exp (-l j * x) := fun i j x => by
    rw [← Real.exp_add]; congr 1; simp only [l]; push_cast; ring
  have hdec : ∀ x, residual034 β n₁ n₂ z b a x =
      ∑ k : Fin 4, (Q k).eval x * Real.exp (-(((k : ℕ) : ℝ) + 1) * β * x) := by
    intro x
    have e1 : ∑ k : Fin 4, (∑ i, (if (k : ℕ) = kIdx i then A i else 0)).eval x *
        Real.exp (-(((k : ℕ) : ℝ) + 1) * β * x) = ∑ i, (A i).eval x * Real.exp (-l i * x) := by
      simp only [eval_finsetSum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsum1 _ (by have := kIdx_le i; omega), hEi]
    have e2 : ∑ k : Fin 4, (∑ i, ∑ j, (if (k : ℕ) = kIdx i + kIdx j + 1 then
        C (a i j) * pIdx i * q j else 0)).eval x * Real.exp (-(((k : ℕ) : ℝ) + 1) * β * x) =
        ∑ i, ∑ j, (C (a i j) * pIdx i * q j).eval x *
          (Real.exp (-l i * x) * Real.exp (-l j * x)) := by
      simp only [eval_finsetSum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsum1 _ (by have := kIdx_le i; have := kIdx_le j; omega), hEij]
    simp only [Q, eval_add, add_mul, Finset.sum_add_distrib]
    rw [e1, e2]
    unfold residual034
    rw [hder]
    simp only [hint]
    simp only [hphi]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj : ∑ j, a i j * ((pIdx i).eval x * Real.exp (-l i * x)) *
        ((q j).eval 0 - (q j).eval x * Real.exp (-l j * x)) =
        (∑ j, a i j * (q j).eval 0) * ((pIdx i).eval x * Real.exp (-l i * x)) -
          ∑ j, (C (a i j) * pIdx i * q j).eval x * (Real.exp (-l i * x) * Real.exp (-l j * x)) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [eval_mul, eval_C]
      ring
    rw [hj]
    simp only [A, eval_sub, eval_mul, eval_C]
    ring
  have hQ0 := (Novel.SharefFilipovicIndependenceProof.independence β hβ 4 Q 0 0 1 one_pos
    fun x _ => by rw [← hdec, hall, eval_zero]).1
  have hz : ∀ s t, a s s = 0 → a s t = 0 ∧ a t s = 0 := fun s t h => psd_zero ha s t h
  have hqd : ∀ j, (q j).natDegree = (pIdx j).natDegree ∧ (q j).leadingCoeff = (l j)⁻¹ := by
    intro j
    cases j <;> simpa [pIdx] using anti_deg _ (hl _) _ _ (hq _)
  -- the coefficient of `e^{−4βx}`: every `e^{−2βx}` entry of `a` vanishes
  have hR : ∀ μ, a (Sum.inr μ) (Sum.inr μ) = 0 := by
    have h3 := hQ0 3
    simp only [Q, Fintype.sum_sum_type, kIdx, pIdx, Sum.elim_inl, Sum.elim_inr] at h3
    norm_num at h3
    intro μ
    by_contra hμ
    obtain ⟨t0, -, hE⟩ := key' (T := Fin (n₂ + 1)) Fin.val Fin.val_injective
      (fun μ ν => a (Sum.inr μ) (Sum.inr ν)) (fun s t h => hz _ _ h) (fun ν => q (Sum.inr ν))
      (l (Sum.inr 0))⁻¹ (inv_ne_zero (hl _)) (fun ν => by simpa [pIdx, l, kIdx] using hqd (Sum.inr ν))
      0 (by simpa using h3) μ hμ
    exact hE (coeff_zero _)
  -- the coefficient of `e^{−2βx}`: a nonzero `e^{−βx}` diagonal entry has `2μ ≤ n₂`
  have hL : ∀ μ, a (Sum.inl μ) (Sum.inl μ) ≠ 0 → 2 * (μ : ℕ) ≤ n₂ := by
    have h1 := hQ0 1
    simp only [Q, Fintype.sum_sum_type, kIdx, pIdx, Sum.elim_inl, Sum.elim_inr] at h1
    norm_num at h1
    set E := ∑ ν : Fin (n₂ + 1), A (Sum.inr ν)
    have hE : E.natDegree ≤ n₂ := by
      refine natDegree_sum_le_of_forall_le _ _ fun ν _ => ?_
      have hp : (pIdx (Sum.inr ν : Fin (n₁ + 1) ⊕ Fin (n₂ + 1))).natDegree ≤ n₂ := by
        simp [pIdx]; omega
      exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hp)
        ((natDegree_C_mul_le _ _).trans ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hp))))
    intro μ hμ
    obtain ⟨t0, hle, hc⟩ := key' (T := Fin (n₁ + 1)) Fin.val Fin.val_injective
      (fun μ ν => a (Sum.inl μ) (Sum.inl ν)) (fun s t h => hz _ _ h) (fun ν => q (Sum.inl ν))
      (l (Sum.inl 0))⁻¹ (inv_ne_zero (hl _)) (fun ν => by simpa [pIdx, l, kIdx] using hqd (Sum.inl ν))
      E (by linear_combination h1) μ hμ
    have := le_natDegree_of_ne_zero hc
    omega
  intro i j hij
  have hii : a i i ≠ 0 := fun h => hij (hz i j h).1
  have hjj : a j j ≠ 0 := fun h => hij (hz j i h).2
  rcases i with μ | μ
  · rcases j with ν | ν
    · exact ⟨μ, ν, rfl, rfl, by have := hL μ hii; omega, by have := hL ν hjj; omega⟩
    · exact absurd (hR ν) hjj
  · exact absurd (hR μ) hii

theorem sharefFilipovicMaxFactors : Standalone.SharefFilipovicMaxFactors.statement := maxFactors

end Novel.SharefFilipovicMaxFactorsProof

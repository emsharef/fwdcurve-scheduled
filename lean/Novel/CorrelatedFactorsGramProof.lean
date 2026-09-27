import Standalone.CorrelatedFactorsGram
import Novel.CorrelatedFactorsReductionProof
import Novel.NonnegPolySOSProof
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

open Polynomial Filter Topology Set Matrix
open Standalone.CorrelatedFactorsReduction Standalone.CorrelatedFactorsGram
namespace Novel.CorrelatedFactorsGramProof
open Novel.CorrelatedFactorsReductionProof

lemma Pnu_coeff_self (β : ℝ) (ν : ℕ) : (Pnu β ν).coeff ν = 1 / β := by
  rw [Pnu_coeff, ite_eq_left (le_refl _), Nat.sub_self, zero_add, pow_one,
    div_self (by exact_mod_cast Nat.factorial_ne_zero ν)]

lemma Pnu_natDegree_eq (β : ℝ) (hβ : β ≠ 0) (ν : ℕ) : (Pnu β ν).natDegree = ν :=
  natDegree_eq_of_le_of_coeff_ne_zero (Pnu_natDegree β ν) (by rw [Pnu_coeff_self]; simpa using hβ)

lemma Pnu_zero (β : ℝ) : Pnu β 0 = C (1 / β) := by
  simp [Pnu]

variable {n : ℕ}

lemma eval_SAn (β : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : ℝ) :
    (SAn β n A).eval x =
      (fun ν : Fin (n + 1) => (Pnu β ν).eval x) ⬝ᵥ (A *ᵥ fun ν => (Pnu β ν).eval x) := by
  simp only [SAn, eval_finsetSum, eval_mul, eval_C, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

lemma SAn_natDegree (β : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (SAn β n A).natDegree ≤ 2 * n := by
  refine natDegree_sum_le_of_forall_le _ _ fun μ _ => natDegree_sum_le_of_forall_le _ _ fun ν _ => ?_
  refine (natDegree_mul_le.trans (add_le_add (natDegree_C_mul_le _ _) (Pnu_natDegree β ν))).trans ?_
  have := Pnu_natDegree β μ
  omega

lemma SAn_top (β : ℝ) (hβ : β ≠ 0) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (SAn β n A).coeff (2 * n) = A (Fin.last n) (Fin.last n) * (1 / β) ^ 2 := by
  have hterm : ∀ μ ν : Fin (n + 1), (C (A μ ν) * Pnu β μ * Pnu β ν).coeff (2 * n) =
      if μ = Fin.last n ∧ ν = Fin.last n then A μ ν * (1 / β) ^ 2 else 0 := by
    intro μ ν
    rw [mul_assoc, coeff_C_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [show 2 * n = (Pnu β n).natDegree + (Pnu β n).natDegree by
        rw [Pnu_natDegree_eq β hβ]; omega]
      simp only [Fin.val_last]
      rw [coeff_mul_degree_add_degree, leadingCoeff, Pnu_natDegree_eq β hβ, Pnu_coeff_self]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
      refine lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (Pnu_natDegree β μ)
        (Pnu_natDegree β ν))) ?_
      have hμ := μ.2
      have hν := ν.2
      by_contra hc
      exact h ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
  simp only [SAn, finsetSum_coeff, hterm]
  rw [Finset.sum_eq_single (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro ν _ hν; rw [ite_eq_right (fun h => hν h.2)]
  · simp
  · intro μ _ hμ; exact Finset.sum_eq_zero fun ν _ => ite_eq_right (fun h => hμ h.1)
  · simp

lemma forward (β : ℝ) (hβ : 0 < β) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    (SAn β n A).natDegree ≤ 2 * n ∧ (∀ x : ℝ, 0 < (SAn β n A).eval x) ∧
      0 < (SAn β n A).coeff (2 * n) := by
  refine ⟨SAn_natDegree β A, fun x => ?_, ?_⟩
  · rw [eval_SAn]
    have hv : (fun ν : Fin (n + 1) => (Pnu β ν).eval x) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp only [Fin.val_zero, Pnu_zero, eval_C, Pi.zero_apply] at this
      exact (one_div_ne_zero hβ.ne') this
    simpa using hA.dotProduct_mulVec_pos hv
  · rw [SAn_top β hβ.ne']
    exact mul_pos hA.diag_pos (by positivity)

/-- In a sum of squares the leading terms do not cancel. -/
lemma sos_deg {m : ℕ} (q : Fin m → ℝ[X]) (N : ℕ) (h : (∑ i, q i ^ 2).natDegree ≤ 2 * N) :
    ∀ i, (q i).natDegree ≤ N := by
  by_contra hc
  push Not at hc
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i, Finset.mem_univ _⟩
    (fun k => (q k).natDegree)
  set d := Finset.univ.sup fun k => (q k).natDegree
  have hid : (q i).natDegree ≤ d := Finset.le_sup (f := fun k => (q k).natDegree) (Finset.mem_univ i)
  have hterm : ∀ k, 0 ≤ (q k ^ 2).coeff (2 * d) := fun k => by
    have hk : (q k).natDegree ≤ d := Finset.le_sup (f := fun k => (q k).natDegree) (Finset.mem_univ k)
    rcases lt_or_eq_of_le hk with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt]
      exact lt_of_le_of_lt natDegree_pow_le (by omega)
    · rw [sq, ← heq, two_mul, coeff_mul_degree_add_degree]
      exact mul_self_nonneg _
  have hjpos : 0 < (q j ^ 2).coeff (2 * d) := by
    have hq0 : q j ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hj; omega
    rw [sq, hj, two_mul, coeff_mul_degree_add_degree]
    exact mul_self_pos.2 (leadingCoeff_ne_zero.2 hq0)
  have hsum : 0 < (∑ k, q k ^ 2).coeff (2 * d) := by
    rw [finsetSum_coeff]
    exact lt_of_lt_of_le hjpos (Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j))
  have := le_natDegree_of_ne_zero hsum.ne'
  omega

/-- The `P_ν` span the polynomials of degree at most `n`. -/
lemma basis (β : ℝ) (hβ : β ≠ 0) : ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n →
    ∃ v : Fin (n + 1) → ℝ, q = ∑ ν : Fin (n + 1), C (v ν) * Pnu β ν := by
  intro n
  induction n with
  | zero =>
    intro q hq
    refine ⟨fun _ => β * q.coeff 0, ?_⟩
    conv_lhs => rw [eq_C_of_natDegree_le_zero hq]
    rw [Fin.sum_univ_one, Fin.val_zero, Pnu_zero, ← C_mul]
    congr 1
    field_simp
  | succ n ih =>
    intro q hq
    set c := β * q.coeff (n + 1)
    have hr : (q - C c * Pnu β (n + 1)).natDegree ≤ n := by
      refine natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_
      rw [coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt (by exact_mod_cast hk) : n + 1 ≤ k) with h | h
      · subst h
        rw [Pnu_coeff_self]
        simp only [c]
        field_simp
        ring
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Pnu_natDegree β (n + 1)) h)]
        ring
    obtain ⟨v', hv'⟩ := ih _ hr
    refine ⟨Fin.snoc v' c, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [← hv']
    ring

/-- `G = ∑_ν P_ν²` is positive on `ℝ`. -/
lemma G_pos (β : ℝ) (hβ : β ≠ 0) (x : ℝ) :
    0 < (SAn β n (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).eval x := by
  rw [eval_SAn]
  simp only [Matrix.one_mulVec, dotProduct]
  have h0 : 0 < (Pnu β (0 : Fin (n + 1))).eval x * (Pnu β (0 : Fin (n + 1))).eval x := by
    simp only [Fin.val_zero, Pnu_zero, eval_C]
    exact mul_self_pos.2 (one_div_ne_zero hβ)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum
    (f := fun k : Fin (n + 1) => (Pnu β k).eval x * (Pnu β k).eval x)
    (fun k _ => mul_self_nonneg _) (Finset.mem_univ (0 : Fin (n + 1))))

/-- A positive polynomial dominates `ε` times another positive one of the same degree. -/
lemma eps_bound (S G : ℝ[X]) (hS : ∀ x, 0 < S.eval x) (hG : ∀ x, 0 < G.eval x)
    (hdeg : S.degree = G.degree) (hlc : 0 < S.leadingCoeff / G.leadingCoeff) :
    ∃ ε > 0, ∀ x, ε * G.eval x ≤ S.eval x := by
  set L := S.leadingCoeff / G.leadingCoeff
  let f : ℝ → ℝ := fun x => S.eval x / G.eval x
  have hf : Continuous f := S.continuous.div G.continuous fun x => (hG x).ne'
  have htop := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq S G hdeg
  have hbot := Polynomial.div_tendsto_atBot_leadingCoeff_div_of_degree_eq S G hdeg
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (htop.eventually (lt_mem_nhds (half_lt_self hlc)))
  obtain ⟨R₂, hR₂⟩ := eventually_atBot.1 (hbot.eventually (lt_mem_nhds (half_lt_self hlc)))
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (min_le_max : min R₂ R₁ ≤ max R₂ R₁)) hf.continuousOn
  have hm : 0 < f x₀ := div_pos (hS x₀) (hG x₀)
  refine ⟨min (L / 2) (f x₀), lt_min (half_pos hlc) hm, fun x => ?_⟩
  have hfx : min (L / 2) (f x₀) ≤ f x := by
    by_cases h1 : R₁ ≤ x
    · exact (min_le_left _ _).trans (hR₁ x h1).le
    by_cases h2 : x ≤ R₂
    · exact (min_le_left _ _).trans (hR₂ x h2).le
    push Not at h1 h2
    exact (min_le_right _ _).trans (hmin ⟨by
      exact (min_le_left _ _).trans h2.le, by exact h1.le.trans (le_max_right _ _)⟩)
  have := (le_div_iff₀ (hG x)).1 hfx
  linarith

lemma SAn_add (β : ℝ) (A₁ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    SAn β n (A₁ + A₂) = SAn β n A₁ + SAn β n A₂ := by
  simp only [SAn, Matrix.add_apply, C_add, add_mul, Finset.sum_add_distrib]

lemma SAn_smul (β c : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    SAn β n (c • A) = C c * SAn β n A := by
  simp only [SAn, Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]

lemma backward (β : ℝ) (hβ : 0 < β) (S : ℝ[X]) (hdeg : S.natDegree ≤ 2 * n)
    (hpos : ∀ x : ℝ, 0 < S.eval x) (htop : 0 < S.coeff (2 * n)) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, A.PosDef ∧ S = SAn β n A := by
  have hβ0 : β ≠ 0 := hβ.ne'
  set G := SAn β n (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  have hGtop : G.coeff (2 * n) = (1 / β) ^ 2 := by
    rw [SAn_top β hβ0]; simp
  have hSd : S.natDegree = 2 * n := natDegree_eq_of_le_of_coeff_ne_zero hdeg htop.ne'
  have hGd : G.natDegree = 2 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero (SAn_natDegree β _) (by rw [hGtop]; positivity)
  have hS0 : S ≠ 0 := fun h => by rw [h, coeff_zero] at htop; exact lt_irrefl _ htop
  have hG0 : G ≠ 0 := by
    intro h
    have h2 : G.coeff (2 * n) = 0 := by rw [h, coeff_zero]
    rw [hGtop] at h2
    exact (pow_pos (one_div_pos.2 hβ) 2).ne' h2
  have hdegeq : S.degree = G.degree := by
    rw [degree_eq_natDegree hS0, degree_eq_natDegree hG0, hSd, hGd]
  have hlc : 0 < S.leadingCoeff / G.leadingCoeff := by
    rw [leadingCoeff, leadingCoeff, hSd, hGd, hGtop]
    positivity
  obtain ⟨ε, hε, hεb⟩ := eps_bound S G hpos (G_pos β hβ0) hdegeq hlc
  set T := S - C ε * G
  have hT : ∀ x, 0 ≤ T.eval x := fun x => by
    simp only [T, eval_sub, eval_mul, eval_C]; linarith [hεb x]
  obtain ⟨m, q, hq⟩ := Novel.NonnegPolySOSProof.sos T hT
  have hTd : T.natDegree ≤ 2 * n :=
    (natDegree_sub_le _ _).trans (max_le hdeg ((natDegree_C_mul_le _ _).trans (hGd ▸ le_rfl)))
  have hqd := sos_deg q n (hq ▸ hTd)
  choose v hv using fun i => basis β hβ0 n (q i) (hqd i)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun μ ν => ∑ i, v i μ * v i ν
  have hB : B.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.of fun i ν => v i ν)
    convert h using 1
    ext μ ν
    simp [B, Matrix.mul_apply]
  have hTB : T = SAn β n B := by
    rw [hq]
    have hi : ∀ i, q i ^ 2 = ∑ μ : Fin (n + 1), ∑ ν : Fin (n + 1),
        C (v i μ * v i ν) * Pnu β μ * Pnu β ν := fun i => by
      rw [hv i, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [C_mul]; ring
    unfold SAn
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [B, map_sum, Finset.sum_mul]
  refine ⟨B + ε • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hε), ?_⟩
  rw [SAn_add, SAn_smul, ← hTB]
  simp only [T, G]
  ring

lemma gram : gramStatement := by
  intro β hβ n S
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact forward β hβ A hA
  · rintro ⟨h1, h2, h3⟩
    exact backward β hβ S h1 h2 h3

theorem correlatedFactorsGram : Standalone.CorrelatedFactorsGram.statement := gram

end Novel.CorrelatedFactorsGramProof

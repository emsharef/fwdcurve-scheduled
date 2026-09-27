import Standalone.CorrelatedFactorsSmall
import Novel.CorrelatedFactorsExistsProof
import Mathlib.Tactic.ComputeDegree

open Polynomial
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsSmall
namespace Novel.CorrelatedFactorsSmallProof

/-- A polynomial of degree at most 2 evaluates as `s₀ + s₁ x + s₂ x²`. -/
lemma eval_two (S : ℝ[X]) (h : S.natDegree ≤ 2) (x : ℝ) :
    S.eval x = S.coeff 0 + S.coeff 1 * x + S.coeff 2 * x ^ 2 := by
  rw [eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]

lemma zero : zeroStatement := by
  intro β hβ n₁ z hz0
  rw [Solvable, Novel.CorrelatedFactorsExistsProof.exists_ β hβ n₁ 1 (by omega) z]
  have hc : c2 z (0 + 1) = z (Sum.inr 1) := by simp [c2]
  constructor
  · rintro ⟨S, hdeg, -, htop, hk⟩
    have h := hk 0 (by simp) hz0
    have hS1 : S.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hdeg; omega)
    simp only [Fin.val_zero, tk, hS1, Nat.cast_zero, hc] at h
    norm_num at htop
    nlinarith
  · intro hz1
    refine ⟨C (z (Sum.inr 1) / β), by simp, fun x => by simpa using div_pos hz1 hβ,
      by simpa using div_pos hz1 hβ, fun k hk _ => ?_⟩
    have hk0 : k = 0 := Fin.ext (by simpa using hk)
    subst hk0
    simp only [Fin.val_zero, tk, Nat.cast_zero, hc, coeff_C]
    simp
    field_simp

lemma one : oneStatement := by
  intro β hβ n₁ hn z hz2 hz1
  rw [Solvable, Novel.CorrelatedFactorsExistsProof.exists_ β hβ n₁ 3 (by omega) z]
  have h32 : 2 * (3 / 2) = 2 := by norm_num
  have hc1 : c2 z (0 + 1) = z (Sum.inr 1) := by simp [c2]
  have hc3 : c2 z (2 + 1) = z (Sum.inr 3) := by simp [c2]
  constructor
  · rintro ⟨S, hdeg, hpos, htop, hk⟩
    rw [h32] at hdeg htop
    have hS3 : S.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 := hk 2 (by simp) hz2
    simp only [tk, hS3, hc3, show ((2 : Fin (3 + 1)) : ℕ) = 2 from rfl] at h2
    push_cast at h2
    have hz3 : 0 < z (Sum.inr 3) := by nlinarith
    refine ⟨hz3, fun hz0 => ?_⟩
    have h0 := hk 0 (by simp) hz0
    simp only [tk, hc1, Fin.val_zero, Nat.cast_zero] at h0
    set s0 := S.coeff 0
    set s1 := S.coeff 1
    set s2 := S.coeff 2
    have he := hpos (-s1 / (2 * s2))
    rw [eval_two S hdeg] at he
    have hdisc : 0 < 4 * s0 * s2 - s1 ^ 2 := by
      have : 4 * s2 * (s0 + s1 * (-s1 / (2 * s2)) + s2 * (-s1 / (2 * s2)) ^ 2) =
          4 * s0 * s2 - s1 ^ 2 := by field_simp; ring
      rw [← this]; positivity
    have key : s2 * (3 * z (Sum.inr 3) + 4 * β ^ 2 * z (Sum.inr 1)) =
        β * (s2 - β * s1) ^ 2 + β ^ 3 * (4 * s0 * s2 - s1 ^ 2) := by
      rw [show 3 * z (Sum.inr 3) = β * s2 by linarith,
        show z (Sum.inr 1) = β * s0 - s1 / 2 by linarith]; ring
    have : 0 < s2 * (3 * z (Sum.inr 3) + 4 * β ^ 2 * z (Sum.inr 1)) := by
      rw [key]; positivity
    exact pos_of_mul_pos_right this htop.le
  · rintro ⟨hz3, hcond⟩
    set s2 := 3 * z (Sum.inr 3) / β with hs2
    have hs2p : 0 < s2 := by positivity
    have hk3 : ∀ k : Fin (3 + 1), (k : ℕ) ≤ 2 * (3 / 2) → z (Sum.inr k) = 0 →
        k = 0 ∧ z (Sum.inr 0) = 0 ∨ k = 2 := fun k hk hzk => by
      fin_cases k
      · exact Or.inl ⟨rfl, hzk⟩
      · exact absurd hzk hz1
      · exact Or.inr rfl
      · simp at hk
    by_cases hz0 : z (Sum.inr 0) = 0
    · set s1 := s2 / β
      set s0 := (z (Sum.inr 1) + s1 / 2) / β
      have hdisc : 0 < 4 * s0 * s2 - s1 ^ 2 := by
        have : 4 * s0 * s2 - s1 ^ 2 =
            s2 / β ^ 3 * (3 * z (Sum.inr 3) + 4 * β ^ 2 * z (Sum.inr 1)) := by
          simp only [s0, s1, hs2]; field_simp; ring
        rw [this]; have := hcond hz0; positivity
      refine ⟨C s0 + C s1 * X + C s2 * X ^ 2, by rw [h32]; compute_degree!, fun x => ?_,
        by simpa [h32] using hs2p, fun k hk hzk => ?_⟩
      · simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        nlinarith [sq_nonneg (2 * s2 * x + s1)]
      · rcases hk3 k hk hzk with ⟨rfl, -⟩ | rfl
        · simp only [tk, hc1, Fin.val_zero, Nat.cast_zero]
          simp [coeff_X, coeff_C]
          simp only [s0]; field_simp; ring
        · simp only [tk, hc3, show ((2 : Fin (3 + 1)) : ℕ) = 2 from rfl]
          simp [coeff_X_pow]
          simp only [hs2]; field_simp; ring
    · refine ⟨1 + C s2 * X ^ 2, by rw [h32]; compute_degree!, fun x => ?_,
        by simpa [h32, coeff_one] using hs2p, fun k hk hzk => ?_⟩
      · simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
        positivity
      · rcases hk3 k hk hzk with ⟨-, h⟩ | rfl
        · exact absurd h hz0
        · simp only [tk, hc3, show ((2 : Fin (3 + 1)) : ℕ) = 2 from rfl]
          simp [coeff_one, coeff_X_pow]
          simp only [hs2]; field_simp; ring

theorem correlatedFactorsSmall : Standalone.CorrelatedFactorsSmall.statement := ⟨zero, one⟩

end Novel.CorrelatedFactorsSmallProof

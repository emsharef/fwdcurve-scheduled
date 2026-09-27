import Standalone.CorrelatedFactorsSign
import Novel.CorrelatedFactorsReductionProof

open Polynomial
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsSign
namespace Novel.CorrelatedFactorsSignProof
open Novel.CorrelatedFactorsReductionProof

/-- With `a` supported on `μ, ν ≤ n`, the coefficient of `x^{2n}` in `S_A` is `a_{nn}/β²`. -/
lemma SA_top (β : ℝ) (hβ : β ≠ 0) {n₁ n₂ : ℕ} (n : ℕ) (hn : n ≤ n₁)
    (a : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (hsupp : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
      (μ : ℕ) ≤ n ∧ (ν : ℕ) ≤ n) :
    (SA β a).coeff (2 * n) =
      a (Sum.inl ⟨n, by omega⟩) (Sum.inl ⟨n, by omega⟩) * (1 / β) ^ 2 := by
  have hterm : ∀ μ ν : Fin (n₁ + 1), (C (a (Sum.inl μ) (Sum.inl ν)) * Pnu β μ * Pnu β ν).coeff
      (2 * n) = if (μ : ℕ) = n ∧ (ν : ℕ) = n then a (Sum.inl μ) (Sum.inl ν) * (1 / β) ^ 2
        else 0 := by
    intro μ ν
    rw [mul_assoc, coeff_C_mul]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have hc : (Pnu β n).coeff n = 1 / β := by
        rw [Pnu_coeff, ite_eq_left (le_refl _), Nat.sub_self, zero_add, pow_one,
          div_self (by exact_mod_cast Nat.factorial_ne_zero n)]
      have hdeg : (Pnu β n).natDegree = n :=
        natDegree_eq_of_le_of_coeff_ne_zero (Pnu_natDegree β n) (by rw [hc]; simpa using hβ)
      rw [h1, h2, show 2 * n = (Pnu β n).natDegree + (Pnu β n).natDegree by omega,
        coeff_mul_degree_add_degree, leadingCoeff, hdeg, hc]
      ring
    · by_cases ha : a (Sum.inl μ) (Sum.inl ν) = 0
      · rw [ha, zero_mul]
      obtain ⟨μ', ν', h1, h2, hμ, hν⟩ := hsupp _ _ ha
      cases Sum.inl_injective h1
      cases Sum.inl_injective h2
      rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
      exact lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (Pnu_natDegree β μ)
        (Pnu_natDegree β ν))) (by omega)
  simp only [SA, finsetSum_coeff, hterm]
  rw [Finset.sum_eq_single ⟨n, by omega⟩, Finset.sum_eq_single ⟨n, by omega⟩]
  · simp
  · intro ν _ hν
    rw [ite_eq_right (fun h => hν (Fin.ext h.2))]
  · simp
  · intro μ _ hμ
    exact Finset.sum_eq_zero fun ν _ => ite_eq_right (fun h => hμ (Fin.ext h.1))
  · simp

lemma sign : signStatement := by
  intro β hβ n₁ n hn z b a ha hK0 hz hres hpos
  obtain ⟨hsupp, -, -, htk⟩ :=
    (reduction β hβ n₁ (2 * n + 1) z b a ha hK0).1 hres
  have hn2 : (2 * n + 1) / 2 = n := by omega
  have hsupp' : ∀ i j, a i j ≠ 0 → ∃ μ ν : Fin (n₁ + 1), i = Sum.inl μ ∧ j = Sum.inl ν ∧
      (μ : ℕ) ≤ n ∧ (ν : ℕ) ≤ n := fun i j h => by
    obtain ⟨μ, ν, h1, h2, h3, h4⟩ := hsupp i j h
    exact ⟨μ, ν, h1, h2, hn2 ▸ h3, hn2 ▸ h4⟩
  have h := htk ⟨2 * n, by omega⟩ (by simp; omega) hz
  have hc2 : c2 z (2 * n + 1) = z (Sum.inr ⟨2 * n + 1, by omega⟩) := by
    unfold c2; simp
  simp only at h
  have hβ0 : β ≠ 0 := hβ.ne'
  rw [hc2, tk, SA_top β hβ0 n hn a hsupp', SA_coeff_zero β a hsupp (2 * n + 1) (by omega)] at h
  have key : ((2 * n : ℕ) + 1 : ℝ) * z (Sum.inr ⟨2 * n + 1, by omega⟩) =
      a (Sum.inl ⟨n, by omega⟩) (Sum.inl ⟨n, by omega⟩) / β := by
    rw [← h]
    field_simp
    ring
  have : (0 : ℝ) < ((2 * n : ℕ) + 1 : ℝ) * z (Sum.inr ⟨2 * n + 1, by omega⟩) := by
    rw [key]; exact div_pos hpos hβ
  exact pos_of_mul_pos_right this (by positivity)

lemma counterexample : counterexampleStatement := by
  refine ⟨⟨le_rfl, fun i => by fin_cases i; simp [zEx], Or.inr (by simp [zEx]),
    by simp [zEx]⟩, fun b a ha hb hres => ?_⟩
  have hK0 : ∀ k : Fin (1 + 1), (k : ℕ) ≤ 2 * (1 / 2) → zEx (Sum.inr k) = 0 →
      b (Sum.inr k) = 0 := fun k hk _ => by
    have : k = 0 := Fin.ext (by simpa using hk)
    rw [this]; exact hb
  obtain ⟨hsupp, -, -, htk⟩ := (reduction 1 one_pos 0 1 zEx b a ha hK0).1 hres
  have h := htk 0 (by simp) (by simp [zEx])
  have htop := SA_top 1 one_ne_zero 0 le_rfl a (fun i j hij => by
    obtain ⟨μ, ν, h1, h2, h3, h4⟩ := hsupp i j hij
    exact ⟨μ, ν, h1, h2, by simp at h3; omega, by simp at h4; omega⟩)
  have hnn := ha.diag_nonneg (i := Sum.inl 0)
  have h1 := SA_coeff_zero 1 a hsupp 1 (by norm_num)
  simp only [mul_zero] at htop
  simp only [tk, Fin.val_zero, Nat.cast_zero, zero_add, htop, h1] at h
  have hc : c2 zEx 1 = -1 := by
    unfold c2
    simp [zEx]
  have e0 : a (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = a (Sum.inl 0) (Sum.inl 0) := rfl
  rw [hc, e0] at h
  norm_num at h
  linarith

theorem correlatedFactorsSign : Standalone.CorrelatedFactorsSign.statement := ⟨sign, counterexample⟩

end Novel.CorrelatedFactorsSignProof

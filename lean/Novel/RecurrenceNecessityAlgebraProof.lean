import Standalone.RecurrenceNecessityAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
open Standalone.MeetingLoadingHankel Standalone.RecurrenceNecessityAlgebra
namespace Novel.RecurrenceNecessityAlgebraProof

lemma pow_mul_inv_pow {r : ℕ} (E : Matrix (Fin r) (Fin r) ℝ) (hE : IsUnit E.det) :
    ∀ l : ℕ, E ^ l * E⁻¹ ^ l = 1
  | 0 => by simp
  | l + 1 => by
    rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc E, mul_nonsing_inv E hE, one_mul,
      pow_mul_inv_pow E hE l]

lemma pow_inv_cancel {r : ℕ} (E : Matrix (Fin r) (Fin r) ℝ) (hE : IsUnit E.det) (i l : ℕ) :
    E ^ (i + l) * E⁻¹ ^ l = E ^ i := by
  rw [pow_add, mul_assoc, pow_mul_inv_pow E hE, mul_one]

lemma recurrence : Standalone.RecurrenceNecessityAlgebra.recurrenceStatement := by
  intro r a c E hc hE q hq
  classical
  let K : ℕ → Submodule ℝ (Fin (q+1) → ℝ) := fun n =>
    LinearMap.ker (blockHankel032 a c E q n)ᵀ.mulVecLin
  have hmem : ∀ n (d : Fin (q+1) → ℝ), d ∈ K n ↔
      ∀ ls : Fin n × Fin r, ∑ i, blockHankel032 a c E q n i ls * d i = 0 := by
    intro n d
    simp only [K, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
    simp [Matrix.mulVec, dotProduct, transpose_apply, mul_comm]
  have hanti : Antitone K := by
    refine antitone_nat_of_succ_le fun n d hd => ?_
    rw [hmem] at hd ⊢
    intro ls
    exact hd (⟨⟨ls.1, by omega⟩, ls.2⟩)
  have hpos : ∀ n, 1 ≤ Module.finrank ℝ (K n) := by
    intro n
    have h := LinearMap.finrank_range_add_finrank_ker (blockHankel032 a c E q n)ᵀ.mulVecLin
    have hr : Module.finrank ℝ (LinearMap.range (blockHankel032 a c E q n)ᵀ.mulVecLin) ≤ q := by
      have := hq q n
      rw [← Matrix.rank_transpose] at this
      exact this
    simp only [Module.finrank_fin_fun] at h
    simp only [K]
    omega
  have hex : ∃ k, ∃ n, Module.finrank ℝ (K n) = k := ⟨_, 0, rfl⟩
  obtain ⟨n0, hn0⟩ := Nat.find_spec hex
  have hstable : ∀ n, n0 ≤ n → K n = K n0 := by
    intro n hn
    apply Submodule.eq_of_le_of_finrank_eq (hanti hn)
    apply le_antisymm (Submodule.finrank_mono (hanti hn))
    rw [hn0]
    exact Nat.find_min' hex ⟨n, rfl⟩
  have hne : K n0 ≠ ⊥ := by
    intro h
    have := hpos n0
    rw [h, finrank_bot] at this
    omega
  obtain ⟨d, hdK, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hall : ∀ (l : ℕ) (s : Fin r),
      ∑ i : Fin (q+1), a (i + l + 1) * (c ᵥ* (E ^ ((i:ℕ) + l + 1))) s * d i = 0 := by
    intro l s
    have hdn : d ∈ K (max (l+1) n0) := by rw [hstable _ (le_max_right _ _)]; exact hdK
    exact (hmem _ d).1 hdn (⟨⟨l, by omega⟩, s⟩)
  -- remove the powers of `E` belonging to the column
  have hvec : ∀ l : ℕ, ∑ i : Fin (q+1), (d i * a (i + l + 1)) • (c ᵥ* (E ^ (i:ℕ))) = 0 := by
    intro l
    have h0 : ∑ i : Fin (q+1), (d i * a (i + l + 1)) • (c ᵥ* (E ^ ((i:ℕ) + l + 1))) = 0 := by
      funext s
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hall l s]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h1 := congrArg (fun y => y ᵥ* (E⁻¹ ^ (l + 1))) h0
    simp only [zero_vecMul, sum_vecMul, smul_vecMul, vecMul_vecMul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (i:ℕ) + l + 1 = i + (l + 1) by ring, pow_inv_cancel E hE]
  -- a nonzero coordinate
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hd0
  have hcE : c ᵥ* (E ^ (i0:ℕ)) ≠ 0 := by
    intro h
    apply hc
    have := congrArg (fun y => y ᵥ* (E⁻¹ ^ (i0:ℕ))) h
    simp only [zero_vecMul, vecMul_vecMul] at this
    rwa [show E ^ (i0:ℕ) * E⁻¹ ^ (i0:ℕ) = 1 by simpa using pow_inv_cancel E hE 0 (i0:ℕ),
      vecMul_one] at this
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hcE
  let e : Fin (q+1) → ℝ := fun i => d i * (c ᵥ* (E ^ (i:ℕ))) s
  have he0 : e i0 ≠ 0 := mul_ne_zero hi0 hs
  have hrel : ∀ l : ℕ, ∑ i : Fin (q+1), e i * a (i + l + 1) = 0 := by
    intro l
    have := congrFun (hvec l) s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by simp only [e]; ring
  -- the last nonzero coefficient
  let eN : ℕ → ℝ := fun i => if h : i < q+1 then e ⟨i, h⟩ else 0
  have heN : ∀ i : Fin (q+1), eN i = e i := fun i => by simp only [eN, dif_pos i.isLt]
  set S := (Finset.range (q+1)).filter (fun i => eN i ≠ 0) with hS
  have hSne : S.Nonempty :=
    ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_range.2 i0.isLt, by rw [heN]; exact he0⟩⟩
  set L := S.max' hSne
  have hLS : L ∈ S := S.max'_mem hSne
  have hLq : L ≤ q := by
    have := (Finset.mem_filter.1 hLS).1
    rw [Finset.mem_range] at this
    omega
  have heL : eN L ≠ 0 := (Finset.mem_filter.1 hLS).2
  have htail : ∀ i, L < i → eN i = 0 := by
    intro i hi
    by_contra h
    have hiq : i < q+1 := by
      by_contra hiq
      exact h (by simp only [eN, dif_neg hiq])
    exact absurd (S.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_range.2 hiq, h⟩)) (not_le.2 hi)
  have hrelN : ∀ l : ℕ, eN L * a (L + l + 1) = -∑ i ∈ Finset.range L, eN i * a (i + l + 1) := by
    intro l
    have h1 : ∑ i ∈ Finset.range (q+1), eN i * a (i + l + 1) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => eN i * a (i + l + 1))]
      simpa only [heN] using hrel l
    have h2 : ∑ i ∈ Finset.range (q+1), eN i * a (i + l + 1) =
        ∑ i ∈ Finset.range (L+1), eN i * a (i + l + 1) := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
      intro i _ hi
      rw [Finset.mem_range, not_lt] at hi
      rw [htail i (by omega), zero_mul]
    rw [h2, Finset.sum_range_succ] at h1
    linarith
  refine ⟨L + 1, by omega, fun j => if (j:ℕ) = 0 then 0 else -eN ((j:ℕ) - 1) / eN L, fun k => ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_true, zero_mul, zero_add, Fin.val_succ, Nat.succ_ne_zero, if_false,
    Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i => -eN i / eN L * a (k + (i + 1))) L]
  have h := hrelN k
  apply mul_left_cancel₀ heL
  rw [Finset.mul_sum, show k + (L + 1) = L + k + 1 by ring, h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show k + (i + 1) = i + k + 1 by ring]
  field_simp

theorem recurrenceNecessityAlgebra : Standalone.RecurrenceNecessityAlgebra.statement := recurrence

end Novel.RecurrenceNecessityAlgebraProof

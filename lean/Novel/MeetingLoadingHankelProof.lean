import Standalone.MeetingLoadingHankel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators
open Polynomial Standalone.MeetingLoadingHankel
namespace Novel.MeetingLoadingHankelProof

lemma recurrence : recurrenceStatement := by
  intro a q hq
  classical
  let K : ℕ → Submodule ℝ (Fin (q+1) → ℝ) := fun R => LinearMap.ker (hankel029 a R q).mulVecLin
  have hmem : ∀ R (c : Fin (q+1) → ℝ), c ∈ K R ↔ ∀ i : Fin (R+1), ∑ l : Fin (q+1), a (i + l) * c l = 0 := by
    intro R c
    simp only [K, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
    simp [Matrix.mulVec, dotProduct, hankel029]
  have hanti : Antitone K := by
    refine antitone_nat_of_succ_le fun R c hc => ?_
    rw [hmem] at hc ⊢
    intro i
    exact hc ⟨i, by omega⟩
  have hpos : ∀ R, 1 ≤ Module.finrank ℝ (K R) := by
    intro R
    have h := LinearMap.finrank_range_add_finrank_ker (hankel029 a R q).mulVecLin
    have hr : Module.finrank ℝ (LinearMap.range (hankel029 a R q).mulVecLin) ≤ q := hq R q
    simp only [Module.finrank_fin_fun] at h
    simp only [K]
    omega
  have hex : ∃ k, ∃ R, Module.finrank ℝ (K R) = k := ⟨_, 0, rfl⟩
  obtain ⟨R0, hR0⟩ := Nat.find_spec hex
  have hstable : ∀ R, R0 ≤ R → K R = K R0 := by
    intro R hR
    apply Submodule.eq_of_le_of_finrank_eq (hanti hR)
    apply le_antisymm (Submodule.finrank_mono (hanti hR))
    rw [hR0]
    exact Nat.find_min' hex ⟨R, rfl⟩
  have hne : K R0 ≠ ⊥ := by
    intro h
    have := hpos R0
    rw [h, finrank_bot] at this
    omega
  obtain ⟨c, hcK, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hall : ∀ i : ℕ, ∑ l : Fin (q+1), a (i + l) * c l = 0 := by
    intro i
    have hcR : c ∈ K (max i R0) := by rw [hstable _ (le_max_right _ _)]; exact hcK
    exact (hmem _ c).1 hcR ⟨i, by omega⟩
  -- the coefficients as a function on ℕ
  let cN : ℕ → ℝ := fun l => if h : l < q+1 then c ⟨l, h⟩ else 0
  have hcN : ∀ l : Fin (q+1), cN l = c l := fun l => by simp only [cN, dif_pos l.isLt]
  have hallN : ∀ i : ℕ, ∑ l ∈ Finset.range (q+1), a (i + l) * cN l = 0 := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range (fun l => a (i + l) * cN l)]
    simpa only [hcN] using hall i
  -- the last nonzero coefficient
  set s := (Finset.range (q+1)).filter (fun l => cN l ≠ 0) with hs
  have hsne : s.Nonempty := by
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hc0
    exact ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 l.isLt, by rw [hcN]; exact hl⟩⟩
  set L := s.max' hsne with hLdef
  have hLs : L ∈ s := s.max'_mem hsne
  have hLq : L ≤ q := by
    have := (Finset.mem_filter.1 hLs).1
    rw [Finset.mem_range] at this
    omega
  have hcL : cN L ≠ 0 := (Finset.mem_filter.1 hLs).2
  have htail : ∀ l, L < l → cN l = 0 := by
    intro l hl
    by_contra h
    have hlq : l < q+1 := by
      by_contra hlq
      exact h (by simp only [cN, dif_neg hlq])
    have : l ∈ s := Finset.mem_filter.2 ⟨Finset.mem_range.2 hlq, h⟩
    exact absurd (s.le_max' l this) (not_le.2 hl)
  refine ⟨L, hLq, fun l => -cN l / cN L, fun i => ?_⟩
  have h1 : ∑ l ∈ Finset.range (q+1), a (i + l) * cN l =
      ∑ l ∈ Finset.range (L+1), a (i + l) * cN l := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro l _ hl
    rw [Finset.mem_range, not_lt] at hl
    rw [htail l (by omega), mul_zero]
  have h2 := hallN i
  rw [h1, Finset.sum_range_succ] at h2
  rw [Fin.sum_univ_eq_sum_range (fun l => -cN l / cN L * a (i + l)) L]
  have h3 : (∑ l ∈ Finset.range L, -cN l / cN L * a (i + l)) * cN L =
      -(∑ l ∈ Finset.range L, a (i + l) * cN l) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    field_simp
  apply mul_right_cancel₀ hcL
  rw [h3]
  linarith

lemma harmonic_succ (j : ℕ) : harmonic029 (j+1) - harmonic029 j = 1 / ((j:ℝ) + 1) := by
  simp [harmonic029, Finset.sum_range_succ]

lemma harmonic : harmonicStatement := by
  intro L c hrec
  classical
  -- the recurrence for the meeting weights
  have hw : ∀ i : ℕ, 1 / (((i + L : ℕ) : ℝ) + 1) = ∑ l : Fin L, c l * (1 / (((i + l : ℕ) : ℝ) + 1)) := by
    intro i
    have h1 := hrec (i+1)
    have h0 := hrec i
    rw [← harmonic_succ (i + L)]
    have e : i + 1 + L = i + L + 1 := by ring
    rw [e] at h1
    rw [h1, h0, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← harmonic_succ (i + l), mul_sub]
    congr 2
    ring_nf
  let P : ℝ[X] := ∏ l : Fin L, (X + C ((l:ℝ) + 1))
  let Q : ℝ[X] := ∑ l : Fin L, C (c l) * (X + C ((L:ℝ) + 1)) *
    ∏ l' ∈ Finset.univ.erase l, (X + C ((l':ℝ) + 1))
  have hPQ : ∀ i : ℕ, P.eval (i:ℝ) = Q.eval (i:ℝ) := by
    intro i
    have hx : ∀ l : ℕ, ((i:ℝ) + l + 1) ≠ 0 := fun l => by positivity
    have hw' := hw i
    push_cast at hw'
    simp only [P, Q, eval_prod, eval_finsetSum, eval_mul, eval_add, eval_X, eval_C]
    calc ∏ l : Fin L, ((i:ℝ) + ((l:ℝ) + 1))
        = (1 / ((i:ℝ) + L + 1)) * (((i:ℝ) + L + 1) * ∏ l : Fin L, ((i:ℝ) + ((l:ℝ) + 1))) := by
          field_simp [hx L]
      _ = (∑ l : Fin L, c l * (1 / ((i:ℝ) + l + 1))) *
            (((i:ℝ) + L + 1) * ∏ l : Fin L, ((i:ℝ) + ((l:ℝ) + 1))) := by rw [hw']
      _ = ∑ l : Fin L, c l * ((i:ℝ) + ((L:ℝ) + 1)) *
            ∏ l' ∈ Finset.univ.erase l, ((i:ℝ) + ((l':ℝ) + 1)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          rw [← Finset.mul_prod_erase Finset.univ (fun l' : Fin L => (i:ℝ) + ((l':ℝ) + 1))
            (Finset.mem_univ l)]
          have := hx l
          field_simp
          ring
  have hinf : Set.Infinite {x : ℝ | P.eval x = Q.eval x} := by
    refine (Set.infinite_range_of_injective Nat.cast_injective).mono ?_
    rintro _ ⟨i, rfl⟩
    exact hPQ i
  have hPQ' := Polynomial.eq_of_infinite_eval_eq P Q hinf
  have hev := congrArg (Polynomial.eval (-((L:ℝ) + 1))) hPQ'
  simp only [P, Q, eval_prod, eval_finsetSum, eval_mul, eval_add, eval_X, eval_C] at hev
  have hQ0 : ∑ l : Fin L, c l * (-((L:ℝ) + 1) + ((L:ℝ) + 1)) *
      ∏ l' ∈ Finset.univ.erase l, (-((L:ℝ) + 1) + ((l':ℝ) + 1)) = 0 := by
    simp
  rw [hQ0] at hev
  have hP0 : ∏ l : Fin L, (-((L:ℝ) + 1) + ((l:ℝ) + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l _
    have : (l:ℝ) < L := by exact_mod_cast l.isLt
    linarith
  exact hP0 hev

lemma unbounded : unboundedStatement := by
  intro q
  by_contra h
  push Not at h
  obtain ⟨L, -, c, hrec⟩ := recurrence harmonic029 q h
  exact harmonic L c hrec

theorem meetingLoadingHankel : Standalone.MeetingLoadingHankel.statement :=
  ⟨recurrence, harmonic, unbounded⟩

end Novel.MeetingLoadingHankelProof

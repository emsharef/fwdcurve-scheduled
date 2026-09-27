import Standalone.CorrelatedFactorsAlways
import Novel.CorrelatedFactorsHankelProof
import Novel.CorrelatedFactorsExistsProof

open Polynomial Matrix
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsHankel Standalone.CorrelatedFactorsExists
open Standalone.CorrelatedFactorsAlways
namespace Novel.CorrelatedFactorsAlwaysProof

/-- A `2 × 2` principal minor of a positive semidefinite matrix is nonnegative. -/
lemma minor2 {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosSemidef) (i j : Fin m) :
    H i j * H j i ≤ H i i * H j j := by
  have hs : H j i = H i j := by
    have := congrFun (congrFun hH.1.eq i) j
    simpa [conjTranspose_apply] using this
  have hq : ∀ a b : ℝ, 0 ≤ a * a * H i i + 2 * a * b * H i j + b * b * H j j := fun a b => by
    have := (hH.submatrix ![i, j]).dotProduct_mulVec_nonneg ![a, b]
    simp [dotProduct, mulVec, Fin.sum_univ_two, submatrix, hs] at this
    linarith
  rw [hs]
  rcases eq_or_lt_of_le hH.diag_nonneg with h | h
  · have hz := (Novel.SharefFilipovicMaxFactorsProof.psd_zero hH j i h.symm).1
    rw [hs] at hz; rw [hz]; nlinarith [hH.diag_nonneg (i := i)]
  · have := hq (H j j) (-H i j)
    nlinarith

lemma noLambda : noLambdaStatement := by
  intro β hβ n K0 hK hcons h2n lam hH k0 hk0
  by_contra hlk0
  set ℓ := ellOf β K0 lam
  set H := Matrix.of fun i j : Fin (n + 1) => ℓ (i + j)
  have hHij : ∀ i j : Fin (n + 1), H i j = ℓ (i + j) := fun i j => rfl
  -- a zero diagonal entry empties its row
  have hrow : ∀ i : Fin (n + 1), ℓ (2 * i) = 0 → ∀ j : Fin (n + 1), ℓ (i + j) = 0 := by
    intro i hi j
    have : H i i = 0 := by rw [hHij, show (i : ℕ) + i = 2 * i by ring]; exact hi
    exact (Novel.SharefFilipovicMaxFactorsProof.psd_zero hH i j this).1
  have hdiag : ∀ i : Fin (n + 1), 0 ≤ ℓ (2 * i) := fun i => by
    have := hH.diag_nonneg (i := i)
    rwa [hHij, show (i : ℕ) + i = 2 * i by ring] at this
  obtain ⟨i0, j0, hij0⟩ := Novel.CorrelatedFactorsHankelProof.hankel_ne_zero β hβ.ne' n K0 hK lam
    ⟨k0, hk0, hlk0⟩
  have hell : ∀ j, ℓ j = (if j ∈ K0 then β * lam j else 0) -
      (if 0 < j ∧ j - 1 ∈ K0 then (j : ℝ) / 2 * lam (j - 1) else 0) := fun j => rfl
  -- descending induction on the 2 × 2 minors
  have hdesc : ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < ℓ (2 * j) → 2 * j - 1 ∈ K0 → False := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hjn hpos hmem
      have h2j : 2 * (j + 1) ∉ K0 := by
        have := hcons _ hmem; rwa [show 2 * (j + 1) - 1 + 1 = 2 * (j + 1) by omega] at this
      have h2j2 : 2 * j ∉ K0 := fun h => by
        have := hcons _ h; rw [show 2 * j + 1 = 2 * (j + 1) - 1 by omega] at this; exact this hmem
      have hl2 : ℓ (2 * (j + 1)) = -((j : ℝ) + 1) * lam (2 * j + 1) := by
        rw [hell, ite_eq_right h2j, ite_eq_left ⟨by omega, hmem⟩, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
        push_cast; ring
      have hlam : lam (2 * j + 1) ≠ 0 := fun h => by rw [hl2, h, mul_zero] at hpos; exact lt_irrefl _ hpos
      have hl1 : ℓ (2 * j + 1) = β * lam (2 * j + 1) := by
        rw [hell, ite_eq_left (by rwa [show 2 * j + 1 = 2 * (j + 1) - 1 by omega]),
          ite_eq_right (fun h => h2j2 (by simpa using h.2))]
        ring
      have hminor := minor2 H hH ⟨j, by omega⟩ ⟨j + 1, by omega⟩
      simp only [hHij] at hminor
      rw [show j + (j + 1) = 2 * j + 1 by ring, show j + 1 + j = 2 * j + 1 by ring,
        show j + j = 2 * j by ring, show j + 1 + (j + 1) = 2 * (j + 1) by ring, hl1] at hminor
      have hpos0 : 0 < ℓ (2 * j) := by
        have : 0 < (β * lam (2 * j + 1)) * (β * lam (2 * j + 1)) :=
          mul_self_pos.2 (mul_ne_zero hβ.ne' hlam)
        by_contra h
        push Not at h
        nlinarith
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [hell, ite_eq_right (by simpa using h2j2), ite_eq_right (by omega)] at hpos0
        simp at hpos0
      · have hm : 2 * j - 1 ∈ K0 := by
          by_contra h
          rw [hell, ite_eq_right h2j2, ite_eq_right (fun h' => h h'.2)] at hpos0
          simp at hpos0
        exact ih hj (by omega) hpos0 hm
  -- either every diagonal entry beyond the first vanishes, or the last one is positive
  by_cases hA : ∀ i : Fin (n + 1), 0 < (i : ℕ) → ℓ (2 * i) = 0
  · have hz : ∀ m, 1 ≤ m → m ≤ 2 * n → ℓ m = 0 := by
      intro m hm1 hm2
      rcases le_or_gt m n with h | h
      · have := hrow ⟨1, by omega⟩ (hA _ (by simp)) ⟨m - 1, by omega⟩
        simpa [show 1 + (m - 1) = m by omega] using this
      · have := hrow ⟨m - n, by omega⟩ (hA _ (by simp; omega)) ⟨n, by omega⟩
        simpa [show m - n + n = m by omega] using this
    have hi0 : (i0 : ℕ) + j0 = 0 := by
      by_contra h
      exact hij0 (hz _ (by omega) (by have := i0.2; have := j0.2; omega))
    rw [hi0] at hij0
    change ℓ 0 ≠ 0 at hij0
    have h0 : 0 ∈ K0 := by
      by_contra h; rw [hell, ite_eq_right h, ite_eq_right (by omega)] at hij0; simp at hij0
    have hn : 1 ≤ n := by
      by_contra h; exact h2n (by rw [show 2 * n = 0 by omega]; exact h0)
    have h1 : 1 ∉ K0 := hcons 0 h0
    have hl0 : lam 0 ≠ 0 := by
      intro h; rw [hell, ite_eq_left h0, h, mul_zero, ite_eq_right (by omega)] at hij0; simp at hij0
    have := hz 1 le_rfl (by omega)
    rw [hell, ite_eq_right h1, ite_eq_left ⟨by omega, by simpa using h0⟩] at this
    simp at this
    exact hl0 this
  · push Not at hA
    obtain ⟨i1, hi1, hi1ne⟩ := hA
    -- the largest such index is `n`
    have hmax : 0 < ℓ (2 * n) := by
      by_contra hc
      have hzero : ℓ (2 * n) = 0 := le_antisymm (not_lt.1 hc) (hdiag (Fin.last n))
      classical
      have hne : ((Finset.univ : Finset (Fin (n + 1))).filter
          fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ ℓ (2 * i) ≠ 0).Nonempty :=
        ⟨i1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1, hi1ne⟩⟩
      obtain ⟨im, him, hmaxim⟩ := Finset.exists_max_image _ (fun i : Fin (n + 1) => (i : ℕ)) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at him hmaxim
      have hlt : (im : ℕ) < n := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 im.2) with h | h
        · exact h
        · exact absurd (by rw [show (im : ℕ) = n from h] at *; exact hzero) him.2
      have hbig : ∀ i : Fin (n + 1), (im : ℕ) < i → ℓ (2 * i) = 0 := fun i hi => by
        by_contra h
        exact absurd (hmaxim i ⟨by omega, h⟩) (not_le.2 hi)
      have := hrow ⟨max ((im : ℕ) + 1) (2 * (im : ℕ) - n), by omega⟩
        (hbig _ (by simp)) ⟨2 * (im : ℕ) - max ((im : ℕ) + 1) (2 * (im : ℕ) - n), by omega⟩
      simp only at this
      rw [show max (↑im + 1) (2 * ↑im - n) + (2 * ↑im - max (↑im + 1) (2 * ↑im - n)) = 2 * im by
        omega] at this
      exact him.2 this
    have hn : 1 ≤ n := by
      by_contra h
      have : (i1 : ℕ) = 0 := by have := i1.2; omega
      omega
    have hm : 2 * n - 1 ∈ K0 := by
      by_contra h
      rw [hell, ite_eq_right h2n, ite_eq_right (fun h' => h h'.2)] at hmax
      simp at hmax
    exact hdesc n hn le_rfl hmax hm

lemma always : alwaysStatement := by
  intro β hβ n₁ n₂ hn z hC3 h2n
  classical
  set n := n₂ / 2
  set K0 := (Finset.range (2 * n + 1)).filter fun k => c2 z k = 0
  have hK : ∀ k ∈ K0, k ≤ 2 * n := fun k hk => by
    have := (Finset.mem_filter.1 hk).1; simp at this; omega
  have hcons : ∀ k ∈ K0, k + 1 ∉ K0 := fun k hk hk1 => by
    have h1 := Finset.mem_filter.1 hk
    have h2 := Finset.mem_filter.1 hk1
    rcases hC3 k (hK k hk) with h | h
    · exact h h1.2
    · exact h h2.2
  have h2nK : 2 * n ∉ K0 := fun h => h2n (Finset.mem_filter.1 h).2
  have hS := ((Novel.CorrelatedFactorsHankelProof.hankel β hβ n K0
    (fun k => ((k : ℝ) + 1) * c2 z (k + 1)) hK hcons).2 (by
      rintro ⟨lam, ⟨k, hk, hlk⟩, hH, -⟩
      exact hlk (noLambda β hβ n K0 hK hcons h2nK lam hH k hk)))
  obtain ⟨S, h1, h2, h3, h4⟩ := hS
  exact (Novel.CorrelatedFactorsExistsProof.exists_ β hβ n₁ n₂ hn z).2
    ⟨S, h1, h2, h3, fun k hk hz => h4 k (Finset.mem_filter.2 ⟨by simp; omega, by
      simp only [c2, dite_eq_left k.2]; exact hz⟩)⟩

theorem correlatedFactorsAlways : Standalone.CorrelatedFactorsAlways.statement := ⟨noLambda, always⟩

end Novel.CorrelatedFactorsAlwaysProof

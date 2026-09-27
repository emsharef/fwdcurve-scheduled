import Standalone.SpliceExponentZeroResidual
import Novel.SplicePolynomialPartsProof

open Polynomial Set Filter
open Standalone.SpliceVaryingExponents Standalone.SplicePolynomialParts
open Standalone.SpliceExponentZeroResidual
namespace Novel.SpliceExponentZeroResidualProof
open Novel.SpliceVaryingExponentsProof Novel.SplicePolynomialPartsProof

variable {d K : ℕ} {n : Fin K → ℕ}

/-- `coeff_hi` with the extra term: the coefficient of `x^k` in (43.2)'s top part is `E`'s. -/
lemma coeff_hiE (z : Idx d K n → ℝ) (hz : ∀ i, 0 < expo (fun I => z (Sum.inr I)) i)
    (a : Idx d K n → Idx d K n → ℝ) (b : Idx d K n → ℝ) (E : ℝ[X]) (c₀ c₁ : ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → residual43 z a b x + E.eval x = c₀ + c₁ * x) (k : ℕ) (hk : d < k)
    (hk1 : 1 < k) :
    ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      (if (μ : ℕ) + (ν : ℕ) + 1 = k then a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1) else 0) =
        E.coeff k := by
  obtain ⟨Plow, hdeg, G, hG, hR⟩ := decomp43 z hz a b
  let HiP : ℝ[X] := ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
    C (a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1)) * X ^ ((μ : ℕ) + (ν : ℕ) + 1)
  have hHi : ∀ x, HiP.eval x = ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1)) := fun x => by
    simp only [HiP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  let Q : ℝ[X] := C c₀ + C c₁ * X - E - Plow + HiP
  have hQ := (hG.eq_poly Q 0 1 one_pos fun x hx => by
    have := hR x
    have hx' := h x hx.1.le
    rw [← hHi] at this
    simp only [Q, eval_add, eval_sub, eval_mul, eval_C, eval_X]
    linarith).1
  have hc := congrArg (coeff · k) hQ
  simp only [Q, coeff_add, coeff_sub, coeff_C, coeff_C_mul_X, Polynomial.coeff_zero] at hc
  rw [ite_eq_right (by omega), ite_eq_right (by omega),
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hk)] at hc
  have hHk : HiP.coeff k = ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      (if (μ : ℕ) + (ν : ℕ) + 1 = k then a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1) else 0) := by
    simp only [HiP, finsetSum_coeff, coeff_C_mul_X_pow]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
      split_ifs <;> first | rfl | (exfalso; omega)
  rw [← hHk]
  linarith

lemma rows : Standalone.SpliceExponentZeroResidual.rowsStatement := by
  intro d K n hd z hz a b E ha hE ⟨c₀, c₁, h⟩ μ ν hμν
  classical
  set m := (d - 1) / 2
  -- every diagonal entry beyond `m` vanishes
  have hdiag : ∀ ρ : Fin (d + 1), m < (ρ : ℕ) → a (Sum.inl ρ) (Sum.inl ρ) = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨ρ₀, hρ₀m, hρ₀⟩ := hne
    have hS : (Finset.univ.filter fun ρ : Fin (d + 1) => a (Sum.inl ρ) (Sum.inl ρ) ≠ 0).Nonempty :=
      ⟨ρ₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hρ₀⟩⟩
    obtain ⟨ρs, hρs, hmax⟩ := Finset.exists_max_image _ (fun ρ : Fin (d + 1) => (ρ : ℕ)) hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρs hmax
    have hge : (ρ₀ : ℕ) ≤ ρs := hmax ρ₀ hρ₀
    have hbig : ∀ ρ : Fin (d + 1), (ρs : ℕ) < ρ → ∀ σ,
        a (Sum.inl ρ) σ = 0 ∧ a σ (Sum.inl ρ) = 0 := fun ρ hρ σ => by
      have : a (Sum.inl ρ) (Sum.inl ρ) = 0 := by
        by_contra h'; exact absurd (hmax ρ h') (not_le.2 hρ)
      exact Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ σ this
    -- the extra term does not reach degree `2ρ* + 1`
    have hE0 : E.coeff (2 * ρs + 1) = 0 := by
      by_contra hne
      obtain ⟨μ', hk, hμ'⟩ := hE _ hne
      have := hmax μ' hμ'
      omega
    have hc := coeff_hiE z hz a b E c₀ c₁ h (2 * ρs + 1) (by omega) (by omega)
    rw [hE0, Finset.sum_eq_single ρs] at hc
    · rw [Finset.sum_eq_single ρs] at hc
      · rw [ite_eq_left (by ring)] at hc
        have hpos : (0:ℝ) < (ρs : ℕ) + 1 := by positivity
        exact hρs (by field_simp at hc; linarith)
      · intro ν _ hν
        rw [ite_eq_right (fun h => hν (Fin.ext (by omega)))]
      · simp
    · intro μ' _ hμ'
      refine Finset.sum_eq_zero fun ν' _ => ?_
      split_ifs with hs
      · rcases lt_or_gt_of_ne (fun h => hμ' (Fin.ext h)) with hlt | hlt
        · rw [(hbig ν' (by omega) (Sum.inl μ')).2, zero_div]
        · rw [(hbig μ' hlt (Sum.inl ν')).1, zero_div]
      · rfl
    · simp
  rcases hμν with hμ | hν
  · exact (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ (Sum.inl ν) (hdiag μ hμ)).1
  · exact (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ (Sum.inl μ) (hdiag ν hν)).2

lemma attained : Standalone.SpliceExponentZeroResidual.attainedStatement := by
  intro d n hd z a E ha hE
  obtain ⟨b, hb⟩ := Novel.SplicePolynomialPartsProof.attained d n hd z a ha
  -- `E` has degree at most `m + 1 ≤ d`
  have hdeg : E.natDegree < d + 1 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_)
    by_contra hne
    obtain ⟨μ, hkμ, hμ⟩ := hE k hne
    have hμm : (μ : ℕ) ≤ (d - 1) / 2 := by
      by_contra hlt
      exact hμ (ha μ μ (Or.inl (by omega)))
    omega
  refine ⟨fun I => b I - Sum.elim (fun μ : Fin (d + 1) => E.coeff (μ : ℕ)) (fun _ => (0:ℝ)) I,
    fun x => ?_⟩
  have hs := residual_sub z a b
    (fun I => b I - Sum.elim (fun μ : Fin (d + 1) => E.coeff (μ : ℕ)) (fun _ => (0:ℝ)) I) x
  have hsum : ∑ I, (b I - (b I - Sum.elim (fun μ : Fin (d + 1) => E.coeff (μ : ℕ))
      (fun _ => (0:ℝ)) I)) * dF43 z I x = E.eval x := by
    rw [Fintype.sum_sum_type, eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
    simp [dF43]
  rw [hb x] at hs
  linarith

theorem spliceExponentZeroResidual : Standalone.SpliceExponentZeroResidual.statement :=
  ⟨rows, attained⟩

end Novel.SpliceExponentZeroResidualProof

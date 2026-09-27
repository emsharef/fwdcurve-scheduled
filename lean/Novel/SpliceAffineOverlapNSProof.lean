import Standalone.SpliceAffineOverlapNS
import Novel.SharefFilipovicMaxFactorsProof

open Polynomial Set
open Standalone.SpliceAffineOverlapNS
namespace Novel.SpliceAffineOverlapNSProof

lemma hI0 (β x : ℝ) : ∫ η in (0:ℝ)..x, phiNS β 0 η = x := by
  simp [phiNS]

lemma hI1 (β : ℝ) (hβ : β ≠ 0) (x : ℝ) :
    ∫ η in (0:ℝ)..x, phiNS β 1 η = 1 / β - 1 / β * Real.exp (-β * x) := by
  have hq : C β * C (1 / β) - derivative (C (1 / β)) = (C 1 : ℝ[X]) := by
    rw [derivative_C, sub_zero, ← C_mul, mul_one_div_cancel hβ]
  have h := Novel.SharefFilipovicMaxFactorsProof.int_of_anti (C 1) (C (1 / β)) β hq x
  simp only [eval_C, one_mul] at h
  rw [← h]
  rfl

lemma hI2 (β : ℝ) (hβ : β ≠ 0) (x : ℝ) :
    ∫ η in (0:ℝ)..x, phiNS β 2 η = 1 / β ^ 2 - (x / β + 1 / β ^ 2) * Real.exp (-β * x) := by
  have hq : C β * (C (1 / β) * X + C (1 / β ^ 2)) - derivative (C (1 / β) * X + C (1 / β ^ 2)) =
      (X : ℝ[X]) := by
    ext k
    rcases k with _ | _ | k <;> simp [coeff_X, coeff_C, mul_add] <;> field_simp <;> ring
  have h := Novel.SharefFilipovicMaxFactorsProof.int_of_anti X _ β hq x
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add] at h
  rw [show (∫ η in (0:ℝ)..x, phiNS β 2 η) = ∫ η in (0:ℝ)..x, η * Real.exp (-β * η) from rfl, h]
  ring

lemma hd (β : ℝ) (z : Fin 3 → ℝ) (x : ℝ) :
    deriv (FNS β z) x = (z 2 - β * z 1 - β * z 2 * x) * Real.exp (-β * x) := by
  have h := (Novel.SharefFilipovicResidualProof.hd_pe (C (z 1) + C (z 2) * X) β x).const_add (z 0)
  have e : FNS β z = fun x => z 0 + (C (z 1) + C (z 2) * X).eval x * Real.exp (-β * x) := by
    funext x
    simp [FNS, phiNS, Fin.sum_univ_three]
    ring
  rw [e, h.deriv]
  simp
  ring

/-- The residual's closed form: affine, plus `e^{−βx}` and `e^{−2βx}` times quadratics. -/
lemma closed (β : ℝ) (hβ : β ≠ 0) (z b : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (x : ℝ) :
    residualNS β z b a x =
      ((b 0 - a 0 1 / β - a 0 2 / β ^ 2) + (-a 0 0) * x) +
      ((b 1 + a 0 1 / β + a 0 2 / β ^ 2 - a 1 1 / β - a 1 2 / β ^ 2 - z 2 + β * z 1) +
        (b 2 + a 0 2 / β - a 1 0 - a 2 1 / β - a 2 2 / β ^ 2 + β * z 2) * x + (-a 2 0) * x ^ 2) *
        Real.exp (-β * x) +
      ((a 1 1 / β + a 1 2 / β ^ 2) + (a 1 2 / β + a 2 1 / β + a 2 2 / β ^ 2) * x +
        (a 2 2 / β) * x ^ 2) * (Real.exp (-β * x) * Real.exp (-β * x)) := by
  unfold residualNS
  simp only [Fin.sum_univ_three]
  rw [hI0, hI1 β hβ, hI2 β hβ, hd]
  simp only [phiNS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

lemma residualNS_eq : residualStatement := by
  intro β hβ z b a hs hb1 hb2 x
  have hz : ∀ i j, ¬ (i = 0 ∧ j = 0) → a i j = 0 := fun i j h => by
    by_contra hne; exact h (hs i j hne)
  rw [closed β hβ.ne' z b a x, hz 0 1 (by decide), hz 0 2 (by decide), hz 1 0 (by decide),
    hz 1 1 (by decide), hz 1 2 (by decide), hz 2 0 (by decide), hz 2 1 (by decide),
    hz 2 2 (by decide), hb1, hb2]
  ring

lemma ns : nsStatement := by
  intro β hβ z b a ha
  have hβ0 : β ≠ 0 := hβ.ne'
  constructor
  · rintro ⟨c₀, c₁, h⟩
    set B0 := b 1 + a 0 1 / β + a 0 2 / β ^ 2 - a 1 1 / β - a 1 2 / β ^ 2 - z 2 + β * z 1
    set B1 := b 2 + a 0 2 / β - a 1 0 - a 2 1 / β - a 2 2 / β ^ 2 + β * z 2
    set C0 := a 1 1 / β + a 1 2 / β ^ 2
    set C1 := a 1 2 / β + a 2 1 / β + a 2 2 / β ^ 2
    let Qb : ℝ[X] := C B0 + C B1 * X + C (-a 2 0) * X ^ 2
    let Qc : ℝ[X] := C C0 + C C1 * X + C (a 2 2 / β) * X ^ 2
    let P : ℝ[X] := C (c₀ - (b 0 - a 0 1 / β - a 0 2 / β ^ 2)) + C (c₁ + a 0 0) * X
    have hind := Novel.SharefFilipovicIndependenceProof.independence β hβ 2 ![Qb, Qc] P 0 1
      one_pos fun x hx => by
        have e := h x hx.1.le
        rw [closed β hβ0 z b a x] at e
        have ee : Real.exp (-β * x) * Real.exp (-β * x) = Real.exp (-((1:ℝ) + 1) * β * x) := by
          rw [← Real.exp_add]; ring_nf
        rw [ee] at e
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
          Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, Qb, Qc, P, eval_add,
          eval_mul, eval_C, eval_X, eval_pow, Matrix.head_cons]
        rw [show -((1:ℝ) + 1) * β * x = -((1:ℝ) + 1) * β * x from rfl]
        simp only [neg_mul, one_mul] at e ⊢
        linarith
    have hQb := hind.1 0
    have hQc := hind.1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hQb hQc
    have cf : ∀ (p q r : ℝ), (C p + C q * X + C r * X ^ 2 : ℝ[X]) = 0 → p = 0 ∧ q = 0 ∧ r = 0 :=
      fun p q r hpq => by
        have h0 := congrArg (coeff · 0) hpq
        have h1 := congrArg (coeff · 1) hpq
        have h2 := congrArg (coeff · 2) hpq
        simp [coeff_X, coeff_C] at h0 h1 h2
        exact ⟨h0, h1, h2⟩
    obtain ⟨hC0, hC1, hC2⟩ := cf _ _ _ hQc
    obtain ⟨hB0, hB1, -⟩ := cf _ _ _ hQb
    have h22 : a 2 2 = 0 := by field_simp at hC2; linarith
    obtain ⟨h21, h12⟩ := Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 2 1 h22
    obtain ⟨h20, h02⟩ := Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 2 0 h22
    have h11 : a 1 1 = 0 := by
      have e : a 1 1 / β + a 1 2 / β ^ 2 = 0 := hC0
      rw [h12, zero_div, add_zero, div_eq_zero_iff] at e
      exact e.resolve_right hβ0
    obtain ⟨h10, h01⟩ := Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 1 0 h11
    have hz : ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → a i j = 0 := by
      intro i j hn
      fin_cases i <;> fin_cases j <;>
        first | exact (hn ⟨rfl, rfl⟩).elim | exact h01 | exact h02 | exact h10 | exact h11 |
          exact h12 | exact h20 | exact h21 | exact h22
    refine ⟨fun i j hij => by_contra fun hne => hij (hz i j hne), ?_, ?_⟩
    · have e : b 1 + a 0 1 / β + a 0 2 / β ^ 2 - a 1 1 / β - a 1 2 / β ^ 2 - z 2 + β * z 1 = 0 := hB0
      rw [h01, h02, h11, h12] at e
      simp only [zero_div, sub_zero, add_zero] at e
      linarith
    · have e : b 2 + a 0 2 / β - a 1 0 - a 2 1 / β - a 2 2 / β ^ 2 + β * z 2 = 0 := hB1
      rw [h02, h10, h21, h22] at e
      simp only [zero_div, sub_zero, add_zero] at e
      linarith
  · rintro ⟨hs, hb1, hb2⟩
    exact ⟨b 0, -a 0 0, fun x _ => by rw [residualNS_eq β hβ z b a hs hb1 hb2 x]; ring⟩

theorem spliceAffineOverlapNS : Standalone.SpliceAffineOverlapNS.statement := ⟨ns, residualNS_eq⟩

end Novel.SpliceAffineOverlapNSProof

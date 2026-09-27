import Standalone.UnifiedSpliceNecessity
import Novel.UnifiedSpliceAlgebraProof
import Novel.SpliceStateBlockObservabilityProof
import Novel.SpliceExponentZeroQuasiPolyProof

open Matrix NormedSpace Set Polynomial
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceNecessity
namespace Novel.UnifiedSpliceNecessityProof

variable {k r : ℕ}

lemma inv_comm_exp (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (x : ℝ) :
    A⁻¹ * exp (x • A) = exp (x • A) * A⁻¹ := by
  have h : Commute A⁻¹ A := by
    show A⁻¹ * A = A * A⁻¹
    rw [nonsing_inv_mul A hA, mul_nonsing_inv A hA]
  exact ((h.smul_right x).exp_right).eq

/-- The jump in the claim's form: a polynomial part, and the exponential part `c e^{xA}((T − T_m)w
+ A⁻¹w) − c A⁻¹ w`, with `w = H^ζ G`. -/
lemma jump_expand (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (d : ℕ) (V₀ V₁ κ₀ κ₁ : Fin k → ℝ)
    (Tm u T : ℝ) (hκ : κ₁ - κ₀ = -Tm • (V₁ - V₀)) :
    cross Hp Hz c A d V₁ κ₁ u T - cross Hp Hz c A d V₀ κ₀ u T =
      (∑ μ ∈ Finset.range (d + 1), (Hp μ ⬝ᵥ (V₁ - V₀)) *
        ((T - u) ^ μ * (T - Tm) + (T - u) ^ (μ + 1) / (μ + 1))) +
      c ⬝ᵥ (exp ((T - u) • A) *ᵥ ((T - Tm) • (Hz *ᵥ (V₁ - V₀)) + A⁻¹ *ᵥ (Hz *ᵥ (V₁ - V₀)))) -
      c ⬝ᵥ (A⁻¹ *ᵥ (Hz *ᵥ (V₁ - V₀))) := by
  rw [Novel.UnifiedSpliceAlgebraProof.jumpS k r d Hp Hz c A V₀ V₁ κ₀ κ₁ Tm u T hκ,
    Novel.UnifiedSpliceAlgebraProof.sigB_dot, Novel.UnifiedSpliceAlgebraProof.dot_SigB]
  set w := Hz *ᵥ (V₁ - V₀)
  have e1 : ephi c A (T - u) ⬝ᵥ (Hz *ᵥ ((T - Tm) • (V₁ - V₀))) =
      c ⬝ᵥ (exp ((T - u) • A) *ᵥ ((T - Tm) • w)) := by
    rw [ephi, ← dotProduct_mulVec, mulVec_smul]
  have e2 : ePhi c A (T - u) ⬝ᵥ w =
      c ⬝ᵥ (exp ((T - u) • A) *ᵥ (A⁻¹ *ᵥ w)) - c ⬝ᵥ (A⁻¹ *ᵥ w) := by
    rw [ePhi, ← dotProduct_mulVec, mul_sub, mul_one, inv_comm_exp A hA, sub_mulVec,
      dotProduct_sub, ← mulVec_mulVec]
  rw [e1, e2, mulVec_add, dotProduct_add]
  simp only [dotProduct_smul, smul_eq_mul]
  have hs : (∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * ((T - Tm) * (Hp μ ⬝ᵥ (V₁ - V₀)))) +
      (∑ μ ∈ Finset.range (d + 1), (T - u) ^ (μ + 1) / (↑μ + 1) * (Hp μ ⬝ᵥ (V₁ - V₀))) =
      ∑ μ ∈ Finset.range (d + 1), (Hp μ ⬝ᵥ (V₁ - V₀)) *
        ((T - u) ^ μ * (T - Tm) + (T - u) ^ (μ + 1) / (↑μ + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  linear_combination hs

/-! ### The polynomial part and its descent -/

/-- `Q(x) = ∑_μ g_μ (x^{μ+1} + s x^μ + x^{μ+1}/(μ+1))`, the polynomial part in `x = T − u`. -/
noncomputable def Qpoly (g : ℕ → ℝ) (d : ℕ) (s : ℝ) : ℝ[X] :=
  ∑ μ ∈ Finset.range (d + 1), C (g μ) * (X ^ (μ + 1) + C s * X ^ μ + C (1 / ((μ:ℝ) + 1)) * X ^ (μ + 1))

lemma Q_eval (g : ℕ → ℝ) (d : ℕ) (s x : ℝ) :
    (Qpoly g d s).eval x = ∑ μ ∈ Finset.range (d + 1), g μ * (x ^ μ * (x + s) + x ^ (μ + 1) / (μ + 1)) := by
  simp only [Qpoly, eval_finsetSum, eval_mul, eval_C, eval_add, eval_pow, eval_X]
  exact Finset.sum_congr rfl fun μ _ => by ring

lemma Q_coeff (g : ℕ → ℝ) (d : ℕ) (s : ℝ) (n : ℕ) :
    (Qpoly g d s).coeff (n + 2) = (if n + 1 ≤ d then g (n + 1) * (1 + 1 / ((n:ℝ) + 2)) else 0) +
      (if n + 2 ≤ d then s * g (n + 2) else 0) := by
  simp only [Qpoly, finsetSum_coeff, coeff_C_mul, coeff_add, coeff_X_pow, mul_add,
    Finset.sum_add_distrib]
  have h1 : ∀ μ ∈ Finset.range (d + 1), g μ * (if n + 2 = μ + 1 then (1:ℝ) else 0) +
      g μ * (1 / ((μ:ℝ) + 1) * if n + 2 = μ + 1 then 1 else 0) =
      if n + 1 = μ then g (n + 1) * (1 + 1 / ((n:ℝ) + 2)) else 0 := fun μ _ => by
    split_ifs with h h' h'
    · subst h'; push_cast; ring
    · omega
    · omega
    · ring
  have h2 : ∀ μ ∈ Finset.range (d + 1), g μ * (s * if n + 2 = μ then (1:ℝ) else 0) =
      if n + 2 = μ then s * g (n + 2) else 0 := fun μ _ => by
    split_ifs with h
    · subst h; ring
    · ring
  rw [show ∀ a b c : ℝ, a + b + c = (a + c) + b from fun a b c => by ring,
    ← Finset.sum_add_distrib] at *
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega | ring

/-- If the coefficients of `x², x³, …` of `Q` vanish, then `g_μ = 0` for `μ = 1, …, d`. -/
lemma descent (g : ℕ → ℝ) (d : ℕ) (s : ℝ) (hQ : ∀ n, (Qpoly g d s).coeff (n + 2) = 0) :
    ∀ μ, 1 ≤ μ → μ ≤ d → g μ = 0 := by
  suffices ∀ j μ, μ + j = d → 1 ≤ μ → g μ = 0 from fun μ h1 h2 => this (d - μ) μ (by omega) h1
  intro j
  induction j with
  | zero =>
    intro μ hμ h1
    obtain ⟨n, rfl⟩ : ∃ n, μ = n + 1 := ⟨μ - 1, by omega⟩
    have := hQ n
    rw [Q_coeff] at this
    simp only [show n + 1 ≤ d by omega, show ¬ (n + 2 ≤ d) by omega, ite_true, ite_false,
      add_zero] at this
    have hpos : (0:ℝ) < 1 + 1 / ((n:ℝ) + 2) := by positivity
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  | succ j ih =>
    intro μ hμ h1
    obtain ⟨n, rfl⟩ : ∃ n, μ = n + 1 := ⟨μ - 1, by omega⟩
    have hnext := ih (n + 2) (by omega) (by omega)
    have := hQ n
    rw [Q_coeff] at this
    simp only [show n + 1 ≤ d by omega, show n + 2 ≤ d by omega, ite_true, hnext, mul_zero,
      add_zero] at this
    have hpos : (0:ℝ) < 1 + 1 / ((n:ℝ) + 2) := by positivity
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'

/-! ### (a) and (b)(i) -/

lemma necessityS : necessityStatement := by
  intro k r d Hp Hz c A hA hobs V₀ V₁ κ₀ κ₁ Tm u d₁ d₂ α β hd hκ hJ
  set G := V₁ - V₀
  set w := Hz *ᵥ G with hw
  set g : ℕ → ℝ := fun μ => Hp μ ⬝ᵥ G
  set v := exp ((-u) • A) *ᵥ w with hv
  have hsplit : ∀ T : ℝ, exp ((T - u) • A) = exp (T • A) * exp ((-u) • A) := fun T => by
    rw [sub_eq_add_neg, add_smul,
      Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _)]
  have hEform : ∀ T : ℝ, c ⬝ᵥ (exp ((T - u) • A) *ᵥ ((T - Tm) • w + A⁻¹ *ᵥ w)) =
      c ⬝ᵥ (exp (T • A) *ᵥ ((A⁻¹ *ᵥ v - Tm • v) + T • v)) := fun T => by
    rw [hsplit, ← mulVec_mulVec]
    congr 2
    have hc : ∀ y : Fin r → ℝ, exp ((-u) • A) *ᵥ (A⁻¹ *ᵥ y) = A⁻¹ *ᵥ (exp ((-u) • A) *ᵥ y) :=
      fun y => by rw [mulVec_mulVec, mulVec_mulVec, inv_comm_exp A hA]
    rw [mulVec_add, mulVec_smul, hc w, ← hv, sub_smul]
    abel
  -- the exponential part equals a polynomial on the interval
  set P : ℝ[X] := C α + C β * X - ∑ μ ∈ Finset.range (d + 1), C (g μ) *
      ((X - C u) ^ μ * (X - C Tm) + C (1 / ((μ:ℝ) + 1)) * (X - C u) ^ (μ + 1)) +
    C (c ⬝ᵥ (A⁻¹ *ᵥ w))
  have hP : ∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ ((A⁻¹ *ᵥ v - Tm • v) + T • v)) = P.eval T :=
    fun T hT => by
      have h := hJ T hT
      rw [jump_expand Hp Hz c A hA d V₀ V₁ κ₀ κ₁ Tm u T hκ, hEform] at h
      have hs : ∑ μ ∈ Finset.range (d + 1), g μ *
          ((T - u) ^ μ * (T - Tm) + 1 / ((μ:ℝ) + 1) * (T - u) ^ (μ + 1)) =
          ∑ μ ∈ Finset.range (d + 1), (Hp μ ⬝ᵥ (V₁ - V₀)) *
            ((T - u) ^ μ * (T - Tm) + (T - u) ^ (μ + 1) / (μ + 1)) :=
        Finset.sum_congr rfl fun μ _ => by simp only [g, G]; ring
      simp only [P, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_finsetSum, eval_pow]
      rw [hs]
      linarith
  obtain ⟨-, hall⟩ := Novel.SpliceExponentZeroQuasiPolyProof.quasiPoly r A hA c
    (A⁻¹ *ᵥ v - Tm • v) v P d₁ d₂ hd hP
  have hv0 : v = 0 := Novel.SpliceStateBlockObservabilityProof.observability r A hA c hobs Tm 0 1 v
    one_pos fun T _ => by
      have e : (T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ v =
          (A⁻¹ *ᵥ v - Tm • v) + T • v := by
        simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec]
        abel
      rw [e]; exact hall T
  have hw0 : w = 0 := by
    have e : w = exp (u • A) *ᵥ v := by
      rw [hv, mulVec_mulVec,
        ← Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _),
        ← add_smul, add_neg_cancel, zero_smul, exp_zero, one_mulVec]
    rw [e, hv0, mulVec_zero]
  refine ⟨?_, hw0⟩
  -- the polynomial part is affine on an interval, hence as a polynomial
  set s := u - Tm
  set Q : ℝ[X] := Qpoly g d s - (C (α + β * u) + C β * X)
  have hQ : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q
      (Set.Infinite.mono (fun x hx => ?_) (Ioo_infinite (show d₁ - u < d₂ - u by linarith)))
    have hT : x + u ∈ Ioo d₁ d₂ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h := hJ (x + u) hT
    rw [jump_expand Hp Hz c A hA d V₀ V₁ κ₀ κ₁ Tm u (x + u) hκ] at h
    have hw0' : Hz *ᵥ (V₁ - V₀) = 0 := hw0
    simp only [hw0', smul_zero, mulVec_zero, add_zero, dotProduct_zero, sub_zero,
      add_sub_cancel_right] at h
    simp only [Set.mem_ofPred_eq, IsRoot, Q, eval_sub, eval_add, eval_mul, eval_C, eval_X, Q_eval]
    have hs : ∑ μ ∈ Finset.range (d + 1), g μ * (x ^ μ * (x + s) + x ^ (μ + 1) / (μ + 1)) =
        ∑ μ ∈ Finset.range (d + 1), (Hp μ ⬝ᵥ (V₁ - V₀)) *
          (x ^ μ * (x + u - Tm) + x ^ (μ + 1) / (μ + 1)) :=
      Finset.sum_congr rfl fun μ _ => by simp only [g, G, s]; ring
    rw [hs, h]; ring
  refine descent g d s fun n => ?_
  have := congrArg (fun q : ℝ[X] => q.coeff (n + 2)) hQ
  simp only [Q, coeff_sub, coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_zero] at this
  simpa using this

lemma levelJumpS : levelJumpStatement := by
  intro k r d Hp Hz c A V₀ V₁ κ₀ κ₁ Tm u hκ hpoly hz T
  rw [Novel.UnifiedSpliceAlgebraProof.jumpS k r d Hp Hz c A V₀ V₁ κ₀ κ₁ Tm u T hκ,
    Novel.UnifiedSpliceAlgebraProof.sigB_dot, Novel.UnifiedSpliceAlgebraProof.dot_SigB,
    mulVec_smul, hz, smul_zero, dotProduct_zero, add_zero, dotProduct_zero, add_zero,
    ← Finset.sum_add_distrib, Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, zero_add, pow_one, Nat.cast_zero, div_one, dotProduct_smul,
      smul_eq_mul]
    ring
  · intro μ hμ h0
    have := hpoly μ (Nat.one_le_iff_ne_zero.2 h0) (by simpa [Nat.lt_succ_iff] using hμ)
    simp [dotProduct_smul, this]
  · simp

theorem unifiedSpliceNecessity : Standalone.UnifiedSpliceNecessity.statement := ⟨necessityS, levelJumpS⟩

end Novel.UnifiedSpliceNecessityProof

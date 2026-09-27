import Novel.UnifiedSpliceExpPolyProof
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Claim 049 (b2): the complex eigenbasis

For `A` diagonalizable over `ℂ`, `A P = P diag(λ)`, the real exponential read in `ℂ` is
`P diag(e^{xλ}) P⁻¹`, and `c e^{xA} v = Σ_i (cP)_i e^{λ_i x} (P⁻¹ v)_i`. Observability makes the `λ_i`
distinct and every `(cP)_i ≠ 0`; invertibility makes every `λ_i ≠ 0`. `fiber_indep` is stage 6's
independence in the form (b2) uses: the frequencies of a family may coincide, and each fiber's
polynomials sum to zero.
-/

open Matrix NormedSpace Polynomial

namespace Novel.UnifiedSpliceDiagLemmas

variable {r : ℕ}

/-- The real matrix exponential, read in `ℂ`. -/
lemma exp_map (A : Matrix (Fin r) (Fin r) ℝ) :
    (exp A).map Complex.ofReal = exp (A.map Complex.ofReal) := by
  open scoped Matrix.Norms.Operator in
  have h := map_exp (Complex.ofRealHom.mapMatrix :
      Matrix (Fin r) (Fin r) ℝ →+* Matrix (Fin r) (Fin r) ℂ)
    (Continuous.matrix_map continuous_id Complex.continuous_ofReal) A
  exact h

/-- `M_ℂ w_ℂ = (M w)_ℂ`. -/
lemma map_mulVec (M : Matrix (Fin r) (Fin r) ℝ) (w : Fin r → ℝ) :
    M.map Complex.ofReal *ᵥ (fun j => (w j : ℂ)) = fun i => ((M *ᵥ w) i : ℂ) := by
  funext i; simp [mulVec, dotProduct]

lemma cast_dot {A : Matrix (Fin r) (Fin r) ℝ} (c : Fin r → ℝ) (x : ℝ) (w : Fin r → ℝ) :
    (fun i => (c i : ℂ)) ⬝ᵥ ((exp (x • A)).map Complex.ofReal *ᵥ fun j => (w j : ℂ)) =
      ((c ⬝ᵥ (exp (x • A) *ᵥ w) : ℝ) : ℂ) := by
  rw [map_mulVec]; simp [dotProduct]

section Eig
variable {A : Matrix (Fin r) (Fin r) ℝ} {P : Matrix (Fin r) (Fin r) ℂ} {lam : Fin r → ℂ}
  (hP : IsUnit P.det) (hAP : A.map Complex.ofReal * P = P * diagonal lam)
include hP hAP

lemma A_conj : A.map Complex.ofReal = P * diagonal lam * P⁻¹ := by
  rw [← hAP, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]

lemma exp_eig (x : ℝ) :
    (exp (x • A)).map Complex.ofReal = P * diagonal (fun i => Complex.exp (x * lam i)) * P⁻¹ := by
  have hx : (x • A).map Complex.ofReal = P * diagonal (fun i => (x:ℂ) * lam i) * P⁻¹ := by
    have : (x • A).map Complex.ofReal = (x:ℂ) • A.map Complex.ofReal := by
      ext i j; simp
    rw [this, A_conj hP hAP, show (fun i => (x:ℂ) * lam i) = (x:ℂ) • lam from rfl, diagonal_smul,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [exp_map, hx, exp_conj _ _ ((isUnit_iff_isUnit_det P).2 hP), exp_diagonal, Pi.exp_def]
  simp only [Complex.exp_eq_exp_ℂ]

/-- `c e^{xA} y = Σ_i (cP)_i e^{λ_i x} (P⁻¹ y)_i`, for complex `y`. -/
lemma phi_eigC (c : Fin r → ℝ) (x : ℝ) (y : Fin r → ℂ) :
    (fun i => (c i : ℂ)) ⬝ᵥ ((exp (x • A)).map Complex.ofReal *ᵥ y) =
      ∑ i, ((fun i => (c i : ℂ)) ᵥ* P) i * Complex.exp (x * lam i) * (P⁻¹ *ᵥ y) i := by
  rw [exp_eig hP hAP, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The same for a real vector, with the real value cast to `ℂ`. -/
lemma phi_eig (c : Fin r → ℝ) (x : ℝ) (v : Fin r → ℝ) :
    ((c ⬝ᵥ (exp (x • A) *ᵥ v) : ℝ) : ℂ) =
      ∑ i, ((fun i => (c i : ℂ)) ᵥ* P) i * Complex.exp (x * lam i) *
        (P⁻¹ *ᵥ fun j => (v j : ℂ)) i := by
  rw [← phi_eigC hP hAP]
  simp only [dotProduct, mulVec, Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Every eigenvalue is nonzero, since `A` is invertible. -/
lemma lam_ne (hA : IsUnit A.det) (i : Fin r) : lam i ≠ 0 := by
  have h1 : (A.map Complex.ofReal).det = ((A.det : ℝ) : ℂ) := by
    exact (RingHom.map_det Complex.ofRealHom A).symm
  have h2 : (A.map Complex.ofReal).det = ∏ j, lam j := by
    rw [A_conj hP hAP, det_conj ((isUnit_iff_isUnit_det P).2 hP), det_diagonal]
  have h3 : ∏ j, lam j ≠ 0 := by
    rw [← h2, h1]; exact_mod_cast hA.ne_zero
  exact (Finset.prod_ne_zero_iff.1 h3) i (Finset.mem_univ i)

/-- `(P⁻¹ A⁻¹ v)_i = (P⁻¹ v)_i / λ_i`. -/
lemma inv_eig (hA : IsUnit A.det) (v : Fin r → ℝ) (i : Fin r) :
    (P⁻¹ *ᵥ fun j => ((A⁻¹ *ᵥ v) j : ℂ)) i = (P⁻¹ *ᵥ fun j => (v j : ℂ)) i / lam i := by
  have hPA : P⁻¹ * A.map Complex.ofReal = diagonal lam * P⁻¹ := by
    rw [A_conj hP hAP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul P hP,
      Matrix.one_mul]
  have hv : (fun j => (v j : ℂ)) = A.map Complex.ofReal *ᵥ fun j => ((A⁻¹ *ᵥ v) j : ℂ) := by
    rw [map_mulVec, mulVec_mulVec, mul_nonsing_inv A hA, one_mulVec]
  rw [hv, mulVec_mulVec, hPA, ← mulVec_mulVec, mulVec_diagonal,
    mul_div_cancel_left₀ _ (lam_ne hP hAP hA i)]

omit hP hAP in
/-- Observability over `ℂ`. -/
lemma obsC (c : Fin r → ℝ)
    (hobs : ∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0)
    (y : Fin r → ℂ)
    (h : ∀ x : ℝ, (fun i => (c i : ℂ)) ⬝ᵥ ((exp (x • A)).map Complex.ofReal *ᵥ y) = 0) : y = 0 := by
  set yr : Fin r → ℝ := fun j => (y j).re
  set yi : Fin r → ℝ := fun j => (y j).im
  have hy : y = (fun j => (yr j : ℂ)) + Complex.I • fun j => (yi j : ℂ) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, yr, yi]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hsplit : ∀ x : ℝ, ((c ⬝ᵥ (exp (x • A) *ᵥ yr) : ℝ) : ℂ) +
      Complex.I * ((c ⬝ᵥ (exp (x • A) *ᵥ yi) : ℝ) : ℂ) = 0 := fun x => by
    have := h x
    rw [hy, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, cast_dot, cast_dot,
      smul_eq_mul] at this
    exact this
  have hr : yr = 0 := hobs yr fun x => by
    have := congrArg Complex.re (hsplit x); simpa using this
  have hi : yi = 0 := hobs yi fun x => by
    have := congrArg Complex.im (hsplit x); simpa using this
  funext j
  apply Complex.ext
  · simpa using congrFun hr j
  · simpa using congrFun hi j

/-- Observability makes every `(cP)_i` nonzero. -/
lemma cP_ne (c : Fin r → ℝ)
    (hobs : ∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) (i : Fin r) :
    ((fun i => (c i : ℂ)) ᵥ* P) i ≠ 0 := by
  intro h0
  have hy := obsC c hobs (P *ᵥ Pi.single i 1) fun x => by
    rw [phi_eigC hP hAP, mulVec_mulVec, nonsing_inv_mul P hP, one_mulVec]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases eq_or_ne j i with rfl | hji
    · rw [h0]; ring
    · simp [hji]
  have h1 := congrArg (P⁻¹ *ᵥ ·) hy
  simp only [mulVec_mulVec, nonsing_inv_mul P hP, one_mulVec, mulVec_zero] at h1
  have := congrFun h1 i
  simp at this

/-- Observability makes the eigenvalues distinct. -/
lemma lam_inj (c : Fin r → ℝ)
    (hobs : ∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) :
    Function.Injective lam := by
  intro i j hij
  by_contra hne
  set c' := (fun i => (c i : ℂ)) ᵥ* P
  set z : Fin r → ℂ := c' j • Pi.single i 1 - c' i • Pi.single j 1
  have hy := obsC c hobs (P *ᵥ z) fun x => by
    rw [phi_eigC hP hAP, mulVec_mulVec, nonsing_inv_mul P hP, one_mulVec]
    simp only [z, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [hij]; ring
  have h1 := congrArg (P⁻¹ *ᵥ ·) hy
  simp only [mulVec_mulVec, nonsing_inv_mul P hP, one_mulVec, mulVec_zero] at h1
  have := congrFun h1 i
  simp [z, hne] at this
  exact cP_ne hP hAP c hobs j this

end Eig

/-- Stage 6 with coinciding frequencies: each fiber's polynomials sum to zero. -/
lemma fiber_indep {ι : Type*} [Fintype ι] [DecidableEq ℂ] (φ : ι → ℂ) (q : ι → ℂ[X])
    (h : ∀ x : ℝ, ∑ i, (q i).eval (x : ℂ) * Complex.exp (φ i * x) = 0) (ν : ℂ) :
    ∑ i, (if φ i = ν then q i else 0) = 0 := by
  classical
  set s := Finset.univ.image φ
  set p : ℂ → ℂ[X] := fun ν => ∑ i, if φ i = ν then q i else 0
  have hs : ∀ x : ℝ, ∑ ν ∈ s, (p ν).eval (x : ℂ) * Complex.exp (ν * x) = 0 := fun x => by
    rw [← h x]
    simp only [p, eval_finsetSum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (φ i)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hi; exact absurd (Finset.mem_image_of_mem φ (Finset.mem_univ i)) hi
  by_cases hν : ν ∈ s
  · exact Novel.UnifiedSpliceExpPolyProof.expPolyS s p hs ν hν
  · refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · exact absurd (h ▸ Finset.mem_image_of_mem φ (Finset.mem_univ i)) hν
    · rfl

end Novel.UnifiedSpliceDiagLemmas

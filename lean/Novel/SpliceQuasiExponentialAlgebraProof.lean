import Standalone.SpliceQuasiExponentialAlgebra
import Novel.RecurrenceNecessityReductionProof

open Matrix NormedSpace Set Filter Topology Polynomial
open Standalone.SpliceQuasiExponentialAlgebra
namespace Novel.SpliceQuasiExponentialAlgebraProof

lemma vanishing : vanishingStatement := by
  intro r A hA c Tm h1 h2
  have hAi : A * A⁻¹ = 1 := mul_nonsing_inv A hA
  have hiA : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  have e1 : c ᵥ* A⁻¹ = Tm • c := by
    have := h1
    rw [vecMul_sub, vecMul_smul, vecMul_one, sub_eq_zero] at this
    exact this
  have e3 : c = Tm • (c ᵥ* A) := by
    have := congrArg (· ᵥ* A) e1
    simp only [vecMul_vecMul, hiA, vecMul_one, smul_vecMul] at this
    exact this
  have e2 : (2:ℝ) • c - Tm • (c ᵥ* A) = 0 := by
    have := h2
    rw [Matrix.mul_sub, hAi, Matrix.mul_smul, Matrix.mul_one, vecMul_add, vecMul_sub, vecMul_one,
      vecMul_smul] at this
    rw [← this]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  funext i
  have a1 := congrFun e2 i
  have a3 := congrFun e3 i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a1 a3 ⊢
  linarith

/-- Cayley–Hamilton for an invertible matrix: vanishing of `w M^k φ` for `k ≥ 2` gives it for
`k = 0, 1`. -/
lemma ch_low {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsUnit M.det)
    (w φ : ι → ℝ) (h : ∀ k, 2 ≤ k → w ⬝ᵥ ((M ^ k) *ᵥ φ) = 0) :
    w ⬝ᵥ φ = 0 ∧ w ⬝ᵥ (M *ᵥ φ) = 0 := by
  have hCH := Matrix.aeval_self_charpoly M
  rw [aeval_eq_sum_range] at hCH
  have hp0 : M.charpoly.coeff 0 ≠ 0 := by
    intro h0
    have := Matrix.det_eq_sign_charpoly_coeff M
    rw [h0, mul_zero] at this
    exact hM.ne_zero this
  have hsum : ∀ i : ℕ, ∑ j ∈ Finset.range (M.charpoly.natDegree + 1),
      M.charpoly.coeff j * (w ⬝ᵥ ((M ^ (j + i)) *ᵥ φ)) = 0 := by
    intro i
    have := congrArg (fun X => w ⬝ᵥ ((X * M ^ i) *ᵥ φ)) hCH
    simp only [Finset.sum_mul, sum_mulVec, dotProduct_sum, smul_mul_assoc, smul_mulVec,
      dotProduct_smul, smul_eq_mul, zero_mul, zero_mulVec, dotProduct_zero, ← pow_add] at this
    exact this
  have h1 : w ⬝ᵥ (M *ᵥ φ) = 0 := by
    have := hsum 1
    rw [Finset.sum_eq_single 0] at this
    · simpa [hp0] using this
    · intro j _ hj
      rw [h (j + 1) (by omega), mul_zero]
    · intro h; simp at h
  refine ⟨?_, h1⟩
  have := hsum 0
  rw [Finset.sum_eq_single 0] at this
  · simpa [hp0] using this
  · intro j _ hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this
      simp [h1]
    · rw [add_zero, h j hj2, mul_zero]
  · intro h; simp at h

variable {r : ℕ}

/-- The powers of `[[A, I], [0, A]]`. -/
lemma block_pow (A : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) :
    (fromBlocks A 1 0 A) ^ k = fromBlocks (A ^ k) ((k:ℝ) • A ^ (k - 1)) 0 (A ^ k) := by
  induction k with
  | zero => simp [fromBlocks_one]
  | succ k ih =>
    rw [pow_succ, ih, fromBlocks_multiply]
    congr 1
    · simp [pow_succ]
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [Matrix.smul_mul, pow_sub_one_mul (by omega), Matrix.mul_one, show k + 1 - 1 = k by omega]
        push_cast
        rw [add_smul, one_smul, add_comm]
    · simp
    · simp [pow_succ]

lemma block_value (A : Matrix (Fin r) (Fin r) ℝ) (c y z : Fin r → ℝ) (k : ℕ) :
    Sum.elim c 0 ⬝ᵥ ((fromBlocks A 1 0 A) ^ k *ᵥ Sum.elim y z) =
      c ⬝ᵥ ((A ^ k) *ᵥ y) + (k:ℝ) * c ⬝ᵥ ((A ^ (k - 1)) *ᵥ z) := by
  rw [block_pow, fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply,
    smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The functions `h_k(T) = c A^k e^{AT}(y + T z) + k c A^{k−1} e^{AT} z`. -/
noncomputable def hk (A : Matrix (Fin r) (Fin r) ℝ) (c y z : Fin r → ℝ) (k : ℕ) (T : ℝ) : ℝ :=
  c ⬝ᵥ ((A ^ k * exp (T • A)) *ᵥ (y + T • z)) +
    (k:ℝ) * c ⬝ᵥ ((A ^ (k - 1) * exp (T • A)) *ᵥ z)

lemma hk_deriv (A : Matrix (Fin r) (Fin r) ℝ) (c y z : Fin r → ℝ) (k : ℕ) (T : ℝ) :
    HasDerivAt (hk A c y z k) (hk A c y z (k+1) T) T := by
  have d1 := Novel.RecurrenceNecessityReductionProof.deriv_g A c y k T
  have d2 := Novel.RecurrenceNecessityReductionProof.deriv_g A c z k T
  have d3 := Novel.RecurrenceNecessityReductionProof.deriv_g A c z (k - 1) T
  have e : hk A c y z k = fun T => c ⬝ᵥ ((A ^ k * exp (T • A)) *ᵥ y) +
      T * c ⬝ᵥ ((A ^ k * exp (T • A)) *ᵥ z) +
      (k:ℝ) * c ⬝ᵥ ((A ^ (k - 1) * exp (T • A)) *ᵥ z) := by
    funext T
    simp only [hk, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e]
  have h := (d1.add ((hasDerivAt_id T).mul d2)).add (d3.const_mul (k:ℝ))
  convert h using 1
  · funext u
    simp only [Pi.add_apply, Pi.mul_apply, id]
  · show c ⬝ᵥ ((A ^ (k+1) * exp (T • A)) *ᵥ (y + T • z)) +
        ((k+1 : ℕ) : ℝ) * c ⬝ᵥ ((A ^ (k + 1 - 1) * exp (T • A)) *ᵥ z) = _
    rw [show k + 1 - 1 = k by omega]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, id, one_mul]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp; ring
    · rw [show k - 1 + 1 = k by omega]; push_cast; ring

/-- Two functions that agree on an open interval have the same derivative there. -/
lemma deriv_agree {f g : ℝ → ℝ} {f' g' : ℝ → ℝ} {d₁ d₂ : ℝ}
    (hf : ∀ T, HasDerivAt f (f' T) T) (hg : ∀ T, HasDerivAt g (g' T) T)
    (hfg : ∀ T ∈ Ioo d₁ d₂, f T = g T) : ∀ T ∈ Ioo d₁ d₂, f' T = g' T := by
  intro T hT
  have hev : f =ᶠ[𝓝 T] g := by
    filter_upwards [Ioo_mem_nhds hT.1 hT.2] with x hx
    exact hfg x hx
  exact (hf T).unique ((hg T).congr_of_eventuallyEq hev)

lemma affine : affineStatement := by
  intro r A hA c y z d₁ d₂ k₀ k₁ hd h
  have h0 : ∀ T, hk A c y z 0 T = c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) := fun T => by
    simp [hk]
  have hh1 := deriv_agree (fun T => hk_deriv A c y z 0 T)
    (fun T => ((hasDerivAt_id T).const_mul k₁).const_add k₀) (fun T hT => by rw [h0, h T hT]; rfl)
  have hh2 := deriv_agree (fun T => hk_deriv A c y z 1 T) (fun T => hasDerivAt_const T k₁)
    (fun T hT => by rw [hh1 T hT]; simp)
  have hall : ∀ k, 2 ≤ k → ∀ T ∈ Ioo d₁ d₂, hk A c y z k T = 0 := by
    intro k hk2
    induction k, hk2 using Nat.le_induction with
    | base => intro T hT; simpa using hh2 T hT
    | succ k _ ih =>
      exact deriv_agree (fun T => hk_deriv A c y z k T) (fun T => hasDerivAt_const T (0:ℝ)) ih
  intro T0 hT0
  set E0 := exp (T0 • A)
  have hval : ∀ k, hk A c y z k T0 =
      Sum.elim c 0 ⬝ᵥ ((fromBlocks A 1 0 A) ^ k *ᵥ Sum.elim (E0 *ᵥ (y + T0 • z)) (E0 *ᵥ z)) := by
    intro k
    rw [block_value, hk, ← mulVec_mulVec, ← mulVec_mulVec]
  have hdet : IsUnit (fromBlocks A 1 0 A).det := by
    rw [det_fromBlocks_zero₂₁]; exact hA.mul hA
  have := ch_low (fromBlocks A 1 0 A) hdet (Sum.elim c 0) (Sum.elim (E0 *ᵥ (y + T0 • z)) (E0 *ᵥ z))
    (fun k hk2 => by rw [← hval]; exact hall k hk2 T0 hT0)
  rw [← h0, show hk A c y z 0 T0 = _ from by rw [hval 0]]
  simpa using this.1

theorem spliceQuasiExponentialAlgebra : Standalone.SpliceQuasiExponentialAlgebra.statement := ⟨affine, vanishing⟩

end Novel.SpliceQuasiExponentialAlgebraProof

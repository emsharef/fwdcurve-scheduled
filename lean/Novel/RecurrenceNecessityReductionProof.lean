import Standalone.RecurrenceNecessityReduction
import Novel.RecurrentLoadingStatePProof
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Matrix NormedSpace Polynomial Filter Topology
open Standalone.RecurrenceNecessityReduction
namespace Novel.RecurrenceNecessityReductionProof

variable {r : ℕ}

/-- The Krylov matrix `[b, Ab, ..., A^{r−1} b]`. -/
def krylov (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => ((A ^ (j:ℕ)) *ᵥ b) i

/-- The companion matrix of the characteristic polynomial of `A`. -/
noncomputable def comp (A : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => if (i:ℕ) = j + 1 then 1 else if (j:ℕ) + 1 = r then -A.charpoly.coeff i else 0

/-- Cayley–Hamilton, applied to `b`: `A^r b = −∑_{k<r} p_k A^k b`. -/
lemma cayley_vec (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    (A ^ r) *ᵥ b = ∑ k : Fin r, (-A.charpoly.coeff k) • ((A ^ (k:ℕ)) *ᵥ b) := by
  have hCH := Matrix.aeval_self_charpoly A
  rw [aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin, Finset.sum_range_succ] at hCH
  have hlead : A.charpoly.coeff r = 1 := by
    have := (charpoly_monic A).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [hlead, one_smul] at hCH
  have h := congrArg (· *ᵥ b) hCH
  simp only [add_mulVec, zero_mulVec, sum_mulVec, smul_mulVec] at h
  rw [← Fin.sum_univ_eq_sum_range (fun k => A.charpoly.coeff k • ((A ^ k) *ᵥ b))] at h
  simp only [neg_smul, Finset.sum_neg_distrib]
  linear_combination h

lemma krylov_comp (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    A * krylov A b = krylov A b * comp A := by
  ext i j
  have hL : (A * krylov A b) i j = ((A ^ ((j:ℕ) + 1)) *ᵥ b) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [mul_apply, krylov, mulVec, dotProduct]
  rw [hL]
  simp only [mul_apply, krylov, comp, of_apply]
  by_cases hj : (j:ℕ) + 1 < r
  · rw [Finset.sum_eq_single ⟨(j:ℕ) + 1, hj⟩]
    · simp
    · intro k _ hk
      have : (k:ℕ) ≠ j + 1 := fun h => hk (Fin.ext h)
      simp [this, show (j:ℕ) + 1 ≠ r by omega]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hjr : (j:ℕ) + 1 = r := by omega
    have hk : ∀ k : Fin r, ¬ ((k:ℕ) = r) := fun k => by omega
    simp only [hjr, if_true]
    simp only [hk, if_false]
    rw [cayley_vec A b]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Intertwined exponentials: `A Q = Q C` gives `e^{xA} Q = Q e^{xC}`. -/
lemma exp_intertwine (A C Q : Matrix (Fin r) (Fin r) ℝ) (h : A * Q = Q * C) (x : ℝ) :
    exp (x • A) * Q = Q * exp (x • C) := by
  open scoped Matrix.Norms.Operator in
  have hn : ∀ n : ℕ, (x • A) ^ n * Q = Q * (x • C) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, smul_mul_assoc, h, ← mul_smul_comm,
        ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hsA : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (x • A) ^ n) := by
    open scoped Matrix.Norms.Operator in exact expSeries_summable' (𝕂 := ℝ) (x • A)
  have hsC : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (x • C) ^ n) := by
    open scoped Matrix.Norms.Operator in exact expSeries_summable' (𝕂 := ℝ) (x • C)
  rw [exp_eq_tsum ℝ]
  simp only
  rw [← hsA.tsum_mul_right Q, ← hsC.tsum_mul_left Q]
  congr 1
  funext n
  rw [smul_mul_assoc, hn, mul_smul_comm]

/-- The companion matrix shifts the unit vectors. -/
lemma comp_pow_single (A : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) (hk : k < r) :
    (comp A ^ k) *ᵥ Pi.single (⟨0, by omega⟩ : Fin r) 1 = Pi.single (⟨k, hk⟩ : Fin r) 1 := by
  induction k with
  | zero => rw [pow_zero, one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega)]
    funext i
    simp only [mulVec, dotProduct, comp, of_apply]
    rw [Finset.sum_eq_single ⟨k, by omega⟩]
    · simp only [Pi.single_eq_same, mul_one]
      by_cases hi : (i:ℕ) = k + 1
      · have : i = ⟨k+1, hk⟩ := Fin.ext hi
        subst this
        simp
      · have hne : i ≠ ⟨k+1, hk⟩ := fun h => hi (by rw [h])
        simp [hi, hne, show k + 1 ≠ r by omega]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h


lemma exp_entry_cont (C : Matrix (Fin r) (Fin r) ℝ) (i j : Fin r) :
    Continuous fun u : ℝ => exp (u • C) i j :=
  continuous_iff_continuousAt.2 fun u =>
    (Novel.RecurrentLoadingStatePProof.exp_entry_hasDerivAt C i j u).continuousAt

lemma phi_cont (C : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (i : Fin r) :
    Continuous fun u : ℝ => (exp (u • C) *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => (exp_entry_cont C i j).mul continuous_const

/-- The derivative of `u ↦ x · C^k e^{uC} v`. -/
lemma deriv_g (C : Matrix (Fin r) (Fin r) ℝ) (x v : Fin r → ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => x ⬝ᵥ ((C ^ k * exp (u • C)) *ᵥ v))
      (x ⬝ᵥ ((C ^ (k+1) * exp (u • C)) *ᵥ v)) u := by
  have hE : ∀ l j, HasDerivAt (fun u : ℝ => exp (u • C) l j) ((C * exp (u • C)) l j) u :=
    fun l j => Novel.RecurrentLoadingStatePProof.exp_entry_hasDerivAt C l j u
  have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    (HasDerivAt.sum (u := Finset.univ) fun j _ =>
      ((HasDerivAt.sum (u := Finset.univ) fun l _ =>
        (hE l j).const_mul ((C ^ k) i l)).mul_const (v j))).const_mul (x i)
  rw [pow_succ, Matrix.mul_assoc]
  convert h using 1
  · funext w
    simp [dotProduct, mulVec, mul_apply, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  · simp [dotProduct, mulVec, mul_apply, Finset.mul_sum, Finset.sum_mul]

lemma gamma_posDef (A : Matrix (Fin r) (Fin r) ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    (gamma032 (comp A) (Pi.single (⟨0, hr⟩ : Fin r) 1) δ).PosDef := by
  set C := comp A
  set e0 : Fin r → ℝ := Pi.single (⟨0, hr⟩ : Fin r) 1
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, gamma032, of_apply, star_trivial]
    congr 1
    funext u
    ring
  set g : ℝ → ℝ := fun u => x ⬝ᵥ (exp (u • C) *ᵥ e0)
  have hgc : Continuous g := by
    simp only [g, dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (phi_cont C e0 i)
  have hquad : star x ⬝ᵥ (gamma032 C e0 δ *ᵥ x) = ∫ u in (0:ℝ)..δ, g u ^ 2 := by
    set φ : ℝ → Fin r → ℝ := fun u => exp (u • C) *ᵥ e0 with hφ
    have hφc : ∀ i, Continuous fun u => φ u i := phi_cont C e0
    have hii : ∀ i j, IntervalIntegrable (fun u : ℝ => x i * x j * (φ u i * φ u j))
        MeasureTheory.volume 0 δ := fun i j =>
      (continuous_const.mul ((hφc i).mul (hφc j))).intervalIntegrable _ _
    have e : (fun u => g u ^ 2) = fun u => ∑ i, ∑ j, x i * x j * (φ u i * φ u j) := by
      funext u
      simp only [g, dotProduct]
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hii2 : ∀ i, IntervalIntegrable (fun u : ℝ => ∑ j, x i * x j * (φ u i * φ u j))
        MeasureTheory.volume 0 δ := fun i => by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => hii i j) using 1
      funext u
      simp [Finset.sum_apply]
    have hG : ∀ i j, gamma032 C e0 δ i j = ∫ u in (0:ℝ)..δ, φ u i * φ u j := fun i j => rfl
    rw [e, intervalIntegral.integral_finsetSum fun i _ => hii2 i, star_trivial]
    simp only [dotProduct, mulVec, hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => hii i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hquad]
  refine intervalIntegral.integral_pos hδ (hgc.pow 2).continuousOn (fun u _ => sq_nonneg _) ?_
  by_contra hne
  push Not at hne
  have hg0 : ∀ u ∈ Set.Ioo 0 δ, g u = 0 := fun u hu =>
    pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm (hne u (Set.Ioo_subset_Icc_self hu))
      (sq_nonneg _))
  have hz : ∀ k : ℕ, ∀ u ∈ Set.Ioo 0 δ, x ⬝ᵥ ((C ^ k * exp (u • C)) *ᵥ e0) = 0 := by
    intro k
    induction k with
    | zero => intro u hu; simpa [g] using hg0 u hu
    | succ k ih =>
      intro u hu
      have hev : (fun w : ℝ => x ⬝ᵥ ((C ^ k * exp (w • C)) *ᵥ e0)) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw
        exact ih w hw
      exact (deriv_g C x e0 k u).unique ((hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev)
  have hu0 : δ / 2 ∈ Set.Ioo 0 δ := ⟨by positivity, by linarith⟩
  have hcomm : ∀ k : ℕ, C ^ k * exp ((δ / 2) • C) = exp ((δ / 2) • C) * C ^ k := fun k =>
    (exp_intertwine C C (C ^ k) (by rw [← pow_succ', ← pow_succ]) (δ / 2)).symm
  set E0 := exp ((δ / 2) • C)
  have hvk : ∀ k : Fin r, (x ᵥ* E0) k = 0 := by
    intro k
    have h := hz k (δ / 2) hu0
    rw [hcomm, ← mulVec_mulVec, comp_pow_single A k k.isLt, dotProduct_mulVec,
      dotProduct_single, mul_one] at h
    simpa using h
  have hv : x ᵥ* E0 = 0 := funext hvk
  have hdet : IsUnit E0.det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  apply hx
  calc x = (x ᵥ* E0) ᵥ* E0⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hdet, vecMul_one]
    _ = 0 := by rw [hv, zero_vecMul]

lemma reduction : reductionStatement := by
  intro r A b c
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨0, 0, 0, fun x => by simp [dotProduct], fun δ _ => ?_, fun ⟨x, hx⟩ => by
      simp [dotProduct] at hx⟩
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
    ext i
    exact i.elim0
  · set Q := krylov A b
    set e0 : Fin r → ℝ := Pi.single (⟨0, hr⟩ : Fin r) 1
    have hQe : Q *ᵥ e0 = b := by
      funext i
      simp only [mulVec, dotProduct, e0]
      rw [Finset.sum_eq_single ⟨0, hr⟩]
      · simp [Q, krylov]
      · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hlam : ∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ b) = (c ᵥ* Q) ⬝ᵥ (exp (x • comp A) *ᵥ e0) := by
      intro x
      rw [← hQe, mulVec_mulVec, exp_intertwine A (comp A) Q (krylov_comp A b) x,
        ← mulVec_mulVec, dotProduct_mulVec]
    refine ⟨comp A, e0, c ᵥ* Q, hlam, fun δ hδ => gamma_posDef A hr δ hδ, fun ⟨x, hx⟩ h0 => ?_⟩
    apply hx
    rw [hlam x, h0, zero_dotProduct]

theorem recurrenceNecessityReduction : Standalone.RecurrenceNecessityReduction.statement := reduction

end Novel.RecurrenceNecessityReductionProof

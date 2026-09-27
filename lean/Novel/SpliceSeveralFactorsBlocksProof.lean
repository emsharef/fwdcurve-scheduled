import Standalone.SpliceSeveralFactorsBlocks
import Novel.SpliceSeveralFactorsAX01Proof
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix NormedSpace MeasureTheory Set Filter Polynomial
open Standalone.SpliceSeveralFactorsAX01 Standalone.SpliceSeveralFactorsBlocks
namespace Novel.SpliceSeveralFactorsBlocksProof

section General
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `d/dx c e^{Ax} y = c e^{Ax} A y`. -/
lemma cexp_deriv (A : Matrix ι ι ℝ) (c y : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun h : ℝ => c ⬝ᵥ (exp (h • A) *ᵥ y)) (c ⬝ᵥ (exp (t • A) *ᵥ (A *ᵥ y))) t := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun h : ℝ => exp (h • A)) (exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  let Lm : Matrix ι ι ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => c ⬝ᵥ (X *ᵥ y)
        map_add' := fun X Y => by rw [add_mulVec, dotProduct_add]
        map_smul' := fun a X => by rw [smul_mulVec, dotProduct_smul]; rfl }
  have h2 := HasFDerivAt.comp_hasDerivAt (x := t) Lm.hasFDerivAt h1
  convert h2 using 1
  all_goals first
    | rfl
    | (show _ = c ⬝ᵥ ((exp (t • A) * A) *ᵥ y); rw [← mulVec_mulVec])

/-- The unobservable set is invariant under `A`. -/
lemma unobs_A (A : Matrix ι ι ℝ) (c y : ι → ℝ) (hy : ∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) :
    ∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ (A *ᵥ y)) = 0 := fun x => by
  have h0 : HasDerivAt (fun h : ℝ => c ⬝ᵥ (exp (h • A) *ᵥ y)) 0 x := by
    have : (fun h : ℝ => c ⬝ᵥ (exp (h • A) *ᵥ y)) = fun _ => 0 := funext hy
    rw [this]; exact hasDerivAt_const x 0
  exact (cexp_deriv A c y x).unique h0

/-- The unobservable set is invariant under every polynomial in `A`. -/
lemma unobs_poly (A : Matrix ι ι ℝ) (c : ι → ℝ) (q : ℝ[X]) :
    ∀ y : ι → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) →
      ∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ (aeval A q *ᵥ y)) = 0 := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro y hy x
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, mulVec_smul,
      dotProduct_smul, hy x, smul_zero]
  | add p q hp hq =>
    intro y hy x
    rw [map_add, add_mulVec, mulVec_add, dotProduct_add, hp y hy x, hq y hy x, add_zero]
  | monomial n a ih =>
    intro y hy x
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← mulVec_mulVec]
    exact ih (A *ᵥ y) (unobs_A A c y hy) x

/-- Disjoint complex spectra make the characteristic polynomials coprime. -/
lemma coprime_of_disjoint {κ : Type} [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℝ)
    (B : Matrix κ κ ℝ)
    (hd : Disjoint (spectrum ℂ (A.map (algebraMap ℝ ℂ))) (spectrum ℂ (B.map (algebraMap ℝ ℂ)))) :
    IsCoprime A.charpoly B.charpoly := by
  classical
  by_contra hnc
  set d := EuclideanDomain.gcd A.charpoly B.charpoly
  have hu : ¬ IsUnit d := fun h => hnc (EuclideanDomain.gcd_isUnit_iff.1 h)
  have hd0 : d ≠ 0 := fun h => A.charpoly_monic.ne_zero
    ((EuclideanDomain.gcd_eq_zero_iff.1 h).1)
  have hdeg : 0 < (d.map (algebraMap ℝ ℂ)).degree := by
    rw [degree_map]; exact degree_pos_of_ne_zero_of_nonunit hd0 hu
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hroot : ∀ {μ : Type} [Fintype μ] [DecidableEq μ] (M : Matrix μ μ ℝ), d ∣ M.charpoly →
      z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := fun M hM => by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_map]
    exact eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hM) hz
  exact Set.disjoint_left.1 hd (hroot A (EuclideanDomain.gcd_dvd_left _ _))
    (hroot B (EuclideanDomain.gcd_dvd_right _ _))

end General

section Block
variable {J : ℕ} {r : Fin J → ℕ}

/-- `blockDiagonal'` as an algebra homomorphism. -/
noncomputable def bdAlg (J : ℕ) (r : Fin J → ℕ) :
    (∀ j : Fin J, Matrix (Fin (r j)) (Fin (r j)) ℝ) →ₐ[ℝ]
      Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ :=
  { blockDiagonal'RingHom (fun j => Fin (r j)) ℝ with
    commutes' := fun a => by
      show blockDiagonal' (algebraMap ℝ _ a) = algebraMap ℝ _ a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, blockDiagonal'_smul,
        blockDiagonal'_one] }

lemma aeval_bd (A : ∀ j : Fin J, Matrix (Fin (r j)) (Fin (r j)) ℝ) (q : ℝ[X]) :
    aeval (blockDiagonal' A) q = blockDiagonal' fun j => aeval (A j) q := by
  have h := aeval_algHom_apply (bdAlg J r) A q
  rw [aeval_pi_apply] at h
  exact h

lemma exp_bd (A : ∀ j : Fin J, Matrix (Fin (r j)) (Fin (r j)) ℝ) (x : ℝ) :
    exp (x • blockDiagonal' A) = blockDiagonal' fun j => exp (x • A j) := by
  rw [← blockDiagonal'_smul, exp_blockDiagonal']
  congr 1
  funext j
  open scoped Matrix.Norms.Operator in
  exact Pi.coe_exp _ j

lemma bd_mulVec (M : ∀ j : Fin J, Matrix (Fin (r j)) (Fin (r j)) ℝ) (y : (Σ j, Fin (r j)) → ℝ)
    (j : Fin J) (a : Fin (r j)) :
    (blockDiagonal' M *ᵥ y) ⟨j, a⟩ = (M j *ᵥ fun b => y ⟨j, b⟩) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp only [blockDiagonal'_apply_eq]
  · intro i _ hij
    exact Finset.sum_eq_zero fun b _ => by rw [blockDiagonal'_apply_ne M a b (Ne.symm hij), zero_mul]
  · simp

lemma blockC_dot (c : (j : Fin J) → Fin (r j) → ℝ) (v : (Σ j, Fin (r j)) → ℝ) :
    blockC c ⬝ᵥ v = ∑ j, c j ⬝ᵥ fun a => v ⟨j, a⟩ := by
  simp only [dotProduct, blockC, Fintype.sum_sigma]

end Block

lemma pbh : Standalone.SpliceSeveralFactorsBlocks.pbhStatement := by
  intro J r A c hobs hdisj y hy
  classical
  have hblock : ∀ j : Fin J, (fun b => y ⟨j, b⟩) = 0 := by
    intro j
    set q : ℝ[X] := ∏ i ∈ Finset.univ.erase j, (A i).charpoly
    have hq0 : ∀ i, i ≠ j → aeval (A i) q = 0 := fun i hi => by
      obtain ⟨g, hg⟩ := Finset.dvd_prod_of_mem (fun i => (A i).charpoly)
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
      have hq : q = (A i).charpoly * g := hg
      rw [hq, map_mul, aeval_self_charpoly, zero_mul]
    have hN := unobs_poly (blockDiagonal' A) (blockC c) q y hy
    have hj : ∀ x : ℝ, c j ⬝ᵥ (exp (x • A j) *ᵥ (aeval (A j) q *ᵥ fun b => y ⟨j, b⟩)) = 0 := by
      intro x
      have := hN x
      rw [aeval_bd, exp_bd, blockC_dot] at this
      rw [← this, Finset.sum_eq_single j]
      · congr 1
        funext a
        rw [bd_mulVec]
        congr 1
        funext b
        rw [bd_mulVec]
      · intro i _ hij
        have e : (fun a => (blockDiagonal' (fun j => exp (x • A j)) *ᵥ
            (blockDiagonal' (fun j => aeval (A j) q) *ᵥ y)) ⟨i, a⟩) = 0 := by
          funext a
          rw [bd_mulVec]
          have : (fun b => (blockDiagonal' (fun j => aeval (A j) q) *ᵥ y) ⟨i, b⟩) = 0 := by
            funext b
            rw [bd_mulVec, hq0 i hij, zero_mulVec]
          rw [this, mulVec_zero]
        rw [e, dotProduct_zero]
      · simp
    have hzero := hobs j _ hj
    have hcop : IsCoprime (A j).charpoly q := IsCoprime.prod_right fun i hi =>
      coprime_of_disjoint (A j) (A i) (hdisj j i (Finset.ne_of_mem_erase hi).symm)
    obtain ⟨u, v, huv⟩ := hcop
    have h1 := congrArg (aeval (A j)) huv
    rw [map_add, map_mul, map_mul, aeval_self_charpoly, mul_zero, zero_add, map_one] at h1
    calc (fun b => y ⟨j, b⟩) = (aeval (A j) v * aeval (A j) q) *ᵥ fun b => y ⟨j, b⟩ := by
          rw [h1, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hzero, mulVec_zero]
  funext ⟨j, a⟩
  exact congrFun (hblock j) a

lemma reindexObs : Standalone.SpliceSeveralFactorsBlocks.reindexStatement := by
  intro ι κ _ _ _ _ e A c hobs y hy
  have hexp : ∀ x : ℝ, exp (x • reindex e e A) = reindex e e (exp (x • A)) := fun x => by
    open scoped Matrix.Norms.Operator in
    have hc : Continuous (reindexAlgEquiv ℝ ℝ e) :=
      LinearMap.continuous_of_finiteDimensional (reindexAlgEquiv ℝ ℝ e).toLinearEquiv.toLinearMap
    have := map_exp (reindexAlgEquiv ℝ ℝ e) hc (x • A)
    simp only [coe_reindexAlgEquiv, reindex_apply] at this ⊢
    convert this.symm using 2 <;> rfl
  have key : ∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ (y ∘ e)) = 0 := fun x => by
    have := hy x
    rw [hexp] at this
    rw [← this]
    simp only [dotProduct, mulVec, reindex_apply, submatrix_apply, Function.comp]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.symm_apply_apply]
    congr 1
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
  have h0 := hobs _ key
  funext k
  have := congrFun h0 (e.symm k)
  simpa using this

lemma blockwise : Standalone.SpliceSeveralFactorsBlocks.blockwiseStatement := by
  intro J r A c hobs hdisj n e hdet k L s HS HZ dL dC bZ z Tm H h hAX τ hτ hτH
  have hO := reindexObs _ _ e _ _ (pbh J r A c hobs hdisj)
  filter_upwards [Novel.SpliceSeveralFactorsAX01Proof.necessity n k L _ hdet _ hO s HS HZ dL dC bZ
    z Tm H h hAX τ hτ hτH] with u hu hu' j a
  rw [hu hu']
  rfl

theorem spliceSeveralFactorsBlocks : Standalone.SpliceSeveralFactorsBlocks.statement :=
  ⟨pbh, reindexObs, blockwise⟩

end Novel.SpliceSeveralFactorsBlocksProof

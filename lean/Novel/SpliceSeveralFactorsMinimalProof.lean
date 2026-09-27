import Standalone.SpliceSeveralFactorsMinimal
import Novel.SpliceSeveralFactorsBlocksProof

open Matrix NormedSpace MeasureTheory Set Filter Polynomial
open Standalone.SpliceSeveralFactorsAX01 Standalone.SpliceSeveralFactorsBlocks
open Standalone.SpliceSeveralFactorsMinimal
namespace Novel.SpliceSeveralFactorsMinimalProof

variable {r r' : ℕ}

/-- `P 𝒜 = 𝒜' P` carries through the exponential: `P e^{x𝒜} = e^{x𝒜'} P`. -/
lemma exp_intertwine (P : Matrix (Fin r') (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (A' : Matrix (Fin r') (Fin r') ℝ) (h : P * A = A' * P) (x : ℝ) :
    P * exp (x • A) = exp (x • A') * P := by
  have hpow : ∀ n : ℕ, P * (x • A) ^ n = (x • A') ^ n * P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.mul_smul, h,
        ← Matrix.smul_mul, ← Matrix.mul_assoc, ← pow_succ]
  have hA : HasSum (fun n => ((n.factorial : ℝ)⁻¹) • (x • A) ^ n) (exp (x • A)) := by
    open scoped Matrix.Norms.Operator in exact exp_series_hasSum_exp' (x • A)
  have hA' : HasSum (fun n => ((n.factorial : ℝ)⁻¹) • (x • A') ^ n) (exp (x • A')) := by
    open scoped Matrix.Norms.Operator in exact exp_series_hasSum_exp' (x • A')
  let gL : Matrix (Fin r) (Fin r) ℝ →+ Matrix (Fin r') (Fin r) ℝ :=
    { toFun := fun M => P * M, map_zero' := Matrix.mul_zero P, map_add' := Matrix.mul_add P }
  let gR : Matrix (Fin r') (Fin r') ℝ →+ Matrix (Fin r') (Fin r) ℝ :=
    { toFun := fun M => M * P, map_zero' := Matrix.zero_mul P,
      map_add' := fun M N => Matrix.add_mul M N P }
  have h1 := hA.map gL (continuous_const.matrix_mul continuous_id)
  have h2 := hA'.map gR (continuous_id.matrix_mul continuous_const)
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp only [Function.comp, gL, gR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_smul,
    Matrix.smul_mul, hpow]

/-- `P 𝒜^n = 𝒜'^n P`. -/
lemma pow_intertwine (P : Matrix (Fin r') (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (A' : Matrix (Fin r') (Fin r') ℝ) (h : P * A = A' * P) (n : ℕ) : P * A ^ n = A' ^ n * P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← pow_succ]

lemma minimal : Standalone.SpliceSeveralFactorsMinimal.minimalStatement := by
  intro r A hA c
  classical
  -- the unobservable subspace
  let ℓ : ℕ → (Fin r → ℝ) →ₗ[ℝ] ℝ := fun n =>
    { toFun := fun y => c ⬝ᵥ ((A ^ n) *ᵥ y)
      map_add' := fun y z => by rw [mulVec_add, dotProduct_add]
      map_smul' := fun a y => by rw [mulVec_smul, dotProduct_smul]; rfl }
  let N : Submodule ℝ (Fin r → ℝ) := ⨅ n, LinearMap.ker (ℓ n)
  have memN : ∀ y, y ∈ N ↔ ∀ n, c ⬝ᵥ ((A ^ n) *ᵥ y) = 0 := fun y => by
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hAN : ∀ y ∈ N, A *ᵥ y ∈ N := fun y hy => (memN _).2 fun n => by
    rw [mulVec_mulVec, ← pow_succ]; exact (memN y).1 hy (n + 1)
  have hinj : Function.Injective (A *ᵥ ·) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA)
  have hNA : ∀ y, A *ᵥ y ∈ N → y ∈ N := by
    intro y hy
    let f : N →ₗ[ℝ] N := (Matrix.toLin' A).restrict fun y hy => by
      rw [Matrix.toLin'_apply]; exact hAN y hy
    have hf : Function.Injective f := fun a b hab => Subtype.ext (hinj (by
      have := congrArg Subtype.val hab
      simpa [f, Matrix.toLin'_apply] using this))
    obtain ⟨n, hn⟩ := (LinearMap.injective_iff_surjective.1 hf) ⟨A *ᵥ y, hy⟩
    have : A *ᵥ (n : Fin r → ℝ) = A *ᵥ y := by
      have := congrArg Subtype.val hn
      simpa [f, Matrix.toLin'_apply] using this
    rw [← hinj this]
    exact n.2
  -- the quotient and its basis
  let Q := (Fin r → ℝ) ⧸ N
  let b := Module.finBasis ℝ Q
  let AQ : Q →ₗ[ℝ] Q := N.mapQ N (Matrix.toLin' A) fun y hy => by
    rw [Submodule.mem_comap, Matrix.toLin'_apply]; exact hAN y hy
  let cQ : Q →ₗ[ℝ] ℝ := N.liftQ (ℓ 0) fun y hy => by
    rw [LinearMap.mem_ker]; exact (memN y).1 hy 0
  let A' := LinearMap.toMatrix b b AQ
  let P := LinearMap.toMatrix (Pi.basisFun ℝ (Fin r)) b N.mkQ
  let c' : Fin (Module.finrank ℝ Q) → ℝ := fun i => cQ (b i)
  have hP : ∀ z, P *ᵥ z = b.repr (N.mkQ z) := fun z => by
    have := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin r)) b N.mkQ z
    have e : ⇑((Pi.basisFun ℝ (Fin r)).repr z) = z := funext fun i => by simp
    rw [e] at this
    exact this
  have hc' : ∀ q : Q, c' ⬝ᵥ b.repr q = cQ q := fun q => by
    conv_rhs => rw [← b.sum_repr q]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, c']
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcP : ∀ z, c' ⬝ᵥ (P *ᵥ z) = c ⬝ᵥ z := fun z => by
    rw [hP, hc']
    show (N.liftQ (ℓ 0) _) (N.mkQ z) = _
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    show c ⬝ᵥ ((A ^ 0) *ᵥ z) = _
    rw [pow_zero, one_mulVec]
  have hPA : P * A = A' * P := by
    have e1 : LinearMap.toMatrix (Pi.basisFun ℝ (Fin r)) b (N.mkQ.comp (Matrix.toLin' A)) = P * A := by
      rw [LinearMap.toMatrix_comp (Pi.basisFun ℝ (Fin r)) (Pi.basisFun ℝ (Fin r)) b,
        LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have e2 : LinearMap.toMatrix (Pi.basisFun ℝ (Fin r)) b (AQ.comp N.mkQ) = A' * P :=
      LinearMap.toMatrix_comp (Pi.basisFun ℝ (Fin r)) b b AQ N.mkQ
    rw [← e1, ← e2, Submodule.mapQ_mkQ]
  refine ⟨Module.finrank ℝ Q, A', c', P, ?_, ?_, hPA, fun x z => ?_⟩
  · -- `𝒜'` is invertible
    have hker : LinearMap.ker AQ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro q hq
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N q
      have h2 : (Submodule.Quotient.mk (A *ᵥ y) : Q) = 0 := by
        rw [← hq]
        show _ = AQ (N.mkQ y)
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Matrix.toLin'_apply]
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero N).2 (hNA y ((Submodule.Quotient.mk_eq_zero N).1 h2))
    have hu : IsUnit AQ := (LinearMap.isUnit_iff_ker_eq_bot AQ).2 hker
    have hu' : IsUnit A' := hu.map (LinearMap.toMatrixAlgEquiv b)
    exact (Matrix.isUnit_iff_isUnit_det A').1 hu'
  · -- `(𝒜', C')` is observable
    intro v hv
    have hn : ∀ n : ℕ, c' ⬝ᵥ ((A' ^ n) *ᵥ v) = 0 := by
      have hall : ∀ n : ℕ, ∀ x : ℝ, c' ⬝ᵥ (exp (x • A') *ᵥ ((A' ^ n) *ᵥ v)) = 0 := by
        intro n
        induction n with
        | zero => simpa using hv
        | succ n ih =>
          intro x
          rw [pow_succ', ← mulVec_mulVec]
          exact Novel.SpliceSeveralFactorsBlocksProof.unobs_A A' c' _ ih x
      intro n
      have := hall n 0
      simpa using this
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective N (b.equivFun.symm v)
    have hPy : P *ᵥ y = v := by
      rw [hP, hy, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hyN : y ∈ N := (memN y).2 fun n => by
      rw [← hcP, mulVec_mulVec, pow_intertwine P A A' hPA n, ← mulVec_mulVec, hPy]
      exact hn n
    have hq : b.equivFun.symm v = 0 := by
      rw [← hy, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero N).2 hyN
    have := congrArg b.equivFun hq
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · rw [← hcP, mulVec_mulVec, exp_intertwine P A A' hPA x, ← mulVec_mulVec]

lemma reduced : Standalone.SpliceSeveralFactorsMinimal.reducedStatement := by
  intro r k L A hA c s HS HZ dL dC bZ z Tm H h hAX
  obtain ⟨r', A', c', P, hA', hobs, hPA, hexp⟩ := minimal r A hA c
  refine ⟨r', A', c', P, hA', hobs, hexp, ?_⟩
  let HZ' : ℝ → Fin r' → Fin k → ℝ := fun u i l => (P *ᵥ fun i' => HZ u i' l) i
  let bZ' : ℝ → Fin r' → ℝ := fun u => P *ᵥ bZ u
  let z' : ℝ → Fin r' → ℝ := fun u => P *ᵥ z u
  obtain ⟨hs, hHS, hHZ, hz, ⟨C, hsC, hHSC, hHZC, hzC⟩, hdL, hdC, hbZ⟩ := h
  set Cp := ∑ i, ∑ i', |P i i'|
  have hCp : 0 ≤ Cp := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrow : ∀ i, ∑ i', |P i i'| ≤ Cp := fun i =>
    Finset.single_le_sum (f := fun i => ∑ i', |P i i'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hbd : ∀ (w : Fin r → ℝ) (i : Fin r'), (∀ i', |w i'| ≤ |C|) → |(P *ᵥ w) i| ≤ Cp * |C| :=
    fun w i hw => by
      simp only [mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i', |P i i' * w i'| ≤ ∑ i', |P i i'| * |C| := Finset.sum_le_sum fun i' _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw i') (abs_nonneg _)
        _ = (∑ i', |P i i'|) * |C| := by rw [Finset.sum_mul]
        _ ≤ Cp * |C| := mul_le_mul_of_nonneg_right (hrow i) (abs_nonneg _)
  have hmeas : ∀ (w : ℝ → Fin r → ℝ), (∀ i', Measurable fun u => w u i') →
      ∀ i, Measurable fun u => (P *ᵥ w u) i := fun w hw i => by
    simp only [mulVec, dotProduct]
    exact Finset.measurable_sum _ fun i' _ => measurable_const.mul (hw i')
  have hPD' : PathData041 s HS HZ' dL dC bZ' z' H := by
    refine ⟨hs, hHS, fun i l => hmeas (fun u i' => HZ u i' l) (fun i' => hHZ i' l) i,
      fun i => hmeas z hz i, ⟨Cp * |C| + |C|, fun ℓ j u => ?_, fun ℓ u l => ?_, fun u i l => ?_,
      fun u i => ?_⟩, hdL, hdC, fun i => ?_⟩
    · exact ((hsC ℓ j u).trans (le_abs_self C)).trans
        (le_add_of_nonneg_left (mul_nonneg hCp (abs_nonneg _)))
    · exact ((hHSC ℓ u l).trans (le_abs_self C)).trans
        (le_add_of_nonneg_left (mul_nonneg hCp (abs_nonneg _)))
    · exact (hbd _ i fun i' => (hHZC u i' l).trans (le_abs_self C)).trans
        (le_add_of_nonneg_right (abs_nonneg _))
    · exact (hbd _ i fun i' => (hzC u i').trans (le_abs_self C)).trans
        (le_add_of_nonneg_right (abs_nonneg _))
    · show IntervalIntegrable (fun u => ∑ i', P i i' * bZ u i') volume 0 H
      exact Novel.SpliceStateBlockAX01Proof.ii_sum fun i' => (hbZ i').const_mul _
  have hsig : ∀ u v, sigma041 s HS HZ' Tm c' A' u v = sigma041 s HS HZ Tm c A u v :=
    fun u v => funext fun l => by
      simp only [sigma041]
      rw [hexp]
  have hdB : ∀ u T, Standalone.SpliceStateBlockAX01.driftB c' A' bZ' z' u T =
      Standalone.SpliceStateBlockAX01.driftB c A bZ z u T := fun u T => by
    show c' ⬝ᵥ (exp ((T - u) • A') *ᵥ (P *ᵥ bZ u - A' *ᵥ (P *ᵥ z u))) =
      c ⬝ᵥ (exp ((T - u) • A) *ᵥ (bZ u - A *ᵥ z u))
    rw [hexp]
    congr 2
    rw [mulVec_sub, mulVec_mulVec, ← hPA, ← mulVec_mulVec]
  have hAX' : AX01Path041 s HS HZ' dL dC bZ' z' Tm c' A' H := by
    filter_upwards [hAX] with u hu hu0 T hT
    rw [hdB, hu hu0 T hT]
    simp only [hsig]
  exact Novel.SpliceSeveralFactorsAX01Proof.necessity r' k L A' hA' c' hobs s HS HZ' dL dC bZ' z'
    Tm H hPD' hAX'

theorem spliceSeveralFactorsMinimal : Standalone.SpliceSeveralFactorsMinimal.statement :=
  ⟨minimal, reduced⟩

end Novel.SpliceSeveralFactorsMinimalProof

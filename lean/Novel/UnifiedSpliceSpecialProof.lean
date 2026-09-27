import Standalone.UnifiedSpliceSpecial
import Novel.UnifiedSpliceDiagProof

open Matrix NormedSpace
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceSpecial
namespace Novel.UnifiedSpliceSpecialProof

variable {k r r' : ℕ}

/-! ### (c) -/

lemma aggregationS : aggregationStatement := by
  intro k nS s HS m
  refine ⟨by rw [← Finset.sum_sub_distrib]; simp only [sub_smul], fun h r d Hp Hz => ?_⟩
  rw [h]; exact ⟨fun _ _ _ => dotProduct_zero _, mulVec_zero _⟩

lemma cancellationS : cancellationStatement := by
  intro k s HS m hH hs
  rw [Fin.sum_univ_two, hs, hH, neg_smul, neg_add_cancel]

/-- `P e^{A} = e^{A'} P` when `P A = A' P`. -/
lemma intertwine (A : Matrix (Fin r) (Fin r) ℝ) (A' : Matrix (Fin r') (Fin r') ℝ)
    (P : Matrix (Fin r') (Fin r) ℝ) (h : P * A = A' * P) : P * exp A = exp A' * P := by
  open scoped Matrix.Norms.Operator in
  have hpow : ∀ n : ℕ, P * A ^ n = A' ^ n * P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
        ← pow_succ]
  let Lℓ : Matrix (Fin r) (Fin r) ℝ →ₗ[ℝ] Matrix (Fin r') (Fin r) ℝ :=
    { toFun := fun M => P * M, map_add' := Matrix.mul_add P,
      map_smul' := fun a M => Matrix.mul_smul P a M }
  let Rℓ : Matrix (Fin r') (Fin r') ℝ →ₗ[ℝ] Matrix (Fin r') (Fin r) ℝ :=
    { toFun := fun M => M * P, map_add' := fun M N => Matrix.add_mul M N P,
      map_smul' := fun a M => Matrix.smul_mul a M P }
  have h1 := (LinearMap.toContinuousLinearMap Lℓ).map_tsum (expSeries_summable' (𝕂 := ℝ) A)
  have h2 := (LinearMap.toContinuousLinearMap Rℓ).map_tsum (expSeries_summable' (𝕂 := ℝ) A')
  simp only [LinearMap.coe_toContinuousLinearMap', Lℓ, Rℓ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
  rw [exp_eq_tsum ℝ, exp_eq_tsum ℝ]
  simp only
  rw [h1, h2]
  congr 1
  funext n
  rw [Matrix.mul_smul, Matrix.smul_mul, hpow]

section Red
variable {Hp : ℕ → Fin k → ℝ} {Hz : Matrix (Fin r) (Fin k) ℝ} {c : Fin r → ℝ}
  {A : Matrix (Fin r) (Fin r) ℝ} {c' : Fin r' → ℝ} {A' : Matrix (Fin r') (Fin r') ℝ}
  {P : Matrix (Fin r') (Fin r) ℝ} (hA : IsUnit A.det) (hA' : IsUnit A'.det)
  (h : P * A = A' * P) (hc : c = c' ᵥ* P)

include h hc in
lemma ephi_red (x : ℝ) : ephi c A x = ephi c' A' x ᵥ* P := by
  have hE := intertwine (x • A) (x • A') P (by rw [Matrix.mul_smul, Matrix.smul_mul, h])
  rw [ephi, ephi, hc, vecMul_vecMul, hE, ← vecMul_vecMul]

include hA hA' h hc in
lemma ePhi_red (x : ℝ) : ePhi c A x = ePhi c' A' x ᵥ* P := by
  have hE := intertwine (x • A) (x • A') P (by rw [Matrix.mul_smul, Matrix.smul_mul, h])
  have hinv : P * A⁻¹ = A'⁻¹ * P := by
    calc P * A⁻¹ = A'⁻¹ * A' * P * A⁻¹ := by rw [nonsing_inv_mul A' hA', Matrix.one_mul]
      _ = A'⁻¹ * (P * A) * A⁻¹ := by rw [h, Matrix.mul_assoc A'⁻¹]
      _ = A'⁻¹ * P := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv A hA,
            Matrix.mul_one]
  rw [ePhi, ePhi, hc, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, hinv, Matrix.mul_assoc,
    Matrix.mul_sub, hE, Matrix.mul_one, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]

include hA hA' h hc in
lemma sigB_red (d : ℕ) (x : ℝ) : sigB Hp Hz c A d x = sigB Hp (P * Hz) c' A' d x := by
  rw [sigB, sigB, ephi_red h hc, vecMul_vecMul]

include hA hA' h hc in
lemma SigB_red (d : ℕ) (x : ℝ) : SigB Hp Hz c A d x = SigB Hp (P * Hz) c' A' d x := by
  rw [SigB, SigB, ePhi_red hA hA' h hc, vecMul_vecMul]

end Red

lemma reductionS : reductionStatement := by
  intro k r r' d Hp Hz c A c' A' P hA hA' h hc
  refine ⟨fun bP zP bZ z x => ?_, fun V κ u T => ?_⟩
  · rw [resid, resid, sigB_red hA hA' h hc, SigB_red hA hA' h hc, ephi_red h hc,
      ← dotProduct_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h, ← mulVec_mulVec]
  · rw [cross, cross, sigB_red hA hA' h hc, SigB_red hA hA' h hc]

lemma reducedNecessityS : reducedNecessityStatement := by
  intro k r r' d Hp Hz c A c' A' P hA hA' h hc hobs V₀ V₁ κ₀ κ₁ Tm u d₁ d₂ α β hd hκ hJ
  have hred := (reductionS k r r' d Hp Hz c A c' A' P hA hA' h hc).2
  exact Novel.UnifiedSpliceNecessityProof.necessityS k r' d Hp (P * Hz) c' A' hA' hobs V₀ V₁ κ₀
    κ₁ Tm u d₁ d₂ α β hd hκ fun T hT => by rw [← hred, ← hred]; exact hJ T hT

/-! ### Orthogonality alone -/

lemma orthogonalityS : orthogonalityStatement := by
  have hR : ∀ x : ℝ, resid (sharp (fun μ (_ : Fin 1) => if μ = 1 then (1:ℝ) else 0) 0)
      (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 0 1 0 0 0 0 x = -(x ^ 3 / 2) := fun x => by
    simp [resid, sigB, SigB, sharp, Finset.sum_range_succ, dotProduct, ephi, ePhi]
    ring
  refine ⟨fun μ _ _ => dotProduct_zero _, mulVec_zero _, hR, ?_⟩
  rintro ⟨α, β, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [hR] at h0 h1 h2
  norm_num at h0 h1 h2
  linarith

/-! ### (d) -/

lemma prop44S : prop44Statement := by
  intro k r d Hp Hz c A hA hobs hdiag h0 bP zP bZ z V hR
  have := (Novel.UnifiedSpliceDiagProof.effectiveS k r d Hp Hz c A hA hobs hdiag bP zP bZ z V hR).2
  rwa [h0, zero_add] at this

lemma uncorrelatedS : uncorrelatedStatement := by
  intro k r d Hp Hz c A bP zP bZ z V hμ hz x
  have hK : Kfun Hp Hz c A d V x = 0 := by
    rw [Kfun, hz, smul_zero, dotProduct_zero, dotProduct_zero, add_zero, add_zero]
    refine Finset.sum_eq_zero fun μ hμd => ?_
    rw [hμ (μ + 1) (by omega) (by simpa using hμd), zero_mul, zero_mul]
  refine ⟨hK, ?_⟩
  have := Novel.UnifiedSpliceAlgebraProof.effectiveS k r d Hp Hz c A bP zP bZ z V x
  rw [hK, zero_add] at this
  linarith

lemma sharpEntriesS : sharpEntriesStatement := by
  intro k r Hp Hz V
  have h0 : sharp Hp V 0 = Hp 0 + V := by simp [sharp]
  have hμ : ∀ μ, 1 ≤ μ → sharp Hp V μ = Hp μ := fun μ h => by
    simp [sharp, Function.update_of_ne (show μ ≠ 0 by omega)]
  refine ⟨fun μ ν h1 h2 => by rw [hμ μ h1, hμ ν h2], fun ν h => ?_, ?_, fun μ h => by rw [hμ μ h],
    by rw [h0, mulVec_add]⟩
  · rw [h0, hμ ν h, add_dotProduct, dotProduct_comm V]
  · rw [h0, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm V (Hp 0)]; ring

theorem unifiedSpliceSpecial : Standalone.UnifiedSpliceSpecial.statement := ⟨aggregationS, cancellationS, reductionS, reducedNecessityS, orthogonalityS, prop44S, uncorrelatedS, sharpEntriesS⟩

end Novel.UnifiedSpliceSpecialProof

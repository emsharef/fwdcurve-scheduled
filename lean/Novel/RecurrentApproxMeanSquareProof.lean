import Standalone.RecurrentApproxMeanSquare
import Novel.RecurrentApproxEstimatesProof
import Novel.RecurrenceNecessityGaussianProof

open MeasureTheory Set
open scoped NNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxMeanSquare Standalone.ZeroMeanReversionUpstreamBridge
open Novel.MaturityShapeIdentitiesProof (ii_of_bound)
open Novel.RecurrentApproxEstimatesProof
open Novel.RecurrenceNecessityGaussianProof (det_U4 det_U5 second_moment)
namespace Novel.RecurrentApproxMeanSquareProof

/-- A (U5) integral has mean zero. -/
lemma mean_zero {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (G : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (hU5 : U5 S.ℱ S.μ G t) : ∫ ω, S.I k G t ω ∂S.μ = 0 := by
  set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k G (min u t) ω with hM
  have hcond : S.μ[M t | S.ℱ 0] =ᵐ[S.μ] M 0 :=
    (S.int_martingale k G t hU5).1.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t)
  have hM0 : M 0 =ᵐ[S.μ] 0 := by
    filter_upwards [S.int_zero k G hU5.1] with ω hω
    simp [hM, hω]
  calc ∫ ω, S.I k G t ω ∂S.μ = ∫ ω, M t ω ∂S.μ := by simp [hM]
    _ = ∫ ω, (S.μ[M t | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
    _ = ∫ ω, M 0 ω ∂S.μ := integral_congr_ae hcond
    _ = 0 := by rw [integral_congr_ae hM0]; simp

lemma sigT_meas (Tm : Finset ℝ) (b : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) (T : ℝ) :
    Measurable (sigT Tm b lam T) :=
  Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    ((sig_meas Tm b hlam).comp (measurable_subtype_coe.prodMk measurable_const)) measurable_const

section
variable {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam : ℝ → ℝ} {H Λ ε Abar : ℝ}
  (h : Hyp048 Tm a a' lam H Λ ε Abar)
include h

lemma sigT_bound {T : ℝ} (hTH : T ≤ H) (hAΛ : 0 ≤ Abar * Λ) (hεΛ : 0 ≤ ε * Λ) (s : ℝ≥0) :
    |sigT Tm a lam T s| ≤ Abar * Λ ∧ |sigT Tm a' lam T s| ≤ Abar * Λ ∧
      |sigT Tm a lam T s - sigT Tm a' lam T s| ≤ ε * Λ := by
  unfold sigT
  split_ifs with hs
  · exact sig_bound h hs (by linarith [s.coe_nonneg])
  · simp [hAΛ, hεΛ]

lemma alpha_ii (b : ℕ → ℝ) (hb : b = a ∨ b = a') {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hTH : T ≤ H) (hA0 : 0 ≤ Abar) (hl0 : 0 ≤ Λ) :
    IntervalIntegrable (fun s => alpha048 Tm b lam s T) volume 0 t :=
  ii_of_bound (alpha_meas Tm b h.1 T) ht (M := Abar * Λ * (Abar * Λ * T)) fun s hs => by
    have h1 := sig_bound h (hs.2.trans htT) (by linarith [hs.1])
    have h2 := S_bound h hs.1 (hs.2.trans htT) hTH
    have e1 : |sig048 Tm b lam s T| ≤ Abar * Λ := by rcases hb with rfl | rfl; exacts [h1.1, h1.2.1]
    have e2 : |S048 Tm b lam s T| ≤ Abar * Λ * (T - s) := by
      rcases hb with rfl | rfl; exacts [h2.1, h2.2.1]
    rw [alpha048, abs_mul]
    refine mul_le_mul e1 (e2.trans ?_) (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) (by positivity)

end

theorem meanSquareS : meanSquareStatement := by
  intro Ω _ S k hc Tm a a' lam f0 H Λ ε Abar h t T htT hTH
  have := S.isProbabilityMeasure
  have ht : (0:ℝ) ≤ t := t.2
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (htT.trans hTH)⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hb := sigT_bound h hTH (mul_nonneg hA0 hl0) (mul_nonneg hε0 hl0)
  set G := sigT Tm a lam T
  set G' := sigT Tm a' lam T
  set D : ℝ≥0 → ℝ := fun s => G s - G' s with hD
  have mG := sigT_meas Tm a h.1 T
  have mG' := sigT_meas Tm a' h.1 T
  have mD : Measurable D := mG.sub mG'
  have hU := det_U4 S G mG _ fun s => (hb s).1
  have hU' := det_U4 S G' mG' _ fun s => (hb s).2.1
  have hU5 := det_U5 S D mD _ (fun s => (hb s).2.2) t
  -- the difference
  have hlin := S.int_linear k (fun s _ => G s) (fun s _ => G' s) 1 (-1) hU hU' t
  have hfun : ((1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => G s) + (-1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => G' s) :
      ℝ≥0 → Ω → ℝ) = fun s _ => D s := by
    funext s ω; simp [hD, sub_eq_add_neg]
  rw [hfun] at hlin
  have hm : m048 Tm a a' lam t T =
      (∫ s in (0:ℝ)..t, alpha048 Tm a lam s T) - ∫ s in (0:ℝ)..t, alpha048 Tm a' lam s T :=
    intervalIntegral.integral_sub (alpha_ii h a (Or.inl rfl) ht htT hTH hA0 hl0)
      (alpha_ii h a' (Or.inr rfl) ht htT hTH hA0 hl0)
  have hae : (fun ω => fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) =ᵐ[S.μ]
      (fun ω => m048 Tm a a' lam t T + S.I k (fun s _ => sigT Tm a lam T s - sigT Tm a' lam T s) t ω) := by
    filter_upwards [hlin] with ω hω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul] at hω
    simp only [fwd048, hm]
    change _ = _ + S.I k (fun s _ => D s) t ω
    rw [hω]; ring
  -- the second moment
  set X := S.I k (fun s _ => D s) t
  have hL2 : MemLp X 2 S.μ := (S.int_martingale k _ t hU5).2 t le_rfl
  have hX1 : Integrable X S.μ := hL2.integrable one_le_two
  have hmean : ∫ ω, X ω ∂S.μ = 0 := mean_zero S k _ t hU5
  have hsec := second_moment S k D mD _ (fun s => (hb s).2.2) t
  have hint : ∫ s in (0:ℝ)..t, D (Real.toNNReal s) * D (Real.toNNReal s) * S.c k k (Real.toNNReal s) =
      ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have hs' : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    have hsT : s ≤ T := hs.2.trans htT
    simp only [hD, G, G', sigT, hs', hc, mul_one, sq, hsT, ite_true]
  have heq : ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ =
      m048 Tm a a' lam t T ^ 2 +
        ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 := by
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only at hω ⊢; rw [hω])]
    change ∫ ω, (m048 Tm a a' lam t T + X ω) ^ 2 ∂S.μ = _
    have e : (fun ω => (m048 Tm a a' lam t T + X ω) ^ 2) =
        fun ω => (m048 Tm a a' lam t T ^ 2 + 2 * m048 Tm a a' lam t T * X ω) + X ω ^ 2 := by
      funext ω; ring
    set mm := m048 Tm a a' lam t T
    rw [e, integral_add (f := fun ω => mm ^ 2 + 2 * mm * X ω) (g := fun ω => X ω ^ 2)
      ((integrable_const _).add (hX1.const_mul _)) hL2.integrable_sq,
      integral_add (f := fun _ => mm ^ 2) (g := fun ω => 2 * mm * X ω) (integrable_const _)
        (hX1.const_mul _), integral_const, integral_const_mul, hmean, ← hint, ← hsec]
    simp [X]
  obtain ⟨-, -, h3, h4⟩ := meanS Tm a a' lam H Λ ε Abar h t T ht htT hTH
  exact ⟨hae, heq, heq ▸ h3, heq ▸ h3.trans h4⟩

theorem recurrentApproxMeanSquare : Standalone.RecurrentApproxMeanSquare.statement := meanSquareS

end Novel.RecurrentApproxMeanSquareProof

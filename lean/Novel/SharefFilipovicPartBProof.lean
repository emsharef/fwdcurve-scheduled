import Standalone.SharefFilipovicPartB
import Novel.SharefFilipovicPartAProof
import Novel.SharefFilipovicMaxFactorsProof
import Mathlib.Algebra.Order.Star.Real

open Set Filter MeasureTheory Matrix
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicSplit
open Standalone.SharefFilipovicPartB
namespace Novel.SharefFilipovicPartBProof
open Novel.SharefFilipovicSplitProof

lemma bound : boundStatement := by
  intro β hβ n₁ n₂ m Z b sZ DS sS t p q htp hpq hDS hsS hDaff hsaff hsep hAX i j hij
  have hres := (Novel.SharefFilipovicPartAProof.partA β hβ n₁ n₂ m Z b sZ DS sS t p q htp hpq
    hDS hsS hDaff hsaff hsep hAX).1
  let M : Matrix (Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (Fin m) ℝ := Matrix.of sZ
  have hA : M * Mᴴ = fun i j => ∑ k, sZ i k * sZ j k := by
    funext i j
    simp [M, Matrix.mul_apply]
  have hpsd : (M * Mᴴ).PosSemidef := posSemidef_self_mul_conjTranspose M
  exact Novel.SharefFilipovicMaxFactorsProof.maxFactors β hβ n₁ n₂ Z b (M * Mᴴ) hpsd
    (fun x _ => by rw [hA]; exact hres x) i j (by rw [hA]; exact hij)

lemma converse : converseStatement := by
  intro β hβ n₁ n₂ m Z b sZ DS sS t hres hsep T htT hDS hsS hfront
  -- the block's drift is `σ^B · ∫σ^B` at every maturity `u ≥ t`
  have hDB : ∀ u, t ≤ u → DB034 β Z b t u =
      ∑ l, (∫ v in t..u, sB034 β sZ t v l) * sB034 β sZ t u l := by
    intro u hu
    have h := hres (u - t) (sub_nonneg.2 hu)
    rw [block_identity β sZ t u]
    unfold residual034 at h
    unfold DB034
    linarith
  -- so the block satisfies its own AX-01
  have hderiv : ∀ x, HasDerivAt (fun T => (1/2 : ℝ) * ∑ l, (∫ v in t..T, sB034 β sZ t v l) ^ 2)
      (∑ l, (∫ v in t..x, sB034 β sZ t v l) * sB034 β sZ t x l) x := by
    intro x
    have hl := HasDerivAt.sum (u := Finset.univ) fun l _ =>
      (((sB_cont β sZ t l).integral_hasStrictDerivAt t x).hasDerivAt).pow 2
    convert hl.const_mul (1/2 : ℝ) using 1
    · funext T; simp [Finset.sum_apply]
    · simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  have hblock : ∫ u in t..T, DB034 β Z b t u =
      (1/2 : ℝ) * ∑ l, (∫ v in t..T, sB034 β sZ t v l) ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun T =>
        (1/2 : ℝ) * ∑ l, (∫ v in t..T, sB034 β sZ t v l) ^ 2)
      (fun x hx => by
        rw [uIcc_of_le htT] at hx
        rw [hDB x hx.1]
        exact hderiv x)
      ((DB_cont β Z b t).intervalIntegrable _ _)]
    simp
  -- the square splits with no cross term, since the driver groups are separate
  have hsq : ∀ k, (∫ u in t..T, (sS u k + sB034 β sZ t u k)) ^ 2 =
      (∫ u in t..T, sS u k) ^ 2 + (∫ u in t..T, sB034 β sZ t u k) ^ 2 := by
    intro k
    rcases hsep k with h0 | h0
    · simp [h0]
    · have : ∀ u, sB034 β sZ t u k = 0 := fun u => by simp [sB034, h0]
      simp [this]
  rw [intervalIntegral.integral_add hDS ((DB_cont β Z b t).intervalIntegrable _ _), hfront,
    hblock, Finset.sum_congr rfl fun k _ => hsq k, Finset.sum_add_distrib]
  ring

theorem sharefFilipovicPartB : Standalone.SharefFilipovicPartB.statement := ⟨bound, converse⟩

end Novel.SharefFilipovicPartBProof

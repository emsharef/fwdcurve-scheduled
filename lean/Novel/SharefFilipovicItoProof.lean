import Standalone.SharefFilipovicIto
import Novel.SharefFilipovicResidualProof
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

open MeasureTheory Filter Polynomial
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SharefFilipovicResidual
open Standalone.SharefFilipovicIto
namespace Novel.SharefFilipovicItoProof

section Gen
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
open Novel.ZeroMeanReversionUpstreamBridgeProof

/-- Itô's product rule, AX-05, for a smooth deterministic weight and one Itô process with a drift
and several drivers. -/
lemma prodRuleGen (Y : ℝ≥0 → Ω → ℝ) (y0 : ℝ) (H : Fin S.m → ℝ≥0 → Ω → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hH : ∀ k, U4 S.ℱ S.μ (H k)) (hK : LocallyIntegrableDrift S.ℱ S.μ K)
    (hY : ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, Y t ω = y0 + ∑ k, S.I k (H k) t ω +
      ∫ s in (0:ℝ)..t, K (Real.toNNReal s) ω)
    (R : ℝ → ℝ) (hR : ContDiff ℝ 2 R) :
    (∀ k, U4 S.ℱ S.μ (fun s ω => R (s : ℝ) * H k s ω)) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, R t * Y t ω = R 0 * y0 +
      (∫ s in (0 : ℝ)..t, (deriv R s * Y (Real.toNNReal s) ω + R s * K (Real.toNNReal s) ω)) +
      ∑ k, S.I k (fun s ω => R (s : ℝ) * H k s ω) t ω := by
  classical
  let x1 : Fin 1 → ℝ := fun _ => y0
  let H1 : Fin 1 → Fin S.m → ℝ≥0 → Ω → ℝ := fun _ k => H k
  let K1 : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ => K
  obtain ⟨hU4, hae⟩ := S.ito_formula 1 x1 H1 K1 (fprod R 0)
    (fun _ k => hH k) (fun _ => hK) (fprod_contDiff R hR 0)
  have hint : ∀ k, (fun (s : ℝ≥0) ω => dX (fprod R 0)
      ((s : ℝ), driverForm S.I x1 H1 K1 s ω) 0 * H1 0 k s ω) =
      fun (s : ℝ≥0) ω => R (s : ℝ) * H k s ω := fun k => by
    funext s ω
    rw [fprod_dX R hR 0, if_pos rfl]
  refine ⟨fun k => by have := hU4 0 k; rwa [hint k] at this, ?_⟩
  have hdf : ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I x1 H1 K1 t ω =
      fun _ => Y t ω := by
    filter_upwards [hY] with ω hω t
    funext i
    simp only [driverForm]
    rw [hω t]
  filter_upwards [hae, hdf] with ω hω hdf
  intro t
  have h := hω t
  simp only [Fin.sum_univ_one, hint] at h
  rw [intervalIntegral.integral_congr (g := fun s : ℝ =>
    deriv R s * Y (Real.toNNReal s) ω + R s * K (Real.toNNReal s) ω) (fun s _ => by
      simp only [fprod_dXX R hR 0, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
        fprod_dT R hR 0, fprod_dX R hR 0, ite_true, K1]
      rw [hdf (Real.toNNReal s)]), hdf t] at h
  simpa only [fprod, x1] using h

end Gen

lemma phi_contDiff (β : ℝ) {n₁ n₂ : ℕ} (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) :
    ContDiff ℝ 2 (phi034 β n₁ n₂ i) := by
  have e : phi034 β n₁ n₂ i = fun x => (Novel.SharefFilipovicResidualProof.pIdx i).eval x *
      Real.exp (-(((Novel.SharefFilipovicResidualProof.kIdx i : ℕ) : ℝ) + 1) * β * x) :=
    funext fun x => Novel.SharefFilipovicResidualProof.phi_eq β i x
  rw [e]
  have hp : ContDiff ℝ 2 (fun x => (Novel.SharefFilipovicResidualProof.pIdx i).eval x) := by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (Novel.SharefFilipovicResidualProof.pIdx i) 2
  exact hp.mul (Real.contDiff_exp.comp (by fun_prop))

lemma blockIto : blockItoStatement := by
  intro Ω mΩ S β n₁ n₂ T Z z0 H K hH hK hZ
  classical
  let R : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ → ℝ := fun i s => phi034 β n₁ n₂ i (T - s)
  have hR : ∀ i, ContDiff ℝ 2 (R i) := fun i =>
    (phi_contDiff β i).comp (contDiff_const.sub contDiff_id)
  have hpr := fun i => prodRuleGen S (Z i) (z0 i) (H i) (K i) (hH i) (hK i) (hZ i) (R i) (hR i)
  refine ⟨fun i k => (hpr i).1 k, ?_⟩
  filter_upwards [ae_all_iff.2 fun i => (hpr i).2] with ω hω t
  simp only [F034]
  have e1 : ∑ i, Z i t ω * phi034 β n₁ n₂ i (T - t) = ∑ i, R i t * Z i t ω :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, Finset.sum_congr rfl fun i _ => hω i t, Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by simp only [R, sub_zero]; ring
    · refine Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s _ => ?_
      simp only [R, deriv_comp_const_sub]
      ring

theorem sharefFilipovicIto : Standalone.SharefFilipovicIto.statement := blockIto

end Novel.SharefFilipovicItoProof

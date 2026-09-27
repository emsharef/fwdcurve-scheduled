import Standalone.SpliceStateBlockObservability
import Novel.SpliceQuasiExponentialConsistencyProof
import Mathlib.Analysis.Calculus.MeanValue

open Matrix NormedSpace Set Filter Topology
open Standalone.SpliceStateBlockObservability
namespace Novel.SpliceStateBlockObservabilityProof

variable {r : ℕ}

lemma observability : observabilityStatement := by
  intro r A hA c hobs Tm d₁ d₂ v hd hg
  set w := A⁻¹ *ᵥ v with hw
  have hAw : A *ᵥ w = v := by rw [hw, mulVec_mulVec, mul_nonsing_inv A hA, one_mulVec]
  -- `g` in the form `c e^{AT}(y + T z)`, then on all of `ℝ` by analyticity
  have hform : ∀ T : ℝ, c ⬝ᵥ (exp (T • A) *ᵥ
      ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ v)) =
      c ⬝ᵥ (exp (T • A) *ᵥ ((w - Tm • v) + T • v)) := fun T => by
    congr 2
    simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, ← hw]
    abel
  have hall : ∀ T : ℝ, c ⬝ᵥ (exp (T • A) *ᵥ ((w - Tm • v) + T • v)) = 0 := by
    have hF := Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A (w - Tm • v) v
    have hmid : (d₁ + d₂) / 2 ∈ Ioo d₁ d₂ := ⟨by linarith, by linarith⟩
    intro T
    have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; rw [← hform]; exact hg x hx)
      (mem_univ T)
    simpa using this
  -- `k(T) = c e^{AT} A^{−1} v` has derivative `c e^{AT} v`
  let k : ℝ → ℝ := fun T => c ⬝ᵥ (exp (T • A) *ᵥ w)
  have hk : ∀ T, HasDerivAt k (c ⬝ᵥ (exp (T • A) *ᵥ v)) T := fun T => by
    have h := Novel.RecurrenceNecessityReductionProof.deriv_g A c w 0 T
    simp only [pow_zero, one_mul, zero_add, pow_one] at h
    have hc : A * exp (T • A) = exp (T • A) * A :=
      (((Commute.refl A).smul_right T).exp_right).eq
    rw [hc, ← mulVec_mulVec, hAw] at h
    exact h
  -- `(T − T_m) k(T)` has derivative `g = 0`, so it is constant, hence zero
  have hh : ∀ T, HasDerivAt (fun T => (T - Tm) * k T) 0 T := fun T => by
    have h := ((hasDerivAt_id T).sub_const Tm).mul (hk T)
    refine h.congr_deriv ?_
    have := hall T
    simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at this
    simp only [k, id]
    linear_combination this
  have hconst : ∀ T, (T - Tm) * k T = 0 := fun T => by
    have := is_const_of_deriv_eq_zero (fun T => (hh T).differentiableAt)
      (fun T => (hh T).deriv) T Tm
    simpa using this
  -- so `k = 0` off `T_m`, and everywhere by analyticity
  have hk0 : ∀ x, k x = 0 := by
    have hka := Novel.SpliceQuasiExponentialKeyProof.analytic_g A c w
    have hmid : Tm + 1 ∈ Ioi Tm := by simp
    intro x
    have := hka.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by
        filter_upwards [isOpen_Ioi.mem_nhds hmid] with y hy
        have := hconst y
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) (ne_of_gt hy)
        · exact h)
      (mem_univ x)
    simpa using this
  have hw0 : w = 0 := hobs w hk0
  rw [← hAw, hw0, mulVec_zero]

theorem spliceStateBlockObservability : Standalone.SpliceStateBlockObservability.statement :=
  observability

end Novel.SpliceStateBlockObservabilityProof

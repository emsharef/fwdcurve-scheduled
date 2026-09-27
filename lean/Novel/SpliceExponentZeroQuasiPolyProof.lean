import Standalone.SpliceExponentZeroQuasiPoly
import Novel.SpliceQuasiExponentialAlgebraProof
import Novel.SpliceQuasiExponentialConsistencyProof
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Matrix NormedSpace Polynomial Set Filter Topology
open Standalone.SpliceExponentZeroQuasiPoly
namespace Novel.SpliceExponentZeroQuasiPolyProof
open Novel.SpliceQuasiExponentialAlgebraProof

variable {r : ℕ}

/-- The `k`-th derivative of `g` is `h_k`. -/
lemma iter_hk (A : Matrix (Fin r) (Fin r) ℝ) (c y z : Fin r → ℝ) (k : ℕ) :
    iteratedDeriv k (fun T => c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z))) = hk A c y z k := by
  induction k with
  | zero =>
    funext T
    simp [hk]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext T
    exact (hk_deriv A c y z k T).deriv

/-- The `k`-th derivative of a polynomial function. -/
lemma iter_poly (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun T => P.eval T) = fun T => (derivative^[k] P).eval T := by
  induction k with
  | zero => funext T; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext T
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- `∑_k q_k h_k(T) = c e^{AT}(q(A)(y + T z) + q'(A) z)`. -/
lemma sum_hk (A : Matrix (Fin r) (Fin r) ℝ) (c y z : Fin r → ℝ) (q : ℝ[X]) (T : ℝ) :
    ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * hk A c y z k T =
      c ⬝ᵥ ((aeval A q * exp (T • A)) *ᵥ (y + T • z)) +
        c ⬝ᵥ ((aeval A (derivative q) * exp (T • A)) *ᵥ z) := by
  have e1 : aeval A q = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k • A ^ k :=
    aeval_eq_sum_range A
  have e2 : aeval A (derivative q) =
      ∑ k ∈ Finset.range (q.natDegree + 1), (q.coeff k * k) • A ^ (k - 1) := by
    rw [derivative_apply, Polynomial.sum_over_range' _ (fun n => by simp) _ (Nat.lt_succ_self _)]
    simp only [map_sum, map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  rw [e1, e2, Finset.sum_mul, Finset.sum_mul, sum_mulVec, sum_mulVec, dotProduct_sum,
    dotProduct_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hk, smul_mul_assoc, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

lemma quasiPoly : quasiPolyStatement := by
  intro r A hA c y z P d₁ d₂ hd h
  set g : ℝ → ℝ := fun T => c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z))
  set χ := A.charpoly
  set q := χ * χ
  -- `χ(D)² g = 0`
  have hq0 : aeval A q = 0 := by simp [q, χ, aeval_self_charpoly]
  have hq1 : aeval A (derivative q) = 0 := by
    simp [q, χ, derivative_mul, aeval_self_charpoly]
  have hkill : ∀ T, ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * hk A c y z k T = 0 :=
    fun T => by rw [sum_hk, hq0, hq1]; simp
  -- on the interval, `χ(D)² P = 0` as a polynomial
  set R : ℝ[X] := ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * derivative^[k] P
  have hR : ∀ T ∈ Ioo d₁ d₂, R.eval T = 0 := by
    intro T hT
    have hev : g =ᶠ[𝓝 T] fun T => P.eval T := by
      filter_upwards [Ioo_mem_nhds hT.1 hT.2] with x hx using h x hx
    have hk : ∀ k, hk A c y z k T = (derivative^[k] P).eval T := fun k => by
      have := hev.iteratedDeriv_eq k
      rw [iter_hk, iter_poly] at this
      exact this
    rw [← hkill T]
    simp only [R, eval_finsetSum, eval_mul, eval_C, hk]
  have hR0 : R = 0 := by
    apply eq_zero_of_infinite_isRoot
    exact (Ioo_infinite hd).mono fun T hT => hR T hT
  -- the leading coefficient
  have hq00 : q.coeff 0 ≠ 0 := by
    have hdet : χ.coeff 0 ≠ 0 := by
      intro h0
      have := A.det_eq_sign_charpoly_coeff
      rw [h0, mul_zero] at this
      exact hA.ne_zero this
    simpa [q, mul_coeff_zero] using mul_ne_zero hdet hdet
  have hP : P = 0 := by
    by_contra hne
    set m := P.natDegree
    have hc := congrArg (coeff · m) hR0
    simp only [R, finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, coeff_zero] at hc
    rw [Finset.sum_eq_single 0] at hc
    · simp only [add_zero, Nat.descFactorial_zero, one_smul] at hc
      exact hne (leadingCoeff_eq_zero.1 ((mul_eq_zero.1 hc).resolve_left hq00))
    · intro k _ hk0
      rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m + k), smul_zero, mul_zero]
    · simp
  refine ⟨hP, fun T => ?_⟩
  have hF := Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A y z
  have hmid : (d₁ + d₂) / 2 ∈ Ioo d₁ d₂ := ⟨by linarith, by linarith⟩
  have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
    (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [h x hx, hP]) (mem_univ T)
  simpa using this

theorem spliceExponentZeroQuasiPoly : Standalone.SpliceExponentZeroQuasiPoly.statement := quasiPoly

end Novel.SpliceExponentZeroQuasiPolyProof

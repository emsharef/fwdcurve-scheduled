import Standalone.UnifiedSpliceExpPoly
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots

open Polynomial
open Standalone.UnifiedSpliceExpPoly
namespace Novel.UnifiedSpliceExpPolyProof

/-- `(p e^{νx})' = (p' + ν p) e^{νx}`. -/
lemma hasDeriv_term (q : ℂ[X]) (ν : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => q.eval (y : ℂ) * Complex.exp (ν * y))
      ((derivative q + C ν * q).eval (x : ℂ) * Complex.exp (ν * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => q.eval (y : ℂ)) ((derivative q).eval (x : ℂ)) x :=
    (Polynomial.hasDerivAt q (x : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (ν * y)) (Complex.exp (ν * x) * ν) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul ν).cexp.comp_ofReal
    simpa using this
  convert h1.mul h2 using 1
  simp only [eval_add, eval_mul, eval_C]
  ring

/-- `D − ν₀` on the exponential polynomial: `p_ν ↦ p_ν' + (ν − ν₀) p_ν`. -/
noncomputable def op (ν₀ ν : ℂ) (q : ℂ[X]) : ℂ[X] := derivative q + C (ν - ν₀) * q

lemma step (s : Finset ℂ) (q : ℂ → ℂ[X]) (ν₀ : ℂ)
    (h : ∀ x : ℝ, ∑ ν ∈ s, (q ν).eval (x : ℂ) * Complex.exp (ν * x) = 0) :
    ∀ x : ℝ, ∑ ν ∈ s, (op ν₀ ν (q ν)).eval (x : ℂ) * Complex.exp (ν * x) = 0 := by
  intro x
  have hF : (fun y : ℝ => ∑ ν ∈ s, (q ν).eval (y : ℂ) * Complex.exp (ν * y)) = fun _ => 0 :=
    funext h
  have hd : HasDerivAt (fun y : ℝ => ∑ ν ∈ s, (q ν).eval (y : ℂ) * Complex.exp (ν * y))
      (∑ ν ∈ s, (derivative (q ν) + C ν * q ν).eval (x : ℂ) * Complex.exp (ν * x)) x :=
    HasDerivAt.fun_sum fun ν _ => hasDeriv_term (q ν) ν x
  rw [hF] at hd
  have h0 := hd.unique (hasDerivAt_const x (0 : ℂ))
  have e : ∑ ν ∈ s, (op ν₀ ν (q ν)).eval (x : ℂ) * Complex.exp (ν * x) =
      (∑ ν ∈ s, (derivative (q ν) + C ν * q ν).eval (x : ℂ) * Complex.exp (ν * x)) -
        ν₀ * ∑ ν ∈ s, (q ν).eval (x : ℂ) * Complex.exp (ν * x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ν _ => by simp only [op, eval_add, eval_mul, eval_C]; ring
  rw [e, h0, h x, mul_zero, sub_zero]

lemma iter_step (s : Finset ℂ) (q : ℂ → ℂ[X]) (ν₀ : ℂ)
    (h : ∀ x : ℝ, ∑ ν ∈ s, (q ν).eval (x : ℂ) * Complex.exp (ν * x) = 0) (K : ℕ) :
    ∀ x : ℝ, ∑ ν ∈ s, ((op ν₀ ν)^[K] (q ν)).eval (x : ℂ) * Complex.exp (ν * x) = 0 := by
  induction K with
  | zero => simpa using h
  | succ K ih =>
    have := step s (fun ν => (op ν₀ ν)^[K] (q ν)) ν₀ ih
    simpa only [Function.iterate_succ_apply'] using this

lemma op_self (ν₀ : ℂ) (K : ℕ) (q : ℂ[X]) : (op ν₀ ν₀)^[K] q = derivative^[K] q := by
  have : op ν₀ ν₀ = derivative := by
    funext q; simp [op]
  rw [this]

lemma op_inj {ν₀ ν : ℂ} (hν : ν ≠ ν₀) {q : ℂ[X]} (h : op ν₀ ν q = 0) : q = 0 := by
  by_contra hq
  have hc := congrArg (fun p : ℂ[X] => p.coeff q.natDegree) h
  simp only [op, coeff_add, coeff_derivative, coeff_C_mul, coeff_zero] at hc
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, zero_add] at hc
  exact mul_ne_zero (sub_ne_zero.2 hν) (leadingCoeff_ne_zero.2 hq) hc

lemma iter_inj {ν₀ ν : ℂ} (hν : ν ≠ ν₀) (K : ℕ) {q : ℂ[X]} (h : (op ν₀ ν)^[K] q = 0) : q = 0 := by
  induction K generalizing q with
  | zero => simpa using h
  | succ K ih =>
    rw [Function.iterate_succ_apply] at h
    exact op_inj hν (ih h)

theorem expPolyS : expPolyStatement := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro p _ ν hν; simp at hν
  | insert ν₀ s hν₀ ih =>
    intro p h
    set K := (p ν₀).natDegree + 1
    have hK := iter_step (insert ν₀ s) p ν₀ h K
    have hK' : ∀ x : ℝ, ∑ ν ∈ s, ((op ν₀ ν)^[K] (p ν)).eval (x : ℂ) * Complex.exp (ν * x) = 0 := by
      intro x
      have := hK x
      rw [Finset.sum_insert hν₀, op_self, iterate_derivative_eq_zero (Nat.lt_succ_self _),
        eval_zero, zero_mul, zero_add] at this
      exact this
    have hs : ∀ ν ∈ s, p ν = 0 := fun ν hν =>
      iter_inj (fun h : ν = ν₀ => hν₀ (h ▸ hν)) K (ih (fun ν => (op ν₀ ν)^[K] (p ν)) hK' ν hν)
    have h0 : ∀ x : ℝ, (p ν₀).eval (x : ℂ) = 0 := fun x => by
      have := h x
      rw [Finset.sum_insert hν₀, Finset.sum_eq_zero fun ν hν => by rw [hs ν hν, eval_zero, zero_mul],
        add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right (Complex.exp_ne_zero _)
    have hp0 : p ν₀ = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono ?_
        (Set.infinite_range_of_injective Complex.ofReal_injective))
      rintro _ ⟨x, rfl⟩
      exact h0 x
    intro ν hν
    rcases Finset.mem_insert.1 hν with rfl | hν
    · exact hp0
    · exact hs ν hν

theorem unifiedSpliceExpPoly : Standalone.UnifiedSpliceExpPoly.statement := expPolyS

end Novel.UnifiedSpliceExpPolyProof

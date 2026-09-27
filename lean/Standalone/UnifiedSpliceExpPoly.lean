import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Claim 049 (b2), the independence step: exponential polynomials

(b2) compares coefficients of `x^k e^{λx}` in `R♯`, for the complex eigenvalues `λ` of `A`. This is
the linear independence it uses: functions `x ↦ p(x) e^{νx}` with distinct complex frequencies `ν`
and complex polynomials `p` are independent over `ℂ`.

`expPolyStatement`: if `Σ_{ν ∈ s} p_ν(x) e^{νx} = 0` for every real `x`, then every `p_ν = 0`. The
proof is the standard one. `D − ν₀` sends `p e^{νx}` to `(p' + (ν − ν₀) p) e^{νx}`, so it keeps the
frequencies. Applied `deg p_{ν₀} + 1` times, it kills the `ν₀` term, and it is injective on the
others. Induction on `s`, and a polynomial vanishing on `ℝ` is zero.
-/

open Polynomial

namespace Standalone.UnifiedSpliceExpPoly

def expPolyStatement : Prop := ∀ (s : Finset ℂ) (p : ℂ → ℂ[X]),
  (∀ x : ℝ, ∑ ν ∈ s, (p ν).eval (x : ℂ) * Complex.exp (ν * x) = 0) → ∀ ν ∈ s, p ν = 0

def statement : Prop := expPolyStatement

end Standalone.UnifiedSpliceExpPoly

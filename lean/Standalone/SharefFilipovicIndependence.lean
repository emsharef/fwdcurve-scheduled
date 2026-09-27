import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Polynomial.Basic

/-! # Claim 034 (c): the front end absorbs nothing

`independenceStatement` is the linear-independence step of (a) and (c). Let `β > 0` and let
`Q_1, ..., Q_n` and `P` be real polynomials. If `∑_i Q_i(x) e^{−iβx} = P(x)` for every `x` in an
open interval of positive length, then every `Q_i` and `P` vanish. The functions `x^k e^{−iβx}`
(`i ≥ 1`) and `x^k` are linearly independent on every interval. Hence the right side of (34.5),
piecewise polynomial in `T`, vanishes. The exponential polynomial `R(t, ·)` with no exponent-zero
term then vanishes on the interval, and with it every coefficient, so `R(t, x) = 0` for all
`x ≥ 0`, not only for `x ≤ H − t`.
-/

open Set Polynomial
namespace Standalone.SharefFilipovicIndependence

def independenceStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n : ℕ) (Q : Fin n → ℝ[X]) (P : ℝ[X])
  (c d : ℝ), c < d →
  (∀ x ∈ Ioo c d, ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) = P.eval x) →
  (∀ i, Q i = 0) ∧ P = 0

def statement : Prop := independenceStatement

end Standalone.SharefFilipovicIndependence

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Claim 042 (a): varying exponents, pointwise reduction

The block is the bounded exponential-polynomial family BEP(K, n) (42.1),
`F(x, z) = ∑_i p_i(x, z) e^{−β_i x}` with `p_i(x, z) = ∑_{μ ≤ n_i} z_{i,μ} x^μ` and every exponent
`β_i = z_{i,n_i+1}` a parameter. The parameters are indexed by `Σ i, Fin (n_i + 2)`. Index
`⟨i, μ⟩` with `μ ≤ n_i` is the coefficient `z_{i,μ}`, and `⟨i, n_i + 1⟩` is the exponent `β_i`.

`dF z I x` and `d2F z I J x` are the first and second parameter derivatives of `F`, written out.
* `∂F/∂z_{i,μ} = x^μ e^{−β_i x}` and `∂F/∂β_i = −x p_i(x) e^{−β_i x}`.
* The only nonzero second derivatives are, within one block,
  `∂²F/∂z_{i,μ}∂β_i = −x^{μ+1} e^{−β_i x}` and `∂²F/∂β_i² = x² p_i(x) e^{−β_i x}`.

`derivStatement` certifies that these are the partial derivatives. `residualBEP` is the difference
of the two sides of [filipovic2000exponential] (3), which is (34.3) for (42.1):
`R(x) = ∑_I b_I ∂_I F + ½ ∑_{I,J} a_{IJ} ∂_I∂_J F − ∑_{I,J} a_{IJ} ∂_I F ∫_0^x ∂_J F − ∂_x F`.

`reductionStatement` is (a). At a point where every exponent is positive, suppose `R` equals a
polynomial on an open interval, as AX-01 for the splice gives with the front end's polynomial of
degree at most 3 (Claim 034's (34.5)). Then `R = 0` everywhere and the polynomial is zero. That
is, (3) holds at the point, and the front end absorbs nothing.

`transferStatement` is (a) almost everywhere. Take any measure `ν` on the points `(t, ω)`, with
`(Z, a, b)` the parameters and Itô coefficients there. Suppose (P) holds `ν`-almost everywhere,
and the splice's AX-01 holds `ν`-almost everywhere, in the form of (a)'s hypothesis. Then (3)
holds `ν`-almost everywhere. (b), the conclusions of [filipovic2000exponential] Theorem 3.2 and
Corollaries 3.4–3.5, is not stated here. It waits for the ledger entry that cites that theorem
with this hypothesis.
-/

open Polynomial Set
namespace Standalone.SpliceVaryingExponents

variable {K : ℕ} {n : Fin K → ℕ}

/-- The exponent `β_i = z_{i,n_i+1}`. -/
def expo (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) : ℝ := z ⟨i, Fin.last (n i + 1)⟩

/-- `p_i(x, z) = ∑_{μ ≤ n_i} z_{i,μ} x^μ`. -/
def poly (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) (x : ℝ) : ℝ :=
  ∑ μ : Fin (n i + 1), z ⟨i, μ.castSucc⟩ * x ^ (μ : ℕ)

/-- `F(x, z) = ∑_i p_i(x, z) e^{−β_i x}`. -/
noncomputable def FBEP (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, poly z i x * Real.exp (-expo z i * x)

/-- `∂F/∂z_I`. -/
noncomputable def dF (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (I : Σ i : Fin K, Fin (n i + 2))
    (x : ℝ) : ℝ :=
  if (I.2 : ℕ) < n I.1 + 1 then x ^ (I.2 : ℕ) * Real.exp (-expo z I.1 * x)
  else -(x * poly z I.1 x) * Real.exp (-expo z I.1 * x)

/-- `∂²F/∂z_I ∂z_J`. -/
noncomputable def d2F (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (I J : Σ i : Fin K, Fin (n i + 2))
    (x : ℝ) : ℝ :=
  if I.1 = J.1 then
    if (I.2 : ℕ) < n I.1 + 1 then
      (if (J.2 : ℕ) < n J.1 + 1 then 0 else -(x ^ ((I.2 : ℕ) + 1)) * Real.exp (-expo z I.1 * x))
    else
      (if (J.2 : ℕ) < n J.1 + 1 then -(x ^ ((J.2 : ℕ) + 1)) * Real.exp (-expo z I.1 * x)
        else x ^ 2 * poly z I.1 x * Real.exp (-expo z I.1 * x))
  else 0

/-- The difference of the two sides of [filipovic2000exponential] (3). -/
noncomputable def residualBEP (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (a : (Σ i : Fin K, Fin (n i + 2)) → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (x : ℝ) : ℝ :=
  ∑ I, b I * dF z I x + (1 / 2) * ∑ I, ∑ J, a I J * d2F z I J x -
    ∑ I, ∑ J, a I J * dF z I x * (∫ η in (0:ℝ)..x, dF z J η) - deriv (FBEP z) x

def derivStatement : Prop := ∀ (K : ℕ) (n : Fin K → ℕ) (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (I : Σ i : Fin K, Fin (n i + 2)) (x : ℝ),
  HasDerivAt (fun w => FBEP (Function.update z I w) x) (dF z I x) (z I) ∧
  ∀ J : Σ i : Fin K, Fin (n i + 2),
    HasDerivAt (fun w => dF (Function.update z J w) I x) (d2F z I J x) (z J)

def reductionStatement : Prop := ∀ (K : ℕ) (n : Fin K → ℕ) (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (a : (Σ i : Fin K, Fin (n i + 2)) → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ), (∀ i, 0 < expo z i) →
  ∀ (P : ℝ[X]) (c d : ℝ), c < d → (∀ x ∈ Ioo c d, residualBEP z a b x = P.eval x) →
  P = 0 ∧ ∀ x : ℝ, residualBEP z a b x = 0

def transferStatement : Prop := ∀ (K : ℕ) (n : Fin K → ℕ) (X : Type) (_ : MeasurableSpace X)
  (ν : MeasureTheory.Measure X) (Z : X → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (a : X → (Σ i : Fin K, Fin (n i + 2)) → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (b : X → (Σ i : Fin K, Fin (n i + 2)) → ℝ),
  (∀ᵐ p ∂ν, ∀ i, 0 < expo (Z p) i) →
  (∀ᵐ p ∂ν, ∃ (P : ℝ[X]) (c d : ℝ), c < d ∧
    ∀ x ∈ Ioo c d, residualBEP (Z p) (a p) (b p) x = P.eval x) →
  ∀ᵐ p ∂ν, ∀ x : ℝ, residualBEP (Z p) (a p) (b p) x = 0

def statement : Prop := derivStatement ∧ reductionStatement ∧ transferStatement

end Standalone.SpliceVaryingExponents

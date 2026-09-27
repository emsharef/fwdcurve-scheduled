import Standalone.UnifiedSpliceStep0
import Standalone.UnifiedSpliceQuantifiers
import Standalone.UnifiedSpliceConverseAX01
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Claim 050: the unified splice beyond bounded coefficients

(a), (b): Claim 049's Lean statements already quantify over arbitrary real coefficients at each
`(u, ω)`. `UnifiedSpliceStep0`, `UnifiedSpliceQuantifiers` and `UnifiedSpliceConverseAX01` carry no
bound, measurability or integrability hypothesis on the data `D`. AX-01 is the only hypothesis
linking times and paths. So they hold verbatim for the class (L), with the same quantifiers and
without a stopping argument, as the claim's proof says. `carryOverStatement` records this by
restating them.

(d), and the class (L):
* `productStatement`: local square integrability is not closed under products. `u^{−1/3}` is
  square integrable on `(0, 1)`, but the square of `u^{−1/3} · u^{−1/3}` is not.
* `boundedFactorStatement`: a bounded factor keeps square integrability. This is the sufficient
  condition for (L1).
* `rowProductStatement`: the product `x · y` of two square-integrable rows is integrable, by
  `|x · y| ≤ (|x|² + |y|²)/2`. This is (c)'s integrability of `a_{kl}`, `ω̄_k` and `V_m · V_{m′}`.
* `shiftStatement`: the family (49.1) is shift-invariant, `F(x + h, z) = F(x, S_h z)`, with `S_h`
  the binomial shift on `z_0` and `e^{hA}` on `ζ`. `frozenStatement`: under the shift evolution
  `z(t) = S_{t−τ} z(τ)` the curve is frozen after `τ`, whereas freezing the parameters is not. The
  claim uses this only to explain why stopping the parameters is the wrong localization.
-/

open MeasureTheory Matrix NormedSpace Set

namespace Standalone.SpliceLocalization

def carryOverStatement : Prop :=
  Standalone.UnifiedSpliceStep0.statement ∧ Standalone.UnifiedSpliceQuantifiers.statement ∧
  Standalone.UnifiedSpliceConverseAX01.statement

def productStatement : Prop :=
  IntegrableOn (fun u : ℝ => (u ^ (-(1:ℝ) / 3)) ^ 2) (Ioo 0 1) ∧
  ¬ IntegrableOn (fun u : ℝ => (u ^ (-(1:ℝ) / 3) * u ^ (-(1:ℝ) / 3)) ^ 2) (Ioo 0 1)

def boundedFactorStatement : Prop := ∀ (s g : ℝ → ℝ) (I : Set ℝ) (C : ℝ), MeasurableSet I →
  IntegrableOn (fun u => s u ^ 2) I → AEStronglyMeasurable s (volume.restrict I) →
  AEStronglyMeasurable g (volume.restrict I) → (∀ u ∈ I, |g u| ≤ C) →
  IntegrableOn (fun u => (g u * s u) ^ 2) I

def rowProductStatement : Prop := ∀ (k : ℕ) (x y : ℝ → Fin k → ℝ) (I : Set ℝ),
  (∀ l, AEStronglyMeasurable (fun u => x u l) (volume.restrict I)) →
  (∀ l, AEStronglyMeasurable (fun u => y u l) (volume.restrict I)) →
  (∀ l, IntegrableOn (fun u => x u l ^ 2) I) → (∀ l, IntegrableOn (fun u => y u l ^ 2) I) →
  IntegrableOn (fun u => x u ⬝ᵥ y u) I

/-- The block (49.1), `F(x, z) = Σ_{μ ≤ d} z_{0,μ} x^μ + c e^{xA} ζ`. -/
noncomputable def F049 {r : ℕ} (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)
    (zP : ℕ → ℝ) (z : Fin r → ℝ) (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range (d + 1), zP μ * x ^ μ) + c ⬝ᵥ (exp (x • A) *ᵥ z)

/-- The binomial shift of the polynomial state, `(S_h z_0)_ν = Σ_{μ ≥ ν} C(μ, ν) h^{μ−ν} z_{0,μ}`. -/
noncomputable def shiftP (d : ℕ) (h : ℝ) (zP : ℕ → ℝ) (ν : ℕ) : ℝ :=
  ∑ μ ∈ Finset.range (d + 1), if ν ≤ μ then (μ.choose ν : ℝ) * h ^ (μ - ν) * zP μ else 0

def shiftStatement : Prop := ∀ (r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (zP : ℕ → ℝ) (z : Fin r → ℝ) (x h : ℝ),
  F049 c A d zP z (x + h) = F049 c A d (shiftP d h zP) (exp (h • A) *ᵥ z) x

def frozenStatement : Prop := ∀ (r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (zP : ℕ → ℝ) (z : Fin r → ℝ) (τ t T : ℝ),
  F049 c A d (shiftP d (t - τ) zP) (exp ((t - τ) • A) *ᵥ z) (T - t) = F049 c A d zP z (T - τ)

def statement : Prop := carryOverStatement ∧ productStatement ∧ boundedFactorStatement ∧
  rowProductStatement ∧ shiftStatement ∧ frozenStatement

end Standalone.SpliceLocalization

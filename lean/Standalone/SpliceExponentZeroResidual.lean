import Standalone.SplicePolynomialParts

/-! # Claim 044 (b): Claim 043's bound and admissible covariances, with the extra cross terms

Where `Δ_m = 0`, a coefficient `z_{0,μ}` with `μ ≥ 1` may covary with the step noise. Its
jump-free cross term then joins the block's residual (43.2) as a polynomial in `x` of degree at most
`μ + 1`. By Cauchy–Schwarz, `|w_μ| ≤ |H^{0,μ}| |H^S|` and `a_{(0,μ),(0,μ)} = |H^{0,μ}|²`, so the term
is present only if `a_{(0,μ),(0,μ)} ≠ 0`. `CrossPoly a E` says this of a polynomial `E`: each
monomial `x^k` of `E` has `k ≤ μ + 1` for some `μ` with `a_{(0,μ),(0,μ)} ≠ 0`. `m = ⌊(d − 1)/2⌋`.

* `rowsStatement` is Claim 043(b) with the extra term: if `R + E` is affine on `[0, ∞)`, then
  `a_{(0,μ),(0,ν)} = 0` unless `μ, ν ≤ m`.
* `attainedStatement` is Claim 043(c) with the extra term: for a polynomial block, every `a`
  supported on `{(0,μ),(0,ν) : μ, ν ≤ m}` stays admissible with only the drifts changed:
  `R + E = 0` for a suitable `b`.
-/

open Polynomial
namespace Standalone.SpliceExponentZeroResidual
open Standalone.SpliceVaryingExponents Standalone.SplicePolynomialParts

/-- Each monomial `x^k` of `E` has `k ≤ μ + 1` for some `μ` with `a_{(0,μ),(0,μ)} ≠ 0`. -/
def CrossPoly {d K : ℕ} {n : Fin K → ℕ} (a : Idx d K n → Idx d K n → ℝ) (E : ℝ[X]) : Prop :=
  ∀ k, E.coeff k ≠ 0 → ∃ μ : Fin (d + 1), k ≤ (μ : ℕ) + 1 ∧ a (Sum.inl μ) (Sum.inl μ) ≠ 0

def rowsStatement : Prop := ∀ (d K : ℕ) (n : Fin K → ℕ), 1 ≤ d → ∀ (z : Idx d K n → ℝ),
  (∀ i, 0 < expo (fun I => z (Sum.inr I)) i) →
  ∀ (a : Matrix (Idx d K n) (Idx d K n) ℝ) (b : Idx d K n → ℝ) (E : ℝ[X]), a.PosSemidef →
  CrossPoly a E → (∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residual43 z a b x + E.eval x = c₀ + c₁ * x) →
  ∀ μ ν : Fin (d + 1), ((d - 1) / 2 < (μ : ℕ) ∨ (d - 1) / 2 < (ν : ℕ)) →
    a (Sum.inl μ) (Sum.inl ν) = 0

def attainedStatement : Prop := ∀ (d : ℕ) (n : Fin 0 → ℕ), 1 ≤ d → ∀ (z : Idx d 0 n → ℝ)
  (a : Idx d 0 n → Idx d 0 n → ℝ) (E : ℝ[X]),
  (∀ μ ν : Fin (d + 1), ((d - 1) / 2 < (μ : ℕ) ∨ (d - 1) / 2 < (ν : ℕ)) →
    a (Sum.inl μ) (Sum.inl ν) = 0) → CrossPoly a E →
  ∃ b : Idx d 0 n → ℝ, ∀ x : ℝ, residual43 z a b x + E.eval x = 0

def statement : Prop := rowsStatement ∧ attainedStatement

end Standalone.SpliceExponentZeroResidual

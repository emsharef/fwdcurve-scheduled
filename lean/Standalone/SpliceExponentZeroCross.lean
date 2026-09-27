import Standalone.SpliceStateBlockCross
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Claim 044 (a): the polynomial cross terms, their jumps and the argument, on one path

The block (44.1) is `F(x, z) = ∑_{μ ≤ d} z_{0,μ} x^μ + C e^{𝒜x} ζ`. On one path the front end's
step scales are `s_j(u)`. The covariation densities (44.2) are `w_μ(u) ∈ ℝ` for the coefficient
`z_{0,μ}` and `w_ζ(u) ∈ ℝ^r` for `ζ`. The coefficient `z_{0,μ}` has volatility `(T − u)^μ H^{0,μ}(u)`,
so its cross term is `w_μ(u) [σ^S(u, T) (T − u)^{μ+1}/(μ+1) + (T − u)^μ S^S(u, T)]`
(`crossPoly044`). The exponential part's cross term is Claim 040's `cross040` with `w_ζ`.
`cross044` is the sum.

* `jumpStatement`: on the maturity interval before a meeting `τ` and on the one after it, the
  integrated cross term of `z_{0,μ}` is a polynomial `P₀`, `P₁` in `T`. The jump `P₁ − P₀` is
  `J_μ(T) = ∫_0^t Δ_m w_μ [(T − u)^{μ+1}/(μ+1) + (T − u)^μ (T − τ)] du`. It has degree at most
  `μ + 1`, and its coefficient of `T^{μ+1}` is `((μ+2)/(μ+1)) ∫_0^t Δ_m w_μ du`. For `μ = 0` it is
  affine, whatever `w_0` is: the level is exempt.
* `coreStatement` is (a)'s argument on the path, with the hypothesis of Claim 040's
  `coreStatement`: for every `t ∈ [0, τ)` the integrated cross term on `(t, H)` is a function
  affine on each maturity interval plus a real-analytic function. Then `Δ_m w_ζ = 0` and
  `Δ_m w_μ = 0` for `1 ≤ μ ≤ d`, for almost every `u ∈ [0, τ)`. Here `𝒜` is invertible and
  `(𝒜, C)` observable, as in Claim 040.
-/

open Matrix NormedSpace MeasureTheory Set Polynomial
namespace Standalone.SpliceExponentZeroCross
open Standalone.SpliceCrossTermDrift Standalone.SpliceStateBlockCross

variable {r : ℕ}

/-- The cross term `w_μ(u) [σ^S(u, T) (T − u)^{μ+1}/(μ+1) + (T − u)^μ S^S(u, T)]` of `z_{0,μ}`. -/
noncomputable def crossPoly044 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (μ : ℕ) (w : ℝ → ℝ) (u T : ℝ) : ℝ :=
  w u * (sigS033 s Tm u T * (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) + (T - u) ^ μ * SS033 s Tm u T)

/-- The block's cross term: Claim 040's for `ζ` plus the polynomial coefficients'. -/
noncomputable def cross044 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (wζ : ℝ → Fin r → ℝ) (d : ℕ) (wP : ℕ → ℝ → ℝ) (u T : ℝ) : ℝ :=
  cross040 s Tm c A wζ u T + ∑ μ ∈ Finset.range (d + 1), crossPoly044 s Tm μ (wP μ) u T

/-- Measurable, bounded step scales and covariation densities on the path. -/
def PathData044 (s : ℕ → ℝ → ℝ) (wζ : ℝ → Fin r → ℝ) (wP : ℕ → ℝ → ℝ) : Prop :=
  PathData s wζ ∧ (∀ μ, Measurable (wP μ)) ∧ ∃ C : ℝ, ∀ μ u, |wP μ u| ≤ C

def jumpStatement : Prop := ∀ (s : ℕ → ℝ → ℝ) (w : ℝ → ℝ), (∀ j, Measurable (s j)) →
  Measurable w → (∃ C : ℝ, (∀ j u, |s j u| ≤ C) ∧ ∀ u, |w u| ≤ C) →
  ∀ (Tm : Finset ℝ) (μ m : ℕ) (t τ τl τr : ℝ), 0 ≤ t → τl < τ → τ < τr →
  (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) → t < τ →
  ∃ P₀ P₁ : ℝ[X],
    (∀ T ∈ Ioo τl τ, t ≤ T → ∫ u in (0:ℝ)..t, crossPoly044 s Tm μ w u T = P₀.eval T) ∧
    (∀ T ∈ Ico τ τr, ∫ u in (0:ℝ)..t, crossPoly044 s Tm μ w u T = P₁.eval T) ∧
    (∀ T : ℝ, (P₁ - P₀).eval T = ∫ u in (0:ℝ)..t, (s (m + 1) u - s m u) * w u *
      ((T - u) ^ (μ + 1) / ((μ : ℝ) + 1) + (T - u) ^ μ * (T - τ))) ∧
    (P₁ - P₀).natDegree ≤ μ + 1 ∧
    (P₁ - P₀).coeff (μ + 1) =
      ((μ : ℝ) + 2) / ((μ : ℝ) + 1) * ∫ u in (0:ℝ)..t, (s (m + 1) u - s m u) * w u

def coreStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : ℕ → ℝ → ℝ) (wζ : ℝ → Fin r → ℝ) (d : ℕ) (wP : ℕ → ℝ → ℝ), PathData044 s wζ wP →
  ∀ (Tm : Finset ℝ) (τ H : ℝ), τ ∈ Tm → τ < H →
  (∀ t ∈ Ico 0 τ, ∃ (p G : ℝ → ℝ), AnalyticOnNhd ℝ G univ ∧
    (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross044 s Tm c A wζ d wP u T = p T + G T) →
  (∀ᵐ u ∂volume, u ∈ Ico 0 τ → (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • wζ u = 0) ∧
  ∀ μ, 1 ≤ μ → μ ≤ d → ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) * wP μ u = 0

def statement : Prop := jumpStatement ∧ coreStatement

end Standalone.SpliceExponentZeroCross

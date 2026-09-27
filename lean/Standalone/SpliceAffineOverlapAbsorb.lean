import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 037 (a): the front end absorbs exactly the affine part

The block is any family linear in its parameters, `F(x, z) = ∑_i z_i φ_i(x)` (`Flin`), with
real-analytic `φ_i`. At a fixed time `t` and path, as in Claim 034's `SharefFilipovicPartA`, the
block's drift and volatility are the ones Itô's formula gives for the linear `F`:
`D^B(T) = −∂_x F(T − t, Z) + ∑_i b_i φ_i(T − t)` (`DBlin`) and
`σ^B(T) = ∑_i φ_i(T − t) σ_Z^{i,·}` (`sBlin`). The block residual (37.1), with `a = σ_Z σ_Zᵀ`, is
`R(x) = ∑_i b_i φ_i(x) − ∑_{i,j} a_{ij} φ_i(x) ∫_0^x φ_j − ∂_x F(x, Z)` (`Rlin`). The front end
has drift `D^S` and volatility `σ^S`; the two groups of drivers are separate.

* `absorbStatement` is (a)'s first sentence. Take the front end of D2 type on an open piece
  `J = (p, q)` of a maturity interval after `t`: `D^S` affine and `σ^S` constant on `J`. If AX-01
  holds for the whole curve on `J`, then `R` is affine on all of `ℝ`: `R(x) = c₀ + c₁ x`.
  **Hypothesis to note:** the statement assumes that the primitives `x ↦ ∫_0^x φ_i` are
  real-analytic, which holds for every real-analytic `φ_i` but is not in Mathlib. It is used to
  continue `R` analytically from `J − t` to `ℝ`, as in the Statement's proof.
* `converseStatement` is (a)'s converse. Let `R(x) = c₀ + c₁ x` for `x ≥ 0`, and let the front end's
  drift absorb it: `∫_t^T D^S = ½ |∫_t^T σ^S|² − ∫_t^T (c₀ + c₁ (u − t)) du`. This is the
  integrated form of `D^S − σ^S · ∫σ^S = −R(T − t)`. Then the whole curve satisfies AX-01 up to `T`.
-/

open Set MeasureTheory
namespace Standalone.SpliceAffineOverlapAbsorb

variable {N m : ℕ}

/-- `F(x, z) = ∑_i z_i φ_i(x)`. -/
noncomputable def Flin (φ : Fin N → ℝ → ℝ) (Z : Fin N → ℝ) (x : ℝ) : ℝ := ∑ i, Z i * φ i x

/-- The block's Itô drift `−∂_x F(T − t, Z) + ∑_i b_i φ_i(T − t)`. -/
noncomputable def DBlin (φ : Fin N → ℝ → ℝ) (Z b : Fin N → ℝ) (t T : ℝ) : ℝ :=
  -deriv (Flin φ Z) (T - t) + ∑ i, b i * φ i (T - t)

/-- The block's volatility `∑_i φ_i(T − t) σ_Z^{i,l}`. -/
noncomputable def sBlin (φ : Fin N → ℝ → ℝ) (sZ : Fin N → Fin m → ℝ) (t T : ℝ) (l : Fin m) : ℝ :=
  ∑ i, φ i (T - t) * sZ i l

/-- The block residual (37.1). -/
noncomputable def Rlin (φ : Fin N → ℝ → ℝ) (Z b : Fin N → ℝ) (a : Fin N → Fin N → ℝ) (x : ℝ) :
    ℝ :=
  ∑ i, b i * φ i x - ∑ i, ∑ j, a i j * φ i x * (∫ η in (0:ℝ)..x, φ j η) - deriv (Flin φ Z) x

def absorbStatement : Prop := ∀ (N m : ℕ) (φ : Fin N → ℝ → ℝ),
  (∀ i, AnalyticOnNhd ℝ (φ i) univ) →
  (∀ i, AnalyticOnNhd ℝ (fun x => ∫ η in (0:ℝ)..x, φ i η) univ) →
  ∀ (Z b : Fin N → ℝ) (sZ : Fin N → Fin m → ℝ) (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t p q : ℝ),
  t ≤ p → p < q → IntervalIntegrable DS volume t q →
  (∀ k, IntervalIntegrable (fun u => sS u k) volume t q) →
  (∃ d₀ d₁ : ℝ, ∀ T ∈ Ioo p q, DS T = d₀ + d₁ * T) →
  (∃ s₀ : Fin m → ℝ, ∀ T ∈ Ioo p q, sS T = s₀) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  (∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DBlin φ Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2) →
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, Rlin φ Z b (fun i j => ∑ k, sZ i k * sZ j k) x = c₀ + c₁ * x

def converseStatement : Prop := ∀ (N m : ℕ) (φ : Fin N → ℝ → ℝ),
  (∀ i, AnalyticOnNhd ℝ (φ i) univ) →
  ∀ (Z b : Fin N → ℝ) (sZ : Fin N → Fin m → ℝ) (DS : ℝ → ℝ) (sS : ℝ → Fin m → ℝ) (t c₀ c₁ : ℝ),
  (∀ x : ℝ, 0 ≤ x → Rlin φ Z b (fun i j => ∑ k, sZ i k * sZ j k) x = c₀ + c₁ * x) →
  (∀ k, (∀ T, sS T k = 0) ∨ (∀ i, sZ i k = 0)) →
  ∀ T : ℝ, t ≤ T → IntervalIntegrable DS volume t T →
  (∀ k, IntervalIntegrable (fun u => sS u k) volume t T) →
  ∫ u in t..T, DS u = (1/2 : ℝ) * ∑ k, (∫ u in t..T, sS u k) ^ 2 -
    ∫ u in t..T, (c₀ + c₁ * (u - t)) →
  ∫ u in t..T, (DS u + DBlin φ Z b t u) =
    (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2

def statement : Prop := absorbStatement ∧ converseStatement

end Standalone.SpliceAffineOverlapAbsorb

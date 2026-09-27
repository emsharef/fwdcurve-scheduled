import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 035 (b): the subspace step

The block factor is `λ(x) = c e^{Ax} b` with `A` invertible and `(A, b)` controllable (no nonzero
row vector `w` has `w A^k b = 0` for every `k`), and `c ≠ 0`. For a jump `Δ` of the step
volatility at the meeting `T_m`, `vvec A b Δ t` is `v_m(t) = ∫_0^t Δ(u) e^{−Au} b du`, and
`B = A^{−1} − T_m I`.

`keyStatement` is the part of (b) after (35.2): suppose that for every `t ∈ [0, L)` the vector
`v_m(t)` lies in `K = {v : c e^{AT} (T I + B) v = 0 for T in an open interval}`. Then `Δ = 0`
almost everywhere on `[0, L)`. In (b), `L = T_m`, and the hypothesis is what the affine step
(`SpliceQuasiExponentialAlgebra.affineStatement`) gives from consistency, for `T` in a piece of a
maturity interval.

The proof is (b)'s. `v_m` has derivative `Δ(t) e^{−At} b`, so by Lebesgue's differentiation
theorem `e^{−Au} b ∈ K` for almost every `u` with `Δ(u) ≠ 0`. If those `u` had positive measure,
`u ↦ w e^{−Au} b` would vanish on a set with an accumulation point for every `w` annihilating
`K`. It is real-analytic, so it vanishes identically, and its derivatives at `0` put `K_b = ℝ^r`
inside `K`. Then `c e^{AT}(T I + B) = 0` on the interval, and at a point `T₀` of it, with its
derivative, `SpliceQuasiExponentialAlgebra.vanishingStatement` forces `c e^{AT₀} = 0`, so `c = 0`.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceQuasiExponentialKey

/-- `v(t) = ∫_0^t Δ(u) e^{−Au} b du`, componentwise. -/
noncomputable def vvec {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (Δ : ℝ → ℝ)
    (t : ℝ) : Fin r → ℝ :=
  fun i => ∫ u in (0:ℝ)..t, Δ u * (exp (u • (-A)) *ᵥ b) i

def keyStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ), c ≠ 0 → (∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0) →
  ∀ (L Tm d₁ d₂ : ℝ) (Δ : ℝ → ℝ), d₁ < d₂ → LocallyIntegrable Δ volume →
  (∀ t ∈ Ico 0 L, ∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ
    ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ vvec A b Δ t)) = 0) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 L → Δ u = 0

def statement : Prop := keyStatement

end Standalone.SpliceQuasiExponentialKey

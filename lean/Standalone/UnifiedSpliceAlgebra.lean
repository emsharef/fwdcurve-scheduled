import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Claim 049 (b)(i)–(iii): the pointwise algebra of the unified splice

Everything here is at one time `u` on one path, in `x = T − u`. There are `k` drivers. The block
(49.1) is `F(x, z) = ∑_{μ ≤ d} z_{0,μ} x^μ + c e^{Ax} ζ`, with integrand rows `Hp μ = H^{0,μ}(u)` and
`Hz = H^ζ(u) ∈ ℝ^{r×k}`, drifts `bP`, `bZ` and state `zP`, `z`.
* `ephi x = c e^{xA}` and `ePhi x = c A⁻¹(e^{xA} − I)` are the exponential coordinate functions
  `φ_ζ` and their primitives `Φ_ζ`; the polynomial ones are `x^μ` and `x^{μ+1}/(μ+1)`.
* `sigB` is the block volatility `σ^B = ∑_k φ_k H^k` and `SigB` its primitive `∑_k Φ_k H^k`.
* `resid` is the block residual (3.162), `R = ∑_k b_k φ_k − ∂_x F − σ^B·Σ^B`, where
  `σ^B·Σ^B = ∑_{k,l} a_{kl} φ_k Φ_l`.
* `sharp Hp V` is the effective level, `H^{0,0} + V`; `R♯` is `resid` with it.
* `Kfun` is (49.4): `K(x) = ∑_{μ=1}^d ω̄_μ ((μ+2)/(μ+1)) x^{μ+1} + c[x e^{Ax} + A⁻¹(e^{Ax} − I)] ω̄_ζ`,
  with `ω̄_k = H^k V`.
* On the maturity interval `I_m`, the front end has noise `V m` and volatility primitive
  `T V_m + κ_m`, so its cross part with the block is `cross` (the terms of `σ·∫σ` bilinear in
  the front end and the block).

Statements:
* `effectiveLevelStatement`, (49.5): `R − R♯ = K + (2ω̄_0 + |V|²) x`, an affine function of `x`
  apart from `K`.
* `jumpStatement`, (b)(i): if `κ_m − κ_{m−1} = −T_m G_m`, with `G_m = V_m − V_{m−1}` (continuity of the
  primitive at `T_m`), the jump `c_m − c_{m−1}` is `∑_k (H^k G_m)[φ_k (T − T_m) + Φ_k]`.
* `nonLevelStatement`, (b)(ii): with `κ_{j} = −u V_j` on the current interval, and
  `H^k G_{m'} = 0` for every non-level `k` and every later interval `m'`, the non-level part of
  `c_m` is `K(x)` on every later interval.
-/

open Matrix NormedSpace

namespace Standalone.UnifiedSpliceAlgebra

variable {k r : ℕ}

/-- `φ_ζ(x) = c e^{xA}`. -/
noncomputable def ephi (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ) : Fin r → ℝ :=
  vecMul c (exp (x • A))

/-- `Φ_ζ(x) = c A⁻¹ (e^{xA} − I)`. -/
noncomputable def ePhi (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ) : Fin r → ℝ :=
  vecMul c (A⁻¹ * (exp (x • A) - 1))

/-- `σ^B(x) = ∑_μ x^μ H^{0,μ} + φ_ζ(x) H^ζ`. -/
noncomputable def sigB (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (x : ℝ) : Fin k → ℝ :=
  ∑ μ ∈ Finset.range (d + 1), x ^ μ • Hp μ + vecMul (ephi c A x) Hz

/-- `Σ^B(x) = ∑_μ x^{μ+1}/(μ+1) H^{0,μ} + Φ_ζ(x) H^ζ`. -/
noncomputable def SigB (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (x : ℝ) : Fin k → ℝ :=
  ∑ μ ∈ Finset.range (d + 1), (x ^ (μ + 1) / (μ + 1)) • Hp μ + vecMul (ePhi c A x) Hz

/-- The block residual `R = ∑_k b_k φ_k − ∂_x F − σ^B·Σ^B` (3.162). -/
noncomputable def resid (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range (d + 1), bP μ * x ^ μ) + ephi c A x ⬝ᵥ bZ -
    ((∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * zP μ * x ^ (μ - 1)) + ephi c A x ⬝ᵥ (A *ᵥ z)) -
    sigB Hp Hz c A d x ⬝ᵥ SigB Hp Hz c A d x

/-- The effective level `H^{0,0}♯ = H^{0,0} + V`. -/
def sharp (Hp : ℕ → Fin k → ℝ) (V : Fin k → ℝ) : ℕ → Fin k → ℝ := Function.update Hp 0 (Hp 0 + V)

/-- `K(x)` (49.4), with `ω̄_μ = H^{0,μ} V` and `ω̄_ζ = H^ζ V`. -/
noncomputable def Kfun (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (V : Fin k → ℝ) (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range d, (Hp (μ + 1) ⬝ᵥ V) * (((μ : ℝ) + 3) / ((μ : ℝ) + 2)) * x ^ (μ + 2)) +
    (ephi c A x ⬝ᵥ (x • (Hz *ᵥ V)) + ePhi c A x ⬝ᵥ (Hz *ᵥ V))

/-- The cross part on `I_m`: `σ^B(x)·(T V_m + κ_m) + V_m·Σ^B(x)`, `x = T − u`. -/
noncomputable def cross (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (V κ : Fin k → ℝ) (u T : ℝ) : ℝ :=
  sigB Hp Hz c A d (T - u) ⬝ᵥ (T • V + κ) + V ⬝ᵥ SigB Hp Hz c A d (T - u)

/-- The non-level part of `cross`: the same with `H^{0,0} = 0`. -/
noncomputable def crossNL (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (V κ : Fin k → ℝ) (u T : ℝ) : ℝ :=
  cross (Function.update Hp 0 0) Hz c A d V κ u T

def effectiveLevelStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (bP zP : ℕ → ℝ)
  (bZ z : Fin r → ℝ) (V : Fin k → ℝ) (x : ℝ),
    resid Hp Hz c A d bP zP bZ z x - resid (sharp Hp V) Hz c A d bP zP bZ z x =
      Kfun Hp Hz c A d V x + (2 * (Hp 0 ⬝ᵥ V) + V ⬝ᵥ V) * x

def jumpStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (V₀ V₁ κ₀ κ₁ : Fin k → ℝ) (Tm u T : ℝ),
    κ₁ - κ₀ = -Tm • (V₁ - V₀) →
    cross Hp Hz c A d V₁ κ₁ u T - cross Hp Hz c A d V₀ κ₀ u T =
      sigB Hp Hz c A d (T - u) ⬝ᵥ ((T - Tm) • (V₁ - V₀)) + (V₁ - V₀) ⬝ᵥ SigB Hp Hz c A d (T - u)

def nonLevelStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (V κ : ℕ → Fin k → ℝ) (Tm : ℕ → ℝ) (j m : ℕ) (u T : ℝ), j ≤ m →
    κ j = -u • V j →
    (∀ m', j < m' → m' ≤ m → κ m' - κ (m' - 1) = -Tm m' • (V m' - V (m' - 1))) →
    (∀ m', j < m' → m' ≤ m → (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V m' - V (m' - 1)) = 0) ∧
      Hz *ᵥ (V m' - V (m' - 1)) = 0) →
    crossNL Hp Hz c A d (V m) (κ m) u T = Kfun Hp Hz c A d (V j) (T - u)

def statement : Prop := effectiveLevelStatement ∧ jumpStatement ∧ nonLevelStatement

end Standalone.UnifiedSpliceAlgebra

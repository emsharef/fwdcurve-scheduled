import Standalone.RecurrentLoadingDrift
import Standalone.RecurrentLoadingStateQ
import Standalone.RecurrentLoadingRestartP

/-! # Claim 031 (b): the conditions of (R3)–(R5)

The state is `Y = (Z, Ξ, P, Q)` with `Z ∈ ℝⁿ` the scale state, `Ξ, Q ∈ ℝ^m` and `P ∈ ℝ^{m×m}`,
`m = pr` indexed by `Fin p × Fin r`, each block with its sup norm. For the scale equation
`dZ = μ_Z(Z) dt + Σ_Z(Z) dB` with drivers `B_l`, `l ∈ Fin d`, the curve's driver `W = B_{j₀}`
and the scale function `ψ`, the coefficients of (31.2) are

* `drift031`: `(μ_Z(Z), Â Ξ, Â P + P Âᵀ + ψ(Z)² β βᵀ, Â Q + P γ)`;
* `diff031 y l`: `(Σ_Z(Z)_l, ψ(Z) β if l = j₀ else 0, 0, 0)`;

the restart map (31.3) is `restart031 y = (Z, M̂ Ξ, M̂ P M̂ᵀ, M̂ Q)`, and the curve map (31.4) is
`curve031 y D x = k(x, D) · (Ξ + P K(x, D) + Q)`. None of these takes the time, `D` or the
schedule as an argument, except the curve map, which depends on the schedule only through `D`.

`conditionsStatement`: if `μ_Z` and `Σ_Z` are Lipschitz and `ψ` is Lipschitz and bounded, then
the drift and the diffusion are globally Lipschitz in `Y`, the restart map is a fixed continuous
linear map leaving `Z` unchanged, and for each `D` and `x` the curve map is a continuous linear
function of `Y` (so Lipschitz) that does not depend on `Z`. With `ψ ≡ 1` (Claim 030) the scale
block can be dropped.
-/

open Matrix
open scoped NNReal
namespace Standalone.ExternalScaleConditions
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingStateQ
open Standalone.RecurrentLoadingRestartP

/-- The state `(Z, Ξ, P, Q)`. -/
abbrev State031 (n p r : ℕ) :=
  (Fin n → ℝ) × (Fin p × Fin r → ℝ) × (Fin p × Fin r → Fin p × Fin r → ℝ) × (Fin p × Fin r → ℝ)

variable {n d p r : ℕ}

/-- The drift of (31.2). -/
noncomputable def drift031 (μZ : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (u v : Fin p → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (y : State031 n p r) :
    State031 n p r :=
  (μZ y.1, Ahat030 A *ᵥ y.2.1,
    fun i j => (Ahat030 (p := p) A * of y.2.2.1 + of y.2.2.1 * (Ahat030 A)ᵀ :
      Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i j +
      ψ y.1 ^ 2 * (beta030 v b i * beta030 v b j),
    Ahat030 A *ᵥ y.2.2.2 + of y.2.2.1 *ᵥ gamma030 u c)

/-- The diffusion of (31.2), one state vector per driver. -/
noncomputable def diff031 (sZ : (Fin n → ℝ) → Fin d → Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (j₀ : Fin d) (v : Fin p → ℝ) (b : Fin r → ℝ) (y : State031 n p r) :
    Fin d → State031 n p r := fun l =>
  (sZ y.1 l, if l = j₀ then (fun i => ψ y.1 * beta030 v b i) else 0, 0, 0)

/-- The restart map (31.3). -/
def restart031 (M : Matrix (Fin p) (Fin p) ℝ) (y : State031 n p r) : State031 n p r :=
  (y.1, Mhat030 M *ᵥ y.2.1, fun i j => (Mhat030 (r := r) M * of y.2.2.1 * (Mhat030 M)ᵀ :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i j,
    Mhat030 M *ᵥ y.2.2.2)

/-- The curve map (31.4) at time to maturity `x` and distances `D`. -/
noncomputable def curve031 (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (y : State031 n p r) (D : Finset ℝ) (x : ℝ) : ℝ :=
  k030 u M c A x D ⬝ᵥ (y.2.1 + of y.2.2.1 *ᵥ Kvec030 u M c A x D + y.2.2.2)

def conditionsStatement : Prop := ∀ (n d p r : ℕ) (μZ : (Fin n → ℝ) → Fin n → ℝ)
  (sZ : (Fin n → ℝ) → Fin d → Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ) (j₀ : Fin d)
  (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (Lμ Ls Lψ : ℝ≥0) (Kψ : ℝ),
  LipschitzWith Lμ μZ → LipschitzWith Ls sZ → LipschitzWith Lψ ψ → (∀ z, |ψ z| ≤ Kψ) →
  (∃ L : ℝ≥0, LipschitzWith L (drift031 μZ ψ u v c b A)) ∧
  (∃ L : ℝ≥0, LipschitzWith L (diff031 sZ ψ j₀ v b)) ∧
  (∃ R : State031 n p r →L[ℝ] State031 n p r, ⇑R = restart031 M) ∧
  (∀ y : State031 n p r, (restart031 M y).1 = y.1) ∧
  (∀ (D : Finset ℝ) (x : ℝ), ∃ R : State031 n p r →L[ℝ] ℝ,
    ⇑R = fun y => curve031 u M c A y D x) ∧
  (∀ (D : Finset ℝ) (x : ℝ) (y y' : State031 n p r), y.2 = y'.2 →
    curve031 u M c A y D x = curve031 u M c A y' D x)

def statement : Prop := conditionsStatement

end Standalone.ExternalScaleConditions

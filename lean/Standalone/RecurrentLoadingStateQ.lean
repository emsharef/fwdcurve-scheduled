import Standalone.RecurrentLoadingStateP

/-! # Claim 030 (b): the state `Q` between meetings

`gamma030 u c = u ⊗ c` is `γ`. `qEquationStatement`: on an open interval
`(t₀, t₁)` free of meetings, with `t₀ ≥ 0`, the state `Q_t` of (30.8) satisfies
(30.3), `dQ/dt = Â Q + P γ`, coordinate by coordinate. The restart of `Q` and the
equation and restart of `Ξ` are not in this target.
-/

open Matrix
namespace Standalone.RecurrentLoadingStateQ
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP

variable {p r : ℕ}

/-- `γ = u ⊗ c`. -/
def gamma030 (u : Fin p → ℝ) (c : Fin r → ℝ) : Fin p × Fin r → ℝ := fun ij => u ij.1 * c ij.2

def qEquationStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ t t₁ : ℝ),
  0 ≤ t₀ → t₀ < t → t < t₁ → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < t₁)) →
  ∀ a : Fin p × Fin r, HasDerivAt (fun x => Q030 Tm u v M c b A x a)
    ((Ahat030 A *ᵥ Q030 Tm u v M c b A t + P030 Tm v M b A t *ᵥ gamma030 u c) a) t

def statement : Prop := qEquationStatement

end Standalone.RecurrentLoadingStateQ

import Standalone.RecurrentLoadingDrift
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Claim 030 (b): the state `P` between meetings

`Ehat030 A h = I_p ⊗ e^{hA}` is `e^{Â h}` with `Â = I_p ⊗ A` (`Ahat030`), and
`beta030 v b = v ⊗ b` is `β`.

`propagateStatement`: if no meeting lies in `(t₀, t]`, then
`w(s,t) = e^{Â(t−t₀)} w(s,t₀)` for `s ≤ t₀` and `w(s,t) = e^{Â(t−s)} β` for
`t₀ < s ≤ t`; this is the proof's `∂_t w = Â w` between meetings with
`w(t,t) = β`. `pEquationStatement`: on an open interval `(t₀, t₁)` free of
meetings, with `t₀ ≥ 0`, the state `P_t` of (30.8) satisfies (30.3),
`dP/dt = Â P + P Âᵀ + β βᵀ`, entry by entry. The equations for `Q` and `Ξ`,
and the restarts (30.4), are not in this target.
-/

open Matrix NormedSpace
open scoped Kronecker
namespace Standalone.RecurrentLoadingStateP
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift

variable {p r : ℕ}

/-- `e^{Â h} = I_p ⊗ e^{hA}`. -/
noncomputable def Ehat030 (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  (1 : Matrix (Fin p) (Fin p) ℝ) ⊗ₖ exp (h • A)

/-- `Â = I_p ⊗ A`. -/
def Ahat030 (A : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  (1 : Matrix (Fin p) (Fin p) ℝ) ⊗ₖ A

/-- `β = v ⊗ b`. -/
def beta030 (v : Fin p → ℝ) (b : Fin r → ℝ) : Fin p × Fin r → ℝ := fun ij => v ij.1 * b ij.2

def propagateStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ t : ℝ),
  t₀ ≤ t → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ t)) →
  (∀ s, s ≤ t₀ → w030 Tm v M b A s t = Ehat030 (p := p) A (t - t₀) *ᵥ w030 Tm v M b A s t₀) ∧
  (∀ s, t₀ < s → s ≤ t → w030 Tm v M b A s t = Ehat030 (p := p) A (t - s) *ᵥ beta030 v b)

def pEquationStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ t t₁ : ℝ),
  0 ≤ t₀ → t₀ < t → t < t₁ → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < t₁)) →
  ∀ ab cd : Fin p × Fin r, HasDerivAt (fun u => P030 Tm v M b A u ab cd)
    ((Ahat030 A * P030 Tm v M b A t + P030 Tm v M b A t * (Ahat030 A)ᵀ +
      vecMulVec (beta030 v b) (beta030 v b) : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd) t

def statement : Prop := propagateStatement ∧ pEquationStatement

end Standalone.RecurrentLoadingStateP

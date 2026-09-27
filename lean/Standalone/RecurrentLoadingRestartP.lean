import Standalone.RecurrentLoadingStateP
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

/-! # Claim 030 (b): the restart of `P` at a meeting

`Mhat030 M = M ⊗ I_r` is `M̂`. `restartPStatement`: let `T` be a meeting and
`t₀ ≥ 0` a time before it with no meeting in `(t₀, T)`. Then `P_t` has a limit
`P_{T−}` as `t ↑ T`, entry by entry, and `P_T = M̂ P_{T−} M̂ᵀ`; this is the `P`
component of the restart map (30.4). The restarts of `Q` and `Ξ` are not in this
target.
-/

open Matrix Filter Topology
open scoped Kronecker
namespace Standalone.RecurrentLoadingRestartP
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift

variable {p r : ℕ}

/-- `M̂ = M ⊗ I_r`. -/
def Mhat030 (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  M ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)

def restartPStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ T : ℝ),
  0 ≤ t₀ → t₀ < T → T ∈ Tm → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) →
  ∃ Pm : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
    (∀ ab cd, Tendsto (fun u => P030 Tm v M b A u ab cd) (𝓝[<] T) (𝓝 (Pm ab cd))) ∧
    P030 Tm v M b A T = Mhat030 (r := r) M * Pm * (Mhat030 M)ᵀ

def statement : Prop := restartPStatement

end Standalone.RecurrentLoadingRestartP

import Standalone.ExternalScaleDrift
import Standalone.RecurrentLoadingRestartP

/-! # Claim 031 (b): the state `P` with a stochastic scale, pathwise

On a fixed path the scale is a continuous function of time `h s = ψ(Z_s(ω))`,
and `P031 … h t = ∫_0^t h(s)^2 w(s,t) w(s,t)ᵀ ds` is the state `P` of (31.5).
`pEquationStatement`: on an open interval `(t₀, t₁)` free of meetings, with
`t₀ ≥ 0`, it satisfies (31.2), `dP/dt = Â P + P Âᵀ + h(t)^2 β βᵀ`, entry by entry.
`restartStatement`: at a meeting `T` with no meeting in `(t₀, T)`, `P` has a left
limit and `P_T = M̂ P_{T−} M̂ᵀ`, the `P` component of (31.3). The states `Q` and
`Ξ` are not in this target.
-/

open Matrix Filter Topology
namespace Standalone.ExternalScaleStateP
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Standalone.ExternalScaleDrift

def pEquationStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ),
  Continuous h → ∀ t₀ t t₁ : ℝ,
  0 ≤ t₀ → t₀ < t → t < t₁ → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < t₁)) →
  ∀ ab cd : Fin p × Fin r, HasDerivAt (fun x => P031 Tm v M b A h x ab cd)
    ((Ahat030 A * P031 Tm v M b A h t + P031 Tm v M b A h t * (Ahat030 A)ᵀ +
      h t ^ 2 • vecMulVec (beta030 v b) (beta030 v b) :
        Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) ab cd) t

def restartStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ),
  Continuous h → ∀ t₀ T : ℝ,
  0 ≤ t₀ → t₀ < T → T ∈ Tm → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) →
  ∃ Pm : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ,
    (∀ ab cd, Tendsto (fun x => P031 Tm v M b A h x ab cd) (𝓝[<] T) (𝓝 (Pm ab cd))) ∧
    P031 Tm v M b A h T = Mhat030 (r := r) M * Pm * (Mhat030 M)ᵀ

def statement : Prop := pEquationStatement ∧ restartStatement

end Standalone.ExternalScaleStateP

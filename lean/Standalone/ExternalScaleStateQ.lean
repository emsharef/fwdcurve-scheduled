import Standalone.ExternalScaleStateP
import Standalone.RecurrentLoadingStateQ

/-! # Claim 031 (b): the state `Q` with a stochastic scale, pathwise

For a continuous scale path `h` (on each path `h s = ψ(Z_s(ω))`),
`Q031 … h t = ∫_0^t h(s)^2 w(s,t) J̃(s,t) ds` is the state `Q` of (31.5).
`qEquationStatement`: on an open interval `(t₀, t₁)` free of meetings, with
`t₀ ≥ 0`, it satisfies (31.2), `dQ/dt = Â Q + P γ` with `P` the scaled state
`P031`, coordinate by coordinate. `restartStatement`: at a meeting `T` with no
meeting in `(t₀, T)`, `Q` has a left limit and `Q_T = M̂ Q_{T−}`, the `Q` component
of (31.3). The state `Ξ` is not in this target.
-/

open Matrix Filter Topology
namespace Standalone.ExternalScaleStateQ
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Standalone.RecurrentLoadingStateQ Standalone.ExternalScaleDrift

def qEquationStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ),
  Continuous h → ∀ t₀ t t₁ : ℝ,
  0 ≤ t₀ → t₀ < t → t < t₁ → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < t₁)) →
  ∀ a : Fin p × Fin r, HasDerivAt (fun x => Q031 Tm u v M c b A h x a)
    ((Ahat030 A *ᵥ Q031 Tm u v M c b A h t + P031 Tm v M b A h t *ᵥ gamma030 u c) a) t

def restartStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ),
  Continuous h → ∀ t₀ T : ℝ,
  0 ≤ t₀ → t₀ < T → T ∈ Tm → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) →
  ∃ Qm : Fin p × Fin r → ℝ,
    (∀ a, Tendsto (fun x => Q031 Tm u v M c b A h x a) (𝓝[<] T) (𝓝 (Qm a))) ∧
    Q031 Tm u v M c b A h T = Mhat030 (r := r) M *ᵥ Qm

def statement : Prop := qEquationStatement ∧ restartStatement

end Standalone.ExternalScaleStateQ

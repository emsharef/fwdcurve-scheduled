import Standalone.RecurrentLoadingRestartP
import Standalone.RecurrentLoadingStateQ

/-! # Claim 030 (b): the restart of `Q` at a meeting

`restartQStatement`: let `T` be a meeting and `t₀ ≥ 0` a time before it with no
meeting in `(t₀, T)`. Then `Q_t` has a limit `Q_{T−}` as `t ↑ T`, coordinate by
coordinate, and `Q_T = M̂ Q_{T−}`; this is the `Q` component of the restart map
(30.4). The equation and restart of `Ξ` are not in this target.
-/

open Matrix Filter Topology
namespace Standalone.RecurrentLoadingRestartQ
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingRestartP

def restartQStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ T : ℝ),
  0 ≤ t₀ → t₀ < T → T ∈ Tm → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) →
  ∃ Qm : Fin p × Fin r → ℝ,
    (∀ a, Tendsto (fun x => Q030 Tm u v M c b A x a) (𝓝[<] T) (𝓝 (Qm a))) ∧
    Q030 Tm u v M c b A T = Mhat030 (r := r) M *ᵥ Qm

def statement : Prop := restartQStatement

end Standalone.RecurrentLoadingRestartQ

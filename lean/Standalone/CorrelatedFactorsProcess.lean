import Standalone.CorrelatedFactorsReduction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousOn

/-! # Claim 036 (e): no consistent process through the source's point

The setting is `CorrelatedFactorsReduction`'s with `n₂ = 1`, so `n = 0` and `K_0 = {0}` when
`z_{2,0} = 0`: `z_{2,0}` is structurally absent, with drift `b_{2,0} = 0`.

* `pointStatement`: if `z_{2,0} = 0` and `z_{2,1} < 0`, no nonnegative definite `a` and no `b` with
  `b_{2,0} = 0` satisfy (34.3) for all `x ≥ 0`, since (36.1) reads `a_{00}/β = z_{2,1}`. The
  source's point of (e) (`CorrelatedFactorsSign.zEx`, with `z_{2,1} = −1`) is one case.
* `pathStatement`, (e)'s last step, pathwise. A consistent Itô process satisfies (34.3) at almost
  every time along its path. Take a path `t ↦ Z_t` whose coordinate `Z^{2,1}` is right-continuous
  at `t₀` with `Z^{2,1}_{t₀} < 0`, for example `−1` at the source's point. Then for no `δ > 0` can
  `Z^{2,0}_t = 0`, and (34.3) with some nonnegative definite `a_t` and some `b_t` with
  `b_{2,0} = 0`, hold at almost every `t ∈ (t₀, t₀ + δ)`. So no consistent process starts at this
  point, trivial or not.
-/

open MeasureTheory Set
namespace Standalone.CorrelatedFactorsProcess
open Standalone.SharefFilipovicResidual

def pointStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ : ℕ) (z : Fin (n₁ + 1) ⊕ Fin (1 + 1) → ℝ),
  z (Sum.inr 0) = 0 → z (Sum.inr 1) < 0 →
  ∀ (b : Fin (n₁ + 1) ⊕ Fin (1 + 1) → ℝ)
    (a : Matrix (Fin (n₁ + 1) ⊕ Fin (1 + 1)) (Fin (n₁ + 1) ⊕ Fin (1 + 1)) ℝ),
    a.PosSemidef → b (Sum.inr 0) = 0 → ¬ ∀ x : ℝ, 0 ≤ x → residual034 β n₁ 1 z b a x = 0

def pathStatement : Prop := ∀ (β : ℝ), 0 < β → ∀ (n₁ : ℕ)
  (Z : ℝ → Fin (n₁ + 1) ⊕ Fin (1 + 1) → ℝ)
  (a : ℝ → Matrix (Fin (n₁ + 1) ⊕ Fin (1 + 1)) (Fin (n₁ + 1) ⊕ Fin (1 + 1)) ℝ)
  (b : ℝ → Fin (n₁ + 1) ⊕ Fin (1 + 1) → ℝ) (t₀ δ : ℝ), 0 < δ →
  ContinuousWithinAt (fun t => Z t (Sum.inr 1)) (Ici t₀) t₀ → Z t₀ (Sum.inr 1) < 0 →
  ¬ ∀ᵐ t ∂(volume.restrict (Ioo t₀ (t₀ + δ))), Z t (Sum.inr 0) = 0 ∧ (a t).PosSemidef ∧
      b t (Sum.inr 0) = 0 ∧ ∀ x : ℝ, 0 ≤ x → residual034 β n₁ 1 (Z t) (b t) (a t) x = 0

def statement : Prop := pointStatement ∧ pathStatement

end Standalone.CorrelatedFactorsProcess

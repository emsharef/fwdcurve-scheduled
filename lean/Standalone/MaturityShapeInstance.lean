import Standalone.MaturityShapeGauss
import Standalone.D3EventVariances

/-! # Claim 047: `ShapeGaussLaw` is satisfiable with Gaussian meeting jumps

`model011s N τ v` is Claim 011's model as a `ShapeModel`: `ℝ^N` with the product of the centered
Gaussians `N(0, v_i)`, the jumps `Z_i = ω_i` at the dates `τ (i + 1)`, the coordinate filtration,
and no diffusion (`σ² = 0`, `I = 0`, `X = 0`, zero initial curve).
`nonvacuityStatement`: for dates `0 = τ 0 < τ 1 < … < τ N` and every bounded Borel shape `φ`, it
satisfies `ShapeGaussLaw` for every horizon `H`. A model with `σ² ≠ 0` needs a Brownian motion and
its Wiener integrals, which are not built here.
-/

open MeasureTheory

namespace Standalone.MaturityShapeInstance
open Standalone.MaturityShapeGauss

/-- Claim 011's model, with no diffusion. -/
noncomputable def model011s (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal) :
    ShapeModel (Standalone.D3EventVariances.Ω N) N where
  T i := τ (i.val + 1)
  v i := v i
  g _ := 0
  f0 _ := 0
  Z i ω := ω i
  I _ _ := 0
  X _ _ _ := 0
  F t := Standalone.D3EventVariances.filt τ t

def nonvacuityStatement : Prop := ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
  τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → ∀ φ : ℝ → ℝ → ℝ, Measurable (Function.uncurry φ) →
    (∃ C, ∀ s x, |φ s x| ≤ C) → ∀ H : ℝ,
      ShapeGaussLaw (model011s N τ v) φ (Standalone.D3EventVariances.Q v) H

def statement : Prop := nonvacuityStatement

end Standalone.MaturityShapeInstance

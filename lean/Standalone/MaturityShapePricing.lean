import Standalone.MaturityShapeGauss

/-! # Claim 047 (b): pricing with a shape, conditional on `ShapeGaussLaw`

In the model of `MaturityShapeGauss`, **under the hypothesis `ShapeGaussLaw` (not derived in Lean)**:
* `pricingStatement`: `G_t = E_Q[exp ∫_a^b r | F_t]` is an integrable martingale with
  `G_0 = exp(A + p̃)` a.s.; `E_Q[B_S⁻¹] = P(0, S)`, so `Q^S` is a probability measure; under `Q^S`,
  `log G_S ~ N(log m − q/2, q)` with `z̃`, `q` and `m` of (47.3); and the call is
  `C = P(0, S) · C0177 m q K`, Claim 017's Black integral, i.e. (46.5). The recovery of
  `(P(0, S), m, q)` from a surface is then Claim 046's `surfaceStatement`, which is about
  `C0177` alone.
* `accumulationStatement` (deterministic): (47.4) for `0 ≤ S < a < b`, with
  `β(s) = δ⁻¹ ∫_a^b φ(s, T) dT`: `q = δ²[Σ_{T_i ≤ S} v_i + ∫_0^S σ²β²]` and
  `z̃ = δ[Σ_{T_i ≤ S}(S − T_i) v_i + ∫_0^S σ² Φ(s, S) β(s) ds]`; and `z̃ = log G_0 − log m`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.MaturityShapePricing
open Standalone.CompoundedFuturesIdentification Standalone.MaturityShapeIdentities
  Standalone.MaturityShapeGauss

variable {Ω : Type*} {N : ℕ}

/-- `G_t(a, b) = E_Q[exp ∫_a^b r | F_t]`. -/
noncomputable def G [MeasurableSpace Ω] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (Q : Measure Ω)
    (t a b : ℝ) : Ω → ℝ :=
  Q[fun ω => Real.exp (∫ u in a..b, rate M φ u ω) | M.F t]

/-- `B_S⁻¹ = exp(−∫_0^S r)`. -/
noncomputable def disc (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (S : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-∫ u in (0:ℝ)..S, rate M φ u ω)

/-- `P(0, S) = exp(−∫_0^S f(0, u) du)`. -/
noncomputable def P0 (M : ShapeModel Ω N) (S : ℝ) : ℝ := Real.exp (-Aint M 0 S)

/-- `z̃ = Σ_i j_i v_i + ∫_0^S σ(s)² Φ(s, S) W̃(s) ds` (47.3). -/
noncomputable def ztil (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (S a b : ℝ) : ℝ :=
  ∑ i, j S a b (M.T i) * M.v i + ∫ s in (0:ℝ)..S, M.g s * (Phi φ s S * Wt φ a b s)

/-- `q = Σ_i k_i v_i + ∫_0^S σ² W̃²` (47.3). -/
noncomputable def qtil (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (S a b : ℝ) : ℝ :=
  ∑ i, k S a b (M.T i) * M.v i + ∫ s in (0:ℝ)..S, M.g s * Wt φ a b s ^ 2

/-- `m = exp(A + p̃ − z̃)` (47.3). -/
noncomputable def mtil (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (S a b : ℝ) : ℝ :=
  Real.exp (Aint M a b + ptil M φ a b - ztil M φ S a b)

/-- The call `C(S, a, b, K) = E_Q[B_S⁻¹ (G_S − K)⁺]`. -/
noncomputable def call [MeasurableSpace Ω] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (Q : Measure Ω)
    (S a b K : ℝ) : ℝ :=
  ∫ ω, disc M φ S ω * max (G M φ Q S a b ω - K) 0 ∂Q

/-- `Q^S`, with density `B_S⁻¹/P(0, S)`. -/
noncomputable def QS [MeasurableSpace Ω] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (Q : Measure Ω)
    (S : ℝ) : Measure Ω :=
  Q.withDensity fun ω => ENNReal.ofReal (disc M φ S ω / P0 M S)

/-- The window weight `β(s) = δ⁻¹ ∫_a^b φ(s, T) dT`. -/
noncomputable def betaW (φ : ℝ → ℝ → ℝ) (a b s : ℝ) : ℝ := (∫ x in a..b, φ s x) / (b - a)

def pricingStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : ShapeModel Ω N) (φ : ℝ → ℝ → ℝ) (H : ℝ), ShapeGaussLaw M φ Q H →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
    Integrable (fun ω => Real.exp (∫ u in a..b, rate M φ u ω)) Q ∧
    (∀ t, Integrable (G M φ Q t a b) Q) ∧
    (∀ s t, s ≤ t → Q[G M φ Q t a b | M.F s] =ᵐ[Q] G M φ Q s a b) ∧
    (G M φ Q 0 a b =ᵐ[Q] fun _ => Real.exp (Aint M a b + ptil M φ a b)) ∧
    ∀ S, 0 ≤ S → S ≤ H →
      ∫ ω, disc M φ S ω ∂Q = P0 M S ∧ IsProbabilityMeasure (QS M φ Q S) ∧
      HasLaw (fun ω => Real.log (G M φ Q S a b ω))
        (gaussianReal (Real.log (mtil M φ S a b) - qtil M φ S a b / 2) (qtil M φ S a b).toNNReal)
        (QS M φ Q S) ∧
      ∀ K, call M φ Q S a b K = P0 M S * C0177 (mtil M φ S a b) (qtil M φ S a b).toNNReal K

def accumulationStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : ShapeModel Ω N)
  (φ : ℝ → ℝ → ℝ) (S a b : ℝ), (∀ i, 0 < M.T i) → 0 ≤ S → S < a → a < b →
    qtil M φ S a b = (b - a) ^ 2 * (∑ i, (if M.T i ≤ S then M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * betaW φ a b s ^ 2) ∧
    ztil M φ S a b = (b - a) * (∑ i, (if M.T i ≤ S then (S - M.T i) * M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * (Phi φ s S * betaW φ a b s)) ∧
    ztil M φ S a b = (Aint M a b + ptil M φ a b) - Real.log (mtil M φ S a b)

def statement : Prop := pricingStatement ∧ accumulationStatement

end Standalone.MaturityShapePricing

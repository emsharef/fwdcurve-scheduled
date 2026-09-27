import Standalone.JumpShapeCondB

/-! # Claim 045 (d): the pre-meeting forward rate (5.1)

`Ft ≤ G ≤ m₀` are `F_t` and `F_{T_n−}`. `r` is `r_t` (`Ft`-measurable), `J` the short-rate jump and
`fT T ω = f(t, T)(ω)` the initial curve, `B ⊗ Ft`-measurable and integrable on `[T_n, T_n + τ]` for
`τ ∈ [0, L)`. In the model with only the jump at `T_n` (45.11) the curve jumps at `T_n` by
`ξ(T) = r_t + J − f(t, T)`, which is (45.1) with `X = J` and `h(u) = r_t − f(t, T_n + u)`.
`HypD` is (H) for this jump: `E[exp(−∫_{T_n}^T ξ) | F_{T_n−}] = 1` for `T ∈ [T_n, T_n + L)`.
`κ` and `κt` are regular conditional distributions of `J` given `G` and given `Ft` (`RegCond`).
`E_t[g(J)] = ∫ g dκt`.

* `forwardStatement` is (45.12): (H) holds iff, almost surely, `E_{T_n−}[e^{−τJ}] < ∞` on `[0, L)` and
  `f(t, T_n + τ) = r_t + E_{T_n−}[J e^{−τJ}] / E_{T_n−}[e^{−τJ}]` for almost every `τ ∈ (0, L)`.
* `lawStatement` is (i): under (H) the conditional laws of `J` given `F_{T_n−}` and given `F_t`
  agree almost surely, so (45.12) holds with `E_t`: this is (5.1) as printed.
* `rightStatement` is (ii) on `(0, L)`: if `f(t, ·)` is right-continuous there, (5.1) holds at
  every `τ ∈ (0, L)`, almost surely.
* `bondStatement` is (iii): if `f(t, T) = r_t` on `[t, T_n)`, then
  `exp(−∫_t^T f(t, s) ds) = e^{−r_t (T − t)} E_t[e^{−(T − T_n) J}]` for `T ∈ [T_n, T_n + L)`, a.s.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeForward
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond

/-- (H) for the jump of the model at `T_n`. -/
def HypD {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (G : MeasurableSpace Ω)
    (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ τ, InI L τ → ∀ D : Set Ω, MeasurableSet[G] D →
    ∫⁻ ω in D, ENNReal.ofReal (Real.exp (-∫ T in Tn..Tn + τ, (r ω + J ω - fT T ω))) ∂P = P D

/-- The hypotheses of (d). -/
def SettingD {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (Ft G : MeasurableSpace Ω)
    (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞) : Prop :=
  IsProbabilityMeasure P ∧ Ft ≤ G ∧ G ≤ m₀ ∧ Measurable[Ft] r ∧ Measurable[m₀] J ∧
  @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ Ft) _ (Function.uncurry fT) ∧
  ∀ ω τ, InI L τ → IntervalIntegrable (fun T => fT T ω) volume Tn (Tn + τ)

def forwardStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (Ft G : MeasurableSpace Ω) (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _), SettingD P Ft G r J fT Tn L → @IsMarkovKernel Ω ℝ G _ κ →
  RegCond P G J κ →
  (HypD P G r J fT Tn L ↔ ∀ᵐ ω ∂P, LapFinite (κ ω) L ∧
    ∀ᵐ τ ∂volume, InIo L τ → fT (Tn + τ) ω = r ω + tiltMean (κ ω) τ)

def lawStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (Ft G : MeasurableSpace Ω) (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _) (κt : @Kernel Ω ℝ Ft _), 0 < L → SettingD P Ft G r J fT Tn L →
  @IsMarkovKernel Ω ℝ G _ κ → RegCond P G J κ → @IsMarkovKernel Ω ℝ Ft _ κt →
  RegCond P Ft J κt → HypD P G r J fT Tn L →
  (∀ᵐ ω ∂P, κt ω = κ ω) ∧ ∀ᵐ ω ∂P, LapFinite (κt ω) L ∧
    ∀ᵐ τ ∂volume, InIo L τ → fT (Tn + τ) ω = r ω + tiltMean (κt ω) τ

def rightStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (Ft G : MeasurableSpace Ω) (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _), SettingD P Ft G r J fT Tn L → @IsMarkovKernel Ω ℝ G _ κ →
  RegCond P G J κ → HypD P G r J fT Tn L →
  (∀ ω τ, InIo L τ → ContinuousWithinAt (fun T => fT T ω) (Ici (Tn + τ)) (Tn + τ)) →
  ∀ᵐ ω ∂P, ∀ τ, InIo L τ → fT (Tn + τ) ω = r ω + tiltMean (κ ω) τ

def bondStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (Ft G : MeasurableSpace Ω) (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (t Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _) (κt : @Kernel Ω ℝ Ft _), 0 < L → t < Tn → SettingD P Ft G r J fT Tn L →
  (∀ ω T, T ∈ Ico t Tn → fT T ω = r ω) →
  @IsMarkovKernel Ω ℝ G _ κ → RegCond P G J κ → @IsMarkovKernel Ω ℝ Ft _ κt →
  RegCond P Ft J κt → HypD P G r J fT Tn L →
  ∀ᵐ ω ∂P, ∀ τ, InI L τ → Real.exp (-∫ T in t..Tn + τ, fT T ω) =
    Real.exp (-r ω * (Tn + τ - t)) * Mlap (κt ω) τ

def statement : Prop := forwardStatement ∧ lawStatement ∧ rightStatement ∧ bondStatement

end Standalone.JumpShapeForward

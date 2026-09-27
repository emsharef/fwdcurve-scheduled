import Standalone.JumpShapeCondB

/-! # Claim 045 (d′): without a flat short rate

The initial curve `fT T ω = f(t, T)(ω)` is general, and the curve after `T_n` is
`f(T_n, T) = f(t, T) + X + h(T − T_n)`, frozen off `T_n`, so `r_T = f(T_n, T)` for `T ≥ T_n`.
The setting of (a) holds for `X` and `h` with `G = F_{T_n−}`; `fT` is `B ⊗ G`-measurable and
integrable on `[T_n, T_n + τ]` for `τ ∈ [0, L)`.

`tiltRate` is `Ê_τ[r_T]` at `T = T_n + τ`: the conditional expectation of `r_T` given `G` under the
tilt by `exp(−∫_{T_n}^T r_s ds)`, computed from the regular conditional distribution `κ` of `X`.

* `forwardMeasureStatement` is (45.13): under (H), for almost every `ω` and almost every
  `τ ∈ (0, L)`, `f(t, T_n + τ) = Ê_τ[r_{T_n + τ}]`.
* `onlyCaseStatement` is "(5.1) holds only for a flat short rate before and after `T_n`". Let
  `f(t, ·)` have the left limit `r_{T_n−}` at `T_n`, let `f(t, ·)` be right-continuous on
  `[T_n, T_n + L)` and `h(ω, ·)` right-continuous on `[0, L)`. With `J = r_{T_n} − r_{T_n−}`, whose
  conditional law given `G` is `κ(ω, ·)` shifted by `c = f(t, T_n) + h(0) − r_{T_n−}`, under (H),
  almost surely: (5.1) holds at every `τ ∈ (0, L)` iff `r_{T_n−} = r_t` and `r` is constant on
  `[T_n, T_n + L)`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.JumpShapeGeneral
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeCondB

/-- `Ê_τ[r_{T_n + τ}]`: `r_T = f(t, T) + x + h(τ)` weighted by `exp(−∫_{T_n}^T r_s ds)`. -/
noncomputable def tiltRate (ν : Measure ℝ) (fT : ℝ → ℝ) (h : ℝ → ℝ) (Tn τ : ℝ) : ℝ :=
  (∫ x, (fT (Tn + τ) + x + h τ) *
      Real.exp (-∫ u in (0:ℝ)..τ, (fT (Tn + u) + x + h u)) ∂ν) /
    ∫ x, Real.exp (-∫ u in (0:ℝ)..τ, (fT (Tn + u) + x + h u)) ∂ν

def forwardMeasureStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _), Setting P G X h L κ →
  (∀ ω τ, InI L τ → IntervalIntegrable (fun T => fT T ω) volume Tn (Tn + τ)) →
  HypH P G X h L →
  ∀ᵐ ω ∂P, ∀ᵐ τ ∂volume, InIo L τ →
    fT (Tn + τ) ω = tiltRate (κ ω) (fun T => fT T ω) (fun u => h u ω) Tn τ

def onlyCaseStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (G : MeasurableSpace Ω) (X : Ω → ℝ) (h : ℝ → Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _) (rt rl : Ω → ℝ), 0 < L → Setting P G X h L κ → HypH P G X h L →
  (∀ ω, Tendsto (fun T => fT T ω) (𝓝[<] Tn) (𝓝 (rl ω))) →
  (∀ ω τ, InI L τ → ContinuousWithinAt (fun T => fT T ω) (Ici (Tn + τ)) (Tn + τ)) →
  (∀ ω τ, InI L τ → ContinuousWithinAt (fun u => h u ω) (Ici τ) τ) →
  ∀ᵐ ω ∂P,
    ((∀ τ, InIo L τ → fT (Tn + τ) ω = rt ω +
        tiltMean ((κ ω).map fun x => x + (fT Tn ω + h 0 ω - rl ω)) τ) ↔
      (rl ω = rt ω ∧ ∀ τ, InI L τ → fT (Tn + τ) ω + X ω + h τ ω = fT Tn ω + X ω + h 0 ω))

def statement : Prop := forwardMeasureStatement ∧ onlyCaseStatement

end Standalone.JumpShapeGeneral

import Standalone.JumpShapeForward

/-! # Claim 045 (45.7): the shape at `τ = 0`

* `originStatement` is (45.7) at one `ω`: if `M < ∞` on `[0, L)`, `H = K` there (45.4), and `h` is
  right-continuous at `0`, then `∫ |x| ν(dx) < ∞` and `h(0) = −∫ x ν(dx)`.
* `forwardOriginStatement` is (d)(ii) at `τ = 0`: under (H), if `f(t, ·)` is right-continuous at
  `T_n`, then almost surely `E_t|J| < ∞` and `f(t, T_n) = r_t + E_t[J]`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.JumpShapeOrigin
open Standalone.JumpShapeKernel Standalone.JumpShapeProfile Standalone.JumpShapeCond
open Standalone.JumpShapeForward

def originStatement : Prop := ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ≥0∞) (h : ℝ → ℝ),
  0 < L → LapFinite ν L → LocInt h L → ShapeEq ν h L → ContinuousWithinAt h (Ici 0) 0 →
  Integrable (fun x => x) ν ∧ h 0 = -∫ x, x ∂ν

def forwardOriginStatement : Prop := ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (P : Measure Ω)
  (Ft G : MeasurableSpace Ω) (r J : Ω → ℝ) (fT : ℝ → Ω → ℝ) (Tn : ℝ) (L : ℝ≥0∞)
  (κ : @Kernel Ω ℝ G _) (κt : @Kernel Ω ℝ Ft _), 0 < L → SettingD P Ft G r J fT Tn L →
  @IsMarkovKernel Ω ℝ G _ κ → RegCond P G J κ → @IsMarkovKernel Ω ℝ Ft _ κt →
  RegCond P Ft J κt → HypD P G r J fT Tn L →
  (∀ ω, ContinuousWithinAt (fun T => fT T ω) (Ici Tn) Tn) →
  ∀ᵐ ω ∂P, Integrable (fun x => x) (κt ω) ∧ fT Tn ω = r ω + ∫ x, x ∂(κt ω)

def statement : Prop := originStatement ∧ forwardOriginStatement

end Standalone.JumpShapeOrigin

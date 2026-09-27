import Standalone.SeparableMeetingMarkovCoefficients
import Standalone.SeparableMeetingAssembly

/-! # Claim 028: the realization map (28.6)

`state028 z M A` is the state (28.3) with scale block `z` and coefficient
blocks `M`, `A`; `Lambda028 f0 g G x T` is the map (28.6), with `f0` the initial
curve and `G j k` the primitive of `g j k`. It does not depend on time, and it
is affine and continuous in the state.

`curveStatement` is Claim 026's (26.4) with the curve factor `j` driven by the
driver `drv j`: on one event, for all times, the drift integral plus the driver
integrals at a fixed maturity equal `Lambda028` at the state built from the
coefficients `M`, `A` of (26.3), minus the initial curve. So `f(t,T)` is
`Lambda028` of the state, simultaneously in time. The state dimension is
`p + 2 d (N+1)` (`dimStatement`).
-/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingAssembly Standalone.SeparableMeetingMarkovCoefficients
namespace Standalone.SeparableMeetingMarkovRealization

/-- The state (28.3) from its three blocks. -/
def state028 {p d N : ℕ} (z : Fin p → ℝ) (M A : Fin d → Fin (N+1) → ℝ) :
    Fin (dim028 p d N) → ℝ := fun i =>
  Sum.elim z (Sum.elim (fun jk : Fin d × Fin (N+1) => M jk.1 jk.2)
    (fun jk : Fin d × Fin (N+1) => A jk.1 jk.2)) ((equiv028 p d N).symm i)

/-- The map (28.6); `x` is a state of dimension `p + 2 d (N+1)`. -/
def Lambda028 {p d N : ℕ} (f0 : ℝ → ℝ) (g G : Fin d → Fin (N+1) → ℝ → ℝ)
    (x : Fin (dim028 p d N) → ℝ) (T : ℝ) : ℝ :=
  f0 T + ∑ j, ∑ k, g j k T * (x (equiv028 p d N (Sum.inr (Sum.inl (j, k)))) +
    G j k T * x (equiv028 p d N (Sum.inr (Sum.inr (j, k)))))

def dimStatement : Prop := ∀ p d N : ℕ,
  Fintype.card (Index028 p d N) = dim028 p d N ∧ dim028 p d N = p + 2 * d * (N+1)

/-- `Lambda028` reads the coefficient blocks and is continuous in the state. -/
def lambdaStatement : Prop := ∀ (p d N : ℕ) (f0 : ℝ → ℝ) (g G : Fin d → Fin (N+1) → ℝ → ℝ),
  (∀ (z : Fin p → ℝ) (M A : Fin d → Fin (N+1) → ℝ) (T : ℝ),
    Lambda028 f0 g G (state028 z M A) T =
      f0 T + ∑ j, ∑ k, (g j k T * M j k + g j k T * G j k T * A j k)) ∧
  ∀ T : ℝ, Continuous fun x : Fin (dim028 p d N) → ℝ => Lambda028 f0 g G x T

/-- (c): the curve is `Lambda028` of the state, for each maturity, simultaneously
in time. -/
def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0), Monotone Td →
  ∀ (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ) (f0 : ℝ → ℝ)
    (Z : ℝ≥0 → Ω → Fin p → ℝ),
  (∀ j, U4 S.ℱ S.μ (chi j)) → (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  ∀ T : ℝ,
  (∀ j, U4 S.ℱ S.μ (sigma026 Td chi g j T)) ∧
  ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    f0 T + (∫ s in (0:ℝ)..t, alpha026 Td chi g T s ω) +
      ∑ j, S.I (drv j) (sigma026 Td chi g j T) t ω =
    Lambda028 f0 g (fun j k => G026 (g j k))
      (state028 (Z t ω)
        (fun j k => M0262 S (drv j) (chi j) (lo026 Td k) (hi026 Td k) (G026 (g j k)) t ω)
        (fun j k => D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω)) T

def statement : Prop := dimStatement ∧ lambdaStatement ∧ curveStatement

end Standalone.SeparableMeetingMarkovRealization

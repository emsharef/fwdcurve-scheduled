import Standalone.SeparableMeetingMarkovRealization
import Standalone.SeparableMeetingScaleVersion

/-! # Claim 028 (a): the frozen state solves the switching SDE

The time functions of (28.4) are fixed here: the meeting indicator `ind028`
of the predictable interval `(T_k, T_{k+1}]` (Claim 026's representative of
`I_k`; the endpoints are a time-null set), the horizon indicator `eH028` of
`[0, H]`, and `G028`, the primitive `G_{j,k}` at `t min H`. The last date
`Td (N+1)` is the horizon `H`.

The scales are `chi_j(t) = psi_j(t, Z_t)` (28.2) for a scale state `Z` with every
path continuous that solves (28.1) in the sense of `Solution6`, which (a0)
supplies. `XH028` is the frozen state `X^H` of (28.3): the scale block `Z` at
`t min H`, and the coefficients `M`, `A` of (26.3), which are constant after `H`
already. `solutionStatement` is the `Solution6` assertion of (a), with the
deterministic initial value `(z0, 0, 0)`, and `coefficientsStatement` the
`Coefficients6` one for these time functions.
-/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.BoundedVarianceMartingale Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingAssembly Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization
namespace Standalone.SeparableMeetingMarkovSolution

noncomputable def ind028 {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (k : Fin (N+1)) (s : ℝ≥0) : ℝ :=
  if lo026 Td k < s ∧ s ≤ hi026 Td k then 1 else 0

noncomputable def eH028 (Hor : ℝ≥0) (s : ℝ≥0) : ℝ := if s ≤ Hor then 1 else 0

noncomputable def G028 {d N : ℕ} (g : Fin d → Fin (N+1) → ℝ → ℝ) (Hor : ℝ≥0)
    (j : Fin d) (k : Fin (N+1)) (s : ℝ≥0) : ℝ :=
  G026 (g j k) ((min s Hor : ℝ≥0) : ℝ)

/-- The scale (28.2). -/
def chi028 {Ω : Type*} {p d : ℕ} (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ)
    (Z : ℝ≥0 → Ω → Fin p → ℝ) (j : Fin d) : ℝ≥0 → Ω → ℝ :=
  fun s ω => psi j (s, Z s ω)

/-- The frozen state `X^H` of (28.3). -/
noncomputable def XH028 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) {p d N : ℕ}
    (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (Z : ℝ≥0 → Ω → Fin p → ℝ) : ℝ≥0 → Ω → Fin (dim028 p d N) → ℝ := fun t ω =>
  state028 (Z (min t Hor) ω)
    (fun j k => M0262 S (drv j) (chi028 psi Z j) (lo026 Td k) (hi026 Td k) (G026 (g j k)) t ω)
    (fun j k => D026 (H026 (chi028 psi Z j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω)

/-- `Coefficients6` for (28.4) with these time functions. -/
def coefficientsStatement : Prop := ∀ (p d N m : ℕ) (Td : Fin (N+2) → ℝ≥0) (Hor : ℝ≥0)
  (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
  (drv : Fin d → Fin m) (Kψ Lψ : ℝ),
  Coefficients6 beta Sigma → (∀ j, Continuous (psi j)) → (∀ j q, |psi j q| ≤ Kψ) →
  (∀ j t z z', |psi j (t,z) - psi j (t,z')| ≤ Lψ * ‖z - z'‖) →
  (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  Coefficients6 (drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor))
    (diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv)

/-- (a): the frozen state is a `Solution6` solution of (28.4) from `(z0, 0, 0)`. -/
def solutionStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  Predictability S.ℱ → ∀ (p d N : ℕ) (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0)
  (Hor : ℝ≥0), Monotone Td → Td (Fin.last (N+1)) = Hor →
  ∀ (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin S.m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ) (Kψ Lψ : ℝ)
    (z0 : Fin p → ℝ) (Z : ℝ≥0 → Ω → Fin p → ℝ),
  Coefficients6 beta Sigma → (∀ j, Continuous (psi j)) → (∀ j q, |psi j q| ≤ Kψ) →
  (∀ j t z z', |psi j (t,z) - psi j (t,z')| ≤ Lψ * ‖z - z'‖) →
  (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  (∀ ω, Continuous fun t => Z t ω) → Solution6 S beta Sigma (fun _ => z0) Z →
  Solution6 S (drift028 beta psi (ind028 Td) (eH028 Hor) (G028 g Hor))
    (diffusion028 Sigma psi (ind028 Td) (eH028 Hor) drv)
    (fun _ => state028 z0 0 0) (XH028 S drv Td Hor psi g Z)

def statement : Prop := coefficientsStatement ∧ solutionStatement

end Standalone.SeparableMeetingMarkovSolution

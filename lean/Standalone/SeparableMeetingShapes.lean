import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Claim 026: deterministic identities

This target proves the two-shape algebra, primitive splitting, integrated HJM
identity and realized-variance integral equations. It allows signed and zero
loadings and arbitrary interval-integrable maturity functions. The stochastic
construction from the supplied Itô calculus is not part of this target.
-/

open MeasureTheory
open scoped BigOperators
namespace Standalone.SeparableMeetingShapes

noncomputable def G026 (g : ℝ → ℝ) (T : ℝ) : ℝ := ∫ u in (0:ℝ)..T, g u
noncomputable def A026 (q : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, q s
noncomputable def M026 (J : ℝ → ℝ) (q G : ℝ → ℝ) (t : ℝ) : ℝ :=
  J t - ∫ s in (0:ℝ)..t, q s * G s
noncomputable def C026 {n : ℕ} (a B M A : Fin n → ℝ) : ℝ :=
  ∑ k, a k * (M k + B k * A k)
noncomputable def V026 {n : ℕ} (a A : Fin n → ℝ) : ℝ := ∑ k, a k ^ 2 * A k

/-- (26.8), without any sign or continuity assumption on g. -/
def driftStatement : Prop := ∀ (g : ℝ → ℝ) (t T : ℝ),
  IntervalIntegrable g volume t T →
  (∫ u in t..T, g u * (∫ v in t..u, g v)) = (∫ u in t..T, g u)^2 / 2

/-- The independent-driver sum of squares in AX-01, for fixed time. -/
def hjmStatement : Prop := ∀ (d : ℕ) (g : Fin d → ℝ → ℝ) (chi : Fin d → ℝ)
  (t T : ℝ), (∀ j, IntervalIntegrable (g j) volume t T) →
  (∫ u in t..T, ∑ j, chi j ^ 2 * g j u * (∫ v in t..u, g j v)) =
    (1/2:ℝ) * ∑ j, (∫ u in t..T, chi j * g j u)^2

/-- (26.10) retains the complete primitive at the meeting. -/
def primitiveStatement : Prop := ∀ (g phi : ℝ → ℝ) (a b T : ℝ),
  IntervalIntegrable g volume 0 b → IntervalIntegrable g volume b T →
  (∀ u ∈ Set.uIcc b T, g u = a * phi u) →
  G026 g T = G026 g b + a * (∫ u in b..T, phi u)

/-- (26.5)--(26.6), one maturity interval and all time-interval coefficients. -/
def shapeStatement : Prop := ∀ (d n : ℕ) (a B M A : Fin d → Fin n → ℝ)
  (phi Phi : Fin d → ℝ) (f0 : ℝ),
  f0 + ∑ j, ∑ k, ((a j k * phi j) * M j k +
      (a j k * phi j) * (B j k + a j k * Phi j) * A j k) =
    f0 + ∑ j, phi j * (C026 (a j) (B j) (M j) (A j) + Phi j * V026 (a j) (A j))

/-- (26.9) and the integral form of (26.7). q is the masked squared scale;
J is the corresponding driver integral, treated here as a supplied function. -/
def coefficientStatement : Prop := ∀ (n : ℕ) (a B : Fin n → ℝ)
  (J q G : Fin n → ℝ → ℝ) (t : ℝ),
  (∀ k, IntervalIntegrable (q k) volume 0 t) →
  (∀ k, IntervalIntegrable (fun s => q k s * G k s) volume 0 t) →
  C026 a B (fun k => M026 (J k) (q k) (G k) t) (fun k => A026 (q k) t) =
    (∑ k, a k * J k t) +
      ∫ s in (0:ℝ)..t, ∑ k, a k * q k s * (B k - G k s) ∧
  V026 a (fun k => A026 (q k) t) =
    ∫ s in (0:ℝ)..t, ∑ k, a k ^ 2 * q k s

/-- Accumulated nonnegative integrable densities are continuous, nondecreasing,
and of bounded variation on the horizon. The derivative is asserted a.e. only. -/
def varianceStatement : Prop := ∀ (n : ℕ) (a : Fin n → ℝ) (q : Fin n → ℝ → ℝ)
  (H : ℝ), 0 ≤ H → (∀ k, IntervalIntegrable (q k) volume 0 H) →
  (∀ k s, 0 ≤ q k s) →
  let V := fun t => V026 a (fun k => A026 (q k) t)
  V 0 = 0 ∧ (∀ t, 0 ≤ t → 0 ≤ V t) ∧
  MonotoneOn V (Set.Icc 0 H) ∧ ContinuousOn V (Set.Icc 0 H) ∧
  BoundedVariationOn V (Set.Icc 0 H) ∧
  (∀ᵐ t ∂volume, t ∈ Set.Icc 0 H →
    HasDerivAt V (∑ k, a k ^ 2 * q k t) t)

/-- Step specialization: local level and slope, including the initial affine curve. -/
def stepStatement : Prop := ∀ (d : ℕ) (C V : Fin d → ℝ) (level slope b T : ℝ),
  level + slope * (T-b) + (∑ j, (C j + (∫ _u in b..T, (1:ℝ)) * V j)) =
    (level + ∑ j, C j) + (slope + ∑ j, V j) * (T-b)

def statement : Prop := driftStatement ∧ hjmStatement ∧ primitiveStatement ∧
  shapeStatement ∧ coefficientStatement ∧ varianceStatement ∧ stepStatement

end Standalone.SeparableMeetingShapes

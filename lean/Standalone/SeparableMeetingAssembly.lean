import Standalone.SeparableMeetingShapes
import Standalone.SeparableMeetingRepresentation

/-! # Claim 026: assembly of (26.2), (26.4) and (26.6)

Time interval `k` is `(Td k, Td (k+1)]`, the predictable representative of
`I_k`; the dates need only be monotone, and the last date is the horizon. The
coefficients (26.2) are written as sums over the masked scales `H026`;
`pointwiseStatement` shows they equal `chi_j(s) g_{j,k}(T)` and the displayed
drift on the `k`-th interval. The loadings `g j k` are any locally integrable
maturity functions; `loadingStatement` shows the (26.1) loadings, built from
measurable maturity intervals and continuous shapes, are such functions.

`curveStatement` is (26.4) summed over all drivers and time intervals, for one
fixed maturity, on one event for all times: the drift integral plus the driver
integrals equal the finite combination of the `2 d (N+1)` coefficients `M` and
`A`, which do not depend on the maturity. The forward curve is the initial
curve plus the left side, so this is the HJM representation. No stochastic
Fubini theorem, expected-energy bound or new upstream field is used.
-/
open MeasureTheory ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open scoped NNReal
namespace Standalone.SeparableMeetingAssembly

def lo026 {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (k : Fin (N+1)) : ℝ≥0 := Td k.castSucc
def hi026 {N : ℕ} (Td : Fin (N+2) → ℝ≥0) (k : Fin (N+1)) : ℝ≥0 := Td k.succ

/-- `sigma_j(s,T)` of (26.2) as a sum over the masked scales. -/
noncomputable def sigma026 {Ω : Type*} {d N : ℕ} (Td : Fin (N+2) → ℝ≥0)
    (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (j : Fin d) (T : ℝ) : ℝ≥0 → Ω → ℝ := fun s ω =>
  ∑ k, g j k T * H026 (chi j) (lo026 Td k) (hi026 Td k) s ω

/-- `alpha(s,T)` of (26.2) as a sum over the masked scales. -/
noncomputable def alpha026 {Ω : Type*} {d N : ℕ} (Td : Fin (N+2) → ℝ≥0)
    (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (T s : ℝ) (ω : Ω) : ℝ :=
  ∑ j, ∑ k, g j k T * H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2 *
    (G026 (g j k) T - G026 (g j k) s)

/-- On the `k`-th time interval the sums are the displayed (26.2). -/
def pointwiseStatement : Prop := ∀ (Ω : Type) (d N : ℕ) (Td : Fin (N+2) → ℝ≥0),
  Monotone Td → ∀ (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
  (k : Fin (N+1)) (s : ℝ≥0), lo026 Td k < s → s ≤ hi026 Td k → ∀ (T : ℝ) (ω : Ω),
  (∀ j, sigma026 Td chi g j T s ω = chi j s ω * g j k T) ∧
  alpha026 Td chi g T s ω =
    ∑ j, chi j s ω ^ 2 * g j k T * (G026 (g j k) T - G026 (g j k) s)

/-- AX-01 for (26.2), at every time and maturity and on every path. -/
def driftStatement : Prop := ∀ (Ω : Type) (d N : ℕ) (Td : Fin (N+2) → ℝ≥0),
  Monotone Td → ∀ (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ),
  (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  ∀ (s : ℝ≥0) (T : ℝ) (ω : Ω),
  (∫ u in (s:ℝ)..T, alpha026 Td chi g u s ω) =
    (1/2:ℝ) * ∑ j, (∫ u in (s:ℝ)..T, sigma026 Td chi g j u s ω) ^ 2

/-- (26.4) for one fixed maturity, simultaneously in time. -/
def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (N : ℕ) (Td : Fin (N+2) → ℝ≥0), Monotone Td →
  ∀ (chi : Fin S.m → ℝ≥0 → Ω → ℝ) (g : Fin S.m → Fin (N+1) → ℝ → ℝ),
  (∀ j, U4 S.ℱ S.μ (chi j)) → (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  ∀ T : ℝ,
  (∀ j, U4 S.ℱ S.μ (sigma026 Td chi g j T)) ∧
  ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    (∫ s in (0:ℝ)..t, alpha026 Td chi g T s ω) + ∑ j, S.I j (sigma026 Td chi g j T) t ω =
    ∑ j, ∑ k,
      (g j k T * M0262 S j (chi j) (lo026 Td k) (hi026 Td k) (G026 (g j k)) t ω +
        g j k T * G026 (g j k) T *
          D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω)

/-- The ordinary coefficients of (26.3) vanish through the interval's start and
are constant after its end, like `M0262` in `coefficientStatement`. -/
def freezeStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0),
  lo ≤ hi → U4 S.ℱ S.μ chi → ∀ (G : ℝ → ℝ), Continuous G →
  ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    (t ≤ lo → D026 (H026 chi lo hi) G t ω = 0) ∧
    (hi ≤ t → D026 (H026 chi lo hi) G t ω = D026 (H026 chi lo hi) G hi ω)

/-- (26.4) to (26.6): on a maturity interval starting at `b` where every loading
is `a j k * phi j`, the combination in (26.4) is the two-shape form, with the
earlier-interval primitive `G026 (g j k) b` retained in `C026`. -/
def shapeCurveStatement : Prop := ∀ (d n : ℕ) (g : Fin d → Fin n → ℝ → ℝ)
  (phi : Fin d → ℝ → ℝ) (a : Fin d → Fin n → ℝ) (b T : ℝ) (M A : Fin d → Fin n → ℝ),
  (∀ j k x y, IntervalIntegrable (g j k) volume x y) →
  (∀ j k, ∀ u ∈ Set.uIcc b T, g j k u = a j k * phi j u) →
  ∑ j, ∑ k, (g j k T * M j k + g j k T * G026 (g j k) T * A j k) =
    ∑ j, phi j T * (C026 (a j) (fun k => G026 (g j k) b) (M j) (A j) +
      (∫ u in b..T, phi j u) * V026 (a j) (A j))

/-- The loadings of (26.1): locally integrable, and `a m * phi` on the `m`-th
maturity interval when the intervals are disjoint. -/
def loadingStatement : Prop := ∀ (n : ℕ) (I : Fin n → Set ℝ) (a : Fin n → ℝ)
  (phi : ℝ → ℝ), (∀ m, MeasurableSet (I m)) → Continuous phi →
  (∀ x y, IntervalIntegrable
    (fun u => ∑ m, (I m).indicator (fun u => a m * phi u) u) volume x y) ∧
  (Pairwise (fun m m' => Disjoint (I m) (I m')) → ∀ m, ∀ u ∈ I m,
    ∑ m', (I m').indicator (fun u => a m' * phi u) u = a m * phi u)

def statement : Prop := pointwiseStatement ∧ driftStatement ∧ curveStatement ∧
  freezeStatement ∧ shapeCurveStatement ∧ loadingStatement

end Standalone.SeparableMeetingAssembly

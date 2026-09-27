import Standalone.MaturityShapeCalendar

/-! # Claim 047 (d4): the partition `𝒫_8` under shape (S1)

Shape (S1), `phiExp κ = e^{−κ(T − s)}`, `κ > 0`, on the calendar (`MaturityShapeCalendar`), with
`g(κ) = ((1 − e^{−κδ})/(κδ))²`, `δ = 91/360`, and, with exponents in days,
`F(x) = e^{−122x} − e^{−364x} − e^{−10x} + e^{−182x}`.

* `diagonalStatement`: the six same-window diagonal entries of `Λ̃_E(𝒫_8)` are positive, and the
  two window-change entries (rows 5 and 7) both equal `(g(κ)/(2κ)) F(κ/360)`.
* `rootStatement`: `F` has exactly one positive zero `x*`, and `0.0023 < x* < 0.0024`.
* `identifyStatement`: with `κ* = 360 x* ∈ (0.828, 0.864)`, `𝒫_8` identifies under (S1) iff
  `κ ≠ κ*`. These are exact rank statements, not statements about practical identification.
* `windowStatement`: `β_n² = g(κ) e^{−2κ(a_n − s)}`, so a later window has the smaller weight
  (the sign remark of (c)).
-/

namespace Standalone.MaturityShapeS1
open Standalone.MaturityShapeRank Standalone.DiffusionMeetingCalendar
  Standalone.MaturityShapeCalendar

/-- `F(x) = e^{−122x} − e^{−364x} − e^{−10x} + e^{−182x}`. -/
noncomputable def Fexp (x : ℝ) : ℝ :=
  Real.exp (-122 * x) - Real.exp (-364 * x) - Real.exp (-10 * x) + Real.exp (-182 * x)

/-- `g(κ) = ((1 − e^{−κδ})/(κδ))²`, `δ = 91/360`. -/
noncomputable def gK (κ : ℝ) : ℝ := ((1 - Real.exp (-κ * (91 / 360))) / (κ * (91 / 360))) ^ 2

def diagonalStatement : Prop := ∀ κ : ℝ, 0 < κ →
  (∀ k : Fin 8, k ≠ 4 → k ≠ 6 → 0 < lamE8 (phiExp κ) k k) ∧
  lamE8 (phiExp κ) 4 4 = gK κ / (2 * κ) * Fexp (κ / 360) ∧
  lamE8 (phiExp κ) 6 6 = gK κ / (2 * κ) * Fexp (κ / 360)

def rootStatement : Prop :=
  ∃ x, (0 < x ∧ Fexp x = 0) ∧ (∀ y, 0 < y → Fexp y = 0 → y = x) ∧ 0.0023 < x ∧ x < 0.0024

def identifyStatement : Prop :=
  ∃ κs : ℝ, 0.828 < κs ∧ κs < 0.864 ∧ ∀ κ : ℝ, 0 < κ →
    (Function.Injective (panelD TCal SCal (Dsh (phiExp κ) (cells cEight))).mulVec ↔ κ ≠ κs)

/-- (c)'s remark under (S1): `β_n² = g(κ) e^{−2κ(a_n − s)}`, so a later window has the smaller
weight, and the pre-gap term of `Λ̃` is negative when consecutive expiries change window. -/
def windowStatement : Prop := ∀ κ : ℝ, 0 < κ → ∀ (n : Fin 25) (s : ℝ),
  beta (phiExp κ) n s ^ 2 = gK κ * Real.exp (-2 * κ * (aW n - s)) ∧
  ∀ n' : Fin 25, aW n < aW n' → beta (phiExp κ) n' s ^ 2 < beta (phiExp κ) n s ^ 2

def statement : Prop := diagonalStatement ∧ rootStatement ∧ identifyStatement ∧ windowStatement

end Standalone.MaturityShapeS1

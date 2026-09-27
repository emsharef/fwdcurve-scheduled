import Standalone.MaturityShapeRank
import Standalone.DiffusionMeetingCalendar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Claim 047 (d1)–(d2): the listed calendar with a maturity-dependent shape

Claim 046's calendar (`DiffusionMeetingCalendar`: `TCal`, `SCal`, `cells`, `cOne`, `cEight`, in
ACT/360 years from `t_0`). Row `n ≥ 1` of the panel is expiry `n − 1` of (22.3), on future
`(n − 1)/3`, whose Reference Quarter (22.2) is the window `[a_n, b_n]` (`aW`, `bW`), of 91 days.
For a shape `φ(s, T)`:
* `beta φ n s = β_n(s) = δ⁻¹ ∫_{a_n}^{b_n} φ(s, T) dT`;
* `Dsh φ c n p = D_{n,p} = ∫_{(0, S_n] ∩ [c_p, c_{p+1})} β_n²`, so `D_0 = 0`.
The shapes of the claim are `phiExp κ = e^{−κ(T − s)}` (S1) and `phiNext` (S2): `1` if a meeting
lies in `(s, T]`, i.e. `T ≥ T_{j(s)+1}`, and `0` if none does (`T_{N+1} = +∞`).

* `oneCellStatement`, (d1): with `P = 1`, any diffusion column with `D_0 = 0` and `D_{1,1} ≠ 0`
  identifies the 16 meeting variances and `u_1`. Under (S1), `D_{1,1} > 0` for every `κ > 0`;
  under (S2), `D_{1,1} = 14/360`.
* `triangularStatement`, (d2): for every bounded Borel shape, `Λ̃_E(𝒫_8)`, with its rows (the
  meeting-free gaps `freeIdx`) and cells in date order, is lower triangular; its six same-window
  rows (all but the 5th and 7th) have only the diagonal entry; and `𝒫_8` identifies iff all eight
  diagonal entries are nonzero.
-/

namespace Standalone.MaturityShapeCalendar
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
  Standalone.DiffusionMeetingCalendar Standalone.ListedSr3Identification

/-- The window of panel row `n` (expiry `n − 1`, future `(n − 1)/3`), in days: the Reference
Quarter starting at `quarterStarts`, of 91 days (the last, Mar28, ends 15 Mar 2028, day 805). -/
def aDay (n : Fin 25) : ℕ := quarterStarts.getD ((n.val - 1) / 3) 0
def bDay (n : Fin 25) : ℕ := aDay n + 91

noncomputable def aW (n : Fin 25) : ℝ := yr (aDay n)
noncomputable def bW (n : Fin 25) : ℝ := yr (bDay n)

/-- The window weight `β_n(s) = δ⁻¹ ∫_{a_n}^{b_n} φ(s, T) dT`. -/
noncomputable def beta (φ : ℝ → ℝ → ℝ) (n : Fin 25) (s : ℝ) : ℝ :=
  (∫ T in aW n..bW n, φ s T) / (bW n - aW n)

/-- `D_{n,p} = ∫_{(0, S_n] ∩ [c_p, c_{p+1})} β_n²`. -/
noncomputable def Dsh {P : ℕ} (φ : ℝ → ℝ → ℝ) (c : Fin (P + 1) → ℝ) (n : Fin 25) (p : Fin P) : ℝ :=
  ∫ s in Set.Ioc 0 (SCal n) ∩ Set.Ico (c p.castSucc) (c p.succ), beta φ n s ^ 2

/-- (S1): exponential decay. -/
noncomputable def phiExp (κ : ℝ) (s T : ℝ) : ℝ := Real.exp (-κ * (T - s))

open Classical in
/-- (S2): no loading before the next meeting. -/
noncomputable def phiNext (s T : ℝ) : ℝ := if ∃ i, s < TCal i ∧ TCal i ≤ T then 1 else 0

/-- The meeting-free gaps in date order. -/
def freeIdx : Fin 8 → Fin 24 := ![0, 2, 5, 8, 12, 14, 18, 20]

/-- `Λ̃_E(𝒫_8)`, rows and cells in date order. -/
noncomputable def lamE8 (φ : ℝ → ℝ → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun k p => lamT (Dsh φ (cells cEight)) (freeIdx k) p

def oneCellStatement : Prop :=
  (∀ D : Fin 25 → Fin 1 → ℝ, D 0 = 0 → D 1 0 ≠ 0 → Function.Injective (panelD TCal SCal D).mulVec) ∧
  (∀ κ : ℝ, 0 < κ → 0 < Dsh (phiExp κ) (cells cOne) 1 0) ∧
  Dsh phiNext (cells cOne) 1 0 = 14 / 360

def triangularStatement : Prop := ∀ φ : ℝ → ℝ → ℝ, Measurable (Function.uncurry φ) →
  (∃ C, ∀ s T, |φ s T| ≤ C) →
    (∀ k p : Fin 8, k < p → lamE8 φ k p = 0) ∧
    (∀ k p : Fin 8, k ≠ 4 → k ≠ 6 → p ≠ k → lamE8 φ k p = 0) ∧
    (Function.Injective (panelD TCal SCal (Dsh φ (cells cEight))).mulVec ↔
      ∀ k, lamE8 φ k k ≠ 0)

def statement : Prop := oneCellStatement ∧ triangularStatement

end Standalone.MaturityShapeCalendar

import Standalone.MaturityShapeCalendar

/-! # Claim 047 (d3): the listed calendar under shape (S2), in exact arithmetic

Shape (S2), `phiNext`: no loading before the next meeting. On the calendar (`MaturityShapeCalendar`):

* `betaStatement`: on `(0, S_n]`, `β_n = 1`, except for the 11 Dec 2026 expiry (`n = 12`) from the
  meeting of 9 Dec 2026 on, and the 11 Jun 2027 expiry (`n = 18`) from 9 Jun 2027 on, where
  `β = 49/91` (the next meeting lies inside the window), and the 10 Dec 2027 expiry (`n = 24`) from
  8 Dec 2027 on, where `β = 0` (no meeting after `T_16`).
* `diffusionStatement`: hence, for every partition, `D_{n,p} = λ_p((0, S_n]) − ε_n λ_p(J_n)`, with
  `J_n = [j_n, S_n]` the stretch above and `ε_n = 1 − β²` there (`ε_n = 0` elsewhere); `lam` is
  Claim 046's `λ`.
* `eightStatement`: `Λ̃_E(𝒫_8)` is diagonal, with entries `14, 28, 28, 28, 35 + w, 28, 35 + w, 28`
  (days/360), `w = 2(1 − (49/91)²)`, so `𝒫_8` identifies (rank 24 of 24).
* `cellsStatement`: no identifying partition has more than eight cells; merging the last two
  quarters identifies; the quarterly partition does not, with the pair `v_i = 100`, `u_p = 2500`
  against `v = 86, 72, 74` for the meetings of 15 Sep, 27 Oct and 8 Dec 2027 and `u = 2860` on the
  last cell; and the meeting-date partition does not, with Claim 046's pair (`v = 77, 81`,
  `u = 2860`).
-/

namespace Standalone.MaturityShapeS2
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
  Standalone.DiffusionMeetingCalendar Standalone.MaturityShapeCalendar

/-- The start `j_n` of the stretch where `β_n < 1` (`S_n` if there is none). -/
noncomputable def jd (n : Fin 25) : ℝ :=
  if n = 12 then yr 343 else if n = 18 then yr 525 else if n = 24 then yr 707 else SCal n

/-- `ε_n = 1 − β_n²` on that stretch. -/
noncomputable def eps (n : Fin 25) : ℝ :=
  if n = 12 ∨ n = 18 then 1 - (49 / 91) ^ 2 else if n = 24 then 1 else 0

/-- `w = 2(1 − (49/91)²)`. -/
noncomputable def w : ℝ := 2 * (1 - (49 / 91) ^ 2)

/-- The quarterly pair's second vector under (S2). -/
def quarterAlt2 : Fin 16 ⊕ Fin 8 → ℝ :=
  Sum.elim (fun i => if i = 13 then 86 else if i = 14 then 72 else if i = 15 then 74 else 100)
    (fun p => if p = 7 then 2860 else 2500)

def betaStatement : Prop := ∀ n : Fin 25, n ≠ 0 → ∀ s, 0 < s → s ≤ SCal n →
  beta phiNext n s =
    if (n = 12 ∨ n = 18) ∧ jd n ≤ s then 49 / 91 else if n = 24 ∧ jd n ≤ s then 0 else 1

def diffusionStatement : Prop := ∀ {P : ℕ} (c : Fin (P + 1) → ℝ) (n : Fin 25) (p : Fin P),
  Dsh phiNext c n p = lam 0 (SCal n) (c p.castSucc) (c p.succ) -
    eps n * lam (jd n) (SCal n) (c p.castSucc) (c p.succ)

def eightStatement : Prop :=
  (∀ k p : Fin 8, k ≠ p → lamE8 phiNext k p = 0) ∧
  (∀ k : Fin 8, lamE8 phiNext k k = ![14, 28, 28, 28, 35 + w, 28, 35 + w, 28] k / 360) ∧
  Function.Injective (panelD TCal SCal (Dsh phiNext (cells cEight))).mulVec

def cellsStatement : Prop :=
  (∀ (P : ℕ) (c : Fin (P + 1) → ℝ),
    Function.Injective (panelD TCal SCal (Dsh phiNext c)).mulVec → P ≤ 8) ∧
  Function.Injective (panelD TCal SCal (Dsh phiNext (cells cMerged))).mulVec ∧
  quarterAlt2 ≠ base 8 ∧ (∀ k, 0 < quarterAlt2 k) ∧
  (panelD TCal SCal (Dsh phiNext (cells cQuarter))).mulVec quarterAlt2 =
    (panelD TCal SCal (Dsh phiNext (cells cQuarter))).mulVec (base 8) ∧
  meetingAlt ≠ base 17 ∧ (∀ k, 0 < meetingAlt k) ∧
  (panelD TCal SCal (Dsh phiNext (cells cMeeting))).mulVec meetingAlt =
    (panelD TCal SCal (Dsh phiNext (cells cMeeting))).mulVec (base 17)

def statement : Prop :=
  betaStatement ∧ diffusionStatement ∧ eightStatement ∧ cellsStatement

end Standalone.MaturityShapeS2

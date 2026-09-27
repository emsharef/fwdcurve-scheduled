import Standalone.DiffusionMeetingRank
import Standalone.ListedSr3Identification

/-! # Claim 046 (d): the listed calendar

Claim 022's calendar (`ListedSr3Identification`: day numbers with 1 January 2026 = 1, the sixteen
FOMC decision days `meetings`, and the gap endpoints `gaps` = `t_0` and the 24 expiries), in
ACT/360 years from `t_0 = 2 January 2026` (`yr`). Partitions of the diffusion are given by their
day numbers from `t_0` to `S_L` = 10 December 2027 (day 709).

* `freeGapStatement` is (d1): exactly the gaps `0, 2, 5, 8, 12, 14, 18, 20` contain no meeting,
  of 14, 28, 28, 28, 35, 28, 35 and 28 days.
* `oneCellStatement` is (d2): with `σ²` constant the panel identifies the 16 meeting variances and
  `u_1`.
* `cellsStatement` is (d3): no identifying partition has more than eight cells; the eight-cell
  partition at 28 Jan, 18 Mar, 17 Jun, 16 Sep 2026, 27 Jan, 17 Mar and 28 Jul 2027 identifies; the
  quarterly partition does not, with the claim's explicit pair (`v_i = 100`, `u_p = 2500` against
  `v = 86, 72, 72` for the meetings of 15 Sep, 27 Oct, 8 Dec 2027 and `u = 2860` on the last cell,
  in bp² and bp² per year); merging its last two quarters identifies; and the meeting-date partition
  does not, with the pair `v = 77, 81` for the meetings of 18 Mar and 29 Apr 2026 and `u = 2860` on
  `[18 Mar, 29 Apr 2026)`.
-/

namespace Standalone.DiffusionMeetingCalendar
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification

/-- ACT/360 years from `t_0` of a day number. -/
noncomputable def yr (d : ℕ) : ℝ := ((d : ℝ) - 2) / 360

/-- The meeting dates `T_i`. -/
noncomputable def TCal (i : Fin 16) : ℝ := yr (meetings.getD i 0)

/-- The gap endpoints `S_0 = 0 < S_1 < … < S_24`. -/
noncomputable def SCal (ℓ : Fin 25) : ℝ := yr (gaps.getD ℓ 0)

/-- A partition of the diffusion from its day numbers. -/
noncomputable def cells {P : ℕ} (d : Fin (P + 1) → ℕ) : Fin (P + 1) → ℝ := fun p => yr (d p)

def cOne : Fin 2 → ℕ := ![2, 709]
def cEight : Fin 9 → ℕ := ![2, 28, 77, 168, 259, 392, 441, 574, 709]
def cQuarter : Fin 9 → ℕ := ![2, 91, 182, 274, 366, 456, 547, 639, 709]
def cMerged : Fin 8 → ℕ := ![2, 91, 182, 274, 366, 456, 547, 709]
def cMeeting : Fin 18 → ℕ :=
  ![2, 28, 77, 119, 168, 210, 259, 301, 343, 392, 441, 483, 525, 574, 623, 665, 707, 709]

/-- `v_i = 100`, `u_p = 2500`. -/
def base (P : ℕ) : Fin 16 ⊕ Fin P → ℝ := Sum.elim (fun _ => 100) (fun _ => 2500)

/-- The quarterly pair's second vector. -/
def quarterAlt : Fin 16 ⊕ Fin 8 → ℝ :=
  Sum.elim (fun i => if i = 13 then 86 else if i = 14 ∨ i = 15 then 72 else 100)
    (fun p => if p = 7 then 2860 else 2500)

/-- The meeting-date pair's second vector. -/
def meetingAlt : Fin 16 ⊕ Fin 17 → ℝ :=
  Sum.elim (fun i => if i = 1 then 77 else if i = 2 then 81 else 100)
    (fun p => if p = 2 then 2860 else 2500)

def freeGapStatement : Prop :=
  (Finset.univ.filter fun ℓ : Fin 24 => ∀ i : Fin 16, ¬ (gaps.getD ℓ 0 < meetings.getD i 0 ∧
      meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0)) = {0, 2, 5, 8, 12, 14, 18, 20} ∧
  [0, 2, 5, 8, 12, 14, 18, 20].map (fun ℓ => gaps.getD (ℓ + 1) 0 - gaps.getD ℓ 0) =
    [14, 28, 28, 28, 35, 28, 35, 28] ∧
  ∀ ℓ : Fin 24, MeetingFree TCal SCal ℓ ↔ ∀ i : Fin 16,
    ¬ (gaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0)

def oneCellStatement : Prop := Function.Injective (panel TCal (cells cOne) SCal).mulVec

def cellsStatement : Prop :=
  (∀ (P : ℕ) (c : Fin (P + 1) → ℝ), Function.Injective (panel TCal c SCal).mulVec → P ≤ 8) ∧
  Function.Injective (panel TCal (cells cEight) SCal).mulVec ∧
  Function.Injective (panel TCal (cells cMerged) SCal).mulVec ∧
  quarterAlt ≠ base 8 ∧ (∀ k, 0 < quarterAlt k) ∧
  (panel TCal (cells cQuarter) SCal).mulVec quarterAlt =
    (panel TCal (cells cQuarter) SCal).mulVec (base 8) ∧
  meetingAlt ≠ base 17 ∧ (∀ k, 0 < meetingAlt k) ∧
  (panel TCal (cells cMeeting) SCal).mulVec meetingAlt =
    (panel TCal (cells cMeeting) SCal).mulVec (base 17)

def statement : Prop := freeGapStatement ∧ oneCellStatement ∧ cellsStatement

end Standalone.DiffusionMeetingCalendar

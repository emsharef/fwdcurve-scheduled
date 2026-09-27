import Standalone.DiffusionMeetingCalendar

/-! # Claim 046 (c)–(d): rank values

* `rankFormulaStatement`: under (46.8)(i)–(ii), `rank 𝒜 = N + rank Λ_E`. The map `(v, u) ↦ u` is a
  linear isomorphism from the kernel of `𝒜` onto the kernel of `Λ_E`.
* `calendarRankStatement` is (d)'s rank values on the listed calendar: 17 of 17 with `P = 1`, 24 of
  24 for the eight-cell partition, 23 of 24 for the quarterly partition, 23 of 23 with its last two
  quarters merged, and 24 of 33 for the meeting-date partition, where exactly nine cells meet no
  meeting-free gap.
-/

open Matrix

namespace Standalone.DiffusionMeetingRankValue
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification
open Standalone.DiffusionMeetingCalendar

def rankFormulaStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ)
  (S : Fin (L + 1) → ℝ), StrictMono S → S 0 = 0 → (∀ i, 0 < T i) →
  (∀ i, T i ≤ S (Fin.last L)) →
  (∀ (ℓ : Fin L) (i j : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
    S ℓ.castSucc < T j → T j ≤ S ℓ.succ → i = j) →
  (panel T c S).rank = N + (lamE T c S).rank

open Classical in
def calendarRankStatement : Prop :=
  (panel TCal (cells cOne) SCal).rank = 17 ∧
  (panel TCal (cells cEight) SCal).rank = 24 ∧
  (panel TCal (cells cQuarter) SCal).rank = 23 ∧
  (panel TCal (cells cMerged) SCal).rank = 23 ∧
  (panel TCal (cells cMeeting) SCal).rank = 24 ∧
  (Finset.univ.filter fun p : Fin 17 => ∀ ℓ : Fin 24, MeetingFree TCal SCal ℓ →
    lam (SCal ℓ.castSucc) (SCal ℓ.succ) (cells cMeeting p.castSucc) (cells cMeeting p.succ) = 0).card
    = 9

def statement : Prop := rankFormulaStatement ∧ calendarRankStatement

end Standalone.DiffusionMeetingRankValue

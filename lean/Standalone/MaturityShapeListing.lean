import Standalone.MaturityShapeRank
import Standalone.DiffusionMeetingCalendar

/-! # Claim 047 (d5): what the listing of 2 January 2026 identifies

The twelve expiries listed on 2 January 2026 are Claim 022's `reducedExpiries`: the serials of
16 Jan, 13 Feb, 10 Apr and 15 May 2026 and the quarterlies 13 Mar, 12 Jun, 11 Sep, 11 Dec 2026 and
12 Mar, 11 Jun, 10 Sep, 10 Dec 2027, in date order, with `S_0 = t_0` (`SList`, ACT/360 years).
The meetings are Claim 022's sixteen (`TCal`). `gapOf i` is the gap `(S_ℓ, S_{ℓ+1}]` holding
meeting `i`. Take `P = 1` and any diffusion column `D` with `D_0 = 0` and `D_{1,1} ≠ 0`, which covers
every shape of (d1). The panel is `A = panelD TCal SList D`. The unknowns are `θ = (v, u)`, and
`eu`, `gapSum ℓ` are the functionals `u` and `Σ_{T_i ∈ G_ℓ} v_i`. A functional `c` is
`Determined` when it takes the same value on any two strictly positive `θ` with the same panel.

* `countsStatement`: the gaps contain `0, 1, 0, 1, 1, 0, 2, 3, 1, 3, 1, 3` meetings;
  `gapOf` is exact; every meeting lies in `(t_0, 10 Dec 2027]`; and the first gap is meeting-free.
* `spanStatement`: `c` is determined iff `c ∈ span{u, gap sums}`; that span and the row space of
  `A` have dimension 10, so `rank A = 10` (of 17).
* `identifiedStatement`: `u` and every gap sum are determined, and a single meeting variance is
  determined exactly for the meetings of 28 Jan, 18 Mar, 29 Apr 2026, 27 Jan and 28 Jul 2027
  (indices 0, 1, 2, 8, 12), the ones alone in their gap.
* `datesStatement` (day numbers, 1 January 2026 = day 1, a Thursday): every decision day is a
  Wednesday and every expiry of (22.3) a Friday; and moving each meeting to its effective date,
  the next day, changes no gap assignment, for this listing and for the 24 expiries of (d2)–(d4).
  The holiday calendar is not modelled here.
-/

namespace Standalone.MaturityShapeListing
open Standalone.MaturityShapeRank Standalone.DiffusionMeetingCalendar Standalone.DiffusionMeetingRank
  Standalone.ListedSr3Identification

/-- The listing's gap endpoints, `S_0 = t_0 < S_1 < … < S_12`. -/
noncomputable def SList (n : Fin 13) : ℝ := yr (reducedGaps.getD n 0)

/-- The gap of the listing holding each meeting. -/
def gapOf : Fin 16 → Fin 12 := ![1, 3, 4, 6, 6, 7, 7, 7, 8, 9, 9, 9, 10, 11, 11, 11]

/-- The functional `u`. -/
def eu : Fin 16 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The functional `Σ_{T_i ∈ G_ℓ} v_i`. -/
def gapSum (ℓ : Fin 12) : Fin 16 ⊕ Fin 1 → ℝ :=
  Sum.elim (fun i => if gapOf i = ℓ then 1 else 0) (fun _ => 0)

/-- `u` and the twelve gap sums. -/
def gen : Option (Fin 12) → Fin 16 ⊕ Fin 1 → ℝ := fun o => o.elim eu gapSum

/-- `c · θ` takes one value on all strictly positive `θ` with a given panel. -/
def Determined (A : Matrix (Fin 12) (Fin 16 ⊕ Fin 1) ℝ) (c : Fin 16 ⊕ Fin 1 → ℝ) : Prop :=
  ∀ θ θ' : Fin 16 ⊕ Fin 1 → ℝ, (∀ k, 0 < θ k) → (∀ k, 0 < θ' k) →
    A.mulVec θ = A.mulVec θ' → dotProduct c θ = dotProduct c θ'

def countsStatement : Prop :=
  (List.finRange 12).map (fun ℓ : Fin 12 => ((List.finRange 16).filter fun i =>
      reducedGaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ reducedGaps.getD (ℓ.val + 1) 0
    ).length) = [0, 1, 0, 1, 1, 0, 2, 3, 1, 3, 1, 3] ∧
  (∀ (i : Fin 16) (ℓ : Fin 12),
    (SList ℓ.castSucc < TCal i ∧ TCal i ≤ SList ℓ.succ) ↔ gapOf i = ℓ) ∧
  (∀ i, SList 0 < TCal i ∧ TCal i ≤ SList (Fin.last 12)) ∧ MeetingFree TCal SList 0

def spanStatement : Prop := ∀ D : Fin 13 → Fin 1 → ℝ, D 0 = 0 → D 1 0 ≠ 0 →
  (∀ c, Determined (panelD TCal SList D) c ↔ c ∈ Submodule.span ℝ (Set.range gen)) ∧
  Module.finrank ℝ (Submodule.span ℝ (Set.range gen)) = 10 ∧
  (panelD TCal SList D).rank = 10

def identifiedStatement : Prop := ∀ D : Fin 13 → Fin 1 → ℝ, D 0 = 0 → D 1 0 ≠ 0 →
  Determined (panelD TCal SList D) eu ∧
  (∀ ℓ, Determined (panelD TCal SList D) (gapSum ℓ)) ∧
  ∀ i : Fin 16, Determined (panelD TCal SList D) (Pi.single (Sum.inl i) 1) ↔
    i ∈ ({0, 1, 2, 8, 12} : Finset (Fin 16))

def datesStatement : Prop :=
  (∀ i : Fin 16, meetings.getD i 0 % 7 = 0) ∧ (∀ ℓ : Fin 24, expiries.getD ℓ 0 % 7 = 2) ∧
  (∀ (i : Fin 16) (ℓ : Fin 12),
    (reducedGaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ reducedGaps.getD (ℓ.val + 1) 0) ↔
    (reducedGaps.getD ℓ 0 < meetings.getD i 0 + 1 ∧
      meetings.getD i 0 + 1 ≤ reducedGaps.getD (ℓ.val + 1) 0)) ∧
  (∀ (i : Fin 16) (ℓ : Fin 24),
    (gaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ gaps.getD (ℓ.val + 1) 0) ↔
    (gaps.getD ℓ 0 < meetings.getD i 0 + 1 ∧ meetings.getD i 0 + 1 ≤ gaps.getD (ℓ.val + 1) 0))

def statement : Prop :=
  countsStatement ∧ spanStatement ∧ identifiedStatement ∧ datesStatement

end Standalone.MaturityShapeListing

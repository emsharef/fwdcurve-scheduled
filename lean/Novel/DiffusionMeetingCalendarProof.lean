import Standalone.DiffusionMeetingCalendar
import Novel.DiffusionMeetingRankProof

open Matrix
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification
open Standalone.DiffusionMeetingCalendar
namespace Novel.DiffusionMeetingCalendarProof

lemma yr_lt {a b : ℕ} : yr a < yr b ↔ a < b := by
  simp only [yr]
  constructor
  · intro h
    have : (a : ℝ) < b := by linarith
    exact_mod_cast this
  · intro h
    have : (a : ℝ) < b := by exact_mod_cast h
    linarith

lemma yr_le {a b : ℕ} : yr a ≤ yr b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, yr_lt]

lemma free_days : (Finset.univ.filter fun ℓ : Fin 24 => ∀ i : Fin 16,
    ¬ (gaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0)) =
    {0, 2, 5, 8, 12, 14, 18, 20} := by
  decide

lemma freeGapS : Standalone.DiffusionMeetingCalendar.freeGapStatement := by
  refine ⟨free_days, by decide, fun ℓ => ?_⟩
  simp only [MeetingFree, TCal, SCal, Fin.val_castSucc, Fin.val_succ, yr_lt, yr_le]

lemma gaps_mono : ∀ a b : Fin 25, a < b → gaps.getD a 0 < gaps.getD b 0 := by decide

lemma hS : StrictMono SCal := fun a b h => yr_lt.2 (gaps_mono a b h)

lemma hS0 : SCal 0 = 0 := by simp [SCal, yr, gaps, t0]

lemma hT : ∀ i, 0 < TCal i := by
  have : ∀ i : Fin 16, 2 < meetings.getD i 0 := by decide
  intro i
  have := yr_lt.2 (this i)
  simpa [TCal, yr] using this

lemma hTL : ∀ i, TCal i ≤ SCal (Fin.last 24) := by
  have : ∀ i : Fin 16, meetings.getD i 0 ≤ gaps.getD 24 0 := by decide
  intro i
  exact yr_le.2 (this i)

lemma one_per_gap_days : ∀ (ℓ : Fin 24) (i j : Fin 16),
    gaps.getD ℓ 0 < meetings.getD i 0 → meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0 →
    gaps.getD ℓ 0 < meetings.getD j 0 → meetings.getD j 0 ≤ gaps.getD (ℓ + 1) 0 → i = j := by
  decide

lemma one_per_gap : ∀ (ℓ : Fin 24) (i j : Fin 16), SCal ℓ.castSucc < TCal i → TCal i ≤ SCal ℓ.succ →
    SCal ℓ.castSucc < TCal j → TCal j ≤ SCal ℓ.succ → i = j := by
  intro ℓ i j h1 h2 h3 h4
  simp only [SCal, TCal, Fin.val_castSucc, Fin.val_succ, yr_lt, yr_le] at h1 h2 h3 h4
  exact one_per_gap_days ℓ i j h1 h2 h3 h4

lemma free0 : MeetingFree TCal SCal (0 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free2 : MeetingFree TCal SCal (2 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free5 : MeetingFree TCal SCal (5 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free8 : MeetingFree TCal SCal (8 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free12 : MeetingFree TCal SCal (12 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free14 : MeetingFree TCal SCal (14 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free18 : MeetingFree TCal SCal (18 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma free20 : MeetingFree TCal SCal (20 : Fin 24) := by
  rw [freeGapS.2.2]; decide

lemma sL0 : SCal (Fin.castSucc (0 : Fin 24)) = yr 2 := by
  unfold SCal; congr 1
lemma sR0 : SCal (Fin.succ (0 : Fin 24)) = yr 16 := by
  unfold SCal; congr 1

lemma sL2 : SCal (Fin.castSucc (2 : Fin 24)) = yr 44 := by
  unfold SCal; congr 1
lemma sR2 : SCal (Fin.succ (2 : Fin 24)) = yr 72 := by
  unfold SCal; congr 1

lemma sL5 : SCal (Fin.castSucc (5 : Fin 24)) = yr 135 := by
  unfold SCal; congr 1
lemma sR5 : SCal (Fin.succ (5 : Fin 24)) = yr 163 := by
  unfold SCal; congr 1

lemma sL8 : SCal (Fin.castSucc (8 : Fin 24)) = yr 226 := by
  unfold SCal; congr 1
lemma sR8 : SCal (Fin.succ (8 : Fin 24)) = yr 254 := by
  unfold SCal; congr 1

lemma sL12 : SCal (Fin.castSucc (12 : Fin 24)) = yr 345 := by
  unfold SCal; congr 1
lemma sR12 : SCal (Fin.succ (12 : Fin 24)) = yr 380 := by
  unfold SCal; congr 1

lemma sL14 : SCal (Fin.castSucc (14 : Fin 24)) = yr 408 := by
  unfold SCal; congr 1
lemma sR14 : SCal (Fin.succ (14 : Fin 24)) = yr 436 := by
  unfold SCal; congr 1

lemma sL18 : SCal (Fin.castSucc (18 : Fin 24)) = yr 527 := by
  unfold SCal; congr 1
lemma sR18 : SCal (Fin.succ (18 : Fin 24)) = yr 562 := by
  unfold SCal; congr 1

lemma sL20 : SCal (Fin.castSucc (20 : Fin 24)) = yr 590 := by
  unfold SCal; congr 1
lemma sR20 : SCal (Fin.succ (20 : Fin 24)) = yr 618 := by
  unfold SCal; congr 1

lemma lamE_one : Function.Injective (lamE TCal (cells cOne) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro y hy
  have e0 := congrFun hy ⟨0, free0⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL0, sR0] at e0
  norm_num [lam, cells, cOne, yr, max_def, min_def] at e0
  funext p
  fin_cases p
  simpa using e0

lemma lamE_eight : Function.Injective (lamE TCal (cells cEight) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro y hy
  have e0 := congrFun hy ⟨0, free0⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL0, sR0] at e0
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e0
  have e2 := congrFun hy ⟨2, free2⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL2, sR2] at e2
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e2
  have e5 := congrFun hy ⟨5, free5⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL5, sR5] at e5
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e5
  have e8 := congrFun hy ⟨8, free8⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL8, sR8] at e8
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e8
  have e12 := congrFun hy ⟨12, free12⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL12, sR12] at e12
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e12
  have e14 := congrFun hy ⟨14, free14⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL14, sR14] at e14
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e14
  have e18 := congrFun hy ⟨18, free18⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL18, sR18] at e18
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e18
  have e20 := congrFun hy ⟨20, free20⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL20, sR20] at e20
  norm_num [lam, cells, cEight, yr, max_def, min_def] at e20
  funext p
  fin_cases p <;> simp <;> linarith

lemma lamE_merged : Function.Injective (lamE TCal (cells cMerged) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro y hy
  have e0 := congrFun hy ⟨0, free0⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL0, sR0] at e0
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e0
  have e2 := congrFun hy ⟨2, free2⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL2, sR2] at e2
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e2
  have e5 := congrFun hy ⟨5, free5⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL5, sR5] at e5
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e5
  have e8 := congrFun hy ⟨8, free8⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL8, sR8] at e8
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e8
  have e12 := congrFun hy ⟨12, free12⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL12, sR12] at e12
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e12
  have e14 := congrFun hy ⟨14, free14⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL14, sR14] at e14
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e14
  have e18 := congrFun hy ⟨18, free18⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL18, sR18] at e18
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e18
  have e20 := congrFun hy ⟨20, free20⟩
  simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL20, sR20] at e20
  norm_num [lam, cells, cMerged, yr, max_def, min_def] at e20
  funext p
  fin_cases p <;> simp <;> linarith

lemma panel_inj {P : ℕ} (c : Fin (P + 1) → ℝ) (h : Function.Injective (lamE TCal c SCal).mulVec) :
    Function.Injective (panel TCal c SCal).mulVec :=
  (Novel.DiffusionMeetingRankProof.rankS 16 P 24 TCal c SCal hS hS0 hT).2
    ⟨hTL, one_per_gap, h⟩

lemma oneCellS : Standalone.DiffusionMeetingCalendar.oneCellStatement := panel_inj _ lamE_one

/-! ### The bound on the cells and the explicit pairs -/

lemma g0 : gaps.getD 0 0 = 2 := by decide
lemma g1 : gaps.getD 1 0 = 16 := by decide
lemma g2 : gaps.getD 2 0 = 44 := by decide
lemma g3 : gaps.getD 3 0 = 72 := by decide
lemma g4 : gaps.getD 4 0 = 100 := by decide
lemma g5 : gaps.getD 5 0 = 135 := by decide
lemma g6 : gaps.getD 6 0 = 163 := by decide
lemma g7 : gaps.getD 7 0 = 191 := by decide
lemma g8 : gaps.getD 8 0 = 226 := by decide
lemma g9 : gaps.getD 9 0 = 254 := by decide
lemma g10 : gaps.getD 10 0 = 289 := by decide
lemma g11 : gaps.getD 11 0 = 317 := by decide
lemma g12 : gaps.getD 12 0 = 345 := by decide
lemma g13 : gaps.getD 13 0 = 380 := by decide
lemma g14 : gaps.getD 14 0 = 408 := by decide
lemma g15 : gaps.getD 15 0 = 436 := by decide
lemma g16 : gaps.getD 16 0 = 471 := by decide
lemma g17 : gaps.getD 17 0 = 499 := by decide
lemma g18 : gaps.getD 18 0 = 527 := by decide
lemma g19 : gaps.getD 19 0 = 562 := by decide
lemma g20 : gaps.getD 20 0 = 590 := by decide
lemma g21 : gaps.getD 21 0 = 618 := by decide
lemma g22 : gaps.getD 22 0 = 653 := by decide
lemma g23 : gaps.getD 23 0 = 681 := by decide
lemma g24 : gaps.getD 24 0 = 709 := by decide
lemma m0 : meetings.getD 0 0 = 28 := by decide
lemma m1 : meetings.getD 1 0 = 77 := by decide
lemma m2 : meetings.getD 2 0 = 119 := by decide
lemma m3 : meetings.getD 3 0 = 168 := by decide
lemma m4 : meetings.getD 4 0 = 210 := by decide
lemma m5 : meetings.getD 5 0 = 259 := by decide
lemma m6 : meetings.getD 6 0 = 301 := by decide
lemma m7 : meetings.getD 7 0 = 343 := by decide
lemma m8 : meetings.getD 8 0 = 392 := by decide
lemma m9 : meetings.getD 9 0 = 441 := by decide
lemma m10 : meetings.getD 10 0 = 483 := by decide
lemma m11 : meetings.getD 11 0 = 525 := by decide
lemma m12 : meetings.getD 12 0 = 574 := by decide
lemma m13 : meetings.getD 13 0 = 623 := by decide
lemma m14 : meetings.getD 14 0 = 665 := by decide
lemma m15 : meetings.getD 15 0 = 707 := by decide

lemma SCal_cs (ℓ : Fin 24) : SCal ℓ.castSucc = yr (gaps.getD ℓ 0) := rfl
lemma SCal_s (ℓ : Fin 24) : SCal ℓ.succ = yr (gaps.getD (ℓ + 1) 0) := rfl

lemma card_free [Fintype {ℓ : Fin 24 // MeetingFree TCal SCal ℓ}] :
    Fintype.card {ℓ : Fin 24 // MeetingFree TCal SCal ℓ} = 8 := by
  classical
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter fun ℓ : Fin 24 => MeetingFree TCal SCal ℓ) =
      (Finset.univ.filter fun ℓ : Fin 24 => ∀ i : Fin 16, ¬ (gaps.getD ℓ 0 < meetings.getD i 0 ∧
        meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0)) :=
    Finset.filter_congr fun ℓ _ => freeGapS.2.2 ℓ
  rw [e, free_days]
  rfl

lemma cells_le {P : ℕ} (c : Fin (P + 1) → ℝ) (h : Function.Injective (panel TCal c SCal).mulVec) :
    P ≤ 8 := by
  classical
  have hE := ((Novel.DiffusionMeetingRankProof.rankS 16 P 24 TCal c SCal hS hS0 hT).1 h).2.2
  have := LinearMap.finrank_le_finrank_of_injective (f := (lamE TCal c SCal).mulVecLin) hE
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_free,
    Fintype.card_fin] at this
  exact this

lemma quarter_pair : (panel TCal (cells cQuarter) SCal).mulVec quarterAlt =
    (panel TCal (cells cQuarter) SCal).mulVec (base 8) := by
  rw [← sub_eq_zero, ← mulVec_sub, Novel.DiffusionMeetingRankProof.panel_zero_iff hS hS0 hT]
  intro ℓ
  simp only [Novel.DiffusionMeetingRankProof.Df, SCal_cs, SCal_s, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  fin_cases ℓ <;>
    simp only [Fin.isValue, Fin.val_succ, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, TCal] <;>
    norm_num [quarterAlt, base, lam, cells, cQuarter, yr, max_def, min_def]


set_option maxHeartbeats 1000000 in
lemma meeting_pair : (panel TCal (cells cMeeting) SCal).mulVec meetingAlt =
    (panel TCal (cells cMeeting) SCal).mulVec (base 17) := by
  rw [← sub_eq_zero, ← mulVec_sub, Novel.DiffusionMeetingRankProof.panel_zero_iff hS hS0 hT]
  intro ℓ
  simp only [Novel.DiffusionMeetingRankProof.Df, SCal_cs, SCal_s, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  fin_cases ℓ <;>
    simp only [Fin.isValue, Fin.val_succ, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, TCal] <;>
    norm_num [meetingAlt, base, lam, cells, cMeeting, yr, max_def, min_def]

lemma cellsS : Standalone.DiffusionMeetingCalendar.cellsStatement := by
  refine ⟨fun P c h => cells_le c h, panel_inj _ lamE_eight, panel_inj _ lamE_merged,
    fun h => ?_, fun k => ?_, quarter_pair, fun h => ?_, fun k => ?_, meeting_pair⟩
  · have := congrFun h (Sum.inl 13)
    norm_num [quarterAlt, base] at this
  · rcases k with i | p <;> simp only [quarterAlt, Sum.elim_inl, Sum.elim_inr] <;>
      split_ifs <;> norm_num
  · have := congrFun h (Sum.inl 1)
    norm_num [meetingAlt, base] at this
  · rcases k with i | p <;> simp only [meetingAlt, Sum.elim_inl, Sum.elim_inr] <;>
      split_ifs <;> norm_num

theorem diffusionMeetingCalendar : Standalone.DiffusionMeetingCalendar.statement :=
  ⟨freeGapS, oneCellS, cellsS⟩

end Novel.DiffusionMeetingCalendarProof

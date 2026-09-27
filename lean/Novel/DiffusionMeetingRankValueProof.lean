import Standalone.DiffusionMeetingRankValue
import Novel.DiffusionMeetingCalendarProof

open Matrix
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification
open Standalone.DiffusionMeetingCalendar Standalone.DiffusionMeetingRankValue
namespace Novel.DiffusionMeetingRankValueProof
open Novel.DiffusionMeetingRankProof

lemma rankFormulaS : Standalone.DiffusionMeetingRankValue.rankFormulaStatement := by
  intro N P L T c S hS hS0 hT hi hii
  classical
  set A := panel T c S
  set E := lamE T c S
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hE := LinearMap.finrank_range_add_finrank_ker E.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin] at hA
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hE
  -- the projection `(v, u) ↦ u` maps `ker 𝒜` onto `ker Λ_E`
  let π : (Fin N ⊕ Fin P → ℝ) →ₗ[ℝ] (Fin P → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr
  have hmap : ∀ θ : LinearMap.ker A.mulVecLin, π θ.1 ∈ LinearMap.ker E.mulVecLin := by
    rintro ⟨θ, hθ⟩
    rw [LinearMap.mem_ker, mulVecLin_apply] at hθ ⊢
    have hD := (panel_zero_iff hS hS0 hT θ).1 hθ
    funext ℓ
    change (lamE T c S).mulVec (fun p => θ (Sum.inr p)) ℓ = 0
    rw [← meetingFree_row]
    exact hD ℓ.1
  let f : LinearMap.ker A.mulVecLin →ₗ[ℝ] LinearMap.ker E.mulVecLin :=
    LinearMap.codRestrict _ (π.comp (LinearMap.ker A.mulVecLin).subtype) hmap
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨θ, hθ⟩ h0
    have hy : ∀ p, θ (Sum.inr p) = 0 := fun p => congrFun (congrArg Subtype.val h0) p
    rw [LinearMap.mem_ker, mulVecLin_apply] at hθ
    have hD := (panel_zero_iff hS hS0 hT θ).1 hθ
    ext k
    cases k with
    | inr p => exact hy p
    | inl i =>
      obtain ⟨ℓ, hℓ⟩ := gap_exists hS0 (hT i) (hi i)
      have := hD ℓ
      rw [single_row hℓ (fun j h1 h2 => hii ℓ j i h1 h2 hℓ.1 hℓ.2)] at this
      simpa [hy] using this
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [LinearMap.mem_ker, mulVecLin_apply] at hy
    choose g hg using fun i => gap_exists hS0 (hT i) (hi i)
    set x : Fin N → ℝ := fun i =>
      -∑ p, lam (S (g i).castSucc) (S (g i).succ) (c p.castSucc) (c p.succ) * y p
    have hθ : Sum.elim x y ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply, panel_zero_iff hS hS0 hT]
      intro k
      by_cases hk : MeetingFree T S k
      · rw [meetingFree_row _ ⟨k, hk⟩]
        simpa using congrFun hy ⟨k, hk⟩
      · simp only [MeetingFree, not_forall, not_not] at hk
        obtain ⟨i, hik⟩ := hk
        rw [single_row hik (fun j h1 h2 => hii k j i h1 h2 hik.1 hik.2)]
        have hgk : g i = k := gap_unique hS (hg i).1 (hg i).2 hik.1 hik.2
        simp only [Sum.elim_inl, Sum.elim_inr, x, hgk]
        ring
    refine ⟨⟨Sum.elim x y, hθ⟩, ?_⟩
    ext p
    rfl
  have hk := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  have hrA : A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl
  have hrE : E.rank = Module.finrank ℝ (LinearMap.range E.mulVecLin) := rfl
  omega

/-! ### Rank values on the calendar -/

open Novel.DiffusionMeetingCalendarProof

lemma rank_card {m n : Type*} [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) :
    A.rank = Fintype.card n ↔ Function.Injective A.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hr : A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl
  rw [hr, show Function.Injective A.mulVec ↔ Function.Injective A.mulVecLin from Iff.rfl,
    ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

lemma panel_rank {P : ℕ} (c : Fin (P + 1) → ℝ) :
    (panel TCal c SCal).rank = 16 + (lamE TCal c SCal).rank :=
  rankFormulaS 16 P 24 TCal c SCal hS hS0 hT hTL one_per_gap

/-- The quarterly `Λ_E` has the last cell as its kernel. -/
lemma free_end : ∀ ℓ : Fin 24, MeetingFree TCal SCal ℓ → gaps.getD (ℓ + 1) 0 ≤ 618 := by
  intro ℓ h
  rw [freeGapS.2.2] at h
  revert h
  revert ℓ
  decide

lemma quarter_col : ∀ ℓ : {ℓ : Fin 24 // MeetingFree TCal SCal ℓ},
    lamE TCal (cells cQuarter) SCal ℓ 7 = 0 := by
  rintro ⟨ℓ, hℓ⟩
  have h := free_end ℓ hℓ
  have h' : SCal ℓ.succ ≤ yr 618 := by rw [SCal_s]; exact yr_le.2 h
  simp only [lamE, lam, cells, cQuarter]
  have : min (SCal ℓ.succ) (yr 709) - max (SCal ℓ.castSucc) (yr 639) ≤ 0 := by
    have h1 : yr 618 ≤ yr 639 := yr_le.2 (by norm_num)
    have := min_le_left (SCal ℓ.succ) (yr 709)
    have := le_max_right (SCal ℓ.castSucc) (yr 639)
    linarith
  simpa using this

lemma quarter_rank : (lamE TCal (cells cQuarter) SCal).rank = 7 := by
  classical
  have hker : LinearMap.ker (lamE TCal (cells cQuarter) SCal).mulVecLin = Submodule.span ℝ {Pi.single 7 1} := by
    ext y
    rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hy
      have e0 := congrFun hy ⟨0, free0⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL0, sR0] at e0
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e0
      have e2 := congrFun hy ⟨2, free2⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL2, sR2] at e2
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e2
      have e5 := congrFun hy ⟨5, free5⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL5, sR5] at e5
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e5
      have e8 := congrFun hy ⟨8, free8⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL8, sR8] at e8
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e8
      have e12 := congrFun hy ⟨12, free12⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL12, sR12] at e12
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e12
      have e14 := congrFun hy ⟨14, free14⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL14, sR14] at e14
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e14
      have e18 := congrFun hy ⟨18, free18⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL18, sR18] at e18
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e18
      have e20 := congrFun hy ⟨20, free20⟩
      simp only [mulVec, dotProduct, lamE, Fin.sum_univ_succ, sL20, sR20] at e20
      norm_num [lam, cells, cQuarter, yr, max_def, min_def] at e20
      refine ⟨y 7, ?_⟩
      funext p
      fin_cases p <;> simp <;> linarith
    · rintro ⟨a, rfl⟩
      funext ℓ
      simp only [mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.zero_apply]
      rw [Finset.sum_eq_single 7 (fun p _ hp => by simp [hp]) (by simp)]
      simp [quarter_col ℓ]
  have hrn := LinearMap.finrank_range_add_finrank_ker (lamE TCal (cells cQuarter) SCal).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hker,
    finrank_span_singleton (by simp)] at hrn
  have hr : (lamE TCal (cells cQuarter) SCal).rank = Module.finrank ℝ (LinearMap.range (lamE TCal (cells cQuarter) SCal).mulVecLin) := rfl
  omega

/-- Eight cells of the meeting-date partition, one per meeting-free gap. -/
def fMeet : Fin 8 → Fin 17 := ![0, 1, 3, 5, 8, 9, 12, 13]

lemma meeting_sub : Function.Injective
    ((lamE TCal (cells cMeeting) SCal).submatrix id fMeet).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro y hy
  have e0 := congrFun hy ⟨0, free0⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL0, sR0] at e0
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e0
  have e2 := congrFun hy ⟨2, free2⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL2, sR2] at e2
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e2
  have e5 := congrFun hy ⟨5, free5⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL5, sR5] at e5
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e5
  have e8 := congrFun hy ⟨8, free8⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL8, sR8] at e8
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e8
  have e12 := congrFun hy ⟨12, free12⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL12, sR12] at e12
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e12
  have e14 := congrFun hy ⟨14, free14⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL14, sR14] at e14
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e14
  have e18 := congrFun hy ⟨18, free18⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL18, sR18] at e18
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e18
  have e20 := congrFun hy ⟨20, free20⟩
  simp only [mulVec, dotProduct, submatrix_apply, id, lamE, Fin.sum_univ_succ, sL20, sR20] at e20
  norm_num [lam, cells, cMeeting, fMeet, yr, max_def, min_def] at e20
  funext p
  fin_cases p <;> simp <;> linarith

lemma meeting_rank : (lamE TCal (cells cMeeting) SCal).rank = 8 := by
  classical
  have hle := rank_le_card_height (lamE TCal (cells cMeeting) SCal)
  rw [card_free] at hle
  have hsub := rank_submatrix_le (lamE TCal (cells cMeeting) SCal) id fMeet
  have h8 : ((lamE TCal (cells cMeeting) SCal).submatrix id fMeet).rank = 8 := by
    have := (rank_card ((lamE TCal (cells cMeeting) SCal).submatrix id fMeet)).2 meeting_sub
    rwa [Fintype.card_fin] at this
  omega

lemma lam_yr_zero (a b c₀ c₁ : ℕ) :
    lam (yr a) (yr b) (yr c₀) (yr c₁) = 0 ↔ min b c₁ ≤ max a c₀ := by
  have hmin : min (yr b) (yr c₁) = yr (min b c₁) := by
    rcases le_total b c₁ with h | h
    · rw [min_eq_left (yr_le.2 h), min_eq_left h]
    · rw [min_eq_right (yr_le.2 h), min_eq_right h]
  have hmax : max (yr a) (yr c₀) = yr (max a c₀) := by
    rcases le_total a c₀ with h | h
    · rw [max_eq_right (yr_le.2 h), max_eq_right h]
    · rw [max_eq_left (yr_le.2 h), max_eq_left h]
  simp only [lam, hmin, hmax, max_eq_left_iff, sub_nonpos, yr_le]

open Classical in
lemma nine_cells : (Finset.univ.filter fun p : Fin 17 => ∀ ℓ : Fin 24,
    MeetingFree TCal SCal ℓ → lam (SCal ℓ.castSucc) (SCal ℓ.succ)
      (cells cMeeting p.castSucc) (cells cMeeting p.succ) = 0).card = 9 := by
  classical
  have e : (Finset.univ.filter fun p : Fin 17 => ∀ ℓ : Fin 24,
      MeetingFree TCal SCal ℓ → lam (SCal ℓ.castSucc) (SCal ℓ.succ)
        (cells cMeeting p.castSucc) (cells cMeeting p.succ) = 0) =
      Finset.univ.filter fun p : Fin 17 => ∀ ℓ : Fin 24,
        (∀ i : Fin 16, ¬ (gaps.getD ℓ 0 < meetings.getD i 0 ∧
          meetings.getD i 0 ≤ gaps.getD (ℓ + 1) 0)) →
        min (gaps.getD (ℓ + 1) 0) (cMeeting p.succ) ≤ max (gaps.getD ℓ 0) (cMeeting p.castSucc) := by
    refine Finset.filter_congr fun p _ => forall_congr' fun ℓ => ?_
    rw [freeGapS.2.2, SCal_cs, SCal_s]
    exact imp_congr_right fun _ => lam_yr_zero _ _ _ _
  rw [e]
  decide

lemma calendarRankS : Standalone.DiffusionMeetingRankValue.calendarRankStatement := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, nine_cells⟩
  · rw [panel_rank, (rank_card _).2 lamE_one, Fintype.card_fin]
  · rw [panel_rank, (rank_card _).2 lamE_eight, Fintype.card_fin]
  · rw [panel_rank, quarter_rank]
  · rw [panel_rank, (rank_card _).2 lamE_merged, Fintype.card_fin]
  · rw [panel_rank, meeting_rank]

theorem diffusionMeetingRankValue : Standalone.DiffusionMeetingRankValue.statement :=
  ⟨rankFormulaS, calendarRankS⟩

end Novel.DiffusionMeetingRankValueProof

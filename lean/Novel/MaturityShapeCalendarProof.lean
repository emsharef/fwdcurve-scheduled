import Standalone.MaturityShapeCalendar
import Novel.MaturityShapeRankProof
import Novel.DiffusionMeetingCalendarProof
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Block

open MeasureTheory Set Matrix
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
  Standalone.DiffusionMeetingCalendar Standalone.ListedSr3Identification
  Standalone.MaturityShapeCalendar
open Novel.DiffusionMeetingCalendarProof (yr_lt yr_le hS hS0 hT hTL one_per_gap free0)
namespace Novel.MaturityShapeCalendarProof

lemma Dsh_zero {P : ℕ} (φ : ℝ → ℝ → ℝ) (c : Fin (P + 1) → ℝ) : Dsh φ c 0 = 0 := by
  funext p
  simp [Dsh, hS0]

/-- The calendar's conditions (i)–(ii), so a panel identifies iff `Λ̃_E` is injective. -/
lemma panel_iff {P : ℕ} (D : Fin 25 → Fin P → ℝ) (hD : D 0 = 0) :
    Function.Injective (panelD TCal SCal D).mulVec ↔ Function.Injective (lamTE TCal SCal D).mulVec := by
  rw [Novel.MaturityShapeRankProof.rankS 16 P 24 TCal SCal D hS hS0 hT hD]
  exact ⟨fun h => h.2.2, fun h => ⟨hTL, fun ℓ i j h1 h2 h3 h4 => one_per_gap ℓ i j h1 h2 h3 h4, h⟩⟩

lemma one_generic (D : Fin 25 → Fin 1 → ℝ) (hD : D 0 = 0) (h1 : D 1 0 ≠ 0) :
    Function.Injective (panelD TCal SCal D).mulVec := by
  rw [panel_iff D hD, Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro u hu
  have := congrFun hu ⟨0, free0⟩
  simp only [mulVec, dotProduct, lamTE, lamT, Fin.sum_univ_one, Pi.zero_apply] at this
  have e1 : (Fin.succ (0 : Fin 24)) = (1 : Fin 25) := rfl
  have e0 : (Fin.castSucc (0 : Fin 24)) = (0 : Fin 25) := rfl
  rw [e1, e0, hD] at this
  simp only [Pi.zero_apply, sub_zero, mul_eq_zero] at this
  funext p
  rw [Fin.fin_one_eq_zero p]
  exact this.resolve_left h1

lemma aW1 : aW 1 = yr 77 := by simp [aW, aDay, quarterStarts]
lemma bW1 : bW 1 = yr 168 := by simp [bW, bDay, aDay, quarterStarts]
lemma SCal1 : SCal 1 = yr 16 := by simp [SCal, gaps, expiries, t0]
lemma cOne0 : cells cOne (0 : Fin 1).castSucc = 0 := by simp [cells, cOne, yr]
lemma cOne1 : cells cOne (0 : Fin 1).succ = yr 709 := by simp [cells, cOne]

lemma set_one : Ioc 0 (SCal 1) ∩ Ico (cells cOne (0 : Fin 1).castSucc) (cells cOne (0 : Fin 1).succ) =
    Ioc 0 (yr 16) := by
  rw [SCal1, cOne0, cOne1]
  ext s
  simp only [mem_inter_iff, mem_Ioc, mem_Ico]
  have : yr 16 < yr 709 := yr_lt.2 (by norm_num)
  constructor
  · rintro ⟨h1, -⟩; exact h1
  · rintro h; exact ⟨h, h.1.le, h.2.trans_lt this⟩

lemma next_one {s : ℝ} (hs : s ≤ yr 16) {T : ℝ} (hT : yr 77 ≤ T) : phiNext s T = 1 := by
  have h : s < TCal 0 ∧ TCal 0 ≤ T := by
    have e : TCal 0 = yr 28 := by simp [TCal, meetings]
    rw [e]
    exact ⟨hs.trans_lt (yr_lt.2 (by norm_num)), (yr_le.2 (by norm_num)).trans hT⟩
  simp only [phiNext]
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨0, h⟩)

lemma d1_next : Dsh phiNext (cells cOne) 1 0 = 14 / 360 := by
  unfold Dsh
  rw [set_one]
  have hab : yr 77 < yr 168 := yr_lt.2 (by norm_num)
  have hb : ∀ s ∈ Ioc 0 (yr 16), beta phiNext 1 s ^ 2 = 1 := fun s hs => by
    simp only [beta, aW1, bW1]
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) fun T hT => by
      rw [uIcc_of_le hab.le] at hT
      exact next_one hs.2 hT.1]
    simp [(sub_pos.2 hab).ne']
  rw [setIntegral_congr_fun measurableSet_Ioc hb]
  simp [yr]
  norm_num

lemma d1_exp {κ : ℝ} (hκ : 0 < κ) : 0 < Dsh (phiExp κ) (cells cOne) 1 0 := by
  unfold Dsh
  rw [set_one]
  have hab : yr 77 < yr 168 := yr_lt.2 (by norm_num)
  set K := ∫ T in yr 77..yr 168, Real.exp (-κ * T)
  have hK : 0 < K := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun T => Real.exp (-κ * T)).intervalIntegrable _ _)
    (fun T _ => Real.exp_pos _) hab
  have hβ : ∀ s, beta (phiExp κ) 1 s = Real.exp (κ * s) * (K / (yr 168 - yr 77)) := fun s => by
    simp only [beta, aW1, bW1, phiExp, K]
    rw [← mul_div_assoc, ← intervalIntegral.integral_const_mul]
    congr 2
    funext T
    rw [← Real.exp_add]
    ring_nf
  set c := K / (yr 168 - yr 77)
  have hc : 0 < c := div_pos hK (sub_pos.2 hab)
  have hint : IntegrableOn (fun s => beta (phiExp κ) 1 s ^ 2) (Ioc 0 (yr 16)) := by
    simp only [hβ]
    exact (by fun_prop : Continuous fun s => (Real.exp (κ * s) * c) ^ 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hlow : ∀ s ∈ Ioc 0 (yr 16), c ^ 2 ≤ beta (phiExp κ) 1 s ^ 2 := fun s hs => by
    rw [hβ]
    have : 1 ≤ Real.exp (κ * s) := Real.one_le_exp (by nlinarith [hs.1])
    exact pow_le_pow_left₀ hc.le (by nlinarith) 2
  calc 0 < ∫ _ in Ioc 0 (yr 16), c ^ 2 := by
        simp [yr]; positivity
    _ ≤ _ := setIntegral_mono_on (integrableOn_const (by simp)) hint measurableSet_Ioc hlow

lemma oneCellS : Standalone.MaturityShapeCalendar.oneCellStatement :=
  ⟨one_generic, fun _ hκ => d1_exp hκ, d1_next⟩

/-! ### (d2) -/

lemma upper_days : ∀ k p : Fin 8, k < p →
    gaps.getD ((freeIdx k).val + 1) 0 < cEight (Fin.castSucc p) := by decide

lemma lower_days : ∀ k p : Fin 8, p < k → cEight (Fin.succ p) ≤ gaps.getD (freeIdx k).val 0 := by
  decide

lemma same_window : ∀ k : Fin 8, k ≠ 4 → k ≠ 6 →
    aDay (freeIdx k).succ = aDay (freeIdx k).castSucc ∧
      bDay (freeIdx k).succ = bDay (freeIdx k).castSucc := by decide

lemma SCal_succ (ℓ : Fin 24) : SCal ℓ.succ = yr (gaps.getD (ℓ.val + 1) 0) := by
  simp [SCal, Fin.val_succ]

lemma SCal_castSucc (ℓ : Fin 24) : SCal ℓ.castSucc = yr (gaps.getD ℓ.val 0) := by
  simp [SCal]

lemma Dsh_empty {P : ℕ} (φ : ℝ → ℝ → ℝ) (c : Fin (P + 1) → ℝ) {n : Fin 25} {p : Fin P}
    (h : SCal n < c p.castSucc) : Dsh φ c n p = 0 := by
  have : Ioc 0 (SCal n) ∩ Ico (c p.castSucc) (c p.succ) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_empty_iff_false, iff_false, not_and]
    intro _ h2 h3
    linarith
  simp [Dsh, this]

lemma upper (φ : ℝ → ℝ → ℝ) (k p : Fin 8) (hkp : k < p) : lamE8 φ k p = 0 := by
  have h := yr_lt.2 (upper_days k p hkp)
  have hc : cells cEight (Fin.castSucc p) = yr (cEight (Fin.castSucc p)) := rfl
  have hle : SCal (freeIdx k).castSucc ≤ SCal (freeIdx k).succ :=
    hS.monotone (Fin.castSucc_le_succ _)
  rw [← SCal_succ, ← hc] at h
  simp only [lamE8, lamT]
  rw [Dsh_empty φ _ h, Dsh_empty φ _ (hle.trans_lt h), sub_zero]

lemma lower_same (φ : ℝ → ℝ → ℝ) (k p : Fin 8) (hk4 : k ≠ 4) (hk6 : k ≠ 6) (hpk : p < k) :
    lamE8 φ k p = 0 := by
  obtain ⟨ha, hb⟩ := same_window k hk4 hk6
  have hβ : beta φ (freeIdx k).succ = beta φ (freeIdx k).castSucc := by
    funext s; simp only [beta, aW, bW, ha, hb]
  have h := yr_le.2 (lower_days k p hpk)
  have hc : cells cEight (Fin.succ p) = yr (cEight (Fin.succ p)) := rfl
  rw [← SCal_castSucc, ← hc] at h
  have hle : SCal (freeIdx k).castSucc ≤ SCal (freeIdx k).succ :=
    hS.monotone (Fin.castSucc_le_succ _)
  have hset : Ioc 0 (SCal (freeIdx k).succ) ∩ Ico (cells cEight p.castSucc) (cells cEight p.succ) =
      Ioc 0 (SCal (freeIdx k).castSucc) ∩ Ico (cells cEight p.castSucc) (cells cEight p.succ) := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨⟨h1, _⟩, h3, h4⟩; exact ⟨⟨h1, (h4.trans_le h).le⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2.trans hle⟩, h3, h4⟩
  simp only [lamE8, lamT, Dsh]
  rw [hset, hβ, sub_self]

lemma meetingFree_iff (ℓ : Fin 24) : MeetingFree TCal SCal ℓ ↔ ∃ k, freeIdx k = ℓ := by
  rw [(Novel.DiffusionMeetingCalendarProof.freeGapS).2.2 ℓ]
  revert ℓ
  decide

lemma lamTE_iff (φ : ℝ → ℝ → ℝ) :
    Function.Injective (lamTE TCal SCal (Dsh φ (cells cEight))).mulVec ↔
      Function.Injective (lamE8 φ).mulVec := by
  simp only [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  have e : ∀ u : Fin 8 → ℝ, (lamTE TCal SCal (Dsh φ (cells cEight))).mulVec u = 0 ↔
      (lamE8 φ).mulVec u = 0 := fun u => by
    constructor
    · intro h
      funext k
      have := congrFun h ⟨freeIdx k, (meetingFree_iff _).2 ⟨k, rfl⟩⟩
      simpa [mulVec, dotProduct, lamTE, lamE8] using this
    · intro h
      funext ℓ
      obtain ⟨k, hk⟩ := (meetingFree_iff ℓ.1).1 ℓ.2
      have := congrFun h k
      simp only [mulVec, dotProduct, lamE8, Pi.zero_apply] at this
      simp only [mulVec, dotProduct, lamTE, Pi.zero_apply, ← hk]
      exact this
  simp only [e]

lemma lamE8_iff (φ : ℝ → ℝ → ℝ) :
    Function.Injective (lamE8 φ).mulVec ↔ ∀ k, lamE8 φ k k ≠ 0 := by
  have hl : (lamE8 φ).IsLowerTriangular := fun i j hij => upper φ i j hij
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isLowerTriangular _ hl, Finset.prod_ne_zero_iff]
  simp

lemma triangularS : Standalone.MaturityShapeCalendar.triangularStatement := by
  intro φ _ _
  refine ⟨upper φ, fun k p hk4 hk6 hpk => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hpk with h | h
    · exact lower_same φ k p hk4 hk6 h
    · exact upper φ k p h
  · rw [panel_iff _ (Dsh_zero φ _), lamTE_iff, lamE8_iff]

theorem maturityShapeCalendar : Standalone.MaturityShapeCalendar.statement :=
  ⟨oneCellS, triangularS⟩

end Novel.MaturityShapeCalendarProof

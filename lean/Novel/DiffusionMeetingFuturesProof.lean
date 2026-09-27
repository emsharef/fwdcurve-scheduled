import Standalone.DiffusionMeetingFutures
import Novel.DiffusionMeetingRankValueProof

open Matrix MeasureTheory
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification
open Standalone.DiffusionMeetingCalendar Standalone.DiffusionMeetingFutures
namespace Novel.DiffusionMeetingFuturesProof

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

lemma mq0 : meetings[0]?.getD 0 = 28 := by decide
lemma mq1 : meetings[1]?.getD 0 = 77 := by decide
lemma mq2 : meetings[2]?.getD 0 = 119 := by decide
lemma mq3 : meetings[3]?.getD 0 = 168 := by decide
lemma mq4 : meetings[4]?.getD 0 = 210 := by decide
lemma mq5 : meetings[5]?.getD 0 = 259 := by decide
lemma mq6 : meetings[6]?.getD 0 = 301 := by decide
lemma mq7 : meetings[7]?.getD 0 = 343 := by decide
lemma mq8 : meetings[8]?.getD 0 = 392 := by decide
lemma mq9 : meetings[9]?.getD 0 = 441 := by decide
lemma mq10 : meetings[10]?.getD 0 = 483 := by decide
lemma mq11 : meetings[11]?.getD 0 = 525 := by decide
lemma mq12 : meetings[12]?.getD 0 = 574 := by decide
lemma mq13 : meetings[13]?.getD 0 = 623 := by decide
lemma mq14 : meetings[14]?.getD 0 = 665 := by decide
lemma mq15 : meetings[15]?.getD 0 = 707 := by decide
lemma sV0 : SCal (0 : Fin 25) = yr 2 := by
  unfold SCal; congr 1
lemma sV1 : SCal (1 : Fin 25) = yr 16 := by
  unfold SCal; congr 1
lemma sV2 : SCal (2 : Fin 25) = yr 44 := by
  unfold SCal; congr 1
lemma sV3 : SCal (3 : Fin 25) = yr 72 := by
  unfold SCal; congr 1
lemma sV4 : SCal (4 : Fin 25) = yr 100 := by
  unfold SCal; congr 1
lemma sV5 : SCal (5 : Fin 25) = yr 135 := by
  unfold SCal; congr 1
lemma sV6 : SCal (6 : Fin 25) = yr 163 := by
  unfold SCal; congr 1
lemma sV7 : SCal (7 : Fin 25) = yr 191 := by
  unfold SCal; congr 1
lemma sV8 : SCal (8 : Fin 25) = yr 226 := by
  unfold SCal; congr 1
lemma sV9 : SCal (9 : Fin 25) = yr 254 := by
  unfold SCal; congr 1
lemma sV10 : SCal (10 : Fin 25) = yr 289 := by
  unfold SCal; congr 1
lemma sV11 : SCal (11 : Fin 25) = yr 317 := by
  unfold SCal; congr 1
lemma sV12 : SCal (12 : Fin 25) = yr 345 := by
  unfold SCal; congr 1
lemma sV13 : SCal (13 : Fin 25) = yr 380 := by
  unfold SCal; congr 1
lemma sV14 : SCal (14 : Fin 25) = yr 408 := by
  unfold SCal; congr 1
lemma sV15 : SCal (15 : Fin 25) = yr 436 := by
  unfold SCal; congr 1
lemma sV16 : SCal (16 : Fin 25) = yr 471 := by
  unfold SCal; congr 1
lemma sV17 : SCal (17 : Fin 25) = yr 499 := by
  unfold SCal; congr 1
lemma sV18 : SCal (18 : Fin 25) = yr 527 := by
  unfold SCal; congr 1
lemma sV19 : SCal (19 : Fin 25) = yr 562 := by
  unfold SCal; congr 1
lemma sV20 : SCal (20 : Fin 25) = yr 590 := by
  unfold SCal; congr 1
lemma sV21 : SCal (21 : Fin 25) = yr 618 := by
  unfold SCal; congr 1
lemma sV22 : SCal (22 : Fin 25) = yr 653 := by
  unfold SCal; congr 1
lemma sV23 : SCal (23 : Fin 25) = yr 681 := by
  unfold SCal; congr 1
lemma sV24 : SCal (24 : Fin 25) = yr 709 := by
  unfold SCal; congr 1
lemma sR0 : SCal (Fin.succ (0 : Fin 24)) = yr 16 := by
  unfold SCal; congr 1
lemma sR1 : SCal (Fin.succ (1 : Fin 24)) = yr 44 := by
  unfold SCal; congr 1
lemma sR2 : SCal (Fin.succ (2 : Fin 24)) = yr 72 := by
  unfold SCal; congr 1
lemma sR3 : SCal (Fin.succ (3 : Fin 24)) = yr 100 := by
  unfold SCal; congr 1
lemma sR4 : SCal (Fin.succ (4 : Fin 24)) = yr 135 := by
  unfold SCal; congr 1
lemma sR5 : SCal (Fin.succ (5 : Fin 24)) = yr 163 := by
  unfold SCal; congr 1
lemma sR6 : SCal (Fin.succ (6 : Fin 24)) = yr 191 := by
  unfold SCal; congr 1
lemma sR7 : SCal (Fin.succ (7 : Fin 24)) = yr 226 := by
  unfold SCal; congr 1
lemma sR8 : SCal (Fin.succ (8 : Fin 24)) = yr 254 := by
  unfold SCal; congr 1
lemma sR9 : SCal (Fin.succ (9 : Fin 24)) = yr 289 := by
  unfold SCal; congr 1
lemma sR10 : SCal (Fin.succ (10 : Fin 24)) = yr 317 := by
  unfold SCal; congr 1
lemma sR11 : SCal (Fin.succ (11 : Fin 24)) = yr 345 := by
  unfold SCal; congr 1
lemma sR12 : SCal (Fin.succ (12 : Fin 24)) = yr 380 := by
  unfold SCal; congr 1
lemma sR13 : SCal (Fin.succ (13 : Fin 24)) = yr 408 := by
  unfold SCal; congr 1
lemma sR14 : SCal (Fin.succ (14 : Fin 24)) = yr 436 := by
  unfold SCal; congr 1
lemma sR15 : SCal (Fin.succ (15 : Fin 24)) = yr 471 := by
  unfold SCal; congr 1
lemma sR16 : SCal (Fin.succ (16 : Fin 24)) = yr 499 := by
  unfold SCal; congr 1
lemma sR17 : SCal (Fin.succ (17 : Fin 24)) = yr 527 := by
  unfold SCal; congr 1
lemma sR18 : SCal (Fin.succ (18 : Fin 24)) = yr 562 := by
  unfold SCal; congr 1
lemma sR19 : SCal (Fin.succ (19 : Fin 24)) = yr 590 := by
  unfold SCal; congr 1
lemma sR20 : SCal (Fin.succ (20 : Fin 24)) = yr 618 := by
  unfold SCal; congr 1
lemma sR21 : SCal (Fin.succ (21 : Fin 24)) = yr 653 := by
  unfold SCal; congr 1
lemma sR22 : SCal (Fin.succ (22 : Fin 24)) = yr 681 := by
  unfold SCal; congr 1
lemma sR23 : SCal (Fin.succ (23 : Fin 24)) = yr 709 := by
  unfold SCal; congr 1
lemma tC0 : TCal (0 : Fin 16) = yr 28 := by
  unfold TCal; congr 1
lemma tC1 : TCal (1 : Fin 16) = yr 77 := by
  unfold TCal; congr 1
lemma tC2 : TCal (2 : Fin 16) = yr 119 := by
  unfold TCal; congr 1
lemma tC3 : TCal (3 : Fin 16) = yr 168 := by
  unfold TCal; congr 1
lemma tC4 : TCal (4 : Fin 16) = yr 210 := by
  unfold TCal; congr 1
lemma tC5 : TCal (5 : Fin 16) = yr 259 := by
  unfold TCal; congr 1
lemma tC6 : TCal (6 : Fin 16) = yr 301 := by
  unfold TCal; congr 1
lemma tC7 : TCal (7 : Fin 16) = yr 343 := by
  unfold TCal; congr 1
lemma tC8 : TCal (8 : Fin 16) = yr 392 := by
  unfold TCal; congr 1
lemma tC9 : TCal (9 : Fin 16) = yr 441 := by
  unfold TCal; congr 1
lemma tC10 : TCal (10 : Fin 16) = yr 483 := by
  unfold TCal; congr 1
lemma tC11 : TCal (11 : Fin 16) = yr 525 := by
  unfold TCal; congr 1
lemma tC12 : TCal (12 : Fin 16) = yr 574 := by
  unfold TCal; congr 1
lemma tC13 : TCal (13 : Fin 16) = yr 623 := by
  unfold TCal; congr 1
lemma tC14 : TCal (14 : Fin 16) = yr 665 := by
  unfold TCal; congr 1
lemma tC15 : TCal (15 : Fin 16) = yr 707 := by
  unfold TCal; congr 1

/-! ### The per-gap reduction -/

section
open Novel.DiffusionMeetingRankProof
variable {N P L : ℕ}

lemma lam_int (lo hi c₀ c₁ : ℝ) (hlh : lo ≤ hi) :
    Standalone.DiffusionMeetingRank.lam lo hi c₀ c₁ =
      ∫ s in lo..hi, (Set.Ico c₀ c₁).indicator (fun _ => (1:ℝ)) s := by
  rw [intervalIntegral.integral_of_le hlh,
    integral_congr_ae (ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (Ico_ae_eq_Ioc (μ := volume)))),
    setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc]
  rw [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, ENNReal.toReal_ofReal', Standalone.DiffusionMeetingRank.lam, max_comm]

lemma momS : Standalone.DiffusionMeetingFutures.momStatement := by
  intro lo hi c₀ c₁ hlh _
  rw [intervalIntegral.integral_of_le hlh,
    integral_congr_ae (ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (Ico_ae_eq_Ioc (μ := volume)))),
    setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc]
  unfold mom1
  split_ifs with h
  · rw [← intervalIntegral.integral_of_le h.le]
    change _ = ∫ x in max lo c₀..min hi c₁, (fun y => y) (hi - x)
    rw [intervalIntegral.integral_comp_sub_left (fun y => y) hi, integral_id]
  · rw [Set.Ioc_eq_empty (by simpa using h)]
    simp

/-- `mom1 0 b = mom1 0 a + (b − a) λ(0, a) + mom1 a b`. -/
lemma mom_add {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {c₀ c₁ : ℝ} (hc : c₀ ≤ c₁) :
    mom1 0 b c₀ c₁ = mom1 0 a c₀ c₁ + (b - a) * Standalone.DiffusionMeetingRank.lam 0 a c₀ c₁ +
      mom1 a b c₀ c₁ := by
  have hi : ∀ x y : ℝ, ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable ((Set.Ico c₀ c₁).indicator f) volume x y := fun x y f hf =>
    ⟨(hf.intervalIntegrable x y).1.indicator measurableSet_Ico,
      (hf.intervalIntegrable x y).2.indicator measurableSet_Ico⟩
  rw [momS 0 b c₀ c₁ (ha.trans hab) hc, momS 0 a c₀ c₁ ha hc, momS a b c₀ c₁ hab hc,
    lam_int 0 a c₀ c₁ ha, ← intervalIntegral.integral_add_adjacent_intervals
      (hi 0 a (fun s => b - s) (by fun_prop)) (hi a b (fun s => b - s) (by fun_prop)),
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hi 0 a (fun s => a - s) (by fun_prop)) ((hi 0 a (fun _ => 1) continuous_const).const_mul _)]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  by_cases hs : s ∈ Set.Ico c₀ c₁ <;> simp [Set.indicator, hs]

/-- `z(S_n)` for `θ`. -/
noncomputable def Zf (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (n : Fin (L + 1)) : ℝ :=
  ∑ i, (if T i ≤ S n then S n - T i else 0) * θ (Sum.inl i) +
    ∑ p, mom1 0 (S n) (c p.castSucc) (c p.succ) * θ (Sum.inr p)

/-- The `z`-increment over gap `ℓ`, net of the carried `Q`. -/
noncomputable def Ef (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then S ℓ.succ - T i else 0) * θ (Sum.inl i) +
    ∑ p, mom1 (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) * θ (Sum.inr p)

lemma Ef_eq (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (hc : Monotone c) (S : Fin (L + 1) → ℝ)
    (hS : StrictMono S) (hS0 : S 0 = 0) (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) :
    Ef T c S θ ℓ = Zf T c S θ ℓ.succ - Zf T c S θ ℓ.castSucc -
      (S ℓ.succ - S ℓ.castSucc) * Qf T c S θ ℓ.castSucc := by
  have hle : S ℓ.castSucc ≤ S ℓ.succ := hS.monotone (Fin.castSucc_le_succ ℓ)
  have h0 : 0 ≤ S ℓ.castSucc := hS0 ▸ hS.monotone (Fin.zero_le _)
  have e1 : ∀ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then S ℓ.succ - T i else 0) =
      (if T i ≤ S ℓ.succ then S ℓ.succ - T i else 0) -
        (if T i ≤ S ℓ.castSucc then S ℓ.castSucc - T i else 0) -
        (S ℓ.succ - S ℓ.castSucc) * (if T i ≤ S ℓ.castSucc then 1 else 0) := fun i => by
    by_cases h1 : T i ≤ S ℓ.castSucc
    · simp [h1, h1.trans hle, not_lt.2 h1]
    · by_cases h2 : T i ≤ S ℓ.succ
      · simp [h1, h2, not_le.1 h1]
      · simp [h1, h2]
  have e2 : ∀ p : Fin P, mom1 (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) =
      mom1 0 (S ℓ.succ) (c p.castSucc) (c p.succ) - mom1 0 (S ℓ.castSucc) (c p.castSucc) (c p.succ) -
        (S ℓ.succ - S ℓ.castSucc) *
          Standalone.DiffusionMeetingRank.lam 0 (S ℓ.castSucc) (c p.castSucc) (c p.succ) :=
    fun p => by
      linarith [mom_add h0 hle (hc (Fin.castSucc_le_succ p)) (c₀ := c p.castSucc) (c₁ := c p.succ)]
  set d := S ℓ.succ - S ℓ.castSucc
  simp only [Ef, Zf, Qf, e1, e2, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

end

section
open Novel.DiffusionMeetingRankProof
variable {N P L : ℕ}

lemma mom_zero (c₀ c₁ : ℝ) : mom1 0 0 c₀ c₁ = 0 := by
  unfold mom1
  rw [ite_eq_right]
  intro h
  have := min_le_left (0:ℝ) c₁
  have := le_max_left (0:ℝ) c₀
  linarith

lemma stacked_zero_iff {T : Fin N → ℝ} {c : Fin (P + 1) → ℝ} {S : Fin (L + 1) → ℝ}
    (hc : Monotone c) (hS : StrictMono S) (hS0 : S 0 = 0) (hT : ∀ i, 0 < T i)
    (θ : Fin N ⊕ Fin P → ℝ) :
    (stacked T c S).mulVec θ = 0 ↔ ∀ ℓ, Df T c S θ ℓ = 0 ∧ Ef T c S θ ℓ = 0 := by
  have hQ : ∀ ℓ, (stacked T c S).mulVec θ (Sum.inl ℓ) = Qf T c S θ ℓ.succ := fun ℓ => by
    rw [← panel_apply]; rfl
  have hZ : ∀ ℓ, (stacked T c S).mulVec θ (Sum.inr ℓ) = Zf T c S θ ℓ.succ := fun ℓ => by
    simp only [mulVec, dotProduct, stacked, fromRows_apply_inr, zrow, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Zf]
  have hZ0 : Zf T c S θ 0 = 0 := by
    simp only [Zf, hS0, mom_zero, zero_mul, Finset.sum_const_zero, add_zero]
    exact Finset.sum_eq_zero fun i _ => by simp [not_le.2 (hT i)]
  constructor
  · intro h ℓ
    have hq : ∀ k : Fin L, Qf T c S θ k.succ = 0 := fun k => by rw [← hQ, h]; rfl
    have hzz : ∀ k : Fin L, Zf T c S θ k.succ = 0 := fun k => by rw [← hZ, h]; rfl
    have hcs : Qf T c S θ ℓ.castSucc = 0 ∧ Zf T c S θ ℓ.castSucc = 0 := by
      rcases Fin.eq_zero_or_eq_succ ℓ.castSucc with h0 | ⟨j, hj⟩
      · rw [h0]; exact ⟨Qf_zero T c S hS0 hT θ, hZ0⟩
      · rw [hj]; exact ⟨hq j, hzz j⟩
    refine ⟨?_, ?_⟩
    · rw [Df_eq T c S hS hS0, hq ℓ, hcs.1]; ring
    · rw [Ef_eq T c hc S hS hS0, hzz ℓ, hcs.1, hcs.2]; ring
  · intro hD
    have hall : ∀ n : Fin (L + 1), Qf T c S θ n = 0 ∧ Zf T c S θ n = 0 := by
      intro n
      induction n using Fin.induction with
      | zero => exact ⟨Qf_zero T c S hS0 hT θ, hZ0⟩
      | succ k ih =>
        have h1 := (hD k).1
        have h2 := (hD k).2
        rw [Df_eq T c S hS hS0, ih.1] at h1
        rw [Ef_eq T c hc S hS hS0, ih.1, ih.2] at h2
        exact ⟨by linarith, by linarith⟩
    funext k
    rcases k with ℓ | ℓ
    · rw [hQ]; exact (hall _).1
    · rw [hZ]; exact (hall _).2
end

lemma cells_mono {P : ℕ} {d : Fin (P + 1) → ℕ} (hd : Monotone d) : Monotone (cells d) :=
  fun _ _ h => Novel.DiffusionMeetingCalendarProof.yr_le.2 (hd h)

lemma cells_mono_cQuarter : Monotone (cells cQuarter) := cells_mono (by decide)
lemma cells_mono_cMeeting : Monotone (cells cMeeting) := cells_mono (by decide)
lemma cells_mono_cGap : Monotone (cells cGap) := cells_mono (by decide)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
lemma quarter_inj : Function.Injective (stacked TCal (cells cQuarter) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro θ h
  have hz := (stacked_zero_iff (cells_mono_cQuarter) Novel.DiffusionMeetingCalendarProof.hS
    Novel.DiffusionMeetingCalendarProof.hS0 Novel.DiffusionMeetingCalendarProof.hT θ).1 h
  have d0 := (hz (0 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d0
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d0
  have e0 := (hz (0 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e0
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e0
  have d1 := (hz (1 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d1
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d1
  have e1 := (hz (1 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e1
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e1
  have d2 := (hz (2 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d2
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d2
  have e2 := (hz (2 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e2
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e2
  have d3 := (hz (3 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d3
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d3
  have e3 := (hz (3 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e3
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e3
  have d4 := (hz (4 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d4
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d4
  have e4 := (hz (4 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e4
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e4
  have d5 := (hz (5 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d5
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d5
  have e5 := (hz (5 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e5
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e5
  have d6 := (hz (6 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d6
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d6
  have e6 := (hz (6 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e6
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e6
  have d7 := (hz (7 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d7
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d7
  have e7 := (hz (7 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e7
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e7
  have d8 := (hz (8 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d8
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d8
  have e8 := (hz (8 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e8
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e8
  have d9 := (hz (9 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d9
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d9
  have e9 := (hz (9 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e9
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e9
  have d10 := (hz (10 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d10
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d10
  have e10 := (hz (10 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e10
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e10
  have d11 := (hz (11 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d11
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d11
  have e11 := (hz (11 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e11
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e11
  have d12 := (hz (12 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d12
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d12
  have e12 := (hz (12 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e12
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e12
  have d13 := (hz (13 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d13
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d13
  have e13 := (hz (13 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e13
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e13
  have d14 := (hz (14 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d14
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d14
  have e14 := (hz (14 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e14
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e14
  have d15 := (hz (15 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d15
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d15
  have e15 := (hz (15 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e15
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e15
  have d16 := (hz (16 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d16
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d16
  have e16 := (hz (16 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e16
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e16
  have d17 := (hz (17 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d17
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d17
  have e17 := (hz (17 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e17
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e17
  have d18 := (hz (18 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d18
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d18
  have e18 := (hz (18 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e18
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e18
  have d19 := (hz (19 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d19
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d19
  have e19 := (hz (19 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e19
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e19
  have d20 := (hz (20 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d20
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d20
  have e20 := (hz (20 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e20
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e20
  have d21 := (hz (21 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d21
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d21
  have e21 := (hz (21 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e21
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e21
  have d22 := (hz (22 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d22
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d22
  have e22 := (hz (22 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e22
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e22
  have d23 := (hz (23 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d23
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at d23
  have e23 := (hz (23 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e23
  norm_num [lam, mom1, cQuarter, yr, max_def, min_def] at e23
  funext k
  rcases k with i | p
  · fin_cases i <;> simp <;> linarith
  · fin_cases p <;> simp <;> linarith

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
lemma meeting_inj : Function.Injective (stacked TCal (cells cMeeting) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro θ h
  have hz := (stacked_zero_iff (cells_mono_cMeeting) Novel.DiffusionMeetingCalendarProof.hS
    Novel.DiffusionMeetingCalendarProof.hS0 Novel.DiffusionMeetingCalendarProof.hT θ).1 h
  have d0 := (hz (0 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d0
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d0
  have e0 := (hz (0 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e0
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e0
  have d1 := (hz (1 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d1
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d1
  have e1 := (hz (1 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e1
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e1
  have d2 := (hz (2 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d2
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d2
  have e2 := (hz (2 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e2
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e2
  have d3 := (hz (3 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d3
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d3
  have e3 := (hz (3 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e3
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e3
  have d4 := (hz (4 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d4
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d4
  have e4 := (hz (4 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e4
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e4
  have d5 := (hz (5 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d5
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d5
  have e5 := (hz (5 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e5
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e5
  have d6 := (hz (6 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d6
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d6
  have e6 := (hz (6 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e6
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e6
  have d7 := (hz (7 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d7
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d7
  have e7 := (hz (7 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e7
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e7
  have d8 := (hz (8 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d8
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d8
  have e8 := (hz (8 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e8
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e8
  have d9 := (hz (9 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d9
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d9
  have e9 := (hz (9 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e9
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e9
  have d10 := (hz (10 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d10
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d10
  have e10 := (hz (10 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e10
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e10
  have d11 := (hz (11 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d11
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d11
  have e11 := (hz (11 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e11
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e11
  have d12 := (hz (12 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d12
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d12
  have e12 := (hz (12 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e12
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e12
  have d13 := (hz (13 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d13
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d13
  have e13 := (hz (13 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e13
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e13
  have d14 := (hz (14 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d14
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d14
  have e14 := (hz (14 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e14
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e14
  have d15 := (hz (15 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d15
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d15
  have e15 := (hz (15 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e15
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e15
  have d16 := (hz (16 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d16
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d16
  have e16 := (hz (16 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e16
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e16
  have d17 := (hz (17 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d17
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d17
  have e17 := (hz (17 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e17
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e17
  have d18 := (hz (18 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d18
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d18
  have e18 := (hz (18 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e18
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e18
  have d19 := (hz (19 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d19
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d19
  have e19 := (hz (19 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e19
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e19
  have d20 := (hz (20 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d20
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d20
  have e20 := (hz (20 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e20
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e20
  have d21 := (hz (21 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d21
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d21
  have e21 := (hz (21 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e21
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e21
  have d22 := (hz (22 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d22
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d22
  have e22 := (hz (22 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e22
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e22
  have d23 := (hz (23 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d23
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at d23
  have e23 := (hz (23 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e23
  norm_num [lam, mom1, cMeeting, yr, max_def, min_def] at e23
  funext k
  rcases k with i | p
  · fin_cases i <;> simp <;> linarith
  · fin_cases p <;> simp <;> linarith

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
lemma gap_inj : Function.Injective (stacked TCal (cells cGap) SCal).mulVec := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro θ h
  have hz := (stacked_zero_iff (cells_mono_cGap) Novel.DiffusionMeetingCalendarProof.hS
    Novel.DiffusionMeetingCalendarProof.hS0 Novel.DiffusionMeetingCalendarProof.hT θ).1 h
  have d0 := (hz (0 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d0
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d0
  have e0 := (hz (0 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e0
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e0
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e0
  have d1 := (hz (1 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d1
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d1
  have e1 := (hz (1 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e1
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e1
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e1
  have d2 := (hz (2 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d2
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d2
  have e2 := (hz (2 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e2
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e2
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e2
  have d3 := (hz (3 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d3
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d3
  have e3 := (hz (3 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e3
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e3
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e3
  have d4 := (hz (4 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d4
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d4
  have e4 := (hz (4 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e4
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e4
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e4
  have d5 := (hz (5 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d5
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d5
  have e5 := (hz (5 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e5
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e5
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e5
  have d6 := (hz (6 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d6
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d6
  have e6 := (hz (6 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e6
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e6
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e6
  have d7 := (hz (7 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d7
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d7
  have e7 := (hz (7 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e7
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e7
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e7
  have d8 := (hz (8 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d8
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d8
  have e8 := (hz (8 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e8
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e8
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e8
  have d9 := (hz (9 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d9
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d9
  have e9 := (hz (9 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e9
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e9
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e9
  have d10 := (hz (10 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d10
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d10
  have e10 := (hz (10 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e10
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e10
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e10
  have d11 := (hz (11 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d11
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d11
  have e11 := (hz (11 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e11
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e11
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e11
  have d12 := (hz (12 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d12
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d12
  have e12 := (hz (12 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e12
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e12
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e12
  have d13 := (hz (13 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d13
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d13
  have e13 := (hz (13 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e13
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e13
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e13
  have d14 := (hz (14 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d14
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d14
  have e14 := (hz (14 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e14
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e14
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e14
  have d15 := (hz (15 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d15
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d15
  have e15 := (hz (15 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e15
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e15
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e15
  have d16 := (hz (16 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d16
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d16
  have e16 := (hz (16 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e16
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e16
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e16
  have d17 := (hz (17 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d17
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d17
  have e17 := (hz (17 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e17
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e17
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e17
  have d18 := (hz (18 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d18
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d18
  have e18 := (hz (18 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e18
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e18
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e18
  have d19 := (hz (19 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d19
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d19
  have e19 := (hz (19 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e19
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e19
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e19
  have d20 := (hz (20 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d20
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d20
  have e20 := (hz (20 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e20
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e20
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e20
  have d21 := (hz (21 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d21
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d21
  have e21 := (hz (21 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e21
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e21
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e21
  have d22 := (hz (22 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d22
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d22
  have e22 := (hz (22 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e22
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e22
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e22
  have d23 := (hz (23 : Fin 24)).1
  simp only [Novel.DiffusionMeetingRankProof.Df, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at d23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at d23
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at d23
  have e23 := (hz (23 : Fin 24)).2
  simp only [Ef, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr] at e23
  simp only [TCal, SCal, cells, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceAdd, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,] at e23
  norm_num [lam, mom1, cGap, yr, max_def, min_def] at e23
  funext k
  rcases k with i | p
  · fin_cases i <;> simp <;> linarith
  · fin_cases p <;> simp <;> linarith

lemma stackedS : Standalone.DiffusionMeetingFutures.stackedStatement := by
  refine ⟨?_, ?_, ?_⟩
  · have := (Novel.DiffusionMeetingRankValueProof.rank_card _).2 quarter_inj
    simpa using this
  · have := (Novel.DiffusionMeetingRankValueProof.rank_card _).2 meeting_inj
    simpa using this
  · have := (Novel.DiffusionMeetingRankValueProof.rank_card _).2 gap_inj
    simpa using this

theorem diffusionMeetingFutures : Standalone.DiffusionMeetingFutures.statement := ⟨momS, stackedS⟩

end Novel.DiffusionMeetingFuturesProof

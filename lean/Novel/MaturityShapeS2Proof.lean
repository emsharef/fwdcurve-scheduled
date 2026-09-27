import Standalone.MaturityShapeS2
import Novel.MaturityShapeCalendarProof
import Novel.DiffusionMeetingGaussProof

open MeasureTheory Set Matrix
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
  Standalone.DiffusionMeetingCalendar Standalone.ListedSr3Identification
  Standalone.MaturityShapeCalendar Standalone.MaturityShapeS2
open Novel.DiffusionMeetingCalendarProof (yr_lt yr_le hS hS0)
namespace Novel.MaturityShapeS2Proof

/-! ### `β` under (S2) -/

lemma TCal_eq (i : Fin 16) : TCal i = yr (meetings.getD i 0) := rfl
lemma SCal_eq (n : Fin 25) : SCal n = yr (gaps.getD n 0) := rfl
lemma aW_eq (n : Fin 25) : aW n = yr (aDay n) := rfl
lemma bW_eq (n : Fin 25) : bW n = yr (aDay n + 91) := rfl

lemma width (n : Fin 25) : bW n - aW n = 91 / 360 := by
  rw [aW_eq, bW_eq]; simp only [yr]; push_cast; ring

/-- A meeting in `(s, a_n]`: the whole window loads, `β = 1`. -/
lemma beta_one {n : Fin 25} {s : ℝ} (h : ∃ i, s < TCal i ∧ TCal i ≤ aW n) :
    beta phiNext n s = 1 := by
  obtain ⟨i, h1, h2⟩ := h
  have hab : aW n ≤ bW n := by linarith [width n]
  unfold beta
  rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) fun T hT => by
    rw [uIcc_of_le hab] at hT
    simp only [phiNext]
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨i, h1, h2.trans hT.1⟩)]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, width]
  norm_num

/-- No meeting after `s`: nothing loads, `β = 0`. -/
lemma beta_zero {n : Fin 25} {s : ℝ} (h : ∀ i, TCal i ≤ s) : beta phiNext n s = 0 := by
  unfold beta
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun T _ => by
    simp only [phiNext]
    exact ite_eq_right_iff.2 fun ⟨i, h1, _⟩ => absurd (h i) (not_le.2 h1)]
  simp

/-- The next meeting `m` inside the window: `β = (b_n − m)/δ`. -/
lemma beta_mid {n : Fin 25} {s m : ℝ} (hm : ∃ i, TCal i = m) (hsm : s < m)
    (hnext : ∀ i, s < TCal i → m ≤ TCal i) (ham : aW n ≤ m) (hmb : m ≤ bW n) :
    beta phiNext n s = (bW n - m) / (bW n - aW n) := by
  obtain ⟨i0, hi0⟩ := hm
  have hab : aW n ≤ bW n := ham.trans hmb
  have e : ∀ T, phiNext s T = if m ≤ T then 1 + 0 * (T - m) else 0 := fun T => by
    simp only [phiNext, zero_mul, add_zero]
    by_cases hT : m ≤ T
    · rw [ite_eq_left hT]; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨i0, hi0 ▸ hsm, hi0 ▸ hT⟩)
    · rw [ite_eq_right hT]
      exact ite_eq_right_iff.2 fun ⟨i, h1, h2⟩ => absurd ((hnext i h1).trans h2) hT
  unfold beta
  simp only [e]
  rw [Novel.DiffusionMeetingGaussProof.int_step hab m 1 0, Standalone.CompoundedFuturesIdentification.w,
    max_eq_left (sub_nonneg.2 hmb), max_eq_right (sub_nonpos.2 ham)]
  ring

lemma normal_days : ∀ n : Fin 25, n ≠ 0 → n ≠ 12 → n ≠ 18 → n ≠ 24 →
    ∃ i : Fin 16, gaps.getD n 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ aDay n := by decide

lemma betaS : betaStatement := by
  intro n hn0 s hs hsS
  have jd12 : jd 12 = yr 343 := by simp [jd]
  have jd18 : jd 18 = yr 525 := by simp [jd]
  have jd24 : jd 24 = yr 707 := by simp [jd]
  by_cases h12 : n = 12
  · subst h12
    rw [jd12]
    by_cases hj : yr 343 ≤ s
    · rw [ite_eq_left ⟨Or.inl rfl, hj⟩]
      have hS12 : SCal 12 = yr 345 := by simp [SCal_eq, gaps, expiries, t0]
      rw [beta_mid (m := yr 392) ⟨8, by simp [TCal_eq, meetings]⟩ (hsS.trans_lt (by
          rw [hS12]; exact yr_lt.2 (by norm_num)))
        (fun i hi => ?_) (by rw [aW_eq]; exact yr_le.2 (by decide))
        (by rw [bW_eq]; exact yr_le.2 (by decide)), width, bW_eq]
      · simp only [yr, aDay, quarterStarts]; norm_num
      · rw [TCal_eq] at hi ⊢
        have hd : ∀ i : Fin 16, meetings.getD i 0 ≤ 343 ∨ 392 ≤ meetings.getD i 0 := by decide
        rcases hd i with h | h
        · exact absurd (hj.trans_lt hi) (not_lt.2 (yr_le.2 h))
        · exact yr_le.2 h
    · rw [ite_eq_right (fun h => hj h.2), ite_eq_right (by simp)]
      exact beta_one ⟨7, by rw [TCal_eq]; simpa [meetings] using not_le.1 hj,
        by rw [TCal_eq, aW_eq]; exact yr_le.2 (by decide)⟩
  by_cases h18 : n = 18
  · subst h18
    rw [jd18]
    by_cases hj : yr 525 ≤ s
    · rw [ite_eq_left ⟨Or.inr rfl, hj⟩]
      have hS18 : SCal 18 = yr 527 := by simp [SCal_eq, gaps, expiries, t0]
      rw [beta_mid (m := yr 574) ⟨12, by simp [TCal_eq, meetings]⟩ (hsS.trans_lt (by
          rw [hS18]; exact yr_lt.2 (by norm_num)))
        (fun i hi => ?_) (by rw [aW_eq]; exact yr_le.2 (by decide))
        (by rw [bW_eq]; exact yr_le.2 (by decide)), width, bW_eq]
      · simp only [yr, aDay, quarterStarts]; norm_num
      · rw [TCal_eq] at hi ⊢
        have hd : ∀ i : Fin 16, meetings.getD i 0 ≤ 525 ∨ 574 ≤ meetings.getD i 0 := by decide
        rcases hd i with h | h
        · exact absurd (hj.trans_lt hi) (not_lt.2 (yr_le.2 h))
        · exact yr_le.2 h
    · rw [ite_eq_right (fun h => hj h.2), ite_eq_right (by simp)]
      exact beta_one ⟨11, by rw [TCal_eq]; simpa [meetings] using not_le.1 hj,
        by rw [TCal_eq, aW_eq]; exact yr_le.2 (by decide)⟩
  by_cases h24 : n = 24
  · subst h24
    rw [jd24]
    by_cases hj : yr 707 ≤ s
    · rw [ite_eq_right (by simp), ite_eq_left ⟨rfl, hj⟩]
      refine beta_zero fun i => ?_
      rw [TCal_eq]
      have hd : ∀ i : Fin 16, meetings.getD i 0 ≤ 707 := by decide
      exact (yr_le.2 (hd i)).trans hj
    · rw [ite_eq_right (by simp), ite_eq_right (fun h => hj h.2)]
      exact beta_one ⟨15, by rw [TCal_eq]; simpa [meetings] using not_le.1 hj,
        by rw [TCal_eq, aW_eq]; exact yr_le.2 (by decide)⟩
  rw [ite_eq_right (by tauto), ite_eq_right (by tauto)]
  obtain ⟨i, h1, h2⟩ := normal_days n hn0 h12 h18 h24
  exact beta_one ⟨i, hsS.trans_lt (by rw [SCal_eq, TCal_eq]; exact yr_lt.2 h1),
    by rw [TCal_eq, aW_eq]; exact yr_le.2 h2⟩

/-! ### The diffusion columns -/

lemma lam_nonneg (lo hi c0 c1 : ℝ) : 0 ≤ lam lo hi c0 c1 := le_max_left _ _

/-- A set between `(x, y)` and `[x, y]` has measure `y − x`. -/
lemma vol_squeeze {X : Set ℝ} {x y : ℝ} (h1 : Ioo x y ⊆ X) (h2 : X ⊆ Icc x y) :
    volume X = ENNReal.ofReal (y - x) :=
  le_antisymm ((measure_mono h2).trans Real.volume_Icc.le)
    (Real.volume_Ioo.ge.trans (measure_mono h1))

lemma ofReal_lam (lo hi c0 c1 : ℝ) :
    ENNReal.ofReal (min hi c1 - max lo c0) = ENNReal.ofReal (lam lo hi c0 c1) := by
  unfold lam
  rcases le_total 0 (min hi c1 - max lo c0) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

lemma vol_A (S c0 c1 : ℝ) :
    volume (Ioc 0 S ∩ Ico c0 c1) = ENNReal.ofReal (lam 0 S c0 c1) := by
  rw [← ofReal_lam]
  apply vol_squeeze
  · intro s hs
    simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hs
    exact ⟨⟨hs.1.1, hs.2.1.le⟩, hs.1.2.le, hs.2.2⟩
  · intro s hs
    simp only [mem_inter_iff, mem_Ioc, mem_Ico] at hs
    exact ⟨max_le hs.1.1.le hs.2.1, le_min hs.1.2 hs.2.2.le⟩

lemma vol_AJ (S c0 c1 j : ℝ) (hj : 0 ≤ j) :
    volume (Ioc 0 S ∩ Ico c0 c1 ∩ Icc j S) = ENNReal.ofReal (lam j S c0 c1) := by
  rw [← ofReal_lam]
  apply vol_squeeze
  · intro s hs
    simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hs
    exact ⟨⟨⟨hj.trans_lt hs.1.1, hs.2.1.le⟩, hs.1.2.le, hs.2.2⟩, hs.1.1.le, hs.2.1.le⟩
  · intro s hs
    simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_Icc] at hs
    exact ⟨max_le hs.2.1 hs.1.2.1, le_min hs.2.2 hs.1.2.2.le⟩

lemma jd_nonneg (n : Fin 25) : 0 ≤ jd n := by
  have hS : 0 ≤ SCal n := hS0 ▸ hS.monotone (Fin.zero_le n)
  unfold jd
  split_ifs <;> first | exact hS | (simp only [yr]; norm_num)

lemma beta_sq (n : Fin 25) (s : ℝ) (hs : s ∈ Ioc 0 (SCal n)) :
    beta phiNext n s ^ 2 = 1 - eps n * (Icc (jd n) (SCal n)).indicator 1 s := by
  have hn0 : n ≠ 0 := fun h => by
    subst h; rw [hS0] at hs; exact absurd (hs.1.trans_le hs.2) (lt_irrefl 0)
  have hind : (Icc (jd n) (SCal n)).indicator (1 : ℝ → ℝ) s = if jd n ≤ s then 1 else 0 := by
    by_cases h : jd n ≤ s <;> simp [indicator, h, hs.2]
  rw [betaS n hn0 s hs.1 hs.2, hind]
  by_cases h12 : n = 12
  · subst h12; by_cases h : jd 12 ≤ s <;> simp [eps, h]
  by_cases h18 : n = 18
  · subst h18; by_cases h : jd 18 ≤ s <;> simp [eps, h]
  by_cases h24 : n = 24
  · subst h24; by_cases h : jd 24 ≤ s <;> simp [eps, h]
  simp [eps, h12, h18, h24]

lemma diffusionS : diffusionStatement := by
  intro P c n p
  set A := Ioc 0 (SCal n) ∩ Ico (c p.castSucc) (c p.succ)
  have hA : MeasurableSet A := measurableSet_Ioc.inter measurableSet_Ico
  have hAfin : volume A ≠ ⊤ := by rw [vol_A]; exact ENNReal.ofReal_ne_top
  have i1 : IntegrableOn (fun _ => (1:ℝ)) A := integrableOn_const hAfin
  have i2 : IntegrableOn (fun s => eps n * (Icc (jd n) (SCal n)).indicator 1 s) A :=
    (i1.indicator measurableSet_Icc).const_mul _
  unfold Dsh
  rw [setIntegral_congr_fun hA (fun s hs => beta_sq n s hs.1), integral_sub i1 i2,
    integral_const_mul, setIntegral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Pi.one_apply]
  rw [setIntegral_const, Measure.real, Measure.real, vol_A, vol_AJ _ _ _ _ (jd_nonneg n),
    ENNReal.toReal_ofReal (lam_nonneg _ _ _ _), ENNReal.toReal_ofReal (lam_nonneg _ _ _ _)]
  simp

/-! ### `𝒫_8` -/

lemma Dsh_eq {P : ℕ} (c : Fin (P + 1) → ℝ) (n : Fin 25) (p : Fin P) :
    Dsh phiNext c n p = lam 0 (SCal n) (c p.castSucc) (c p.succ) -
      eps n * lam (jd n) (SCal n) (c p.castSucc) (c p.succ) := diffusionS c n p

open Novel.DiffusionMeetingCalendarProof in
lemma entry (k p : Fin 8) : lamE8 phiNext k p =
    (lam 0 (SCal (freeIdx k).succ) (cells cEight p.castSucc) (cells cEight p.succ) -
      eps (freeIdx k).succ *
        lam (jd (freeIdx k).succ) (SCal (freeIdx k).succ) (cells cEight p.castSucc) (cells cEight p.succ)) -
    (lam 0 (SCal (freeIdx k).castSucc) (cells cEight p.castSucc) (cells cEight p.succ) -
      eps (freeIdx k).castSucc *
        lam (jd (freeIdx k).castSucc) (SCal (freeIdx k).castSucc) (cells cEight p.castSucc)
          (cells cEight p.succ)) := by
  simp only [lamE8, lamT, Dsh_eq]

lemma eps_zero {n : Fin 25} (h12 : n ≠ 12) (h18 : n ≠ 18) (h24 : n ≠ 24) : eps n = 0 := by
  simp [eps, h12, h18, h24]

open Novel.DiffusionMeetingCalendarProof in
lemma diag : ∀ k : Fin 8, lamE8 phiNext k k = ![14, 28, 28, 28, 35 + w, 28, 35 + w, 28] k / 360 := by
  intro k
  rw [entry]
  fin_cases k <;>
    simp (config := {decide := true}) [freeIdx, eps, jd, w, SCal, gaps, expiries, t0, lam, cells,
      cEight, yr] <;>
    norm_num [max_def, min_def]

lemma lower46 : ∀ k p : Fin 8, (k = 4 ∨ k = 6) → p < k → lamE8 phiNext k p = 0 := by
  intro k p hk hp
  rw [entry]
  rcases hk with rfl | rfl <;> fin_cases p <;> simp (config := {decide := true}) at hp <;>
    simp (config := {decide := true}) [freeIdx, eps, jd, SCal, gaps, expiries, t0, lam, cells,
      cEight, yr] <;> norm_num [max_def, min_def]

lemma eightS : eightStatement := by
  have htri := Novel.MaturityShapeCalendarProof.triangularS phiNext
  refine ⟨fun k p hkp => ?_, diag, ?_⟩
  · rcases lt_or_gt_of_ne hkp with h | h
    · exact Novel.MaturityShapeCalendarProof.upper phiNext k p h
    · by_cases h46 : k = 4 ∨ k = 6
      · exact lower46 k p h46 h
      · push Not at h46
        exact Novel.MaturityShapeCalendarProof.lower_same phiNext k p h46.1 h46.2 h
  · rw [Novel.MaturityShapeCalendarProof.panel_iff _ (Novel.MaturityShapeCalendarProof.Dsh_zero _ _),
      Novel.MaturityShapeCalendarProof.lamTE_iff, Novel.MaturityShapeCalendarProof.lamE8_iff]
    intro k
    rw [diag]
    fin_cases k <;> simp [w] <;> norm_num

/-! ### Other partitions -/

lemma card_free : Nat.card {ℓ : Fin 24 // MeetingFree TCal SCal ℓ} = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight Novel.MaturityShapeCalendarProof.meetingFree_iff)]
  exact (Nat.card_range_of_injective (f := freeIdx) (by decide)).trans (by simp)

/-- The (S2) panel is Claim 046's, less the correction on the stretches `J_n`. -/
lemma panel_rel {P : ℕ} (c : Fin (P + 1) → ℝ) (θ : Fin 16 ⊕ Fin P → ℝ) (ℓ : Fin 24) :
    (panelD TCal SCal (Dsh phiNext c)).mulVec θ ℓ = (panel TCal c SCal).mulVec θ ℓ -
      ∑ p, eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (c p.castSucc) (c p.succ) * θ (Sum.inr p) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, panelD, panel, Sum.elim_inl, Sum.elim_inr,
    Dsh_eq, sub_mul, Finset.sum_sub_distrib]
  ring

open Novel.DiffusionMeetingCalendarProof in
lemma quarter_pair2 : (panelD TCal SCal (Dsh phiNext (cells cQuarter))).mulVec quarterAlt2 =
    (panelD TCal SCal (Dsh phiNext (cells cQuarter))).mulVec (base 8) := by
  funext ℓ
  rw [panel_rel, panel_rel]
  have h046 := congrFun quarter_pair ℓ
  have hsplit : (panel TCal (cells cQuarter) SCal).mulVec quarterAlt2 ℓ =
      (panel TCal (cells cQuarter) SCal).mulVec quarterAlt ℓ +
        (if TCal 15 ≤ SCal ℓ.succ then 1 else 0) * 2 := by
    have e : quarterAlt2 = quarterAlt + Pi.single (Sum.inl 15) 2 := by
      funext k
      rcases k with i | p
      · fin_cases i <;> simp (config := {decide := true}) [quarterAlt2, quarterAlt] <;> norm_num
      · simp [quarterAlt2, quarterAlt]
    rw [e, mulVec_add, Pi.add_apply]
    simp only [mulVec, dotProduct_single, panel, Sum.elim_inl]
  have hcorr : ∀ θ θ' : Fin 16 ⊕ Fin 8 → ℝ, (∀ p, p ≠ 7 → θ (Sum.inr p) = θ' (Sum.inr p)) →
      (∑ p, eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cQuarter p.castSucc)
        (cells cQuarter p.succ) * θ (Sum.inr p)) -
      (∑ p, eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cQuarter p.castSucc)
        (cells cQuarter p.succ) * θ' (Sum.inr p)) =
      eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cQuarter (Fin.castSucc 7))
        (cells cQuarter (Fin.succ 7)) * (θ (Sum.inr 7) - θ' (Sum.inr 7)) := by
    intro θ θ' h
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (7 : Fin 8) (fun p _ hp => by
      rw [h p hp]; ring) (by simp)]
    ring
  have hc := hcorr quarterAlt2 (base 8) (fun p hp => by simp [quarterAlt2, base, hp])
  have hv : quarterAlt2 (Sum.inr 7) - base 8 (Sum.inr 7) = 2860 - 2500 := by
    simp [quarterAlt2, base]
  rw [hv] at hc
  have hrow : (if TCal 15 ≤ SCal ℓ.succ then (1:ℝ) else 0) * 2 =
      eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cQuarter (Fin.castSucc 7))
        (cells cQuarter (Fin.succ 7)) * (2860 - 2500) := by
    fin_cases ℓ <;>
      simp (config := {decide := true}) [TCal, meetings, eps, jd, SCal, gaps, expiries, t0, lam,
        cells, cQuarter, yr] <;> norm_num [max_def, min_def]
  linarith

open Novel.DiffusionMeetingCalendarProof in
lemma meeting_pair2 : (panelD TCal SCal (Dsh phiNext (cells cMeeting))).mulVec meetingAlt =
    (panelD TCal SCal (Dsh phiNext (cells cMeeting))).mulVec (base 17) := by
  funext ℓ
  rw [panel_rel, panel_rel, congrFun meeting_pair ℓ]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p = 2
  · subst hp
    have h0 : eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cMeeting (Fin.castSucc 2))
        (cells cMeeting (Fin.succ 2)) = 0 := by
      fin_cases ℓ <;>
        simp (config := {decide := true}) [eps, jd, SCal, gaps, expiries, t0, lam, cells,
          cMeeting, yr] <;> norm_num [max_def, min_def]
    rw [h0]; ring
  · simp [meetingAlt, base, hp]

open Novel.DiffusionMeetingCalendarProof in
lemma merged_inj : Function.Injective (panelD TCal SCal (Dsh phiNext (cells cMerged))).mulVec := by
  rw [Novel.MaturityShapeCalendarProof.panel_iff _ (Novel.MaturityShapeCalendarProof.Dsh_zero _ _),
    Novel.DiffusionMeetingRankProof.injective_iff_zero]
  intro y hy
  have row : ∀ (ℓ : Fin 24) (h : MeetingFree TCal SCal ℓ),
      (lamTE TCal SCal (Dsh phiNext (cells cMerged))).mulVec y ⟨ℓ, h⟩ =
        ∑ p, ((lam 0 (SCal ℓ.succ) (cells cMerged p.castSucc) (cells cMerged p.succ) -
          eps ℓ.succ * lam (jd ℓ.succ) (SCal ℓ.succ) (cells cMerged p.castSucc) (cells cMerged p.succ)) -
          (lam 0 (SCal ℓ.castSucc) (cells cMerged p.castSucc) (cells cMerged p.succ) -
          eps ℓ.castSucc * lam (jd ℓ.castSucc) (SCal ℓ.castSucc) (cells cMerged p.castSucc)
            (cells cMerged p.succ))) * y p := fun ℓ h => by
    simp only [mulVec, dotProduct, lamTE, lamT, Dsh_eq]
  have ev : ∀ (ℓ : Fin 24) (h : MeetingFree TCal SCal ℓ), _ := fun ℓ h =>
    (row ℓ h).symm.trans (congrFun hy ⟨ℓ, h⟩)
  have e0 := ev 0 free0
  have e2 := ev 2 free2
  have e5 := ev 5 free5
  have e8 := ev 8 free8
  have e12 := ev 12 free12
  have e14 := ev 14 free14
  have e18 := ev 18 free18
  have e20 := ev 20 free20
  simp (config := {decide := true}) only [Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.zero_apply]
    at e0 e2 e5 e8 e12 e14 e18 e20
  norm_num [eps, jd, SCal, gaps, expiries, t0, lam, cells, cMerged, yr, max_def, min_def]
    at e0 e2 e5 e8 e12 e14 e18 e20
  funext p
  fin_cases p <;> simp <;> linarith

lemma cellsS : Standalone.MaturityShapeS2.cellsStatement := by
  refine ⟨fun P c hinj => ?_, merged_inj, ?_, ?_, quarter_pair2, ?_, ?_, meeting_pair2⟩
  · have := (Novel.MaturityShapeRankProof.inversionS 16 P 24 TCal SCal (Dsh phiNext c)
      Novel.DiffusionMeetingCalendarProof.hS hS0 Novel.DiffusionMeetingCalendarProof.hT
      (Novel.MaturityShapeCalendarProof.Dsh_zero _ _)).2 hinj
    rwa [card_free] at this
  · intro h
    have := congrFun h (Sum.inl 13)
    simp [quarterAlt2, base] at this
  · intro k
    rcases k with i | p
    · simp only [quarterAlt2, Sum.elim_inl]; split_ifs <;> norm_num
    · simp only [quarterAlt2, Sum.elim_inr]; split_ifs <;> norm_num
  · exact (Novel.DiffusionMeetingCalendarProof.cellsS).2.2.2.2.2.2.1
  · exact (Novel.DiffusionMeetingCalendarProof.cellsS).2.2.2.2.2.2.2.1

theorem maturityShapeS2 : Standalone.MaturityShapeS2.statement :=
  ⟨betaS, diffusionS, eightS, cellsS⟩

end Novel.MaturityShapeS2Proof

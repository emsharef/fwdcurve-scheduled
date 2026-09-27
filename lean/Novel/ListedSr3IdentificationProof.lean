import Standalone.ListedSr3Identification
import Novel.CompoundedFuturesIdentificationProof
import Novel.BondOptionPriceIntervalsProof
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Finset
open Standalone.ListedSr3Identification

namespace Novel.ListedSr3IdentificationProof

/-! ### The calendar facts, by computation -/

lemma calendar : calendarStatement := by
  unfold calendarStatement meetings expiries quarterStarts gaps t0
  decide

/-! ### (a) the surface identity (22.4) -/

lemma surface : surfaceStatement := by
  intro N τ v S a b hSa hab
  classical
  simp only [Standalone.CompoundedFuturesIdentification.q, qAcc, NNReal.coe_sum,
    Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [CompoundedFuturesIdentificationProof.w_after (h.trans hSa.le) hab, NNReal.coe_mul,
      Real.coe_toNNReal _ (sq_nonneg _)]
    ring
  · simp

/-! ### (b) identification from the accumulated variances -/

section Identification
variable {N L : ℕ} (τ : ℕ → ℝ) (S : Fin (L+1) → ℝ) (δ : Fin (L+1) → ℝ)

lemma gap_difference (hS : StrictMono S) (hδ : ∀ ℓ, 0 < δ ℓ)
    (hgap : ∀ ℓ : Fin L, ∀ i j : Fin N,
      S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
      S ℓ.castSucc < τ (j.val+1) → τ (j.val+1) ≤ S ℓ.succ → i = j)
    (v : Fin N → NNReal) (ℓ : Fin L) (i : Fin N)
    (hi1 : S ℓ.castSucc < τ (i.val+1)) (hi2 : τ (i.val+1) ≤ S ℓ.succ) :
    (v i : ℝ) = qAcc τ v (δ ℓ.succ) (S ℓ.succ)/(δ ℓ.succ)^2 -
      qAcc τ v (δ ℓ.castSucc) (S ℓ.castSucc)/(δ ℓ.castSucc)^2 := by
  classical
  have hle : S ℓ.castSucc ≤ S ℓ.succ := (hS Fin.castSucc_lt_succ).le
  simp only [qAcc]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 (hδ _).ne'),
    mul_div_cancel_left₀ _ (pow_ne_zero 2 (hδ _).ne')]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun m : Fin N => τ (m.val+1) ≤ S ℓ.succ) (fun m => τ (m.val+1) ≤ S ℓ.castSucc)
    (fun m => (v m : ℝ))
  have h1 : (Finset.univ.filter fun m : Fin N => τ (m.val+1) ≤ S ℓ.succ).filter
      (fun m => τ (m.val+1) ≤ S ℓ.castSucc) =
      Finset.univ.filter fun m => τ (m.val+1) ≤ S ℓ.castSucc := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hle, h⟩⟩
  have h2 : (∑ m ∈ (Finset.univ.filter fun m : Fin N => τ (m.val+1) ≤ S ℓ.succ).filter
      (fun m => ¬ τ (m.val+1) ≤ S ℓ.castSucc), (v m : ℝ)) = v i := by
    rw [Finset.sum_eq_single i]
    · intro m hm hmi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hm
      exact absurd (hgap ℓ m i hm.2 hm.1 hi1 hi2) hmi
    · intro h
      exact absurd (by simp [hi1, hi2] : i ∈ _) h
  rw [h1, h2] at hsplit
  linarith

lemma exists_gap (hS : StrictMono S) (x : ℝ) (h0 : S 0 < x) (hL : x ≤ S (Fin.last L)) :
    ∃ ℓ : Fin L, S ℓ.castSucc < x ∧ x ≤ S ℓ.succ := by
  classical
  have hne : (Finset.univ.filter fun m : Fin (L+1) => x ≤ S m).Nonempty :=
    ⟨Fin.last L, by simpa using hL⟩
  set m₀ := (Finset.univ.filter fun m : Fin (L+1) => x ≤ S m).min' hne with hm₀
  have hm₀mem : x ≤ S m₀ := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hm₀ne : m₀ ≠ 0 := by
    intro h
    rw [h] at hm₀mem
    exact absurd hm₀mem (not_le.mpr h0)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin L, ℓ.succ = m₀ := by
    refine ⟨⟨m₀.val - 1, ?_⟩, ?_⟩
    · have := m₀.isLt
      have hpos : 0 < m₀.val := Nat.pos_of_ne_zero (fun h => hm₀ne (Fin.ext h))
      omega
    · ext
      simp only [Fin.val_succ]
      have hpos : 0 < m₀.val := Nat.pos_of_ne_zero (fun h => hm₀ne (Fin.ext h))
      omega
  refine ⟨ℓ, ?_, hℓ ▸ hm₀mem⟩
  by_contra hcon
  have hmem : ℓ.castSucc ∈ Finset.univ.filter fun m : Fin (L+1) => x ≤ S m := by
    simpa using not_lt.mp hcon
  have := Finset.min'_le _ _ hmem
  rw [← hm₀, ← hℓ] at this
  exact absurd this (not_le.mpr Fin.castSucc_lt_succ)

lemma identification : identificationStatement := by
  intro N L τ S δ hS hδ
  refine ⟨fun hgap => ⟨fun v ℓ i hi1 hi2 => gap_difference τ S δ hS hδ hgap v ℓ i hi1 hi2, ?_⟩, ?_⟩
  · intro v v' hq i h0 hL
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_gap S hS _ h0 hL
    apply NNReal.coe_injective
    rw [gap_difference τ S δ hS hδ hgap v ℓ i hℓ1 hℓ2,
      gap_difference τ S δ hS hδ hgap v' ℓ i hℓ1 hℓ2, hq, hq]
  · intro ℓ i j hij hi1 hi2 hj1 hj2
    classical
    refine ⟨fun m => if m = i then 1 else 0, fun m => if m = j then 1 else 0, ?_, ?_⟩
    · intro h
      have := congrFun h i
      simp [hij] at this
    · intro ℓ'
      simp only [qAcc]
      congr 1
      have key : ∀ a : Fin N, (∑ m ∈ Finset.univ.filter (fun m : Fin N => τ (m.val+1) ≤ S ℓ'),
          ((if m = a then (1 : NNReal) else 0 : NNReal) : ℝ)) =
          if τ (a.val+1) ≤ S ℓ' then 1 else 0 := by
        intro a
        have hc : ∀ m : Fin N, ((if m = a then (1 : NNReal) else 0 : NNReal) : ℝ) =
            if m = a then (1 : ℝ) else 0 := by
          intro m; split_ifs <;> simp
        simp only [hc, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      rw [key i, key j]
      have hiff : τ (i.val+1) ≤ S ℓ' ↔ τ (j.val+1) ≤ S ℓ' := by
        rcases le_or_gt ℓ' ℓ.castSucc with h | h
        · have hS' : S ℓ' ≤ S ℓ.castSucc := hS.monotone h
          exact iff_of_false (not_le.mpr (hS'.trans_lt hi1)) (not_le.mpr (hS'.trans_lt hj1))
        · have hS' : S ℓ.succ ≤ S ℓ' := hS.monotone (Fin.castSucc_lt_iff_succ_le.mp h)
          exact iff_of_true (hi2.trans hS') (hj2.trans hS')
      simp only [hiff]

end Identification

/-! ### (c) the precision arithmetic -/

section Precision
open Standalone.CompoundedFuturesIdentification (C0177 Φ q0178)
open Standalone.BondOptionPriceIntervals (φ0167 y0167 H0162 k0167)
open Novel.BondOptionPriceIntervalsProof (H_deriv H_mono H_nonneg y_nonneg)

/-- `q0178 m` is Claim 016's `H0162 1` at the price scaled by the forward. -/
lemma q0178_eq_H (m : ℝ) : q0178 m = fun c => H0162 1 (c / m) := by
  funext c
  simp only [q0178, H0162, y0167, one_pow, div_one]
  rfl

lemma amp_of_sq (m y : ℝ) (hy : 0 ≤ y) : amp m (4 * y^2) = 4 * y / (m * φ0167 y) := by
  have hs : Real.sqrt (4 * y^2) = 2 * y := by
    rw [show (4 : ℝ) * y^2 = (2 * y)^2 by ring]
    exact Real.sqrt_sq (by linarith)
  unfold amp
  rw [hs, show (2 * y) / 2 = y by ring]
  ring

lemma φ0167_pos (y : ℝ) : 0 < φ0167 y := by
  unfold φ0167
  positivity

lemma q0178_deriv {m c : ℝ} (hm : 0 < m) (hc : c ∈ Set.Ico 0 m) :
    HasDerivAt (q0178 m) (amp m (q0178 m c)) c := by
  have hcm : c / m ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by have := div_nonneg hc.1 hm.le; linarith, (div_lt_one hm).2 hc.2⟩
  have hcm' : c / m ∈ Set.Ico (0 : ℝ) 1 := ⟨div_nonneg hc.1 hm.le, (div_lt_one hm).2 hc.2⟩
  have h := (H_deriv hcm 1).comp c ((hasDerivAt_id c).div_const m)
  have hfun : (H0162 1 ∘ fun x => id x / m) = q0178 m := by
    funext x
    simp [q0178_eq_H]
  rw [hfun] at h
  have hval : k0167 1 (c / m) * (1 / m) = amp m (q0178 m c) := by
    rw [show q0178 m c = 4 * (y0167 (c / m))^2 by rw [q0178_eq_H]; simp [H0162],
      amp_of_sq m _ (y_nonneg hcm')]
    have := φ0167_pos (y0167 (c / m))
    simp only [k0167, one_pow, one_mul]
    field_simp
  rw [hval] at h
  exact h

lemma φ0167_antitone {y y' : ℝ} (hy : 0 ≤ y) (hyy' : y ≤ y') : φ0167 y' ≤ φ0167 y := by
  unfold φ0167
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine Real.exp_le_exp.2 ?_
  nlinarith

lemma amp_mono {m q q' : ℝ} (hm : 0 < m) (hq : 0 ≤ q) (hqq' : q ≤ q') : amp m q ≤ amp m q' := by
  unfold amp
  have hs : Real.sqrt q ≤ Real.sqrt q' := Real.sqrt_le_sqrt hqq'
  refine div_le_div₀ (by positivity) (by linarith) (mul_pos hm (φ0167_pos _)) ?_
  exact mul_le_mul_of_nonneg_left
    (φ0167_antitone (by positivity) (by linarith)) hm.le

lemma q0178_mono {m : ℝ} (hm : 0 < m) : MonotoneOn (q0178 m) (Set.Ico 0 m) := by
  intro a ha b hb hab
  rw [q0178_eq_H]
  have ha' : a / m ∈ Set.Ico (0 : ℝ) 1 := ⟨div_nonneg ha.1 hm.le, (div_lt_one hm).2 ha.2⟩
  have hb' : b / m ∈ Set.Ico (0 : ℝ) 1 := ⟨div_nonneg hb.1 hm.le, (div_lt_one hm).2 hb.2⟩
  exact (H_mono one_pos).monotoneOn ha' hb' (div_le_div_of_nonneg_right hab hm.le)

lemma q0178_nonneg (m c : ℝ) : 0 ≤ q0178 m c := by
  rw [q0178_eq_H]
  exact H_nonneg _ _

lemma q0178_meanValue {m c c' : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hcc' : c ≤ c') (hc' : c' < m) :
    |q0178 m c' - q0178 m c| ≤ amp m (q0178 m c') * (c' - c) := by
  have hc'' : c' ∈ Set.Ico 0 m := ⟨hc.trans hcc', hc'⟩
  have hsub : Set.Icc c c' ⊆ Set.Ico 0 m := fun x hx => ⟨hc.trans hx.1, hx.2.trans_lt hc'⟩
  have hmono : q0178 m c ≤ q0178 m c' := q0178_mono hm ⟨hc, hcc'.trans_lt hc'⟩ hc'' hcc'
  rw [abs_of_nonneg (by linarith)]
  refine (convex_Icc c c').image_sub_le_mul_sub_of_deriv_le ?_ ?_ ?_ c ⟨le_rfl, hcc'⟩ c'
    ⟨hcc', le_rfl⟩ hcc'
  · exact fun x hx => (q0178_deriv hm (hsub hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (q0178_deriv hm (hsub (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' := hsub (Set.Ioo_subset_Icc_self hx)
    rw [(q0178_deriv hm hx').deriv]
    exact amp_mono hm (q0178_nonneg m x) (q0178_mono hm hx' hc'' hx.2.le)

lemma precision : precisionStatement := by
  intro m hm
  refine ⟨fun R => ⟨?_, CompoundedFuturesIdentificationProof.C0177_recover_q hm R⟩,
    fun c hc => q0178_deriv hm hc, fun q q' hq hqq' => amp_mono hm hq hqq',
    fun c c' hc hcc' hc' => q0178_meanValue hm hc hcc' hc', ?_⟩
  · have h := CompoundedFuturesIdentificationProof.C0177_at_mean hm R
    rw [div_eq_iff hm.ne'] at h
    rw [h]
    ring
  · intro N L τ S δ hS hδ hone v v' ℓ i h1 h2
    obtain ⟨hrec, -⟩ := identification N L τ S δ hS hδ
    have hv := (hrec hone).1 v ℓ i h1 h2
    have hv' := (hrec hone).1 v' ℓ i h1 h2
    rw [hv, hv']
    have hd1 : 0 < (δ ℓ.succ)^2 := pow_pos (hδ _) 2
    have hd2 : 0 < (δ ℓ.castSucc)^2 := pow_pos (hδ _) 2
    rw [show qAcc τ v (δ ℓ.succ) (S ℓ.succ) / (δ ℓ.succ)^2 -
        qAcc τ v (δ ℓ.castSucc) (S ℓ.castSucc) / (δ ℓ.castSucc)^2 -
        (qAcc τ v' (δ ℓ.succ) (S ℓ.succ) / (δ ℓ.succ)^2 -
          qAcc τ v' (δ ℓ.castSucc) (S ℓ.castSucc) / (δ ℓ.castSucc)^2) =
        (qAcc τ v (δ ℓ.succ) (S ℓ.succ) - qAcc τ v' (δ ℓ.succ) (S ℓ.succ)) / (δ ℓ.succ)^2 -
        (qAcc τ v (δ ℓ.castSucc) (S ℓ.castSucc) - qAcc τ v' (δ ℓ.castSucc) (S ℓ.castSucc)) /
          (δ ℓ.castSucc)^2 by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_div, abs_of_pos hd1, abs_of_pos hd2]

end Precision

/-! ### The calendar instantiation of (b) and the reduced listing -/

section Calendar

lemma τCal_succ (i : Fin 16) : τCal (i.val+1) = ((meetings.getD i.val 0 : ℕ) : ℝ) := by
  simp [τCal]

lemma SFull_strictMono : StrictMono SFull := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [SFull, gaps, expiries, t0]

lemma SRed_strictMono : StrictMono SRed := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [SRed, reducedGaps, reducedExpiries, t0]

/-- At most one meeting per gap of the full calendar, in the index form of (b). -/
lemma full_one_per_gap : ∀ ℓ : Fin 24, ∀ i j : Fin 16,
    SFull ℓ.castSucc < τCal (i.val+1) → τCal (i.val+1) ≤ SFull ℓ.succ →
    SFull ℓ.castSucc < τCal (j.val+1) → τCal (j.val+1) ≤ SFull ℓ.succ → i = j := by
  intro ℓ i j h1 h2 h3 h4
  rw [τCal_succ] at h1 h2 h3 h4
  simp only [SFull] at h1 h2 h3 h4
  have h1' := Nat.cast_lt.mp h1
  have h2' := Nat.cast_le.mp h2
  have h3' := Nat.cast_lt.mp h3
  have h4' := Nat.cast_le.mp h4
  clear h1 h2 h3 h4
  revert h1' h2' h3' h4'
  revert i j ℓ
  decide

lemma calendarIdentification : calendarIdentificationStatement := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · intro v v' heq
    obtain ⟨hrec, -⟩ := identification 16 24 τCal SFull (fun _ => 91/360) SFull_strictMono
      (fun _ => by norm_num)
    funext i
    refine (hrec full_one_per_gap).2 v v' heq i ?_ ?_
    · rw [τCal_succ]
      simp only [SFull, Fin.val_zero]
      have : (2 : ℕ) < meetings.getD i.val 0 := by
        revert i; decide
      simp [gaps, t0]
      exact_mod_cast this
    · rw [τCal_succ]
      simp only [SFull, Fin.val_last]
      have : meetings.getD i.val 0 ≤ 709 := by
        revert i; decide
      simp [gaps, expiries]
      exact_mod_cast this
  · obtain ⟨-, hpair⟩ := identification 16 12 τCal SRed (fun _ => 91/360) SRed_strictMono
      (fun _ => by norm_num)
    refine hpair ⟨6, by norm_num⟩ ⟨3, by norm_num⟩ ⟨4, by norm_num⟩ (by decide) ?_ ?_ ?_ ?_ <;>
      (rw [τCal_succ]; norm_num [SRed, reducedGaps, reducedExpiries, t0, meetings])

end Calendar

/-! ### (d) the futures rows -/

section FuturesRows
open Standalone.CompoundedFuturesIdentification (h w d)

lemma h_before (a b T : ℝ) (hT : T ≤ a) (hab : a ≤ b) : h a b T = (b - a) * (b - T) := by
  unfold h d w
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma h_inside (a b T : ℝ) (haT : a < T) (hTb : T ≤ b) : h a b T = (b - T)^2 := by
  unfold h d w
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

lemma h_after (a b T : ℝ) (hab : a ≤ b) (hbT : b < T) : h a b T = 0 := by
  unfold h d w
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma futuresRow : futuresRowStatement := by
  refine ⟨h_before, h_inside, h_after, ?_⟩
  intro hLate hFirst Δp
  have hL : hLate = (7/360)^2 := by
    show h (623/360) (714/360) (707/360) = (7/360)^2
    rw [h_inside _ _ _ (by norm_num) (by norm_num)]
    norm_num
  have hF : hFirst = (91/360) * (686/360) := by
    show h (623/360) (714/360) (28/360) = (91/360) * (686/360)
    rw [h_before _ _ _ (by norm_num) (by norm_num)]
    norm_num
  have hΔ : Δp = (91/360) * (1/2) * (1/10000) := rfl
  refine ⟨hL, hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, hF]; norm_num
  · rw [hΔ]; norm_num
  · rw [hΔ]; norm_num
  · rw [hΔ, hL]; norm_num
  · rw [hΔ, hL]; norm_num
  · rw [hΔ, hL]
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [hΔ, hL]
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num

end FuturesRows

/-! ### The thresholds of the rule (22.10) -/

section Thresholds
open Standalone.BondOptionPriceIntervals (φ0167)

lemma coef_eq : 2 / φ0167 0 = 2 * Real.sqrt (2 * Real.pi) := by
  unfold φ0167
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  simp only [neg_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero]
  field_simp

lemma sqrt_two_pi_bounds : 2.5065 < Real.sqrt (2 * Real.pi) ∧ Real.sqrt (2 * Real.pi) < 2.5067 := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.pi_lt_d4
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]
    nlinarith

lemma sqrt_bounds (x lo hi : ℝ) (hlo : 0 ≤ lo) (h1 : lo^2 < x) (h2 : x < hi^2) (hhi : 0 < hi) :
    lo < Real.sqrt x ∧ Real.sqrt x < hi :=
  ⟨(Real.lt_sqrt hlo).2 h1, (Real.sqrt_lt' hhi).2 h2⟩

lemma sqrt_sq_nat (k : ℕ) : Real.sqrt ((k : ℝ)^2) = k := Real.sqrt_sq (Nat.cast_nonneg k)

lemma ratio_eq (ε s0 : ℝ) (n : ℕ) :
    ratio ε s0 n = 2 * Real.sqrt (2 * Real.pi) * (ε / s0) *
      (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) := by
  rw [ratio, coef_eq]

lemma ratio_mono (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) : Monotone (fun n : ℕ => ratio ε s0 n) := by
  intro n m hnm
  simp only [ratio_eq]
  have hc : 0 ≤ 2 * Real.sqrt (2 * Real.pi) * (ε / s0) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnm)
  have h2 : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt ((m : ℝ) - 1) :=
    Real.sqrt_le_sqrt (sub_le_sub_right (Nat.cast_le.mpr hnm) 1)
  linarith

lemma threshold : thresholdStatement := by
  obtain ⟨hp1, hp2⟩ := sqrt_two_pi_bounds
  have h5 := sqrt_bounds 5 2.236 2.2361 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := sqrt_bounds 3 1.732 1.7321 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := sqrt_bounds 10 3.1622 3.1623 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := sqrt_bounds 8 2.8284 2.8285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := sqrt_bounds 15 3.8729 3.873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h9 : Real.sqrt 9 = 3 := by rw [show (9 : ℝ) = 3^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hs2 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hA1 : Real.sqrt (2 * Real.pi) * (2 + Real.sqrt 3) < 2.5067 * (2 + 1.7321) :=
    mul_lt_mul'' hp2 (by linarith [h3.2]) hs2 (by positivity)
  have hA2 : 2.5065 * (2 + 2.236) < Real.sqrt (2 * Real.pi) * (2 + Real.sqrt 5) :=
    mul_lt_mul'' hp1 (by linarith [h5.1]) (by norm_num) (by norm_num)
  have hA3 : Real.sqrt (2 * Real.pi) * (3 + Real.sqrt 8) < 2.5067 * (3 + 2.8285) :=
    mul_lt_mul'' hp2 (by linarith [h8.2]) hs2 (by positivity)
  have hA4 : 2.5065 * (3 + 3.1622) < Real.sqrt (2 * Real.pi) * (3 + Real.sqrt 10) :=
    mul_lt_mul'' hp1 (by linarith [h10.1]) (by norm_num) (by norm_num)
  have hA5 : Real.sqrt (2 * Real.pi) * (4 + Real.sqrt 15) < 2.5067 * (4 + 3.873) :=
    mul_lt_mul'' hp2 (by linarith [h15.2]) hs2 (by positivity)
  have hA6 : 2.5065 * (4 + 3.8729) < Real.sqrt (2 * Real.pi) * (4 + Real.sqrt 15) :=
    mul_lt_mul'' hp1 (by linarith [h15.1]) (by norm_num) (by norm_num)
  refine ⟨coef_eq, ⟨by rw [coef_eq]; linarith, by rw [coef_eq]; linarith⟩, ratio_mono,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  all_goals rw [ratio_eq]
  all_goals simp only [Nat.cast_ofNat]
  · rw [show ((4 : ℝ) - 1) = 3 by norm_num, h4]; nlinarith [hA1]
  · rw [show ((5 : ℝ) - 1) = 4 by norm_num, h4]; nlinarith [hA2]
  · rw [show ((9 : ℝ) - 1) = 8 by norm_num, h9]; nlinarith [hA3]
  · rw [show ((10 : ℝ) - 1) = 9 by norm_num, h9]; nlinarith [hA4]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA6]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]

end Thresholds

/-! ### The ℓ² form of the propagated bound -/

section EllTwo

/-- Telescoping: the partial sums of the recovered increments give back `q`. -/
lemma recover_telescope (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (q : Fin (n+1) → ℝ) (hq0 : q 0 = 0)
    (ℓ : Fin (n+1)) :
    q ℓ = δ^2 * ∑ i : Fin n, if i.val < ℓ.val then recover n δ q i else 0 := by
  classical
  have hδ2 : δ^2 ≠ 0 := by positivity
  have key : ∀ m : ℕ, ∀ hm : m ≤ n, q ⟨m, by omega⟩ =
      δ^2 * ∑ i : Fin n, if i.val < m then recover n δ q i else 0 := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hq0]
    | succ m ih =>
      intro hm
      have hsplit : (∑ i : Fin n, if i.val < m + 1 then recover n δ q i else 0) =
          (∑ i : Fin n, if i.val < m then recover n δ q i else 0) + recover n δ q ⟨m, by omega⟩ := by
        rw [← Finset.sum_add_sum_compl {(⟨m, by omega⟩ : Fin n)}]
        rw [← Finset.sum_add_sum_compl {(⟨m, by omega⟩ : Fin n)}
          (f := fun i : Fin n => if i.val < m then recover n δ q i else 0)]
        simp only [Finset.sum_singleton, lt_self_iff_false, if_false, zero_add,
          Nat.lt_succ_self, if_true]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_compl, Finset.mem_singleton] at hi
        have : i.val ≠ m := fun h => hi (Fin.ext h)
        by_cases h : i.val < m
        · simp [h, Nat.lt_succ_of_lt h]
        · have h' : ¬ i.val < m + 1 := by omega
          simp [h, h']
      rw [hsplit, mul_add, ← ih (by omega)]
      simp only [recover]
      rw [mul_div_cancel₀ _ hδ2]
      have e1 : (⟨m, by omega⟩ : Fin n).succ = ⟨m+1, by omega⟩ := rfl
      have e2 : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := rfl
      rw [e1, e2]
      ring
  exact key ℓ.val (by omega : ℓ.val ≤ n)

lemma ellTwo : ellTwoStatement := by
  intro n δ hδ q q' hq0 hq0'
  refine ⟨recover_telescope n δ hδ q hq0, ?_⟩
  have hδ2 : 0 < δ^2 := by positivity
  set a : Fin (n+1) → ℝ := fun ℓ => q ℓ - q' ℓ with ha
  have hrec : ∀ i : Fin n, recover n δ q i - recover n δ q' i = (a i.succ - a i.castSucc) / δ^2 := by
    intro i
    simp only [recover, ha]
    ring
  simp only [hrec]
  have hterm : ∀ i : Fin n, ((a i.succ - a i.castSucc) / δ^2)^2 ≤
      (2 * (a i.succ)^2 + 2 * (a i.castSucc)^2) / (δ^2)^2 := by
    intro i
    rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [sq_nonneg (a i.succ + a i.castSucc)]
  calc (∑ i : Fin n, ((a i.succ - a i.castSucc) / δ^2)^2)
      ≤ ∑ i : Fin n, (2 * (a i.succ)^2 + 2 * (a i.castSucc)^2) / (δ^2)^2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (2 * ∑ i : Fin n, (a i.succ)^2 + 2 * ∑ i : Fin n, (a i.castSucc)^2) / (δ^2)^2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (2 * ∑ ℓ : Fin (n+1), (a ℓ)^2 + 2 * ∑ ℓ : Fin (n+1), (a ℓ)^2) / (δ^2)^2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h1 : ∑ i : Fin n, (a i.succ)^2 ≤ ∑ ℓ : Fin (n+1), (a ℓ)^2 := by
          rw [Fin.sum_univ_succ]
          linarith [sq_nonneg (a 0)]
        have h2 : ∑ i : Fin n, (a i.castSucc)^2 ≤ ∑ ℓ : Fin (n+1), (a ℓ)^2 := by
          rw [Fin.sum_univ_castSucc]
          linarith [sq_nonneg (a (Fin.last n))]
        linarith
    _ = (2 / δ^2)^2 * ∑ ℓ, (q ℓ - q' ℓ)^2 := by
        simp only [ha]
        field_simp
        ring

end EllTwo

/-! ### The displayed values of (22.6) -/

section SingularValues

lemma sigmaK_last : sigmaK 16 16 = (91/360 : ℝ)^2 / (2 * Real.cos (Real.pi / 33)) := by
  unfold sigmaK
  have : (2 * ((16 : ℕ) : ℝ) - 1) * Real.pi / (2 * (2 * ((16 : ℕ) : ℝ) + 1)) =
      Real.pi / 2 - Real.pi / 33 := by
    push_cast
    ring
  rw [this, Real.sin_pi_div_two_sub]

lemma sigmaK_first : sigmaK 16 1 = (91/360 : ℝ)^2 / (2 * Real.sin (Real.pi / 66)) := by
  unfold sigmaK
  congr 3
  push_cast
  ring

lemma cos_pi_div_33_bounds :
    0.99546 < Real.cos (Real.pi / 33) ∧ Real.cos (Real.pi / 33) < 0.99548 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  set x := Real.pi / 33 with hx
  have hx1 : 0.09519 < x := by rw [hx]; linarith
  have hx2 : x < 0.09521 := by rw [hx]; linarith
  have hlow := Real.one_sub_sq_div_two_lt_cos (x := x) (by rw [hx]; positivity)
  have hb := Real.cos_bound (show |x| ≤ 1 by rw [abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (show (0 : ℝ) < x by linarith)] at hb
  have hup : Real.cos x ≤ 1 - x^2/2 + x^4 * (5/96) := by
    have := (abs_le.mp hb).2
    linarith
  constructor
  · nlinarith
  · nlinarith [pow_le_pow_left₀ (by linarith) hx2.le 4, pow_le_pow_left₀ (by linarith) hx1.le 2]

lemma sin_pi_div_66_bounds :
    0.04758 < Real.sin (Real.pi / 66) ∧ Real.sin (Real.pi / 66) < 0.04760 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  set x := Real.pi / 66 with hx
  have hx1 : 0.047598 < x := by rw [hx]; linarith
  have hx2 : x < 0.047600 := by rw [hx]; linarith
  have hlow := Real.sin_gt_sub_cube (x := x) (by rw [hx]; positivity)
  have hup := Real.sin_lt (x := x) (by rw [hx]; positivity)
  constructor
  · nlinarith [pow_le_pow_left₀ (by linarith) hx2.le 3]
  · linarith

lemma singularValue : singularValueStatement := by
  obtain ⟨hc1, hc2⟩ := cos_pi_div_33_bounds
  obtain ⟨hs1, hs2⟩ := sin_pi_div_66_bounds
  have hcpos : 0 < Real.cos (Real.pi / 33) := by linarith
  have hspos : 0 < Real.sin (Real.pi / 66) := by linarith
  have hκ : sigmaK 16 1 / sigmaK 16 16 = Real.cos (Real.pi / 33) / Real.sin (Real.pi / 66) := by
    rw [sigmaK_first, sigmaK_last]
    field_simp
  refine ⟨sigmaK_last, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [sigmaK_last, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [sigmaK_last, div_lt_iff₀ (by positivity)]; nlinarith
  · rw [sigmaK_first, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [sigmaK_first, div_lt_iff₀ (by positivity)]; nlinarith
  · rw [hκ, lt_div_iff₀ hspos]
    nlinarith
  · rw [hκ, div_lt_iff₀ hspos]
    nlinarith

end SingularValues

/-! ### The singular values of the lower triangular matrix of ones -/

section Eigen
open Matrix

lemma Dmat_apply (n : ℕ) (i j : Fin n) :
    Dmat n i j = (if j = i then 1 else 0) - (if j.val + 1 = i.val then 1 else 0) := by
  unfold Dmat
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ j = i := fun e => h e.symm
    simp only [h, h', if_false, zero_sub]
    by_cases h2 : j.val + 1 = i.val <;> simp [h2]

/-- A sum over `Fin n` of a term supported at the index of value `c`. -/
lemma sum_ite_val (n : ℕ) (f : Fin n → ℝ) (c : ℕ) :
    (∑ m : Fin n, if m.val = c then f m else 0) = if h : c < n then f ⟨c, h⟩ else 0 := by
  by_cases h : c < n
  · rw [dif_pos h, Finset.sum_eq_single ⟨c, h⟩]
    · simp
    · intro m _ hm
      have : m.val ≠ c := fun e => hm (Fin.ext e)
      simp [this]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun m _ => ?_
    have : m.val ≠ c := fun e => h (e ▸ m.isLt)
    simp [this]

lemma Dmat_mulVec (n : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    (Dmat n).mulVec y i = y i - (if h : 0 < i.val then y ⟨i.val - 1, by omega⟩ else 0) := by
  simp only [mulVec, dotProduct, Dmat_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul]
  congr 1
  · rw [Finset.sum_ite_eq' Finset.univ i]
    simp
  · have : (∑ m : Fin n, if m.val + 1 = i.val then y m else 0) =
        ∑ m : Fin n, if m.val = i.val - 1 then (if 0 < i.val then y m else 0) else 0 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, sum_ite_val]
    by_cases h : 0 < i.val
    · have h' : i.val - 1 < n := by have := i.isLt; omega
      simp [h, h']
    · simp [h]

lemma Dmat_transpose_mulVec (n : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    (Dmat n).transpose.mulVec y i = y i - (if h : i.val + 1 < n then y ⟨i.val + 1, h⟩ else 0) := by
  simp only [mulVec, dotProduct, transpose_apply, Dmat_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul]
  congr 1
  · rw [Finset.sum_ite_eq Finset.univ i]
    simp
  · have : (∑ m : Fin n, if i.val + 1 = m.val then y m else 0) =
        ∑ m : Fin n, if m.val = i.val + 1 then y m else 0 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, sum_ite_val]

lemma Lmat_apply (n : ℕ) (i j : Fin n) : Lmat n i j = if j ≤ i then 1 else 0 := rfl

lemma Lmat_mul_Dmat (n : ℕ) : Lmat n * Dmat n = 1 := by
  ext i j
  have : (Lmat n * Dmat n) i j = (Dmat n).transpose.mulVec (fun m => Lmat n i m) j := by
    simp only [mul_apply, mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [this, Dmat_transpose_mulVec]
  simp only [Lmat_apply, one_apply]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    by_cases hlt : j.val + 1 < n
    · rw [dif_pos hlt]
      by_cases hle : (⟨j.val + 1, hlt⟩ : Fin n) ≤ i
      · rw [if_pos hle]
        have h2 : j.val + 1 ≤ i.val := hle
        have : ¬ i = j := fun e => by subst e; omega
        simp [this]
      · rw [if_neg hle]
        have : i = j := by
          apply Fin.ext
          have h1 : j.val ≤ i.val := hji
          have h2 : ¬ j.val + 1 ≤ i.val := fun h => hle h
          omega
        simp [this]
    · rw [dif_neg hlt]
      have : i = j := by
        apply Fin.ext
        have h1 : j.val ≤ i.val := hji
        have := i.isLt
        omega
      simp [this]
  · rw [if_neg hji]
    have hne : ¬ i = j := fun e => hji (e ▸ le_rfl)
    simp only [hne, if_false, zero_sub, neg_eq_zero]
    by_cases hlt : j.val + 1 < n
    · rw [dif_pos hlt]
      have h3 : ¬ j.val ≤ i.val := fun h => hji h
      have : ¬ (⟨j.val + 1, hlt⟩ : Fin n) ≤ i := fun h => by
        have h4 : j.val + 1 ≤ i.val := h
        omega
      simp [this]
    · simp [hlt]

lemma Dmat_mul_Lmat (n : ℕ) : Dmat n * Lmat n = 1 := by
  ext i j
  have : (Dmat n * Lmat n) i j = (Dmat n).mulVec (fun m => Lmat n m j) i := by
    simp only [mul_apply, mulVec, dotProduct]
  rw [this, Dmat_mulVec]
  simp only [Lmat_apply, one_apply]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    by_cases hpos : 0 < i.val
    · rw [dif_pos hpos]
      by_cases hle : j ≤ (⟨i.val - 1, by omega⟩ : Fin n)
      · rw [if_pos hle]
        have h2 : j.val ≤ i.val - 1 := hle
        have : ¬ i = j := fun e => by subst e; omega
        simp [this]
      · rw [if_neg hle]
        have : i = j := by
          apply Fin.ext
          have h1 : j.val ≤ i.val := hji
          have h2 : ¬ j.val ≤ i.val - 1 := fun h => hle h
          omega
        simp [this]
    · rw [dif_neg hpos]
      have : i = j := by
        apply Fin.ext
        have h1 : j.val ≤ i.val := hji
        omega
      simp [this]
  · rw [if_neg hji]
    have hne : ¬ i = j := fun e => hji (e ▸ le_rfl)
    simp only [hne, if_false, zero_sub, neg_eq_zero]
    by_cases hpos : 0 < i.val
    · rw [dif_pos hpos]
      have h3 : ¬ j.val ≤ i.val := fun h => hji h
      have : ¬ j ≤ (⟨i.val - 1, by omega⟩ : Fin n) := fun h => by
        have h4 : j.val ≤ i.val - 1 := h
        omega
      simp [this]
    · simp [hpos]

lemma θ22_pos (n k : ℕ) : 0 < θ22 n k := by unfold θ22; positivity

lemma θ22_lt_pi (n : ℕ) (k : Fin n) : θ22 n k < Real.pi := by
  unfold θ22
  rw [div_lt_iff₀ (by positivity)]
  have := k.isLt
  have : (k : ℝ) + 1 ≤ n := by exact_mod_cast this
  nlinarith [Real.pi_pos]

/-- The boundary identity `sin((n+1)θ_k) = sin(nθ_k)`. -/
lemma sin_boundary (n k : ℕ) : Real.sin (((n : ℝ) + 1) * θ22 n k) = Real.sin ((n : ℝ) * θ22 n k) := by
  rw [← sub_eq_zero, Real.sin_sub_sin]
  have hc : Real.cos ((((n : ℝ) + 1) * θ22 n k + (n : ℝ) * θ22 n k) / 2) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨k, ?_⟩
    unfold θ22
    field_simp
    push_cast
    ring
  rw [hc]
  ring

/-- The interior three-term identity. -/
lemma sin_three_term (θ a : ℝ) :
    2 * Real.sin (a * θ) - Real.sin ((a - 1) * θ) - Real.sin ((a + 1) * θ) =
      (2 - 2 * Real.cos θ) * Real.sin (a * θ) := by
  have h : Real.sin ((a - 1) * θ) + Real.sin ((a + 1) * θ) = 2 * Real.sin (a * θ) * Real.cos θ := by
    rw [Real.sin_add_sin, show ((a - 1) * θ + (a + 1) * θ) / 2 = a * θ by ring,
      show ((a - 1) * θ - (a + 1) * θ) / 2 = -θ by ring, Real.cos_neg]
  linarith

lemma eigen_D (n : ℕ) (hn : 0 < n) (k : Fin n) :
    ((Dmat n).transpose * Dmat n).mulVec (xvec n k) = lam22 n k • xvec n k := by
  rw [← mulVec_mulVec]
  funext i
  rw [Dmat_transpose_mulVec, Pi.smul_apply, smul_eq_mul]
  simp only [Dmat_mulVec]
  set θ := θ22 n k with hθ
  -- the value of `x` at index `i`, with `x_{−1} = 0` and `x_n = x_{n−1}` at the ends
  have hx : ∀ j : Fin n, xvec n k j = Real.sin (((j.val : ℝ) + 1) * θ) := fun j => rfl
  by_cases hlt : i.val + 1 < n
  · rw [dif_pos hlt]
    simp only [hx, dif_pos (show 0 < i.val + 1 by omega)]
    by_cases hpos : 0 < i.val
    · rw [dif_pos hpos]
      have e1 : ((⟨i.val - 1, by omega⟩ : Fin n).val : ℝ) + 1 = ((i.val : ℝ) + 1) - 1 := by
        simp only; push_cast [Nat.cast_sub hpos]; ring
      have e2 : ((⟨i.val + 1, hlt⟩ : Fin n).val : ℝ) + 1 = ((i.val : ℝ) + 1) + 1 := by
        simp only; push_cast; ring
      have e3 : ((⟨i.val + 1 - 1, by omega⟩ : Fin n).val : ℝ) + 1 = (i.val : ℝ) + 1 := by
        simp only [Nat.add_sub_cancel]
      rw [e1, e2, e3]
      have := sin_three_term θ ((i.val : ℝ) + 1)
      unfold lam22
      rw [← hθ]
      linarith
    · have hi0 : i.val = 0 := by omega
      rw [dif_neg hpos]
      have e2 : ((⟨i.val + 1, hlt⟩ : Fin n).val : ℝ) + 1 = ((i.val : ℝ) + 1) + 1 := by
        simp only; push_cast; ring
      have e3 : ((⟨i.val + 1 - 1, by omega⟩ : Fin n).val : ℝ) + 1 = (i.val : ℝ) + 1 := by
        simp only [Nat.add_sub_cancel]
      rw [e2, e3]
      have := sin_three_term θ ((i.val : ℝ) + 1)
      have h0 : Real.sin (((i.val : ℝ) + 1 - 1) * θ) = 0 := by
        rw [hi0]; simp
      unfold lam22
      rw [← hθ]
      linarith
  · rw [dif_neg hlt]
    have hi : i.val + 1 = n := by have := i.isLt; omega
    simp only [hx]
    by_cases hpos : 0 < i.val
    · rw [dif_pos hpos]
      have e1 : ((⟨i.val - 1, by omega⟩ : Fin n).val : ℝ) + 1 = ((i.val : ℝ) + 1) - 1 := by
        simp only; push_cast [Nat.cast_sub hpos]; ring
      rw [e1]
      have h3 := sin_three_term θ ((i.val : ℝ) + 1)
      have hb : Real.sin (((i.val : ℝ) + 1 + 1) * θ) = Real.sin (((i.val : ℝ) + 1) * θ) := by
        have := sin_boundary n k
        rw [← hθ] at this
        have hn' : (n : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hi.symm
        rw [hn'] at this
        exact this
      unfold lam22
      rw [← hθ]
      linarith
    · rw [dif_neg hpos]
      have hi0 : i.val = 0 := by omega
      have hn1 : n = 1 := by omega
      have h3 := sin_three_term θ ((i.val : ℝ) + 1)
      have hb : Real.sin (((i.val : ℝ) + 1 + 1) * θ) = Real.sin (((i.val : ℝ) + 1) * θ) := by
        have := sin_boundary n k
        rw [← hθ] at this
        have hn' : (n : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hi.symm
        rw [hn'] at this
        exact this
      have h0 : Real.sin (((i.val : ℝ) + 1 - 1) * θ) = 0 := by rw [hi0]; simp
      unfold lam22
      rw [← hθ]
      linarith

lemma lam22_pos (n : ℕ) (k : Fin n) : 0 < lam22 n k := by
  unfold lam22
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (θ22_lt_pi n k).le (θ22_pos n k)
  rw [Real.cos_zero] at this
  linarith

lemma lam22_eq (n k : ℕ) : lam22 n k = 4 * Real.sin (θ22 n k / 2)^2 := by
  unfold lam22
  have := Real.sin_sq_eq_half_sub (θ22 n k / 2)
  rw [show 2 * (θ22 n k / 2) = θ22 n k by ring] at this
  linarith

lemma xvec_ne_zero (n : ℕ) (hn : 0 < n) (k : Fin n) : xvec n k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, hn⟩
  simp only [xvec, Pi.zero_apply, Nat.cast_zero, zero_add, one_mul] at h0
  exact (Real.sin_pos_of_pos_of_lt_pi (θ22_pos n k) (θ22_lt_pi n k)).ne' h0

lemma eigen_L (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (Lmat n * (Lmat n).transpose).mulVec (xvec n k) = (1 / lam22 n k) • xvec n k := by
  have hlam := lam22_pos n k
  have hinv : (Lmat n * (Lmat n).transpose) * ((Dmat n).transpose * Dmat n) = 1 := by
    have h1 : (Lmat n).transpose * (Dmat n).transpose = 1 := by
      rw [← transpose_mul, Dmat_mul_Lmat, transpose_one]
    calc (Lmat n * (Lmat n).transpose) * ((Dmat n).transpose * Dmat n)
        = Lmat n * ((Lmat n).transpose * (Dmat n).transpose) * Dmat n := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Lmat_mul_Dmat]
  have h := congrArg (fun v => (Lmat n * (Lmat n).transpose).mulVec v) (eigen_D n hn k)
  simp only [mulVec_mulVec, hinv, one_mulVec, mulVec_smul] at h
  have h2 := congrArg (fun v => (1 / lam22 n k) • v) h
  simp only [smul_smul, one_div, inv_mul_cancel₀ hlam.ne', one_smul] at h2
  rw [one_div]; exact h2.symm

lemma lam22_strictMono (n : ℕ) : StrictMono (fun k : Fin n => lam22 n k) := by
  intro a b hab
  simp only [lam22]
  have hθ : θ22 n a < θ22 n b := by
    unfold θ22
    have : (a : ℝ) < b := by exact_mod_cast hab
    have hd : 0 < 2 * (n : ℝ) + 1 := by positivity
    apply div_lt_div_of_pos_right _ hd
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (θ22_pos n a).le (θ22_lt_pi n b).le hθ
  linarith

lemma eigen : eigenStatement := by
  intro n hn
  refine ⟨Lmat_mul_Dmat n, Dmat_mul_Lmat n, fun k => ⟨lam22_pos n k, lam22_eq n k, xvec_ne_zero n hn k,
    eigen_D n hn k, eigen_L n hn k⟩, lam22_strictMono n, fun k => ?_⟩
  rw [lam22_eq]
  have hs : 0 < Real.sin (θ22 16 k / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := θ22_pos 16 k; linarith
    · have := θ22_lt_pi 16 k; linarith [Real.pi_pos]
  have hθ : θ22 16 k / 2 = (2 * (k : ℝ) + 1) * Real.pi / 66 := by unfold θ22; ring
  rw [hθ] at hs ⊢
  field_simp
  ring

end Eigen

/-! ### The exact expression (22.8) at the stated sizes -/

section ExactPrecision
open Standalone.BondOptionPriceIntervals (φ0167)

/-- The argument `y_k = δ s_0 √k / 2` of the density in the `k`-th term. -/
noncomputable def yk (s0 : ℝ) (k : ℕ) : ℝ := δ26 * (s0 * 1e-4) * Real.sqrt k / 2

lemma δ26_pos : 0 < δ26 := by unfold δ26; norm_num

lemma yk_nonneg (s0 : ℝ) (hs0 : 0 ≤ s0) (k : ℕ) : 0 ≤ yk s0 k := by
  unfold yk; have := δ26_pos; positivity

lemma exactTerm_eq (ε s0 : ℝ) (hs0 : 0 < s0) (k : ℕ) :
    exactTerm ε s0 k = 2 * Real.sqrt k * (ε / s0) / φ0167 (yk s0 k) := by
  have hsq : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
  have hq : δ26^2 * k * (s0 * 1e-4)^2 = 4 * (yk s0 k)^2 := by
    unfold yk
    linear_combination (-(δ26^2 * (s0 * 1e-4)^2)) * hsq
  unfold exactTerm
  rw [hq, amp_of_sq 1 _ (yk_nonneg s0 hs0.le k), one_mul]
  have hφ := φ0167_pos (yk s0 k)
  have hδ := δ26_pos
  unfold yk at hφ ⊢
  field_simp
  ring

lemma ratio_eq_terms (ε s0 : ℝ) (n : ℕ) :
    ratio ε s0 n = 2 * Real.sqrt n * (ε / s0) / φ0167 0 +
      2 * Real.sqrt ((n - 1 : ℕ) : ℝ) * (ε / s0) / φ0167 0 := by
  unfold ratio
  have : Real.sqrt ((n : ℝ) - 1) = Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    rcases n with _ | n
    · simp only [Nat.cast_zero, zero_sub, Nat.zero_sub, Real.sqrt_zero]
      exact Real.sqrt_eq_zero'.mpr (by norm_num)
    · simp
  rw [this]; ring

lemma term_lower (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) (k : ℕ) :
    2 * Real.sqrt k * (ε / s0) / φ0167 0 ≤ exactTerm ε s0 k := by
  rw [exactTerm_eq ε s0 hs0]
  have hy := yk_nonneg s0 hs0.le k
  have h1 := φ0167_antitone (le_refl 0) hy
  have h2 := φ0167_pos (yk s0 k)
  have hnum : 0 ≤ 2 * Real.sqrt k * (ε / s0) := by positivity
  exact div_le_div_of_nonneg_left hnum h2 h1

/-- Near zero the density is within a factor `1 + 2·10⁻⁶` of its value at zero. -/
lemma inv_φ_le (y : ℝ) (hy2 : y^2 ≤ 2e-6) : 1 / φ0167 y ≤ (1 + 2e-6) * (1 / φ0167 0) := by
  unfold φ0167
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have he : 1 - y^2/2 ≤ Real.exp (-y^2/2) := by
    have := Real.add_one_le_exp (-y^2/2); linarith
  have hex := Real.exp_pos (-y^2/2)
  simp only [neg_zero, zero_pow two_ne_zero, zero_div, Real.exp_zero, one_div_div, div_one]
  rw [div_le_iff₀ hex]
  have h1 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (1 + 2e-6) * Real.sqrt (2 * Real.pi))
  have h2 := mul_le_mul_of_nonneg_left hy2 hs.le
  nlinarith

lemma term_upper (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) (hs25 : s0 ≤ 25) (k : ℕ) (hk : k ≤ 16) :
    exactTerm ε s0 k ≤ (1 + 2e-6) * (2 * Real.sqrt k * (ε / s0) / φ0167 0) := by
  rw [exactTerm_eq ε s0 hs0]
  have hy2 : (yk s0 k)^2 ≤ 2e-6 := by
    unfold yk δ26
    have hsq : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
    have hk16 : (k : ℝ) ≤ 16 := by exact_mod_cast hk
    have h0 : 0 ≤ s0 := hs0.le
    calc (91/360 * (s0 * 1e-4) * Real.sqrt k / 2)^2
        = (91/360)^2 * (s0 * 1e-4)^2 * k / 4 := by
          linear_combination ((91/360)^2 * (s0 * 1e-4)^2 / 4) * hsq
      _ ≤ (91/360)^2 * (25 * 1e-4)^2 * 16 / 4 := by gcongr
      _ ≤ 2e-6 := by norm_num
  have hnum : 0 ≤ 2 * Real.sqrt k * (ε / s0) := by positivity
  have := inv_φ_le (yk s0 k) hy2
  calc 2 * Real.sqrt k * (ε / s0) / φ0167 (yk s0 k)
      = (2 * Real.sqrt k * (ε / s0)) * (1 / φ0167 (yk s0 k)) := by ring
    _ ≤ (2 * Real.sqrt k * (ε / s0)) * ((1 + 2e-6) * (1 / φ0167 0)) :=
        mul_le_mul_of_nonneg_left this hnum
    _ = (1 + 2e-6) * (2 * Real.sqrt k * (ε / s0) / φ0167 0) := by ring

lemma exactTerm_mono (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) :
    Monotone (fun k : ℕ => exactTerm ε s0 k) := by
  intro a b hab
  simp only [exactTerm_eq ε s0 hs0]
  have hsa : Real.sqrt (a : ℝ) ≤ Real.sqrt b := Real.sqrt_le_sqrt (by exact_mod_cast hab)
  have hya : yk s0 a ≤ yk s0 b := by
    unfold yk
    have hδ := δ26_pos
    have h0 := hs0.le
    gcongr
  have hφ := φ0167_antitone (yk_nonneg s0 hs0.le a) hya
  have hpb := φ0167_pos (yk s0 b)
  have hnum : 0 ≤ 2 * Real.sqrt a * (ε / s0) := by positivity
  calc 2 * Real.sqrt a * (ε / s0) / φ0167 (yk s0 a)
      ≤ 2 * Real.sqrt a * (ε / s0) / φ0167 (yk s0 b) := div_le_div_of_nonneg_left hnum hpb hφ
    _ ≤ 2 * Real.sqrt b * (ε / s0) / φ0167 (yk s0 b) := by
        have h0 : 0 ≤ ε / s0 := by positivity
        gcongr

lemma exactRatio_mono (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) :
    Monotone (fun n : ℕ => exactRatio ε s0 n) := by
  intro n m hnm
  simp only [exactRatio]
  exact add_le_add (exactTerm_mono ε s0 hε hs0 hnm)
    (exactTerm_mono ε s0 hε hs0 (Nat.sub_le_sub_right hnm 1))

lemma ratio_le_exactRatio (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) (n : ℕ) :
    ratio ε s0 n ≤ exactRatio ε s0 n := by
  rw [ratio_eq_terms]
  exact add_le_add (term_lower ε s0 hε hs0 n) (term_lower ε s0 hε hs0 (n - 1))

lemma exactRatio_le (ε s0 : ℝ) (hε : 0 ≤ ε) (hs0 : 0 < s0) (hs25 : s0 ≤ 25) (n : ℕ)
    (hn : n ≤ 16) : exactRatio ε s0 n ≤ (1 + 2e-6) * ratio ε s0 n := by
  rw [ratio_eq_terms, mul_add]
  exact add_le_add (term_upper ε s0 hε hs0 hs25 n hn)
    (term_upper ε s0 hε hs0 hs25 (n - 1) (by omega))

/-- Numeric upper bounds on the rule's ratio with room for the factor `1 + 2·10⁻⁶`. -/
lemma ratio_num_bounds :
    ratio (1/2) 10 4 < 0.936 ∧ ratio (1/2) 15 9 < 0.975 ∧ ratio (1/2) 25 16 < 0.79 ∧
    ratio (1/4) 10 16 < 0.987 ∧ ratio (1/4) 15 16 < 0.66 ∧ ratio (1/4) 25 16 < 0.4 := by
  obtain ⟨hp1, hp2⟩ := sqrt_two_pi_bounds
  have h3 := sqrt_bounds 3 1.732 1.7321 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := sqrt_bounds 8 2.8284 2.8285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := sqrt_bounds 15 3.8729 3.873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h9 : Real.sqrt 9 = 3 := by rw [show (9 : ℝ) = 3^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hs2 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hA1 : Real.sqrt (2 * Real.pi) * (2 + Real.sqrt 3) < 2.5067 * (2 + 1.7321) :=
    mul_lt_mul'' hp2 (by linarith [h3.2]) hs2 (by positivity)
  have hA3 : Real.sqrt (2 * Real.pi) * (3 + Real.sqrt 8) < 2.5067 * (3 + 2.8285) :=
    mul_lt_mul'' hp2 (by linarith [h8.2]) hs2 (by positivity)
  have hA5 : Real.sqrt (2 * Real.pi) * (4 + Real.sqrt 15) < 2.5067 * (4 + 3.873) :=
    mul_lt_mul'' hp2 (by linarith [h15.2]) hs2 (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [ratio_eq]
  all_goals simp only [Nat.cast_ofNat]
  · rw [show ((4 : ℝ) - 1) = 3 by norm_num, h4]; nlinarith [hA1]
  · rw [show ((9 : ℝ) - 1) = 8 by norm_num, h9]; nlinarith [hA3]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]
  · rw [show ((16 : ℝ) - 1) = 15 by norm_num, h16]; nlinarith [hA5]

lemma exactPrecision : exactPrecisionStatement := by
  refine ⟨fun ε s0 n hε hs0 => ratio_le_exactRatio ε s0 hε hs0 n,
    fun ε s0 n hε hs0 hs25 hn => exactRatio_le ε s0 hε hs0 hs25 n hn,
    fun ε s0 hε hs0 => exactRatio_mono ε s0 hε hs0, ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ratio_num_bounds
  obtain ⟨_, _, _, ⟨_, t2⟩, ⟨_, t4⟩, _, ⟨t7, _⟩, _, _⟩ := threshold
  have U1 := exactRatio_le (1/2) 10 (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num)
  have L2 := ratio_le_exactRatio (1/2) 10 (by norm_num) (by norm_num) 5
  have U3 := exactRatio_le (1/2) 15 (by norm_num) (by norm_num) (by norm_num) 9 (by norm_num)
  have L4 := ratio_le_exactRatio (1/2) 15 (by norm_num) (by norm_num) 10
  have U5 := exactRatio_le (1/2) 25 (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  have L7 := ratio_le_exactRatio (1/4) 10 (by norm_num) (by norm_num) 16
  have U7 := exactRatio_le (1/4) 10 (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  have U8 := exactRatio_le (1/4) 15 (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  have U9 := exactRatio_le (1/4) 25 (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

end ExactPrecision

theorem listedSr3Identification : Standalone.ListedSr3Identification.statement :=
  ⟨calendar, surface, identification, precision, calendarIdentification, futuresRow, threshold,
    ellTwo, singularValue, eigen, exactPrecision⟩

end Novel.ListedSr3IdentificationProof

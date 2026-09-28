import Standalone.MaturityNull
import Novel.UnifiedSpliceStep0Proof
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Claim 051: one exceptional set for all maturities (proof)

Step 1 intersects (H2) at the positive rational maturities with (H1), a countable intersection
of almost-everywhere statements (`ae_all_iff`). Step 2 passes from the rationals to every maturity
by continuity of the primitives (`integrated_at`). Step 3 differentiates the identity at a
continuity point (`diff_at`), and (b′) finds the open maturity interval around `T`
(`interval_nhds`).

Reused, not reproved: `Novel.UnifiedSpliceStep0Proof.prod_Icc` (`Q ⊗ dt` on `Ω × [0, T]` as a
restriction) and `Novel.UnifiedSpliceStep0Proof.rat_closure` (the rationals are dense in
`[u, H]`), which Claim 049's Step 0 uses for its specific coefficients.
-/

open MeasureTheory Set Filter Topology
open Standalone.MaturityNull
open Novel.UnifiedSpliceStep0Proof (prod_Icc rat_closure)

namespace Novel.MaturityNullProof

variable {Ω : Type} {d : ℕ}

/-- `Q ⊗ dt` on `Ω × [0, ∞)` as a restriction of `Q ⊗ dt`. -/
lemma prod_Ici [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ] :
    μ.prod (volume.restrict (Ici (0 : ℝ))) = (μ.prod volume).restrict (univ ×ˢ Ici 0) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

section Path
variable (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) (t : ℝ)

/-- Step 2: (51.1) at every maturity of `[t, T]` from (51.1) at the rationals of `(t, T)`,
given integrability on `[t, T]`. -/
lemma integrated_at {T : ℝ} (htT : t ≤ T)
    (hα : IntegrableOn (fun u => α t u ω) (Icc t T))
    (hσ : IntegrableOn (fun u => σ t u ω) (Icc t T))
    (hq : ∀ ρ : ℚ, t < ρ → (ρ : ℝ) < T → driftAt α σ ω t ρ) :
    driftAt α σ ω t T := by
  rcases htT.eq_or_lt with rfl | hlt
  · simp [driftAt]
  have hαi : IntervalIntegrable (fun u => α t u ω) volume t T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le htT).2 hα
  have hσi : IntervalIntegrable (fun u => σ t u ω) volume t T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le htT).2 hσ
  have hF : ContinuousOn (fun T => ∫ u in t..T, α t u ω) (Icc t T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hαi left_mem_uIcc
    rwa [uIcc_of_le htT] at this
  have hS : ContinuousOn (fun T => ∫ u in t..T, σ t u ω) (Icc t T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hσi left_mem_uIcc
    rwa [uIcc_of_le htT] at this
  have hEq : EqOn (fun T => ∫ u in t..T, α t u ω)
      (fun T => (1 / 2 : ℝ) * ‖∫ u in t..T, σ t u ω‖ ^ 2) (Icc t T) := by
    refine EqOn.of_subset_closure (s := Ioo t T ∩ range ((↑) : ℚ → ℝ)) ?_ hF
      (continuousOn_const.mul (hS.norm.pow 2))
      (inter_subset_left.trans Ioo_subset_Icc_self) (rat_closure hlt)
    rintro x ⟨hx, ρ, rfl⟩
    exact hq ρ hx.1 hx.2
  exact hEq (right_mem_Icc.2 htT)

/-- Step 3: (51.2) at a continuity point `T` of both maturity sections, when (51.1) holds on a
neighbourhood `(t, T')` of `T` and the sections are integrable on `[t, T']`. -/
lemma diff_at {T T' : ℝ} (htT : t < T) (hTT' : T < T')
    (hα : IntegrableOn (fun u => α t u ω) (Icc t T'))
    (hσ : IntegrableOn (fun u => σ t u ω) (Icc t T'))
    (hid : ∀ y ∈ Ioo t T', driftAt α σ ω t y)
    (hαc : ContinuousAt (fun u => α t u ω) T) (hσc : ContinuousAt (fun u => σ t u ω) T) :
    diffDriftAt α σ ω t T := by
  have hsub : Icc t T ⊆ Icc t T' := Icc_subset_Icc_right hTT'.le
  have hnhds : Ioo t T' ∈ 𝓝 T := isOpen_Ioo.mem_nhds ⟨htT, hTT'⟩
  have hF : HasDerivAt (fun y => ∫ u in t..y, α t u ω) (α t T ω) T :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Icc_of_le htT.le).2 (hα.mono_set hsub))
      ⟨Ioo t T', hnhds, (hα.mono_set Ioo_subset_Icc_self).aestronglyMeasurable⟩ hαc
  have hS : HasDerivAt (fun y => ∫ u in t..y, σ t u ω) (σ t T ω) T :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Icc_of_le htT.le).2 (hσ.mono_set hsub))
      ⟨Ioo t T', hnhds, (hσ.mono_set Ioo_subset_Icc_self).aestronglyMeasurable⟩ hσc
  have hG : HasDerivAt (fun y => (1 / 2 : ℝ) * ‖∫ u in t..y, σ t u ω‖ ^ 2)
      ((1 / 2 : ℝ) * (2 * inner ℝ (∫ u in t..T, σ t u ω) (σ t T ω))) T :=
    hS.norm_sq.const_mul _
  have hev : (fun y => ∫ u in t..y, α t u ω) =ᶠ[𝓝 T]
      (fun y => (1 / 2 : ℝ) * ‖∫ u in t..y, σ t u ω‖ ^ 2) := by
    filter_upwards [hnhds] with y hy using hid y hy
  have := hF.unique (hG.congr_of_eventuallyEq hev)
  rw [diffDriftAt, this, real_inner_comm]
  ring

end Path

/-- (b′)'s bookkeeping: a maturity `T > 0` other than `T_1, …, T_n` has an open maturity
interval around it on which a function continuous inside each interval is continuous. -/
lemma interval_nhds {f : ℝ → ℝ} {g : ℝ → EuclideanSpace ℝ (Fin d)} (n : ℕ) (τ : ℕ → ℝ)
    (hτ0 : τ 0 = 0) (hk : ∀ k < n, ContinuousOn f (Ioo (τ k) (τ (k + 1))) ∧
      ContinuousOn g (Ioo (τ k) (τ (k + 1))))
    (hf : ContinuousOn f (Ioi (τ n))) (hg : ContinuousOn g (Ioi (τ n)))
    {T : ℝ} (hT : 0 < T) (hne : ∀ i, 1 ≤ i → i ≤ n → T ≠ τ i) :
    ContinuousAt f T ∧ ContinuousAt g T := by
  by_cases hn : τ n < T
  · have h := isOpen_Ioi.mem_nhds (mem_Ioi.2 hn)
    exact ⟨hf.continuousAt h, hg.continuousAt h⟩
  have hex : ∃ k, k < n ∧ T < τ (k + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd (hτ0 ▸ hT) hn
    refine ⟨n - 1, Nat.sub_lt hpos one_pos, ?_⟩
    rw [show n - 1 + 1 = n by omega]
    exact (not_lt.1 hn).lt_of_ne (hne n hpos le_rfl)
  classical
  set k := Nat.find hex
  obtain ⟨hkn, hkT⟩ := Nat.find_spec hex
  have hlow : τ k < T := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, hτ0]; exact hT
    have hmin := Nat.find_min hex (show k - 1 < k from Nat.sub_lt hpos one_pos)
    rw [show k - 1 + 1 = k by omega] at hmin
    have hle : τ k ≤ T := by
      by_contra h
      exact hmin ⟨(Nat.sub_le k 1).trans_lt hkn, not_le.1 h⟩
    exact hle.lt_of_ne (hne k hpos hkn.le).symm
  have h := isOpen_Ioo.mem_nhds ⟨hlow, hkT⟩
  exact ⟨(hk k hkn).1.continuousAt h, (hk k hkn).2.continuousAt h⟩

/-- Steps 1–3 off one null set: (a), and (51.2) at every maturity `t < T < H` where both maturity
sections are continuous. -/
lemma main [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal)
    (hint : hypIntegrable μ α σ H) (hdrift : hypDrift μ α σ H) :
    ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), integratedAt α σ H p ∧
      ∀ T : ℝ, p.2 < T → (T : EReal) < H →
        ContinuousAt (fun u => α p.2 u p.1) T → ContinuousAt (fun u => σ p.2 u p.1) T →
        diffDriftAt α σ p.1 p.2 T := by
  -- Step 1: (H2) at every positive rational maturity `ρ ≤ H`, off one null set
  have hρ : ∀ ρ : ℚ, ∀ᵐ p ∂(μ.prod volume), p ∈ (univ : Set Ω) ×ˢ Ici (0 : ℝ) →
      0 < (ρ : ℝ) → ((ρ : ℝ) : EReal) ≤ H → p.2 ≤ ρ → driftAt α σ p.1 p.2 ρ := fun ρ => by
    by_cases h : 0 < (ρ : ℝ) ∧ ((ρ : ℝ) : EReal) ≤ H
    · have := hdrift ρ h.1 h.2
      rw [prod_Icc, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)] at this
      filter_upwards [this] with p hp hmem _ _ hle
      exact hp ⟨mem_univ _, hmem.2, hle⟩
    · exact Eventually.of_forall fun _ _ h1 h2 => absurd ⟨h1, h2⟩ h
  have hs : MeasurableSet ((univ : Set Ω) ×ˢ Ici (0 : ℝ)) := MeasurableSet.univ.prod measurableSet_Ici
  rw [hypIntegrable, prod_Ici, ae_restrict_iff' hs] at hint
  rw [prod_Ici, ae_restrict_iff' hs]
  filter_upwards [ae_all_iff.2 hρ, hint] with p hq hi hmem
  have ht0 : (0 : ℝ) ≤ p.2 := hmem.2
  -- Step 2: every maturity in `[t, H]`
  have ha : integratedAt α σ H p := by
    intro htH T htT hTH
    obtain ⟨hα, hσ⟩ := hi hmem htH T htT hTH
    refine integrated_at α σ p.1 p.2 htT hα hσ fun ρ htρ hρT => ?_
    exact hq ρ hmem (ht0.trans_lt htρ) ((EReal.coe_le_coe_iff.2 hρT.le).trans hTH) htρ.le
  refine ⟨ha, fun T htT hTH hαc hσc => ?_⟩
  -- Step 3: a maturity `T' ∈ (T, H]`, then differentiate
  obtain ⟨T', hTT', hT'H⟩ := EReal.lt_iff_exists_real_btwn.1 hTH
  have hTT' : T < T' := EReal.coe_lt_coe_iff.1 hTT'
  have htH : (p.2 : EReal) ≤ H := (EReal.coe_le_coe_iff.2 (htT.trans hTT').le).trans hT'H.le
  obtain ⟨hα, hσ⟩ := hi hmem htH T' (htT.trans hTT').le hT'H.le
  refine diff_at α σ p.1 p.2 htT hTT' hα hσ (fun y hy => ?_) hαc hσc
  exact ha htH y hy.1.le ((EReal.coe_le_coe_iff.2 hy.2.le).trans hT'H.le)

theorem integrated : integratedStatement := by
  intro Ω _ μ _ d α σ H _ hint hdrift
  filter_upwards [main μ α σ H hint hdrift] with p hp using hp.1

theorem differentiated : differentiatedStatement := by
  intro Ω _ μ _ d α σ H _ hint hdrift
  exact main μ α σ H hint hdrift

theorem interval : intervalStatement := by
  intro Ω _ μ _ d α σ H n τ hτ0 _ _ hint hdrift
  have h0 : ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), (0 : ℝ) ≤ p.2 := by
    rw [prod_Ici]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ici)] with p hp
    exact hp.2
  filter_upwards [main μ α σ H hint hdrift, h0] with p hp ht0
  refine ⟨hp.1, fun hk hf hg T htT hTH hne => ?_⟩
  obtain ⟨hαc, hσc⟩ := interval_nhds n τ hτ0 hk hf hg (ht0.trans_lt htT) hne
  exact hp.2 T htT hTH hαc hσc

theorem maturityNull : Standalone.MaturityNull.statement :=
  ⟨integrated, differentiated, interval⟩

end Novel.MaturityNullProof

import Standalone.SpliceLocalizationConverse
import Novel.UnifiedSpliceConverseAX01Proof

open Matrix NormedSpace MeasureTheory Set
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse
open Novel.UnifiedSpliceQuantifiersProof (nS_const nS_step prim_lin)
open Novel.UnifiedSpliceConverseAX01Proof (nS_mono same_free)
namespace Novel.SpliceLocalizationConverseProof

variable {k r : ℕ}

lemma ite_pos' {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma ite_neg' {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-! ### The front end's primitive, explicitly -/

/-- `P(u, T) = T V_{n(T)} − u V_{n(u)} − Σ_{τ ∈ S, u < τ ≤ T} τ (V_{n(τ)} − V_{n(τ)−1})`. -/
lemma primK (S : Finset ℝ) (p : Pt049 k r) (u : ℝ) :
    ∀ T, u ≤ T → prim049 S p u T = T • p.V (nS S T) - u • p.V (nS S u) -
      ∑ τ ∈ S, if u < τ ∧ τ ≤ T then τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0 := by
  classical
  suffices ∀ N T, (S.filter fun τ => u < τ ∧ τ ≤ T).card = N → u ≤ T →
      prim049 S p u T = T • p.V (nS S T) - u • p.V (nS S u) -
        ∑ τ ∈ S, if u < τ ∧ τ ≤ T then τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0 from
    fun T h => this _ T rfl h
  have hP0 : prim049 S p u u = 0 := by funext l; simp [prim049]
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hN huT
  set M := S.filter fun τ => u < τ ∧ τ ≤ T
  by_cases hM : M.Nonempty
  · set τ := M.max' hM
    have hτM := M.max'_mem hM
    simp only [M, Finset.mem_filter] at hτM
    have hfreeR : ∀ τ' ∈ S, τ' ∉ Ioo τ T := fun τ' hτ' hI => by
      have : τ' ≤ τ := M.le_max' τ' (by simp [M, hτ', hτM.2.1.trans hI.1, hI.2.le])
      linarith [hI.1]
    have hTτ : nS S T = nS S τ :=
      nS_const S hτM.2.2 fun τ' hτ' hI => by
        rcases eq_or_lt_of_le hI.2 with h | h
        · subst h; linarith [hI.1, M.le_max' τ' (by simp [M, hτ', hτM.2.1.trans hI.1])]
        · exact hfreeR τ' hτ' ⟨hI.1, h⟩
    set M' := S.filter fun τ' => u < τ' ∧ τ' < τ
    set w : ℝ := if h : M'.Nonempty then M'.max' h else u
    have hw : u ≤ w ∧ w < τ ∧ ∀ τ' ∈ S, τ' ∉ Ioo w τ := by
      by_cases h : M'.Nonempty
      · have hwM := M'.max'_mem h
        simp only [M', Finset.mem_filter] at hwM
        refine ⟨by simp only [w, h, ↓reduceDIte]; exact hwM.2.1.le,
          by simp only [w, h, ↓reduceDIte]; exact hwM.2.2, fun τ' hτ' hI => ?_⟩
        simp only [w, h, ↓reduceDIte] at hI
        have : τ' ≤ M'.max' h := M'.le_max' τ' (by simp [M', hτ', hwM.2.1.trans hI.1, hI.2])
        linarith [hI.1]
      · refine ⟨by simp [w, h], by simp [w, h]; exact hτM.2.1, fun τ' hτ' hI => ?_⟩
        simp only [w, h, ↓reduceDIte] at hI
        exact h ⟨τ', by simp [M', hτ', hI.1, hI.2]⟩
    obtain ⟨huw, hwτ, hfreeL⟩ := hw
    have hstep : nS S w = nS S τ - 1 := nS_step S hτM.1 hwτ hfreeL
    have hPT := prim_lin S p u hτM.2.2 hfreeR
    have hPτ := prim_lin S p u hwτ.le hfreeL
    have hIH := ih ((S.filter fun τ' => u < τ' ∧ τ' ≤ w).card) (by
      rw [← hN]
      refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨τ, ?_, ?_⟩)
      · simp only [M, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.1, hx.2.2.trans (hwτ.le.trans hτM.2.2)⟩
      · simp only [M, Finset.mem_filter]; exact hτM
      · simp only [Finset.mem_filter, not_and, not_le]; exact fun _ _ => hwτ) w rfl huw
    have hsum : (∑ τ' ∈ S, if u < τ' ∧ τ' ≤ T then τ' • (p.V (nS S τ') - p.V (nS S τ' - 1))
        else 0) = (∑ τ' ∈ S, if u < τ' ∧ τ' ≤ w then τ' • (p.V (nS S τ') - p.V (nS S τ' - 1))
        else 0) + τ • (p.V (nS S τ) - p.V (nS S τ - 1)) := by
      have hsing : τ • (p.V (nS S τ) - p.V (nS S τ - 1)) = ∑ τ' ∈ S,
          if τ' = τ then τ' • (p.V (nS S τ') - p.V (nS S τ' - 1)) else 0 := by
        rw [Finset.sum_eq_single τ (fun b _ hb => by rw [ite_neg' (hb)])
          (fun h => absurd hτM.1 h), ite_pos' (rfl)]
      rw [hsing, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ' hτ' => ?_
      by_cases h1 : u < τ' ∧ τ' ≤ w
      · have : τ' ≠ τ := fun h => by subst h; linarith [h1.2]
        rw [ite_pos' (⟨h1.1, h1.2.trans (hwτ.le.trans hτM.2.2)⟩), ite_pos' (h1), ite_neg' (this), add_zero]
      · rw [ite_neg' (h1), zero_add]
        by_cases h2 : τ' = τ
        · subst h2; rw [ite_pos' (⟨hτM.2.1, hτM.2.2⟩), ite_pos' (rfl)]
        · rw [ite_neg' (h2), ite_eq_right_iff]
          rintro ⟨h3, h4⟩
          exfalso
          rcases lt_trichotomy τ' τ with h5 | h5 | h5
          · exact h1 ⟨h3, not_lt.1 fun h6 => hfreeL τ' hτ' ⟨h6, h5⟩⟩
          · exact h2 h5
          · rcases eq_or_lt_of_le h4 with h6 | h6
            · subst h6; linarith [M.le_max' τ' (by simp [M, hτ', h3])]
            · exact hfreeR τ' hτ' ⟨h5, h6⟩
    rw [hPT, hPτ, hIH, hsum, hTτ, hstep]
    funext l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have hfree : ∀ τ ∈ S, τ ∉ Ioc u T := fun τ hτ hI => hM ⟨τ, by simp [M, hτ, hI.1, hI.2]⟩
    have hn : nS S T = nS S u := nS_const S huT hfree
    have hz : (∑ τ ∈ S, if u < τ ∧ τ ≤ T then τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0) =
        0 := Finset.sum_eq_zero fun τ hτ => by
      rw [ite_eq_right_iff]; exact fun h => absurd h (hfree τ hτ)
    rw [prim_lin S p u huT fun τ hτ hI => hfree τ hτ ⟨hI.1, hI.2.le⟩, hP0, hn, hz]
    funext l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_add, Pi.zero_apply]
    ring

/-- A meeting after `T` has a larger index. -/
lemma nS_lt (S : Finset ℝ) {T τ : ℝ} (hτ : τ ∈ S) (h : T < τ) : nS S T < nS S τ := by
  unfold nS
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨τ, ?_, ?_⟩)
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h.le⟩
  · simp only [Finset.mem_filter]; exact ⟨hτ, le_rfl⟩
  · simp only [Finset.mem_filter, not_and, not_le]; exact fun _ => h

/-- Off the meetings, `P(u, T) = T V_{n(T)} + κ_{n(T)}`. -/
lemma prim_kap (S : Finset ℝ) (p : Pt049 k r) {u T : ℝ} (huT : u ≤ T) :
    prim049 S p u T = T • p.V (nS S T) + kap050 S p u (nS S T) := by
  rw [primK S p u T huT, kap050]
  have hs : (∑ τ ∈ S, if u < τ ∧ τ ≤ T then τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0) =
      ∑ τ ∈ S, if u < τ ∧ nS S τ ≤ nS S T then τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0 :=
    Finset.sum_congr rfl fun τ hτ => by
      congr 1
      exact propext ⟨fun h => ⟨h.1, nS_mono S h.2⟩,
        fun h => ⟨h.1, not_lt.1 fun h' => absurd h.2 (not_le.2 (nS_lt S hτ h'))⟩⟩
  rw [hs]
  funext l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (c): the explicit converse -/

lemma explicitS : explicitStatement := by
  intro k r d c A hA S H u p hu0 huH huS h492 ⟨α, β, hR⟩ T hT
  have hα : alpha050 c A d S p u = α := by rw [alpha050, hR]; ring
  have hβ : beta050 c A d S p u = β := by rw [beta050, hR, hR]; ring
  have h := Novel.UnifiedSpliceConverseAX01Proof.converse_kappa hA p hu0 huH huS h492
    (α := α) (β := β) (fun x => hR x) (kap050 S p u)
    (fun T' hT' _ => prim_kap S p hT'.1.le) T hT
  have e1 : dL050 c A d S p u = Novel.UnifiedSpliceConverseAX01Proof.dLk S p u α β (kap050 S p u) :=
    funext fun m => by
      rw [dL050, Novel.UnifiedSpliceConverseAX01Proof.dLk, hα, hβ]
  have e2 : dC050 c A d S p u = Novel.UnifiedSpliceConverseAX01Proof.dCk S p u β :=
    funext fun m => by rw [dC050, Novel.UnifiedSpliceConverseAX01Proof.dCk, hβ]
  rw [e1, e2]
  exact h

/-! ### (c): local integrability -/

section Int
variable {H : ℝ}

local notation "μI" => (volume.restrict (Icc (0:ℝ) H))

lemma bdd_u : ∀ᵐ u ∂μI, ‖u‖ ≤ |H| := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact hu.2.trans (le_abs_self H)

/-- A multiplier bounded on `[0, H]` keeps `L²`. -/
lemma L2_mul {f g : ℝ → ℝ} (hf : MemLp f 2 μI) (hg : AEStronglyMeasurable g μI) {C : ℝ}
    (hC : ∀ᵐ u ∂μI, ‖g u‖ ≤ C) : MemLp (fun u => g u * f u) 2 μI :=
  hf.of_le_mul (hg.mul hf.aestronglyMeasurable) (by
    filter_upwards [hC] with u hu
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hu (norm_nonneg _))

lemma L2_umul {f : ℝ → ℝ} (hf : MemLp f 2 μI) : MemLp (fun u => u * f u) 2 μI :=
  L2_mul hf measurable_id.aestronglyMeasurable (bdd_u (H := H))

lemma int_umul {f : ℝ → ℝ} (hf : Integrable f μI) : Integrable (fun u => u * f u) μI :=
  hf.bdd_mul measurable_id.aestronglyMeasurable (bdd_u (H := H))

/-- The dot product of two `L²` rows is integrable (Cauchy–Schwarz). -/
lemma dot_int {x y : ℝ → Fin k → ℝ} (hx : ∀ l, MemLp (fun u => x u l) 2 μI)
    (hy : ∀ l, MemLp (fun u => y u l) 2 μI) : Integrable (fun u => x u ⬝ᵥ y u) μI := by
  simp only [dotProduct]
  exact integrable_finsetSum _ fun l _ => (hx l).integrable_mul (hy l)

lemma L2_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 μI) :
    MemLp (fun u => ∑ i ∈ s, f i u) 2 μI := memLp_finsetSum s hf

/-- The current noise `V_{n(u)}(u)` is `L²`. -/
lemma L2_cur (S : Finset ℝ) (D : ℝ → Pt049 k r)
    (hV : ∀ m ≤ S.card, ∀ l, MemLp (fun u => (D u).V m l) 2 μI) (l : Fin k) :
    MemLp (fun u => (D u).V (nS S u) l) 2 μI := by
  have e : (fun u => (D u).V (nS S u) l) = fun u => ∑ m ∈ Finset.range (S.card + 1),
      (if nS S u = m then (1:ℝ) else 0) * (D u).V m l := by
    funext u
    rw [Finset.sum_eq_single (nS S u)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_filter_le _ _))) h
  rw [e]
  refine L2_sum _ fun m hm => L2_mul (hV m (by simpa [Nat.lt_succ_iff] using hm) l) ?_ (C := 1) ?_
  · exact (Measurable.ite ((Novel.UnifiedSpliceStep0Proof.nS_meas S) (measurableSet_singleton m))
      measurable_const measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by split_ifs <;> simp

section Data
variable {d : ℕ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} {S : Finset ℝ} {D : ℝ → Pt049 k r}
  (hV : ∀ m ≤ S.card, ∀ l, MemLp (fun u => (D u).V m l) 2 (volume.restrict (Icc (0:ℝ) H)))
  (hHp : ∀ μ ≤ d, ∀ l, MemLp (fun u => (D u).Hp μ l) 2 (volume.restrict (Icc (0:ℝ) H)))
  (hHz : ∀ i l, MemLp (fun u => (D u).Hz i l) 2 (volume.restrict (Icc (0:ℝ) H)))

include hV in
lemma L2_kap (m : ℕ) (l : Fin k) : MemLp (fun u => kap050 S (D u) u m l) 2 (volume.restrict (Icc (0:ℝ) H)) := by
  have e : (fun u => kap050 S (D u) u m l) = fun u => -(u * (D u).V (nS S u) l) -
      ∑ τ ∈ S, (if u < τ ∧ nS S τ ≤ m then (1:ℝ) else 0) *
        (τ * ((D u).V (nS S τ) l - (D u).V (nS S τ - 1) l)) := by
    funext u
    simp only [kap050, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun τ _ => ?_
      split_ifs <;> simp
  rw [e]
  refine (L2_umul (L2_cur S D hV l)).neg.sub (L2_sum _ fun τ hτ => ?_)
  have hle : nS S τ ≤ S.card := Finset.card_filter_le _ _
  refine L2_mul (((hV _ hle l).sub (hV _ (by omega) l)).const_mul τ) ?_ (C := 1) ?_
  · exact (Measurable.ite ((measurableSet_lt measurable_id measurable_const).inter
      (MeasurableSet.const (nS S τ ≤ m))) measurable_const measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by split_ifs <;> simp

include hV hHp hHz in
/-- The components of `σ^B♯(x)` are `L²`. -/
lemma L2_sigB (x : ℝ) (l : Fin k) :
    MemLp (fun u => sigB (sharp (D u).Hp ((D u).V (nS S u))) (D u).Hz c A d x l) 2 (volume.restrict (Icc (0:ℝ) H)) := by
  simp only [sigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
  refine (L2_sum _ fun μ hμ => ?_).add (L2_sum _ fun i _ => (hHz i l).const_mul _)
  refine MemLp.const_mul ?_ _
  rcases Nat.eq_zero_or_pos μ with rfl | hpos
  · simp only [sharp, Function.update_self, Pi.add_apply]
    exact (hHp 0 (Nat.zero_le _) l).add (L2_cur S D hV l)
  · simp only [sharp, Function.update_of_ne (show μ ≠ 0 by omega)]
    exact hHp μ (by simpa [Nat.lt_succ_iff] using hμ) l

include hV hHp hHz in
/-- The components of `Σ^B♯(x)` are `L²`. -/
lemma L2_SigB (x : ℝ) (l : Fin k) :
    MemLp (fun u => SigB (sharp (D u).Hp ((D u).V (nS S u))) (D u).Hz c A d x l) 2 (volume.restrict (Icc (0:ℝ) H)) := by
  simp only [SigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
  refine (L2_sum _ fun μ hμ => ?_).add (L2_sum _ fun i _ => (hHz i l).const_mul _)
  refine MemLp.const_mul ?_ _
  rcases Nat.eq_zero_or_pos μ with rfl | hpos
  · simp only [sharp, Function.update_self, Pi.add_apply]
    exact (hHp 0 (Nat.zero_le _) l).add (L2_cur S D hV l)
  · simp only [sharp, Function.update_of_ne (show μ ≠ 0 by omega)]
    exact hHp μ (by simpa [Nat.lt_succ_iff] using hμ) l

include hV hHp hHz in
/-- `R♯(u, x)` at a fixed `x` is integrable in `u`. -/
lemma int_Rsharp (hbP : ∀ μ ≤ d, Integrable (fun u => (D u).bP μ) (volume.restrict (Icc (0:ℝ) H)))
    (hbZ : ∀ i, Integrable (fun u => (D u).bZ i) (volume.restrict (Icc (0:ℝ) H)))
    (hzP : ∀ μ ≤ d, Integrable (fun u => (D u).zP μ) (volume.restrict (Icc (0:ℝ) H)))
    (hz : ∀ i, Integrable (fun u => (D u).z i) (volume.restrict (Icc (0:ℝ) H))) (x : ℝ) :
    Integrable (fun u => Rsharp c A d S (D u) u x) (volume.restrict (Icc (0:ℝ) H)) := by
  have hmem : ∀ μ ∈ Finset.range (d + 1), μ ≤ d := fun μ hμ => by simpa [Nat.lt_succ_iff] using hμ
  simp only [Rsharp, resid]
  refine Integrable.sub (Integrable.sub (Integrable.add ?_ ?_) (Integrable.add ?_ ?_)) ?_
  · exact integrable_finsetSum _ fun μ hμ => (hbP μ (hmem μ hμ)).mul_const _
  · simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hbZ i).const_mul _
  · exact integrable_finsetSum _ fun μ hμ => ((hzP μ (hmem μ hμ)).const_mul _).mul_const _
  · simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      (hz j).const_mul _).const_mul _
  · exact dot_int (fun l => L2_sigB hV hHp hHz x l) (fun l => L2_SigB hV hHp hHz x l)

end Data

end Int

theorem integrabilityS : integrabilityStatement := by
  intro k r d c A S H D hV hHp hHz hbP hbZ hzP hz m hm
  have hR0 := int_Rsharp (c := c) (A := A) hV hHp hHz hbP hbZ hzP hz 0
  have hR1 := int_Rsharp (c := c) (A := A) hV hHp hHz hbP hbZ hzP hz 1
  have hα : Integrable (fun u => alpha050 c A d S (D u) u) (volume.restrict (Icc 0 H)) := hR0
  have hβ : Integrable (fun u => beta050 c A d S (D u) u) (volume.restrict (Icc 0 H)) :=
    hR1.sub hR0
  have hVm := hV m hm
  have hH0 := hHp 0 (Nat.zero_le _)
  have hcur := L2_cur S D hV
  have hsV : Integrable (fun u => 2 * ((D u).Hp 0 ⬝ᵥ (D u).V (nS S u)) +
      (D u).V (nS S u) ⬝ᵥ (D u).V (nS S u)) (volume.restrict (Icc 0 H)) :=
    ((dot_int hH0 hcur).const_mul 2).add (dot_int hcur hcur)
  refine ⟨?_, ?_⟩
  · simp only [dL050]
    exact (((((dot_int hVm (L2_kap hV m)).add (dot_int hH0 (L2_kap hV m))).sub
      (int_umul (dot_int hVm hH0))).sub hα).add
      ((int_umul hβ).congr (Filter.Eventually.of_forall fun u => by ring))).add
      ((int_umul hsV).congr (Filter.Eventually.of_forall fun u => by ring))
  · simp only [dC050]
    exact ((((dot_int hVm hVm).add (dot_int hH0 hVm)).add (dot_int hVm hH0)).sub hβ).sub hsV

theorem spliceLocalizationConverse : Standalone.SpliceLocalizationConverse.statement := ⟨explicitS, integrabilityS⟩

end Novel.SpliceLocalizationConverseProof

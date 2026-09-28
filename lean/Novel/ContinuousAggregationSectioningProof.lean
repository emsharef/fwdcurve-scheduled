import Standalone.ContinuousAggregationSectioning

/-! # Claim 054 (54-S): sectioning on a product with a right-continuous filtration (proof)

≥: for a `G⁺`-stopping time `ρ`, `ρ ∘ pr₂` is an `F⁺`-stopping time (a null set of `μ₂` pulls back
to a null set of `μ₁ ⊗ μ₂`), with the same value by the marginal law.

≤: let `τ` be an `F⁺`-stopping time. For each rational `q`, `{τ ≤ q} ∈ F⁺_q`, so for every `n` there
is a `σ(E₁) ⊗ G_{q + 1/(n+1)}`-measurable set a.e. equal to it. Their limsup `C_q` is measurable for
`σ(E₁) ⊗ G_s` for every `s > q` (Red's device in the review of Claim 054) and a.e. equal to
`{τ ≤ q}`. The raw time `τ₀ = inf{q ∈ ℚ ∩ [A, S] : e ∈ C_q} ∧ S` (`rawTime`, as in Claim 020) is
measurable, equals `τ` a.e., and `{τ₀ ≤ t} ∈ σ(E₁) ⊗ G_s` for every `s > t`. Each section
`τ₀(e₁, ·)` is then a `G⁺`-stopping time, and Fubini with domination bounds the value of `τ` by
the value over `G⁺`-stopping times.

The raw-time lemmas are Claim 020's (`Novel.PreWindowVarianceAggregatesProof`), restated for a
general space; the right-continuity step is new.
-/

open MeasureTheory Set Filter
open Standalone.ContinuousAggregationSectioning

namespace Novel.ContinuousAggregationSectioningProof

/-! ### The completed measure -/

section Completion
variable {E : Type*} [m : MeasurableSpace E] (μ : Measure E)

lemma id_meas : @Measurable (NullMeasurableSpace E μ) E _ m (fun e => e) :=
  fun s hs => ⟨s, hs, EventuallyEq.refl _ _⟩

lemma map_id_completion :
    @Measure.map (NullMeasurableSpace E μ) E _ m (fun e => e) μ.completion = μ := by
  ext s hs
  rw [Measure.map_apply (id_meas μ) hs]
  rfl

variable {μ}

lemma integral_completion {f : E → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ e, f e ∂μ.completion = ∫ e, f e ∂μ := by
  have h := integral_map (μ := μ.completion) (id_meas μ).aemeasurable (f := f)
    (by rw [map_id_completion]; exact hf)
  rw [map_id_completion] at h
  exact h.symm

lemma aesm_of_completion {f : NullMeasurableSpace E μ → ℝ} (hf : Measurable f) :
    AEStronglyMeasurable (fun e : E => f e) μ :=
  (show NullMeasurable (fun e : E => f e) μ from fun _ hs => hf hs).aemeasurable.aestronglyMeasurable

end Completion

/-! ### The raw time of events at rational times (Claim 020's device, for a general space) -/

section Raw
variable {α : Type*}

/-- The rational times in `[A, S]`. -/
def ratTimes (A S : ℝ) : Set ℚ := {q | A ≤ (q : ℝ) ∧ (q : ℝ) ≤ S}

def rawSet (A S : ℝ) (C : ℚ → Set α) (x : α) : Set ℝ :=
  ((fun q : ℚ => (q : ℝ)) '' {q | q ∈ ratTimes A S ∧ x ∈ C q}) ∪ {S}

/-- `inf{q ∈ ℚ ∩ [A, S] : x ∈ C q} ∧ S`. -/
noncomputable def rawTime (A S : ℝ) (C : ℚ → Set α) (x : α) : ℝ := sInf (rawSet A S C x)

lemma rawSet_nonempty (A S : ℝ) (C : ℚ → Set α) (x : α) : (rawSet A S C x).Nonempty :=
  ⟨S, Or.inr rfl⟩

lemma rawSet_lower {A S : ℝ} (hAS : A ≤ S) (C : ℚ → Set α) (x : α) :
    ∀ y ∈ rawSet A S C x, A ≤ y := by
  rintro y (⟨q, ⟨hq, -⟩, rfl⟩ | rfl)
  · exact hq.1
  · exact hAS

lemma rawSet_bddBelow {A S : ℝ} (hAS : A ≤ S) (C : ℚ → Set α) (x : α) :
    BddBelow (rawSet A S C x) :=
  ⟨A, fun y hy => rawSet_lower hAS C x y hy⟩

lemma rawTime_mem {A S : ℝ} (hAS : A ≤ S) (C : ℚ → Set α) (x : α) :
    rawTime A S C x ∈ Icc A S :=
  ⟨le_csInf (rawSet_nonempty A S C x) (rawSet_lower hAS C x),
    csInf_le (rawSet_bddBelow hAS C x) (Or.inr rfl)⟩

/-- Where the events are exactly `{y ≤ q}` for a value `y ∈ [A, S]`, the raw time is `y`. -/
lemma rawTime_eq {A S : ℝ} (hAS : A ≤ S) (C : ℚ → Set α) (x : α) (y : ℝ) (hy : y ∈ Icc A S)
    (h : ∀ q ∈ ratTimes A S, x ∈ C q ↔ y ≤ q) : rawTime A S C x = y := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt_rat_imp_le fun q hq => ?_
    by_cases hqS : S ≤ (q : ℝ)
    · exact (csInf_le (rawSet_bddBelow hAS C x) (Or.inr rfl)).trans hqS
    · have hq' : q ∈ ratTimes A S := ⟨hy.1.trans hq.le, (not_le.mp hqS).le⟩
      exact csInf_le (rawSet_bddBelow hAS C x) (Or.inl ⟨q, ⟨hq', (h q hq').mpr hq.le⟩, rfl⟩)
  · refine le_csInf (rawSet_nonempty A S C x) ?_
    rintro z (⟨q, ⟨hq, hxq⟩, rfl⟩ | rfl)
    · exact (h q hq).mp hxq
    · exact hy.2

lemma rawTime_le_iff {A S : ℝ} (hAS : A ≤ S) (C : ℚ → Set α) (x : α) (t : ℝ) (htA : A ≤ t)
    (htS : t < S) :
    rawTime A S C x ≤ t ↔
      ∀ q' ∈ ratTimes A S, t < q' → ∃ q ∈ ratTimes A S, (q : ℝ) ≤ q' ∧ x ∈ C q := by
  constructor
  · intro hle q' hq' htq'
    have hlt : sInf (rawSet A S C x) < q' := hle.trans_lt htq'
    obtain ⟨z, hz, hzq⟩ := exists_lt_of_csInf_lt (rawSet_nonempty A S C x) hlt
    rcases hz with ⟨q, ⟨hq, hxq⟩, rfl⟩ | rfl
    · exact ⟨q, hq, hzq.le, hxq⟩
    · exact absurd hzq (not_lt.mpr hq'.2)
  · intro h
    refine le_of_forall_lt_rat_imp_le fun q' hq' => ?_
    by_cases hqS : S ≤ (q' : ℝ)
    · exact (csInf_le (rawSet_bddBelow hAS C x) (Or.inr rfl)).trans hqS
    · have hq'' : q' ∈ ratTimes A S := ⟨htA.trans hq'.le, (not_le.mp hqS).le⟩
      obtain ⟨q, hq, hqq', hxq⟩ := h q' hq'' hq'
      exact (csInf_le (rawSet_bddBelow hAS C x) (Or.inl ⟨q, ⟨hq, hxq⟩, rfl⟩)).trans hqq'

/-- If each event `C q` is measurable for `M s` at every `s > q`, then
`{rawTime ≤ t}` is measurable for `M s` at every `s > t`: the raw time is a stopping time of the
right-continuous regularization of `M`. -/
lemma rawTime_meas {A S : ℝ} (hAS : A ≤ S) (M : ℝ → MeasurableSpace α)
    (C : ℚ → Set α) (hC : ∀ q : ℚ, ∀ s, (q : ℝ) < s → MeasurableSet[M s] (C q)) (t s : ℝ)
    (hts : t < s) : MeasurableSet[M s] {x | rawTime A S C x ≤ t} := by
  by_cases htA : A ≤ t
  · by_cases htS : t < S
    · obtain ⟨q₀, hq₀t, hq₀s⟩ := exists_rat_btwn (lt_min hts htS : t < min s S)
      have hq₀ : q₀ ∈ ratTimes A S := ⟨htA.trans hq₀t.le, (hq₀s.trans_le (min_le_right _ _)).le⟩
      have he : {x | rawTime A S C x ≤ t} =
          ⋂ q' : {q' : ℚ // q' ∈ ratTimes A S ∧ t < (q' : ℝ) ∧ (q' : ℝ) ≤ q₀},
            ⋃ q : {q : ℚ // q ∈ ratTimes A S ∧ (q : ℝ) ≤ q'.1}, C q.1 := by
        ext x
        simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, Subtype.exists, exists_prop,
          Subtype.forall]
        rw [rawTime_le_iff hAS C x t htA htS]
        constructor
        · rintro h q' ⟨hq', htq', -⟩
          obtain ⟨q, hq, hqq', hxq⟩ := h q' hq' htq'
          exact ⟨q, ⟨hq, hqq'⟩, hxq⟩
        · intro h q' hq' htq'
          by_cases hle : (q' : ℝ) ≤ q₀
          · obtain ⟨q, ⟨hq, hqq'⟩, hxq⟩ := h q' ⟨hq', htq', hle⟩
            exact ⟨q, hq, hqq', hxq⟩
          · obtain ⟨q, ⟨hq, hqq'⟩, hxq⟩ := h q₀ ⟨hq₀, hq₀t, le_rfl⟩
            exact ⟨q, hq, hqq'.trans (not_le.mp hle).le, hxq⟩
      rw [he]
      refine MeasurableSet.iInter fun q' => MeasurableSet.iUnion fun q => ?_
      exact hC q.1 s ((q.2.2.trans q'.2.2.2).trans_lt (hq₀s.trans_le (min_le_left _ _)))
    · have he : {x | rawTime A S C x ≤ t} = univ := by
        ext x
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (rawTime_mem hAS C x).2.trans (not_lt.mp htS)
      rw [he]
      exact @MeasurableSet.univ _ (M s)
  · have he : {x | rawTime A S C x ≤ t} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact (not_le.mp htA).trans_le (rawTime_mem hAS C x).1
    rw [he]
    exact @MeasurableSet.empty _ (M s)

end Raw

/-! ### Stopping times and their values -/

section Main
variable {E₁ E₂ : Type} [m₁ : MeasurableSpace E₁] [m₂ : MeasurableSpace E₂]

/-- A stopping time with values in `[A, S]` is measurable on the completed space. -/
lemma times_meas {E : Type*} [m : MeasurableSpace E] {μ : Measure E} {F : Filtration ℝ m}
    {A S : ℝ} {τ : NullMeasurableSpace E μ → ℝ} (hτ : τ ∈ times μ F A S) : Measurable τ := by
  have h := hτ.2.measurable_of_le (fun e =>
    show (τ e : WithTop ℝ) ≤ S from WithTop.coe_le_coe.mpr (hτ.1 e).2)
  have h' := h.untopA.mono ((aug μ F).le S) le_rfl
  simpa using h'

lemma const_mem {E : Type*} [m : MeasurableSpace E] (μ : Measure E) (F : Filtration ℝ m)
    {A S : ℝ} (hAS : A ≤ S) : (fun _ => S) ∈ times μ F A S :=
  ⟨fun _ => ⟨hAS, le_rfl⟩, isStoppingTime_const _ _⟩

/-- The measurable sets of `aug μ F` at `t`. -/
lemma aug_iff {E : Type*} [m : MeasurableSpace E] {μ : Measure E} {F : Filtration ℝ m} {t : ℝ}
    {B : Set E} : MeasurableSet[aug μ F t] B ↔
      ∀ s, t < s → ∃ C, MeasurableSet[F s] C ∧ B =ᶠ[ae μ] C := by
  show MeasurableSet[⨅ s ∈ Ioi t, eventuallyMeasurableSpace (F s) (ae μ)] B ↔ _
  simp only [MeasurableSpace.measurableSet_iInf, mem_Ioi]
  rfl

variable {μ₁ : Measure E₁} {μ₂ : Measure E₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  {G : Filtration ℝ m₂} {A S : ℝ} {Pay : ℝ × E₂ → ℝ} {D : E₂ → ℝ}

omit [IsProbabilityMeasure μ₂] in
/-- The value of `ρ` as an integral under `μ₂`. -/
lemma val₂_eq (hPay : Measurable Pay) {ρ : NullMeasurableSpace E₂ μ₂ → ℝ}
    (hρ : ρ ∈ times μ₂ G A S) :
    ∫ e, Pay (ρ e, e) ∂μ₂.completion = ∫ e : E₂, Pay (ρ e, e) ∂μ₂ :=
  integral_completion (aesm_of_completion (hPay.comp ((times_meas hρ).prodMk (id_meas μ₂))))

omit [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] in
/-- The value of `τ` as an integral under `μ₁ ⊗ μ₂`. -/
lemma valProd_eq (hPay : Measurable Pay) {τ : NullMeasurableSpace (E₁ × E₂) (μ₁.prod μ₂) → ℝ}
    (hτ : τ ∈ times (μ₁.prod μ₂) (prodFilt G) A S) :
    ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion =
      ∫ e : E₁ × E₂, Pay (τ e, e.2) ∂(μ₁.prod μ₂) :=
  integral_completion (aesm_of_completion
    (hPay.comp ((times_meas hτ).prodMk (measurable_snd.comp (id_meas (μ₁.prod μ₂))))))

variable (hPay : Measurable Pay) (hDi : Integrable D μ₂)
  (hbd : ∀ t ∈ Icc A S, ∀ e, |Pay (t, e)| ≤ D e)
include hPay hDi hbd

omit [IsProbabilityMeasure μ₂] in
lemma bdd₂ : BddAbove ((fun ρ => ∫ e, Pay (ρ e, e) ∂μ₂.completion) '' times μ₂ G A S) := by
  refine ⟨∫ e, D e ∂μ₂, ?_⟩
  rintro x ⟨ρ, hρ, rfl⟩
  refine (le_of_eq (val₂_eq hPay hρ)).trans ((le_abs_self _).trans ?_)
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hDi (Eventually.of_forall fun e => by
    rw [Real.norm_eq_abs]; exact hbd _ (hρ.1 e) e)

lemma bddProd : BddAbove ((fun τ => ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion) ''
    times (μ₁.prod μ₂) (prodFilt G) A S) := by
  refine ⟨∫ e : E₁ × E₂, D e.2 ∂(μ₁.prod μ₂), ?_⟩
  rintro x ⟨τ, hτ, rfl⟩
  refine (le_of_eq (valProd_eq hPay hτ)).trans ((le_abs_self _).trans ?_)
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hDi.comp_snd μ₁) (Eventually.of_forall fun e => by
    rw [Real.norm_eq_abs]; exact hbd _ (hτ.1 e) e.2)

omit [IsProbabilityMeasure μ₁] hPay hDi hbd in
/-- ≥: `ρ ∘ pr₂` is an `F⁺`-stopping time. -/
lemma lift_mem {ρ : NullMeasurableSpace E₂ μ₂ → ℝ} (hρ : ρ ∈ times μ₂ G A S) :
    (fun e : NullMeasurableSpace (E₁ × E₂) (μ₁.prod μ₂) => ρ (e : E₁ × E₂).2) ∈
      times (μ₁.prod μ₂) (prodFilt G) A S := by
  refine ⟨fun e => hρ.1 _, fun t => ?_⟩
  have h := (aug_iff (E := E₂) (μ := μ₂) (F := G)).1 (hρ.2 t)
  refine (aug_iff (E := E₁ × E₂) (μ := μ₁.prod μ₂) (F := prodFilt G)).2 fun s hs => ?_
  obtain ⟨C, hC, hCe⟩ := h s hs
  refine ⟨Prod.snd ⁻¹' C, (le_sup_right : MeasurableSpace.comap Prod.snd (G s) ≤ prodFilt G s) _
    ⟨C, hC, rfl⟩, ?_⟩
  exact (Measure.quasiMeasurePreserving_snd (μ := μ₁) (ν := μ₂)).preimage_ae_eq hCe

omit hDi hbd in
lemma lift_val {ρ : NullMeasurableSpace E₂ μ₂ → ℝ} (hρ : ρ ∈ times μ₂ G A S) :
    ∫ e, Pay (ρ (e : E₁ × E₂).2, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion =
      ∫ e, Pay (ρ e, e) ∂μ₂.completion := by
  have hF : AEStronglyMeasurable (fun e : E₂ => Pay (ρ e, e)) μ₂ :=
    aesm_of_completion (hPay.comp ((times_meas hρ).prodMk (id_meas μ₂)))
  have hF' := hF.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := μ₁) (ν := μ₂))
  refine (integral_completion hF').trans (Eq.trans ?_ (val₂_eq hPay hρ).symm)
  have hmap : (μ₁.prod μ₂).map Prod.snd = μ₂ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have := integral_map (μ := μ₁.prod μ₂) measurable_snd.aemeasurable (f := fun e : E₂ =>
    Pay (ρ e, e)) (by rw [hmap]; exact hF)
  rw [hmap] at this
  exact this.symm

omit [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] hPay hDi hbd in
/-- ≤, the rational-time events: for each rational `q` there is a set, measurable for
`σ(E₁) ⊗ G_s` at every `s > q`, almost everywhere equal to `{τ ≤ q}`. -/
lemma exists_C {τ : NullMeasurableSpace (E₁ × E₂) (μ₁.prod μ₂) → ℝ}
    (hτ : τ ∈ times (μ₁.prod μ₂) (prodFilt G) A S) (q : ℚ) :
    ∃ C : Set (E₁ × E₂), (∀ s, (q : ℝ) < s → MeasurableSet[prodFilt G s] C) ∧
      ∀ᵐ e ∂(μ₁.prod μ₂), (e ∈ C ↔ τ e ≤ q) := by
  have h := (aug_iff (E := E₁ × E₂) (μ := μ₁.prod μ₂) (F := prodFilt G)).1 (hτ.2 (q : ℝ))
  have hpos : ∀ n : ℕ, (q : ℝ) < q + 1 / ((n : ℝ) + 1) := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose B hB hBe using fun n : ℕ => h _ (hpos n)
  refine ⟨⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n, fun s hs => ?_, ?_⟩
  · obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (sub_pos.2 hs)
    have key : (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n) =
        ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : max N N₀ ≤ n), B n := by
      ext e
      simp only [mem_iInter, mem_iUnion, exists_prop]
      constructor
      · intro h N; exact h (max N N₀)
      · intro h N
        obtain ⟨n, hn, he⟩ := h N
        exact ⟨n, (le_max_left _ _).trans hn, he⟩
    rw [key]
    refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun hn => (prodFilt G).mono ?_ _ (hB n)
    have hn' : N₀ ≤ n := (le_max_right _ _).trans hn
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn' 1)
    linarith
  · have hall := ae_all_iff.2 fun n => hBe n
    filter_upwards [hall] with e he
    have he' : ∀ n, e ∈ B n ↔ τ e ≤ q := fun n =>
      (Iff.of_eq (he n).symm).trans WithTop.coe_le_coe
    show (e ∈ ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n) ↔ τ e ≤ q
    simp only [mem_iInter, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, -, hn⟩ := h 0
      exact (he' n).1 hn
    · intro h N
      exact ⟨N, le_rfl, (he' N).2 h⟩

omit [IsProbabilityMeasure μ₂] hPay hDi hbd in
/-- ≤, a section of the raw time is a `G⁺`-stopping time. -/
lemma section_mem (hAS : A ≤ S) (C : ℚ → Set (E₁ × E₂))
    (hC : ∀ q : ℚ, ∀ s, (q : ℝ) < s → MeasurableSet[prodFilt G s] (C q)) (e₁ : E₁) :
    (fun e₂ : NullMeasurableSpace E₂ μ₂ => rawTime A S C (e₁, (e₂ : E₂))) ∈ times μ₂ G A S := by
  refine ⟨fun e₂ => rawTime_mem hAS C _, fun t =>
    (aug_iff (E := E₂) (μ := μ₂) (F := G)).2 fun s hs => ?_⟩
  have hset : {e₂ : E₂ | ((rawTime A S C (e₁, e₂) : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)} =
      (Prod.mk e₁) ⁻¹' {e | rawTime A S C e ≤ t} := by
    ext e₂; simp
  refine ⟨_, ?_, EventuallyEq.refl _ _⟩
  show MeasurableSet[G s] {e₂ : E₂ | ((rawTime A S C (e₁, e₂) : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)}
  rw [hset]
  exact (@measurable_prodMk_left E₁ E₂ m₁ (G s) e₁)
    (rawTime_meas hAS (fun s => prodFilt G s) C hC t s hs)

/-- ≤: the value of an `F⁺`-stopping time is at most the value over `G⁺`-stopping times. -/
lemma val_le (hAS : A ≤ S) {τ : NullMeasurableSpace (E₁ × E₂) (μ₁.prod μ₂) → ℝ}
    (hτ : τ ∈ times (μ₁.prod μ₂) (prodFilt G) A S) :
    ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion ≤ value₂ μ₂ G A S Pay := by
  choose C hCm hCe using exists_C hτ
  set τ₀ := rawTime A S C
  have hτ₀m : Measurable τ₀ := measurable_of_Iic fun x =>
    (prodFilt G).le (x + 1) _ (rawTime_meas hAS (fun s => prodFilt G s) C hCm x (x + 1)
      (by linarith))
  have hae : ∀ᵐ e ∂(μ₁.prod μ₂), τ₀ e = τ e := by
    filter_upwards [ae_all_iff.2 hCe] with e he
    exact rawTime_eq hAS C e (τ e) (hτ.1 e) fun q _ => he q
  have hGm : Measurable fun e : E₁ × E₂ => Pay (τ₀ e, e.2) := hPay.comp (hτ₀m.prodMk measurable_snd)
  have hint : Integrable (fun e : E₁ × E₂ => Pay (τ₀ e, e.2)) (μ₁.prod μ₂) :=
    (hDi.comp_snd μ₁).mono' hGm.aestronglyMeasurable (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs]; exact hbd _ (rawTime_mem hAS C e) e.2)
  have h1 : ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion =
      ∫ e : E₁ × E₂, Pay (τ₀ e, e.2) ∂(μ₁.prod μ₂) := by
    rw [valProd_eq hPay hτ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with e he
    rw [he]
  rw [h1, integral_prod _ hint]
  have hsec : ∀ e₁ : E₁, ∫ e₂, Pay (τ₀ (e₁, e₂), e₂) ∂μ₂ ≤ value₂ μ₂ G A S Pay := fun e₁ => by
    have hmem := section_mem (μ₂ := μ₂) hAS C hCm e₁
    exact (val₂_eq hPay hmem).symm.trans_le (le_csSup (bdd₂ hPay hDi hbd) ⟨_, hmem, rfl⟩)
  calc (∫ e₁, ∫ e₂, Pay (τ₀ (e₁, e₂), e₂) ∂μ₂ ∂μ₁) ≤ ∫ _ : E₁, value₂ μ₂ G A S Pay ∂μ₁ :=
        integral_mono hint.integral_prod_left (integrable_const _) hsec
    _ = value₂ μ₂ G A S Pay := by rw [integral_const, probReal_univ, one_smul]

end Main

theorem sectioningS : sectioningStatement := by
  intro E₁ E₂ _ _ μ₁ μ₂ _ _ G A S hAS Pay D hPay hDm hDi hbd
  have hb₂ := bdd₂ (μ₂ := μ₂) (G := G) hPay hDi hbd
  have hbP := bddProd (μ₁ := μ₁) (μ₂ := μ₂) (G := G) hPay hDi hbd
  refine ⟨hb₂, hbP, le_antisymm ?_ ?_⟩
  · refine csSup_le ⟨_, ⟨fun _ => S, const_mem _ _ hAS, rfl⟩⟩ ?_
    rintro x ⟨τ, hτ, rfl⟩
    exact val_le hPay hDi hbd hAS hτ
  · refine csSup_le ⟨_, ⟨fun _ => S, const_mem _ _ hAS, rfl⟩⟩ ?_
    rintro x ⟨ρ, hρ, rfl⟩
    exact (lift_val (μ₁ := μ₁) hPay hρ).symm.trans_le (le_csSup hbP ⟨_, lift_mem hρ, rfl⟩)

theorem continuousAggregationSectioning : Standalone.ContinuousAggregationSectioning.statement :=
  sectioningS

end Novel.ContinuousAggregationSectioningProof

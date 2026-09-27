import Standalone.SeparableMeetingMarkovSeveral
import Novel.SeparableMeetingMarkovPropertyProof
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal symmDiff
open Standalone.SeparableMeetingMarkovProperty Standalone.SeparableMeetingMarkovSeveral
namespace Novel.SeparableMeetingMarkovSeveralProof

section Abstract
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {n : ℕ} {X : ℝ≥0 → Ω → Fin n → ℝ}

lemma integrable_bdd {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)

variable (hX : ∀ t, Measurable[ℱ t] (X t))
  (hM : ∀ s t : ℝ≥0, s ≤ t → ∀ f : (Fin n → ℝ) → ℝ, BoundedBorel13 f →
    μ[f ∘ X t | ℱ s] =ᵐ[μ] μ[f ∘ X t | MeasurableSpace.comap (X s) inferInstance])
include hX

omit [IsProbabilityMeasure μ] in
lemma hXm (t : ℝ≥0) : Measurable (X t) := (hX t).mono (ℱ.le t) le_rfl

include hM in
/-- The single-time property with a Borel function bounded like the test function. -/
lemma single (s t : ℝ≥0) (hst : s ≤ t) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C) :
    ∃ g : (Fin n → ℝ) → ℝ, Measurable g ∧ (∀ x, |g x| ≤ C) ∧
      μ[f ∘ X t | ℱ s] =ᵐ[μ] g ∘ X s := by
  have h1 := hM s t hst f ⟨hf, C, hC⟩
  obtain ⟨h, hh, heq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap (X s) inferInstance)
      (f := f ∘ X t) (μ := μ)).exists_eq_measurable_comp
  have hb : ∀ᵐ ω ∂μ, |(μ[f ∘ X t | MeasurableSpace.comap (X s) inferInstance]) ω| ≤
      ((⟨C, hC0⟩ : ℝ≥0) : ℝ) :=
    ae_bdd_condExp_of_ae_bdd (ae_of_all _ fun ω => hC _)
  refine ⟨fun x => max (-C) (min C (h x)),
    measurable_const.max (measurable_const.min hh.measurable), fun x => ?_, ?_⟩
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [h1, hb] with ω h1ω hbω
    rw [h1ω]
    have hω : (μ[f ∘ X t | MeasurableSpace.comap (X s) inferInstance]) ω = h (X s ω) := by
      rw [heq]; rfl
    rw [hω] at hbω ⊢
    obtain ⟨hl, hu⟩ := abs_le.1 hbω
    simp only [Function.comp, min_eq_right hu, max_eq_right hl]

include hM in
/-- Products of bounded Borel functions of the state at ordered times. -/
lemma product (r : ℕ) : ∀ (s : ℝ≥0) (t : Fin r → ℝ≥0), Monotone t → (∀ i, s ≤ t i) →
    ∀ (f : Fin r → (Fin n → ℝ) → ℝ), (∀ i, Measurable (f i)) → ∀ C : Fin r → ℝ,
    (∀ i, 0 ≤ C i) → (∀ i x, |f i x| ≤ C i) →
    ∃ g : (Fin n → ℝ) → ℝ, Measurable g ∧ (∀ x, |g x| ≤ ∏ i, C i) ∧
      μ[fun ω => ∏ i, f i (X (t i) ω) | ℱ s] =ᵐ[μ] g ∘ X s := by
  induction r with
  | zero =>
    intro s t _ _ f _ C _ _
    refine ⟨fun _ => 1, measurable_const, fun x => by simp, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [condExp_const (ℱ.le s)]
    rfl
  | succ r ih =>
    intro s t ht hs f hf C hC0 hC
    have ht' : Monotone (t ∘ Fin.succ) := ht.comp (Fin.strictMono_succ.monotone)
    have hs' : ∀ i, t 0 ≤ (t ∘ Fin.succ) i := fun i => ht (Fin.zero_le _)
    obtain ⟨g1, hg1, hg1b, hg1e⟩ := ih (t 0) (t ∘ Fin.succ) ht' hs' (fun i => f i.succ)
      (fun i => hf i.succ) (fun i => C i.succ) (fun i => hC0 i.succ) (fun i => hC i.succ)
    have hP0 : 0 ≤ ∏ i : Fin r, C i.succ := Finset.prod_nonneg fun i _ => hC0 i.succ
    obtain ⟨g, hg, hgb, hge⟩ := single hX hM s (t 0) (hs 0) (fun x => f 0 x * g1 x)
      ((hf 0).mul hg1) (C 0 * ∏ i : Fin r, C i.succ) (mul_nonneg (hC0 0) hP0)
      (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hC 0 x) (hg1b x) (abs_nonneg _) (hC0 0))
    refine ⟨g, hg, fun x => by rw [Fin.prod_univ_succ]; exact hgb x, ?_⟩
    -- split off the first factor
    set f0 : Ω → ℝ := fun ω => f 0 (X (t 0) ω) with hf0
    set T : Ω → ℝ := fun ω => ∏ i : Fin r, f i.succ (X (t i.succ) ω) with hT
    have hsplit : (fun ω => ∏ i, f i (X (t i) ω)) = f0 * T := by
      funext ω
      simp [hf0, hT, Fin.prod_univ_succ]
    have hf0m : StronglyMeasurable[ℱ (t 0)] f0 :=
      ((hf 0).comp (hX (t 0))).stronglyMeasurable
    have hTm : Measurable T :=
      Finset.measurable_prod _ fun i _ => (hf i.succ).comp (hXm hX _)
    have hTb : ∀ ω, |T ω| ≤ ∏ i : Fin r, C i.succ := by
      intro ω
      rw [hT, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hC i.succ _)
    have hTi : Integrable T μ := integrable_bdd hTm _ hTb
    have hf0T : Integrable (f0 * T) μ := by
      refine integrable_bdd (((hf 0).comp (hXm hX _)).mul hTm) (C 0 * ∏ i : Fin r, C i.succ)
        fun ω => ?_
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hC 0 _) (hTb ω) (abs_nonneg _) (hC0 0)
    have hinner : μ[f0 * T | ℱ (t 0)] =ᵐ[μ] (fun x => f 0 x * g1 x) ∘ X (t 0) := by
      filter_upwards [condExp_mul_of_stronglyMeasurable_left hf0m hf0T hTi, hg1e] with ω h1 h2
      rw [h1, Pi.mul_apply]
      have : (μ[T | ℱ (t 0)]) ω = g1 (X (t 0) ω) := by rw [hT]; exact h2
      rw [this]
      rfl
    rw [hsplit]
    calc μ[f0 * T | ℱ s] =ᵐ[μ] μ[μ[f0 * T | ℱ (t 0)] | ℱ s] :=
          (condExp_condExp_of_le (ℱ.mono (hs 0)) (ℱ.le (t 0))).symm
      _ =ᵐ[μ] μ[(fun x => f 0 x * g1 x) ∘ X (t 0) | ℱ s] := condExp_congr_ae hinner
      _ =ᵐ[μ] g ∘ X s := hge

include hM in
/-- Ordered times: the conditional expectation given `ℱ s` equals that given `X_s`. -/
lemma ordered (r : ℕ) (s : ℝ≥0) (t : Fin r → ℝ≥0) (ht : Monotone t) (hs : ∀ i, s ≤ t i)
    (F : (Fin r → Fin n → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) :
    μ[fun ω => F (fun i => X (t i) ω) | ℱ s] =ᵐ[μ]
      μ[fun ω => F (fun i => X (t i) ω) | MeasurableSpace.comap (X s) inferInstance] := by
  classical
  set W : Ω → (Fin r → Fin n → ℝ) := fun ω i => X (t i) ω with hWdef
  have hW : Measurable W := measurable_pi_iff.2 fun i => hXm hX (t i)
  set ν : Measure (Fin r → Fin n → ℝ) := μ.map W with hν
  have hWp : MeasurePreserving W μ ν := ⟨hW, rfl⟩
  set mc : MeasurableSpace Ω := MeasurableSpace.comap (X s) inferInstance with hmcdef
  have hmcs : mc ≤ ℱ s := (hX s).comap_le
  have hmc : mc ≤ mΩ := hmcs.trans (ℱ.le s)
  let Pf : ((Fin r → Fin n → ℝ) → ℝ) → Prop := fun G => μ[G ∘ W | ℱ s] =ᵐ[μ] μ[G ∘ W | mc]
  have Pf_congr : ∀ G G', G =ᵐ[ν] G' → Pf G → Pf G' := by
    intro G G' h hG
    have h' : G ∘ W =ᵐ[μ] G' ∘ W := ae_eq_comp hW.aemeasurable h
    exact (condExp_congr_ae h'.symm).trans (hG.trans (condExp_congr_ae h'))
  -- boxes, from the product lemma
  have Pf_box : ∀ A : Fin r → Set (Fin n → ℝ), (∀ i, MeasurableSet (A i)) →
      Pf ((Set.pi Set.univ A).indicator fun _ => (1:ℝ)) := by
    intro A hA
    obtain ⟨g, hg, hgb, hge⟩ := product hX hM r s t ht hs
      (fun i => (A i).indicator fun _ => (1:ℝ))
      (fun i => measurable_const.indicator (hA i)) (fun _ => 1) (fun _ => zero_le_one)
      (fun i x => by by_cases h : x ∈ A i <;> simp [h])
    have heq : ((Set.pi Set.univ A).indicator fun _ => (1:ℝ)) ∘ W =
        fun ω => ∏ i, (A i).indicator (fun _ => (1:ℝ)) (X (t i) ω) := by
      funext ω
      simp only [Function.comp, Set.indicator_apply, Set.mem_pi, Set.mem_univ, true_implies, hWdef]
      split_ifs with h
      · exact (Finset.prod_eq_one fun i _ => by simp [h i]).symm
      · push Not at h
        obtain ⟨i, hi⟩ := h
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    show μ[_ ∘ W | ℱ s] =ᵐ[μ] μ[_ ∘ W | mc]
    rw [heq]
    have hgm : StronglyMeasurable[mc] (g ∘ X s) :=
      (hg.comp (comap_measurable (X s))).stronglyMeasurable
    have hgi : Integrable (g ∘ X s) μ :=
      integrable_bdd (hg.comp (hXm hX s)) _ (fun ω => hgb _)
    calc μ[fun ω => ∏ i, (A i).indicator (fun _ => (1:ℝ)) (X (t i) ω) | ℱ s]
        =ᵐ[μ] g ∘ X s := hge
      _ = μ[g ∘ X s | mc] := (condExp_of_stronglyMeasurable hmc hgm hgi).symm
      _ =ᵐ[μ] μ[μ[fun ω => ∏ i, (A i).indicator (fun _ => (1:ℝ)) (X (t i) ω) | ℱ s] | mc] :=
          (condExp_congr_ae hge).symm
      _ =ᵐ[μ] μ[fun ω => ∏ i, (A i).indicator (fun _ => (1:ℝ)) (X (t i) ω) | mc] :=
          condExp_condExp_of_le hmcs (ℱ.le s)
  -- the operator whose kernel is the property
  let Φ : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 μ := (Lp.compMeasurePreservingₗᵢ ℝ W hWp).toContinuousLinearMap
  let T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 μ :=
    (condExpL1CLM ℝ (ℱ.le s) μ).comp Φ - (condExpL1CLM ℝ hmc μ).comp Φ
  let K : Submodule ℝ (Lp ℝ 1 ν) := LinearMap.ker (T : Lp ℝ 1 ν →ₗ[ℝ] Lp ℝ 1 μ)
  have hΦ : ∀ G : Lp ℝ 1 ν, ⇑(Φ G) =ᵐ[μ] ⇑G ∘ W :=
    fun G => Lp.coeFn_compMeasurePreserving G hWp
  have memT : ∀ G : Lp ℝ 1 ν, G ∈ K ↔ Pf ⇑G := by
    intro G
    have hi : Integrable (⇑(Φ G)) μ := L1.integrable_coeFn (Φ G)
    have h1 := condExp_ae_eq_condExpL1CLM (ℱ.le s) hi
    have h2 := condExp_ae_eq_condExpL1CLM hmc hi
    rw [Integrable.toL1_coeFn] at h1 h2
    have e1 : μ[⇑(Φ G) | ℱ s] =ᵐ[μ] μ[⇑G ∘ W | ℱ s] := condExp_congr_ae (hΦ G)
    have e2 : μ[⇑(Φ G) | mc] =ᵐ[μ] μ[⇑G ∘ W | mc] := condExp_congr_ae (hΦ G)
    have hT : T G = condExpL1CLM ℝ (ℱ.le s) μ (Φ G) - condExpL1CLM ℝ hmc μ (Φ G) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT, sub_eq_zero]
    constructor
    · intro h
      show μ[⇑G ∘ W | ℱ s] =ᵐ[μ] μ[⇑G ∘ W | mc]
      refine e1.symm.trans (h1.trans ?_)
      rw [h]
      exact h2.symm.trans e2
    · intro h
      apply Lp.ext
      exact h1.symm.trans (e1.trans (h.trans (e2.symm.trans h2)))
  have hker : IsClosed (K : Set (Lp ℝ 1 ν)) := T.isClosed_ker
  -- sets
  have hfin : ∀ A : Set (Fin r → Fin n → ℝ), ν A ≠ ⊤ := fun A => measure_ne_top ν A
  have Cs_iff : ∀ A (hA : MeasurableSet A),
      indicatorConstLp 1 hA (hfin A) (1:ℝ) ∈ K ↔
        Pf (A.indicator fun _ => (1:ℝ)) := by
    intro A hA
    rw [memT]
    exact ⟨Pf_congr _ _ indicatorConstLp_coeFn, Pf_congr _ _ indicatorConstLp_coeFn.symm⟩
  have hset : ∀ A (hA : MeasurableSet A),
      indicatorConstLp 1 hA (hfin A) (1:ℝ) ∈ K := by
    intro A hA
    refine MeasurableSpace.induction_on_inter
      (C := fun A hA => indicatorConstLp 1 hA (hfin A) (1:ℝ) ∈ K)
      generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ A hA
    · show indicatorConstLp 1 _ _ (1:ℝ) ∈ K
      rw [indicatorConstLp_empty]
      exact zero_mem _
    · intro t ht
      obtain ⟨B, hB, rfl⟩ := ht
      exact (Cs_iff _ _).2 (Pf_box B fun i => hB i (Set.mem_univ i))
    · intro A hA hCA
      have huniv : indicatorConstLp 1 MeasurableSet.univ (hfin _) (1:ℝ) ∈ K := by
        have := Pf_box (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
        rw [Set.pi_univ] at this
        exact (Cs_iff _ _).2 this
      have heq : indicatorConstLp 1 hA.compl (hfin _) (1:ℝ) =
          indicatorConstLp 1 MeasurableSet.univ (hfin _) 1 - indicatorConstLp 1 hA (hfin _) 1 := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hA.compl) (hμs := hfin _) (c := (1:ℝ)),
          Lp.coeFn_sub (indicatorConstLp 1 MeasurableSet.univ (hfin _) (1:ℝ))
            (indicatorConstLp 1 hA (hfin _) 1),
          indicatorConstLp_coeFn (p := 1) (hs := MeasurableSet.univ) (hμs := hfin _) (c := (1:ℝ)),
          indicatorConstLp_coeFn (p := 1) (hs := hA) (hμs := hfin _) (c := (1:ℝ))]
          with x h1 h2 h3 h4
        rw [h1, h2, Pi.sub_apply, h3, h4]
        by_cases hx : x ∈ A <;> simp [hx]
      rw [heq]
      exact sub_mem huniv hCA
    · intro f hdisj hfm hCf
      -- partial unions
      let B : ℕ → Set (Fin r → Fin n → ℝ) := fun k => ⋃ i ∈ Finset.range k, f i
      have hBm : ∀ k, MeasurableSet (B k) :=
        fun k => Finset.measurableSet_biUnion _ fun i _ => hfm i
      have hB : ∀ k, indicatorConstLp 1 (hBm k) (hfin _) (1:ℝ) ∈ K := by
        intro k
        induction k with
        | zero =>
          have h0 : B 0 = ∅ := by simp [B]
          have : indicatorConstLp 1 (hBm 0) (hfin _) (1:ℝ) = 0 := by
            apply Lp.ext
            filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hBm 0) (hμs := hfin _)
              (c := (1:ℝ)), Lp.coeFn_zero ℝ 1 ν] with x h1 h2
            rw [h1, h2, h0]
            simp
          rw [this]
          exact zero_mem _
        | succ k ih =>
          have hsplit : B (k+1) = B k ∪ f k := by
            simp only [B, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
          have hd : Disjoint (B k) (f k) := by
            simp only [B, Set.disjoint_iUnion_left]
            intro i hi
            exact hdisj (by simp at hi; omega)
          have : indicatorConstLp 1 (hBm (k+1)) (hfin _) (1:ℝ) =
              indicatorConstLp 1 (hBm k) (hfin _) 1 + indicatorConstLp 1 (hfm k) (hfin _) 1 := by
            rw [← indicatorConstLp_disjoint_union (hBm k) (hfm k) (hfin _) (hfin _) hd]
            congr 1
          rw [this]
          exact add_mem ih (hCf k)
      have hsub : ∀ k, B k ⊆ ⋃ i, f i :=
        fun k => Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
      have hlim : Filter.Tendsto (fun k => ν (B k ∆ (⋃ i, f i))) Filter.atTop (nhds 0) := by
        have hanti : Antitone fun k => (⋃ i, f i) \ B k := by
          intro a b hab
          apply Set.diff_subset_diff_right
          exact Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 (Finset.range_subset_range.2 hab))
        have hinter : (⋂ k, (⋃ i, f i) \ B k) = ∅ := by
          ext x
          refine ⟨fun h => ?_, fun h => h.elim⟩
          rw [Set.mem_iInter] at h
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (h 0).1
          exact ((h (i+1)).2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), hi⟩)).elim
        have ht := tendsto_measure_iInter_atTop (μ := ν)
          (fun k => ((MeasurableSet.iUnion hfm).diff (hBm k)).nullMeasurableSet) hanti
          ⟨0, hfin _⟩
        rw [hinter, measure_empty] at ht
        refine ht.congr fun k => ?_
        simp only [Function.comp, symmDiff_of_le (hsub k)]
      exact hker.mem_of_tendsto
        (tendsto_indicatorConstLp_set (hs := MeasurableSet.iUnion hfm) (hμs := hfin _)
          (ht := hBm) (hμt := fun _ => hfin _) ENNReal.one_ne_top hlim)
        (Eventually.of_forall hB)
  -- all of L¹
  have hall : ∀ G : Lp ℝ 1 ν, G ∈ K := by
    refine Lp.induction ENNReal.one_ne_top (motive := fun G => G ∈ K) ?_ ?_ hker
    · intro c A hA hμA
      have : (Lp.simpleFunc.indicatorConst 1 hA hμA.ne c : Lp ℝ 1 ν) =
          c • indicatorConstLp 1 hA (hfin _) (1:ℝ) := by
        rw [Lp.simpleFunc.coe_indicatorConst]
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hA) (hμs := hμA.ne) (c := c),
          Lp.coeFn_smul c (indicatorConstLp 1 hA (hfin _) (1:ℝ)),
          indicatorConstLp_coeFn (p := 1) (hs := hA) (hμs := hfin _) (c := (1:ℝ))] with x h1 h2 h3
        rw [h1, h2, Pi.smul_apply, h3]
        by_cases hx : x ∈ A <;> simp [hx]
      rw [this]
      exact Submodule.smul_mem _ c (hset A hA)
    · intro f g _ _ _ hf hg
      exact add_mem hf hg
  -- the given function
  have hFL : MemLp F 1 ν :=
    MemLp.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  exact Pf_congr _ _ (MemLp.coeFn_toLp hFL) ((memT _).1 (hall (hFL.toLp F)))

end Abstract

lemma several : severalStatement := by
  intro Ω mΩ μ hμ ℱ n X hX hM r s t hs F hF hFb
  obtain ⟨C, hC⟩ := hFb
  set σ := Tuple.sort t
  have hmono : Monotone (t ∘ σ) := Tuple.monotone_sort t
  let F' : (Fin r → Fin n → ℝ) → ℝ := fun y => F (fun i => y (σ.symm i))
  have hF' : Measurable F' := hF.comp (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  have h := ordered hX hM r s (t ∘ σ) hmono (fun i => hs _) F' hF' C (fun x => hC _)
  have heq : (fun ω => F' (fun i => X ((t ∘ σ) i) ω)) = fun ω => F (fun i => X (t i) ω) := by
    funext ω
    simp [F', Equiv.apply_symm_apply]
  rw [heq] at h
  obtain ⟨g, hg, hge⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap (X s) inferInstance)
      (f := fun ω => F (fun i => X (t i) ω)) (μ := μ)).exists_eq_measurable_comp
  exact ⟨g, hg.measurable, h.trans (EventuallyEq.of_eq hge)⟩

lemma markov : Standalone.SeparableMeetingMarkovSeveral.markovStatement := by
  intro Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z hset r s t hs F hF hFb
  have hset' := hset
  obtain ⟨hTd, hlast, hcoef, hψc, ⟨Kψ, hψ⟩, ⟨Lψ, hψL⟩, hg, hZc, hZsol⟩ := hset'
  have hsol := Novel.SeparableMeetingMarkovSolutionProof.solution Ω mΩ S P p d N drv Td Hor
    hTd hlast beta Sigma psi g Kψ Lψ z0 Z hcoef hψc hψ hψL hg hZc hZsol
  exact several Ω mΩ S.μ inferInstance S.ℱ _ (Standalone.SeparableMeetingMarkovSolution.XH028
    S drv Td Hor psi g Z) hsol.1
    (fun s t hst f hf => (Novel.SeparableMeetingMarkovPropertyProof.markov Ω mΩ S P M hB p d N
      drv Td Hor beta Sigma psi g z0 Z hset s t hst f hf).1) r s t hs F hF hFb

lemma curve : Standalone.SeparableMeetingMarkovSeveral.curveStatement := by
  intro Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z f0 hset r s t T hs F hF hFb
  obtain ⟨C, hC⟩ := hFb
  have hΛ (i : Fin r) := (Novel.SeparableMeetingMarkovRealizationProof.lambda p d N f0 g
    (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k))).2 (T i)
  exact markov Ω mΩ S P M hB p d N drv Td Hor beta Sigma psi g z0 Z hset r s t hs
    (fun y => F (fun i => Standalone.SeparableMeetingMarkovRealization.Lambda028 f0 g
      (fun j k => Standalone.SeparableMeetingShapes.G026 (g j k)) (y i) (T i)))
    (hF.comp (measurable_pi_iff.2 fun i => (hΛ i).measurable.comp (measurable_pi_apply i)))
    ⟨C, fun y => hC _⟩

theorem separableMeetingMarkovSeveral : Standalone.SeparableMeetingMarkovSeveral.statement :=
  ⟨several, markov, curve⟩

end Novel.SeparableMeetingMarkovSeveralProof

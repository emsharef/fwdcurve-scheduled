import Standalone.MaturityShapeListing
import Novel.DiffusionMeetingCalendarProof
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
  Standalone.DiffusionMeetingCalendar Standalone.ListedSr3Identification
  Standalone.MaturityShapeListing
open Novel.DiffusionMeetingCalendarProof (yr_lt yr_le)
namespace Novel.MaturityShapeListingProof

/-! ### The gaps of the listing -/

lemma le_days : ∀ (i : Fin 16) (ℓ : Fin 12),
    meetings.getD i 0 ≤ reducedGaps.getD (ℓ.val + 1) 0 ↔ gapOf i ≤ ℓ := by decide

lemma lt_days : ∀ (i : Fin 16) (ℓ : Fin 12),
    reducedGaps.getD ℓ 0 < meetings.getD i 0 ↔ ℓ ≤ gapOf i := by decide

lemma TCal_eq (i : Fin 16) : TCal i = yr (meetings.getD i 0) := rfl
lemma SList_succ (ℓ : Fin 12) : SList ℓ.succ = yr (reducedGaps.getD (ℓ.val + 1) 0) := by
  simp [SList, Fin.val_succ]
lemma SList_castSucc (ℓ : Fin 12) : SList ℓ.castSucc = yr (reducedGaps.getD ℓ 0) := by
  simp [SList]

lemma le_iff (i : Fin 16) (ℓ : Fin 12) : TCal i ≤ SList ℓ.succ ↔ gapOf i ≤ ℓ := by
  rw [TCal_eq, SList_succ, yr_le, le_days]

lemma lt_iff (i : Fin 16) (ℓ : Fin 12) : SList ℓ.castSucc < TCal i ↔ ℓ ≤ gapOf i := by
  rw [TCal_eq, SList_castSucc, yr_lt, lt_days]

lemma countsS : countsStatement := by
  refine ⟨by decide, fun i ℓ => ?_, fun i => ?_, fun i h => ?_⟩
  · rw [lt_iff, le_iff]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  · have h1 : ∀ i : Fin 16, reducedGaps.getD 0 0 < meetings.getD i 0 := by decide
    have h2 : ∀ i : Fin 16, meetings.getD i 0 ≤ reducedGaps.getD 12 0 := by decide
    exact ⟨by rw [TCal_eq]; exact yr_lt.2 (h1 i), by rw [TCal_eq]; exact yr_le.2 (h2 i)⟩
  · rw [lt_iff, le_iff] at h
    have : gapOf i ≠ 0 := by revert i; decide
    exact this (le_antisymm h.2 h.1)

/-! ### The rows of the panel -/

/-- `Σ_{m ≤ ℓ} Σ_{T_i ∈ G_m} v_i`. -/
noncomputable def rowSum (ℓ : Fin 12) : Fin 16 ⊕ Fin 1 → ℝ :=
  ∑ m ∈ Finset.univ.filter (· ≤ ℓ), gapSum m

lemma rowSum_inl (ℓ : Fin 12) (i : Fin 16) : rowSum ℓ (Sum.inl i) = if gapOf i ≤ ℓ then 1 else 0 := by
  simp only [rowSum, Finset.sum_apply, gapSum, Sum.elim_inl]
  rw [Finset.sum_ite_eq]
  simp

lemma rowSum_inr (ℓ : Fin 12) (p : Fin 1) : rowSum ℓ (Sum.inr p) = 0 := by
  simp [rowSum, Finset.sum_apply, gapSum]

section
variable (D : Fin 13 → Fin 1 → ℝ)

lemma panel_inl (ℓ : Fin 12) (i : Fin 16) :
    panelD TCal SList D ℓ (Sum.inl i) = if gapOf i ≤ ℓ then 1 else 0 := by
  simp only [panelD, Sum.elim_inl, le_iff]

/-- Row `ℓ` is `D_{ℓ+1} u + Σ_{m ≤ ℓ} Σ_{T_i ∈ G_m} v_i`. -/
lemma row_eq (ℓ : Fin 12) : (panelD TCal SList D).row ℓ = D ℓ.succ 0 • eu + rowSum ℓ := by
  funext k
  rcases k with i | p
  · simp [row, panel_inl, eu, rowSum_inl]
  · rw [Fin.fin_one_eq_zero p]
    simp [row, panelD, eu, rowSum_inr]

lemma gapSum_zero : gapSum 0 = 0 := by
  funext k
  rcases k with i | p
  · have : gapOf i ≠ 0 := by revert i; decide
    simp [gapSum, this]
  · simp [gapSum]

lemma rowSum_zero : rowSum 0 = 0 := by
  funext k
  rcases k with i | p
  · have : ¬ gapOf i ≤ 0 := by revert i; decide
    simp [rowSum_inl, this]
  · simp [rowSum_inr]

variable {D}

lemma span_eq (hD1 : D 1 0 ≠ 0) :
    Submodule.span ℝ (Set.range (panelD TCal SList D).row) = Submodule.span ℝ (Set.range gen) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨ℓ, rfl⟩
    rw [row_eq]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨some m, rfl⟩)
  · have heu : eu ∈ Submodule.span ℝ (Set.range (panelD TCal SList D).row) := by
      have h0 := row_eq D 0
      rw [rowSum_zero, add_zero] at h0
      have : eu = (D 1 0)⁻¹ • (panelD TCal SList D).row 0 := by
        rw [h0, smul_smul, show Fin.succ (0 : Fin 12) = 1 from rfl, inv_mul_cancel₀ hD1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    rw [Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    rcases o with _ | ℓ
    · exact heu
    · simp only [gen, Option.elim_some]
      by_cases hℓ : ℓ = 0
      · subst hℓ; rw [gapSum_zero]; exact Submodule.zero_mem _
      · set ℓ' : Fin 12 := ⟨ℓ.val - 1, by omega⟩
        have hne : ℓ.val ≠ 0 := fun h => hℓ (Fin.ext h)
        have hdiff : gapSum ℓ = (panelD TCal SList D).row ℓ - (panelD TCal SList D).row ℓ' -
            (D ℓ.succ 0 - D ℓ'.succ 0) • eu := by
          rw [row_eq, row_eq]
          funext k
          rcases k with i | p
          · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eu, Sum.elim_inl,
              mul_zero, zero_add, sub_zero, rowSum_inl, gapSum]
            rcases lt_trichotomy (gapOf i).val ℓ.val with h | h | h
            · have h1 : gapOf i ≤ ℓ := Fin.le_def.2 h.le
              have h2 : gapOf i ≤ ℓ' := Fin.le_def.2 (by simp only [ℓ']; omega)
              have h3 : gapOf i ≠ ℓ := fun e => by rw [e] at h; exact lt_irrefl _ h
              simp [h1, h2, h3]
            · have h1 : gapOf i = ℓ := Fin.ext h
              have h2 : ¬ gapOf i ≤ ℓ' := fun e => by
                have := Fin.le_def.1 e; simp only [ℓ'] at this; omega
              rw [h1] at h2 ⊢
              simp [h2]
            · have h1 : ¬ gapOf i ≤ ℓ := fun e => by have := Fin.le_def.1 e; omega
              have h2 : ¬ gapOf i ≤ ℓ' := fun e => by
                have := Fin.le_def.1 e; simp only [ℓ'] at this; omega
              have h3 : gapOf i ≠ ℓ := fun e => by rw [e] at h; exact lt_irrefl _ h
              simp [h1, h2, h3]
          · rw [Fin.fin_one_eq_zero p]
            simp [eu, gapSum, rowSum_inr]
        rw [hdiff]
        exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨ℓ, rfl⟩)
          (Submodule.subset_span ⟨ℓ', rfl⟩)) (Submodule.smul_mem _ _ heu)
end

/-! ### Dimension ten -/

/-- The ten nonzero generators: `u` and the nine gaps with meetings. -/
def g10 : Fin 10 → Fin 16 ⊕ Fin 1 → ℝ :=
  ![eu, gapSum 1, gapSum 3, gapSum 4, gapSum 6, gapSum 7, gapSum 8, gapSum 9, gapSum 10, gapSum 11]

lemma gapSum_empty (ℓ : Fin 12) (h : ∀ i, gapOf i ≠ ℓ) : gapSum ℓ = 0 := by
  funext k
  rcases k with i | p
  · simp [gapSum, h i]
  · simp [gapSum]

lemma span_gen : Submodule.span ℝ (Set.range gen) = Submodule.span ℝ (Set.range g10) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    rcases o with _ | ℓ
    · exact Submodule.subset_span ⟨0, rfl⟩
    · simp only [gen, Option.elim_some]
      fin_cases ℓ
      · rw [gapSum_empty _ (by decide)]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨1, rfl⟩
      · rw [gapSum_empty _ (by decide)]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨2, rfl⟩
      · exact Submodule.subset_span ⟨3, rfl⟩
      · rw [gapSum_empty _ (by decide)]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨4, rfl⟩
      · exact Submodule.subset_span ⟨5, rfl⟩
      · exact Submodule.subset_span ⟨6, rfl⟩
      · exact Submodule.subset_span ⟨7, rfl⟩
      · exact Submodule.subset_span ⟨8, rfl⟩
      · exact Submodule.subset_span ⟨9, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Submodule.subset_span ⟨none, rfl⟩
    all_goals exact Submodule.subset_span ⟨some _, rfl⟩

lemma g10_li : LinearIndependent ℝ g10 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have ev : ∀ k, (∑ j, c j • g10 j) k = 0 := fun k => by rw [hc]; rfl
  have e0 := ev (Sum.inr 0)
  have e1 := ev (Sum.inl 0)
  have e2 := ev (Sum.inl 1)
  have e3 := ev (Sum.inl 2)
  have e4 := ev (Sum.inl 3)
  have e5 := ev (Sum.inl 5)
  have e6 := ev (Sum.inl 8)
  have e7 := ev (Sum.inl 9)
  have e8 := ev (Sum.inl 12)
  have e9 := ev (Sum.inl 13)
  simp (config := {decide := true}) [Fin.sum_univ_succ, g10, gapSum, eu, gapOf] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  intro j
  fin_cases j <;> assumption

lemma finrank_gen : Module.finrank ℝ (Submodule.span ℝ (Set.range gen)) = 10 := by
  rw [span_gen, finrank_span_eq_card g10_li]
  simp

/-! ### Determined functionals -/

section
variable {D : Fin 13 → Fin 1 → ℝ}

/-- A determined functional agrees on meetings of the same gap. -/
lemma det_same (c : Fin 16 ⊕ Fin 1 → ℝ) (hc : Determined (panelD TCal SList D) c) (i j : Fin 16)
    (h : gapOf i = gapOf j) : c (Sum.inl i) = c (Sum.inl j) := by
  set x : Fin 16 ⊕ Fin 1 → ℝ := Pi.single (Sum.inl i) 1 - Pi.single (Sum.inl j) 1
  have hker : (panelD TCal SList D).mulVec x = 0 := by
    funext ℓ
    simp only [x, mulVec_sub, Pi.sub_apply, Pi.zero_apply]
    simp only [mulVec, dotProduct_single, mul_one, panel_inl, h]
    ring
  set θ : Fin 16 ⊕ Fin 1 → ℝ := fun _ => 1
  have hpos : ∀ k, 0 < (θ + (1 / 2 : ℝ) • x) k := fun k => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, θ, x, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  have := hc θ (θ + (1 / 2 : ℝ) • x) (fun _ => one_pos) hpos
    (by rw [mulVec_add, mulVec_smul, hker, smul_zero, add_zero])
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have hx : dotProduct c x = 0 := by linarith
  simp only [x, dotProduct_sub, dotProduct_single, mul_one] at hx
  linarith

/-- A representative meeting of each gap (arbitrary for the empty ones). -/
def rep : Fin 12 → Fin 16 := ![0, 0, 0, 1, 2, 0, 3, 5, 8, 9, 12, 13]

lemma det_iff (hD1 : D 1 0 ≠ 0) (c : Fin 16 ⊕ Fin 1 → ℝ) :
    Determined (panelD TCal SList D) c ↔ c ∈ Submodule.span ℝ (Set.range gen) := by
  constructor
  · intro hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun o => o.elim (c (Sum.inr 0)) fun ℓ => c (Sum.inl (rep ℓ)), ?_⟩
    rw [Fintype.sum_option]
    funext k
    rcases k with i | p
    · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gen, Option.elim_none,
        Option.elim_some, eu, gapSum, Sum.elim_inl, mul_zero, zero_add, mul_ite, mul_one]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      exact det_same c hc _ _ (by revert i; decide)
    · rw [Fin.fin_one_eq_zero p]
      simp [gen, eu, gapSum]
  · intro hc θ θ' _ _ he
    rw [← span_eq hD1, Submodule.mem_span_range_iff_exists_fun] at hc
    obtain ⟨y, hy⟩ := hc
    have hv : c = vecMul y (panelD TCal SList D) := by
      rw [← hy]
      funext k
      simp [vecMul, dotProduct, Finset.sum_apply, row]
    rw [hv, ← dotProduct_mulVec, ← dotProduct_mulVec, he]

lemma spanS : spanStatement := by
  intro D _ hD1
  refine ⟨det_iff hD1, finrank_gen, ?_⟩
  rw [rank_eq_finrank_span_row, span_eq hD1, finrank_gen]

lemma identifiedS : identifiedStatement := by
  intro D _ hD1
  refine ⟨(det_iff hD1 _).2 (Submodule.subset_span ⟨none, rfl⟩),
    fun ℓ => (det_iff hD1 _).2 (Submodule.subset_span ⟨some ℓ, rfl⟩), fun i => ?_⟩
  have alone : ∀ i : Fin 16, (∀ j, gapOf j = gapOf i → j = i) ↔
      i ∈ ({0, 1, 2, 8, 12} : Finset (Fin 16)) := by decide
  rw [← alone]
  constructor
  · intro hd j hj
    by_contra hne
    have := det_same _ hd j i hj
    simp [hne] at this
  · intro h
    have : (Pi.single (Sum.inl i) 1 : Fin 16 ⊕ Fin 1 → ℝ) = gapSum (gapOf i) := by
      funext k
      rcases k with j | p
      · by_cases hj : j = i
        · subst hj; simp [gapSum]
        · have hg : gapOf j ≠ gapOf i := fun e => hj (h j e)
          simp [gapSum, hj, hg]
      · simp [gapSum]
    rw [this]
    exact (det_iff hD1 _).2 (Submodule.subset_span ⟨some _, rfl⟩)
end

lemma datesS : datesStatement := ⟨by decide, by decide, by decide, by decide⟩

theorem maturityShapeListing : Standalone.MaturityShapeListing.statement :=
  ⟨countsS, spanS, identifiedS, datesS⟩

end Novel.MaturityShapeListingProof

import Standalone.DiffusionMeetingRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Matrix
open Standalone.DiffusionMeetingRank
namespace Novel.DiffusionMeetingRankProof

variable {N P L : ℕ}

lemma lam_add {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) (c₀ c₁ : ℝ) :
    lam lo mid c₀ c₁ + lam mid hi c₀ c₁ = lam lo hi c₀ c₁ := by
  simp only [lam, max_def, min_def]
  split_ifs <;> linarith

lemma lam_self (a c₀ c₁ : ℝ) : lam a a c₀ c₁ = 0 := by
  simp only [lam, max_def, min_def]
  split_ifs <;> linarith

/-- `Q(S_n)` for `θ = (v, u)`. -/
noncomputable def Qf (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (n : Fin (L + 1)) : ℝ :=
  ∑ i, (if T i ≤ S n then 1 else 0) * θ (Sum.inl i) +
    ∑ p, lam 0 (S n) (c p.castSucc) (c p.succ) * θ (Sum.inr p)

/-- The increment over the gap `ℓ`. -/
noncomputable def Df (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then 1 else 0) * θ (Sum.inl i) +
    ∑ p, lam (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) * θ (Sum.inr p)

lemma panel_apply (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) : (panel T c S).mulVec θ ℓ = Qf T c S θ ℓ.succ := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, panel, Sum.elim_inl, Sum.elim_inr, Qf]

lemma Qf_zero (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) (hS0 : S 0 = 0)
    (hT : ∀ i, 0 < T i) (θ : Fin N ⊕ Fin P → ℝ) : Qf T c S θ 0 = 0 := by
  simp only [Qf, hS0, lam_self, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_eq_zero fun i _ => by simp [not_le.2 (hT i)]

lemma Df_eq (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) (hS : StrictMono S)
    (hS0 : S 0 = 0) (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) :
    Df T c S θ ℓ = Qf T c S θ ℓ.succ - Qf T c S θ ℓ.castSucc := by
  have hle : S ℓ.castSucc ≤ S ℓ.succ := hS.monotone (Fin.castSucc_le_succ ℓ)
  have h0 : 0 ≤ S ℓ.castSucc := hS0 ▸ hS.monotone (Fin.zero_le _)
  simp only [Df, Qf]
  have e1 : ∀ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then (1:ℝ) else 0) =
      (if T i ≤ S ℓ.succ then 1 else 0) - (if T i ≤ S ℓ.castSucc then 1 else 0) := fun i => by
    by_cases h1 : T i ≤ S ℓ.castSucc
    · simp [h1, h1.trans hle, not_lt.2 h1]
    · by_cases h2 : T i ≤ S ℓ.succ
      · simp [h1, h2, not_le.1 h1]
      · simp [h1, h2]
  have e2 : ∀ p : Fin P, lam (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) =
      lam 0 (S ℓ.succ) (c p.castSucc) (c p.succ) - lam 0 (S ℓ.castSucc) (c p.castSucc) (c p.succ) :=
    fun p => by linarith [lam_add h0 hle (c p.castSucc) (c p.succ)]
  simp only [e1, e2, sub_mul, Finset.sum_sub_distrib]
  ring

section
variable {T : Fin N → ℝ} {c : Fin (P + 1) → ℝ} {S : Fin (L + 1) → ℝ}

lemma panel_zero_iff (hS : StrictMono S) (hS0 : S 0 = 0) (hT : ∀ i, 0 < T i)
    (θ : Fin N ⊕ Fin P → ℝ) : (panel T c S).mulVec θ = 0 ↔ ∀ ℓ, Df T c S θ ℓ = 0 := by
  constructor
  · intro h ℓ
    have hq : ∀ k : Fin L, Qf T c S θ k.succ = 0 := fun k => by
      rw [← panel_apply]; simp [h]
    rw [Df_eq T c S hS hS0, hq ℓ]
    rcases Fin.eq_zero_or_eq_succ ℓ.castSucc with h0 | ⟨j, hj⟩
    · rw [h0, Qf_zero T c S hS0 hT]; ring
    · rw [hj, hq j]; ring
  · intro hD
    have hq : ∀ n : Fin (L + 1), Qf T c S θ n = 0 := by
      intro n
      induction n using Fin.induction with
      | zero => exact Qf_zero T c S hS0 hT θ
      | succ k ih =>
        have := hD k
        rw [Df_eq T c S hS hS0, ih] at this
        linarith
    funext ℓ
    rw [panel_apply, hq]
    rfl

lemma gap_exists (hS0 : S 0 = 0) {t : ℝ} (ht : 0 < t) (htL : t ≤ S (Fin.last L)) :
    ∃ ℓ : Fin L, S ℓ.castSucc < t ∧ t ≤ S ℓ.succ := by
  by_contra hne
  push Not at hne
  have : ∀ n : Fin (L + 1), S n < t := by
    intro n
    induction n using Fin.induction with
    | zero => rw [hS0]; exact ht
    | succ k ih => exact hne k ih
  exact absurd htL (not_le.2 (this _))

lemma gap_unique (hS : StrictMono S) {t : ℝ} {ℓ ℓ' : Fin L} (h1 : S ℓ.castSucc < t)
    (h2 : t ≤ S ℓ.succ) (h1' : S ℓ'.castSucc < t) (h2' : t ≤ S ℓ'.succ) : ℓ = ℓ' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : S ℓ.succ ≤ S ℓ'.castSucc := hS.monotone (Fin.succ_le_castSucc_iff.2 h)
    linarith
  · have : S ℓ'.succ ≤ S ℓ.castSucc := hS.monotone (Fin.succ_le_castSucc_iff.2 h)
    linarith

lemma injective_iff_zero {m n : Type*} [Fintype n] (A : Matrix m n ℝ) :
    Function.Injective A.mulVec ↔ ∀ θ, A.mulVec θ = 0 → θ = 0 := by
  constructor
  · intro h θ hθ
    exact h (by rw [hθ, mulVec_zero])
  · intro h θ θ' he
    have := h (θ - θ') (by rw [mulVec_sub, he, sub_self])
    exact sub_eq_zero.1 this
end

section Rank
variable {T : Fin N → ℝ} {c : Fin (P + 1) → ℝ} {S : Fin (L + 1) → ℝ}

/-- The `ℓ`-th increment of a pure `v`-vector concentrated on meeting `i`. -/
lemma Df_single (i : Fin N) (a : ℝ) (ℓ : Fin L) :
    Df T c S (Pi.single (Sum.inl i) a) ℓ =
      (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then 1 else 0) * a := by
  simp only [Df, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma meetingFree_row (θ : Fin N ⊕ Fin P → ℝ) (ℓ : {ℓ : Fin L // MeetingFree T S ℓ}) :
    Df T c S θ ℓ.1 = (lamE T c S).mulVec (fun p => θ (Sum.inr p)) ℓ := by
  simp only [Df, mulVec, dotProduct, lamE]
  have : ∀ i, (if S ℓ.1.castSucc < T i ∧ T i ≤ S ℓ.1.succ then (1:ℝ) else 0) = 0 :=
    fun i => by simp [ℓ.2 i]
  simp [this]

/-- A gap holding exactly the meeting `i`. -/
lemma single_row {ℓ : Fin L} {i : Fin N} (hi : S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ)
    (h2 : ∀ j, S ℓ.castSucc < T j → T j ≤ S ℓ.succ → j = i) (θ : Fin N ⊕ Fin P → ℝ) :
    Df T c S θ ℓ = θ (Sum.inl i) +
      ∑ p, lam (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) * θ (Sum.inr p) := by
  simp only [Df]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [ite_eq_right (fun h => hj (h2 j h.1 h.2)), zero_mul]) (by simp), ite_eq_left hi, one_mul]

lemma rankS : Standalone.DiffusionMeetingRank.rankStatement := by
  intro N P L T c S hS hS0 hT
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
  constructor
  · intro hinj
    -- (i)
    have hi : ∀ i, T i ≤ S (Fin.last L) := by
      intro i
      by_contra hlt
      push Not at hlt
      have hz := hinj (Pi.single (Sum.inl i) 1) ((panel_zero_iff hS hS0 hT _).2 fun ℓ => by
        rw [Df_single]
        have : ¬ (S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ) := fun h =>
          absurd (h.2.trans (hS.monotone (Fin.le_last _))) (not_le.2 hlt)
        simp [this])
      have := congrFun hz (Sum.inl i)
      simp at this
    -- (ii)
    have hii : ∀ (ℓ : Fin L) (i j : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
        S ℓ.castSucc < T j → T j ≤ S ℓ.succ → i = j := by
      intro ℓ i j hi1 hi2 hj1 hj2
      by_contra hne
      have hz := hinj (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inl j) 1)
        ((panel_zero_iff hS hS0 hT _).2 fun k => by
          have hsub : Df T c S (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inl j) 1) k =
              Df T c S (Pi.single (Sum.inl i) 1) k - Df T c S (Pi.single (Sum.inl j) 1) k := by
            simp only [Df, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
            ring
          rw [hsub, Df_single, Df_single]
          have hiff : (S k.castSucc < T i ∧ T i ≤ S k.succ) ↔
              (S k.castSucc < T j ∧ T j ≤ S k.succ) := by
            constructor
            · intro h
              have := gap_unique hS h.1 h.2 hi1 hi2
              subst this
              exact ⟨hj1, hj2⟩
            · intro h
              have := gap_unique hS h.1 h.2 hj1 hj2
              subst this
              exact ⟨hi1, hi2⟩
          by_cases h : S k.castSucc < T i ∧ T i ≤ S k.succ
          · simp [h, hiff.1 h]
          · simp [h, mt hiff.2 h])
      have := congrFun hz (Sum.inl i)
      simp [hne] at this
    refine ⟨hi, hii, ?_⟩
    -- (iii)
    rw [Novel.DiffusionMeetingRankProof.injective_iff_zero]
    intro y hy
    choose g hg using fun i => gap_exists hS0 (hT i) (hi i)
    set x : Fin N → ℝ := fun i =>
      -∑ p, lam (S (g i).castSucc) (S (g i).succ) (c p.castSucc) (c p.succ) * y p
    have hz := hinj (Sum.elim x y) ((panel_zero_iff hS hS0 hT _).2 fun k => by
      by_cases hk : MeetingFree T S k
      · rw [meetingFree_row _ ⟨k, hk⟩]
        simpa using congrFun hy ⟨k, hk⟩
      · simp only [MeetingFree, not_forall, not_not] at hk
        obtain ⟨i, hik⟩ := hk
        rw [single_row hik (fun j h1 h2 => hii k j i h1 h2 hik.1 hik.2)]
        have hgk : g i = k := gap_unique hS (hg i).1 (hg i).2 hik.1 hik.2
        simp only [Sum.elim_inl, Sum.elim_inr, x, hgk]
        ring)
    funext p
    simpa using congrFun hz (Sum.inr p)
  · rintro ⟨hi, hii, hiii⟩ θ hθ
    have hD := (panel_zero_iff hS hS0 hT θ).1 hθ
    have hy : (fun p => θ (Sum.inr p)) = 0 := by
      rw [Novel.DiffusionMeetingRankProof.injective_iff_zero] at hiii
      refine hiii _ (funext fun ℓ => ?_)
      rw [← meetingFree_row]
      exact hD ℓ.1
    funext k
    cases k with
    | inr p => exact congrFun hy p
    | inl i =>
      obtain ⟨ℓ, hℓ⟩ := gap_exists hS0 (hT i) (hi i)
      have := hD ℓ
      rw [single_row hℓ (fun j h1 h2 => hii ℓ j i h1 h2 hℓ.1 hℓ.2)] at this
      have h0 : ∀ p, θ (Sum.inr p) = 0 := fun p => congrFun hy p
      simpa [h0] using this
end Rank

lemma rank_iff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix (Fin L) n ℝ) :
    A.rank = Fintype.card n ↔ Function.Injective A.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hr : A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl
  rw [hr, show Function.Injective A.mulVec ↔ Function.Injective A.mulVecLin from Iff.rfl,
    ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

/-- Off an injective panel, a strictly positive `θ` moves along a kernel vector. -/
lemma perturb {n : Type*} [Fintype n] (A : Matrix (Fin L) n ℝ) (hA : ¬ Function.Injective A.mulVec)
    (θ : n → ℝ) (hθ : ∀ k, 0 < θ k) :
    ∃ θ' : n → ℝ, (∀ k, 0 < θ' k) ∧ θ' ≠ θ ∧ A.mulVec θ' = A.mulVec θ := by
  rw [Novel.DiffusionMeetingRankProof.injective_iff_zero] at hA
  push Not at hA
  obtain ⟨κ, hκ, hκ0⟩ := hA
  set Sm := ∑ j, |κ j| / θ j
  have hSm : 0 ≤ Sm := Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (hθ j).le
  set ε := 1 / (1 + Sm)
  have hε : 0 < ε := by positivity
  refine ⟨θ + ε • κ, fun k => ?_, fun h => hκ0 ?_, ?_⟩
  · have hk : |κ k| / θ k ≤ Sm :=
      Finset.single_le_sum (f := fun j => |κ j| / θ j)
        (fun j _ => div_nonneg (abs_nonneg _) (hθ j).le) (Finset.mem_univ k)
    have h1 : ε * |κ k| < θ k := by
      have : |κ k| ≤ Sm * θ k := by rwa [div_le_iff₀ (hθ k)] at hk
      have hlt : ε * Sm < 1 := by
        simp only [ε]
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith
      calc ε * |κ k| ≤ ε * (Sm * θ k) := mul_le_mul_of_nonneg_left this hε.le
        _ = (ε * Sm) * θ k := by ring
        _ < 1 * θ k := mul_lt_mul_of_pos_right hlt (hθ k)
        _ = θ k := one_mul _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [neg_abs_le (κ k), abs_nonneg (κ k)]
  · have : ε • κ = 0 := by
      have := congrArg (· - θ) h
      simpa using this
    exact (smul_eq_zero.1 this).resolve_left hε.ne'
  · rw [mulVec_add, mulVec_smul, hκ, smul_zero, add_zero]

lemma injectiveS : Standalone.DiffusionMeetingRank.injectiveStatement := by
  intro N P L T c S
  refine ⟨?_, fun h θ hθ => perturb _ h θ hθ⟩
  rw [← rank_iff]
  simp

theorem diffusionMeetingRank : Standalone.DiffusionMeetingRank.statement := ⟨injectiveS, rankS⟩

end Novel.DiffusionMeetingRankProof

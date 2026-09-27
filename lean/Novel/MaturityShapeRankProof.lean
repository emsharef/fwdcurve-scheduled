import Standalone.MaturityShapeRank
import Novel.DiffusionMeetingRankProof

open Matrix
open Standalone.DiffusionMeetingRank Standalone.MaturityShapeRank
open Novel.DiffusionMeetingRankProof (gap_exists gap_unique injective_iff_zero rank_iff perturb)
namespace Novel.MaturityShapeRankProof

variable {N P L : ℕ} {T : Fin N → ℝ} {S : Fin (L + 1) → ℝ} {D : Fin (L + 1) → Fin P → ℝ}

/-- The increment over the gap `ℓ`. -/
noncomputable def Dg (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ) (D : Fin (L + 1) → Fin P → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then 1 else 0) * θ (Sum.inl i) +
    ∑ p, lamT D ℓ p * θ (Sum.inr p)

lemma panel_apply (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) :
    (panelD T S D).mulVec θ ℓ = Qp T S D θ ℓ.succ := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, panelD, Sum.elim_inl, Sum.elim_inr, Qp,
    ite_mul, one_mul, zero_mul]

lemma Qp_zero (hS0 : S 0 = 0) (hT : ∀ i, 0 < T i) (hD : D 0 = 0) (θ : Fin N ⊕ Fin P → ℝ) :
    Qp T S D θ 0 = 0 := by
  simp only [Qp, hS0, hD, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_eq_zero fun i _ => by simp [not_le.2 (hT i)]

lemma Dg_eq (hS : StrictMono S) (θ : Fin N ⊕ Fin P → ℝ) (ℓ : Fin L) :
    Dg T S D θ ℓ = Qp T S D θ ℓ.succ - Qp T S D θ ℓ.castSucc := by
  have hle : S ℓ.castSucc ≤ S ℓ.succ := hS.monotone (Fin.castSucc_le_succ ℓ)
  simp only [Dg, Qp, lamT]
  have e1 : ∀ i, (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then (1:ℝ) else 0) * θ (Sum.inl i) =
      (if T i ≤ S ℓ.succ then θ (Sum.inl i) else 0) -
        (if T i ≤ S ℓ.castSucc then θ (Sum.inl i) else 0) := fun i => by
    by_cases h1 : T i ≤ S ℓ.castSucc
    · simp [h1, h1.trans hle, not_lt.2 h1]
    · by_cases h2 : T i ≤ S ℓ.succ
      · simp [h1, h2, not_le.1 h1]
      · simp [h1, h2]
  simp only [e1, sub_mul, Finset.sum_sub_distrib]
  ring

lemma panel_zero_iff (hS : StrictMono S) (hS0 : S 0 = 0) (hT : ∀ i, 0 < T i) (hD : D 0 = 0)
    (θ : Fin N ⊕ Fin P → ℝ) : (panelD T S D).mulVec θ = 0 ↔ ∀ ℓ, Dg T S D θ ℓ = 0 := by
  constructor
  · intro h ℓ
    have hq : ∀ k : Fin L, Qp T S D θ k.succ = 0 := fun k => by
      rw [← panel_apply]; simp [h]
    rw [Dg_eq hS, hq ℓ]
    rcases Fin.eq_zero_or_eq_succ ℓ.castSucc with h0 | ⟨j, hj⟩
    · rw [h0, Qp_zero hS0 hT hD]; ring
    · rw [hj, hq j]; ring
  · intro hDg
    have hq : ∀ n : Fin (L + 1), Qp T S D θ n = 0 := by
      intro n
      induction n using Fin.induction with
      | zero => exact Qp_zero hS0 hT hD θ
      | succ k ih =>
        have := hDg k
        rw [Dg_eq hS, ih] at this
        linarith
    funext ℓ
    rw [panel_apply, hq]
    rfl

lemma Dg_single (i : Fin N) (a : ℝ) (ℓ : Fin L) :
    Dg T S D (Pi.single (Sum.inl i) a) ℓ =
      (if S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ then 1 else 0) * a := by
  simp only [Dg, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma meetingFree_row (θ : Fin N ⊕ Fin P → ℝ) (ℓ : {ℓ : Fin L // MeetingFree T S ℓ}) :
    Dg T S D θ ℓ.1 = (lamTE T S D).mulVec (fun p => θ (Sum.inr p)) ℓ := by
  simp only [Dg, mulVec, dotProduct, lamTE]
  have : ∀ i, (if S ℓ.1.castSucc < T i ∧ T i ≤ S ℓ.1.succ then (1:ℝ) else 0) = 0 :=
    fun i => by simp [ℓ.2 i]
  simp [this]

/-- A gap holding exactly the meeting `i`. -/
lemma single_row {ℓ : Fin L} {i : Fin N} (hi : S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ)
    (h2 : ∀ j, S ℓ.castSucc < T j → T j ≤ S ℓ.succ → j = i) (θ : Fin N ⊕ Fin P → ℝ) :
    Dg T S D θ ℓ = θ (Sum.inl i) + ∑ p, lamT D ℓ p * θ (Sum.inr p) := by
  simp only [Dg]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [ite_eq_right (fun h => hj (h2 j h.1 h.2)), zero_mul]) (by simp), ite_eq_left hi, one_mul]

lemma rankS : Standalone.MaturityShapeRank.rankStatement := by
  intro N P L T S D hS hS0 hT hD
  rw [injective_iff_zero]
  constructor
  · intro hinj
    have hi : ∀ i, T i ≤ S (Fin.last L) := by
      intro i
      by_contra hlt
      push Not at hlt
      have hz := hinj (Pi.single (Sum.inl i) 1) ((panel_zero_iff hS hS0 hT hD _).2 fun ℓ => by
        rw [Dg_single]
        have : ¬ (S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ) := fun h =>
          absurd (h.2.trans (hS.monotone (Fin.le_last _))) (not_le.2 hlt)
        simp [this])
      have := congrFun hz (Sum.inl i)
      simp at this
    have hii : ∀ (ℓ : Fin L) (i j : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
        S ℓ.castSucc < T j → T j ≤ S ℓ.succ → i = j := by
      intro ℓ i j hi1 hi2 hj1 hj2
      by_contra hne
      have hz := hinj (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inl j) 1)
        ((panel_zero_iff hS hS0 hT hD _).2 fun k => by
          have hsub : Dg T S D (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inl j) 1) k =
              Dg T S D (Pi.single (Sum.inl i) 1) k - Dg T S D (Pi.single (Sum.inl j) 1) k := by
            simp only [Dg, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
            ring
          rw [hsub, Dg_single, Dg_single]
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
    rw [injective_iff_zero]
    intro y hy
    choose g hg using fun i => gap_exists hS0 (hT i) (hi i)
    set x : Fin N → ℝ := fun i => -∑ p, lamT D (g i) p * y p
    have hz := hinj (Sum.elim x y) ((panel_zero_iff hS hS0 hT hD _).2 fun k => by
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
    have hDg := (panel_zero_iff hS hS0 hT hD θ).1 hθ
    have hy : (fun p => θ (Sum.inr p)) = 0 := by
      rw [injective_iff_zero] at hiii
      refine hiii _ (funext fun ℓ => ?_)
      rw [← meetingFree_row]
      exact hDg ℓ.1
    funext k
    cases k with
    | inr p => exact congrFun hy p
    | inl i =>
      obtain ⟨ℓ, hℓ⟩ := gap_exists hS0 (hT i) (hi i)
      have := hDg ℓ
      rw [single_row hℓ (fun j h1 h2 => hii ℓ j i h1 h2 hℓ.1 hℓ.2)] at this
      have h0 : ∀ p, θ (Sum.inr p) = 0 := fun p => congrFun hy p
      simpa [h0] using this

lemma injectiveS : Standalone.MaturityShapeRank.injectiveStatement := by
  intro N P L T S D
  refine ⟨?_, fun h θ hθ => perturb _ h θ hθ⟩
  rw [← rank_iff]
  simp

/-- An injective `n × P` matrix has at least `P` rows. -/
lemma card_le {n : Type*} [Finite n] (A : Matrix n (Fin P) ℝ) (h : Function.Injective A.mulVec) :
    P ≤ Nat.card n := by
  classical
  have := Fintype.ofFinite n
  have h' := LinearMap.finrank_le_finrank_of_injective (f := A.mulVecLin) h
  simpa [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using h'

lemma inversionS : Standalone.MaturityShapeRank.inversionStatement := by
  intro N P L T S D hS hS0 hT hD
  refine ⟨fun θ => ?_, fun hinj => card_le _ ((rankS N P L T S D hS hS0 hT hD).1 hinj).2.2⟩
  have hrow : ∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ},
      (lamTE T S D).mulVec (fun p => θ (Sum.inr p)) ℓ =
        Qp T S D θ ℓ.1.succ - Qp T S D θ ℓ.1.castSucc := fun ℓ => by
    rw [← meetingFree_row, Dg_eq hS]
  refine ⟨Qp_zero hS0 hT hD θ, fun ℓ => panel_apply θ ℓ, hrow,
    fun hinj u hu => hinj (funext fun ℓ => by rw [hu, hrow]), fun ℓ i h1 h2 h3 => ?_⟩
  have := single_row (D := D) ⟨h1, h2⟩ h3 θ
  rw [Dg_eq hS] at this
  linarith

theorem maturityShapeRank : Standalone.MaturityShapeRank.statement :=
  ⟨injectiveS, rankS, inversionS⟩

end Novel.MaturityShapeRankProof

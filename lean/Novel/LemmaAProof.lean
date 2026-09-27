import Standalone.LemmaA

/-!
# Claim 002 (Lemma A): proof

Follows `math/claims/002-lemma-a.md`. Step 1 of the claim is `piece` below: on any `[a, b)`
contained in one scheduled interval, `σ` is constant, so `∫_a^b σ = (b - a) • s_k` (2.9)
via `intervalIntegral.integral_congr_Ioo_of_le` (the endpoint `b` is null) and
`intervalIntegral.integral_const`. Step 3 is the chain (2.11)–(2.12):
`intervalIntegral.integral_add_adjacent_intervals` twice around the middle block, and
`intervalIntegral.sum_integral_adjacent_intervals_Ico` for the middle block itself.
-/

open MeasureTheory Set

namespace Novel.LemmaAProof

open Standalone.LemmaA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma mem_I_iff {τ : ℕ → ℝ} {N k : ℕ} {u : ℝ} :
    u ∈ I τ N k ↔ τ k ≤ u ∧ (k < N → u < τ (k + 1)) := by
  unfold I
  split_ifs with h <;> simp [h]

/-- (2.9): if `σ = v` on `[a, b)` and `a ≤ b` then `∫_a^b σ = (b - a) • v`. -/
lemma integral_eq_of_eqOn_Ico {σ : ℝ → E} {v : E} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ico a b, σ u = v) :
    ∫ u in a..b, σ u = (b - a) • v := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hab (g := fun _ => v)
    (fun u hu => h u (Ioo_subset_Ico_self hu))]
  exact intervalIntegral.integral_const v

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma intervalIntegrable_of_eqOn_Ico {σ : ℝ → E} {v : E} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ico a b, σ u = v) : IntervalIntegrable σ volume a b :=
  (intervalIntegrable_const (c := v)).congr_uIoo (by
    rw [uIoo_of_le hab]
    exact fun u hu => (h u (Ioo_subset_Ico_self hu)).symm)

/-- `σ` is the constant `s k` on `[a, b)` whenever `[a, b) ⊆ I_k`, so its integral there is
`(b - a) • s k` and it is interval integrable. -/
lemma piece {N : ℕ} {τ : ℕ → ℝ} {s : ℕ → E} {σ : ℝ → E}
    (hσ : ∀ k ≤ N, ∀ u ∈ I τ N k, σ u = s k) {k : ℕ} (hk : k ≤ N) {a b : ℝ}
    (hab : a ≤ b) (ha : τ k ≤ a) (hb : k < N → b ≤ τ (k + 1)) :
    (∫ u in a..b, σ u = (b - a) • s k) ∧ IntervalIntegrable σ volume a b := by
  have h : ∀ u ∈ Ico a b, σ u = s k := fun u hu =>
    hσ k hk u (mem_I_iff.2 ⟨ha.trans hu.1, fun hkN => hu.2.trans_le (hb hkN)⟩)
  exact ⟨integral_eq_of_eqOn_Ico hab h, intervalIntegrable_of_eqOn_Ico hab h⟩

theorem lemmaA : Standalone.LemmaA.statement := by
  intro N d τ s σ _hτ0 hτ hσ
  have mono : ∀ {m n : ℕ}, m ≤ n → n ≤ N → τ m ≤ τ n := fun hmn hn =>
    hτ.monotoneOn (mem_Iic.2 (hmn.trans hn)) (mem_Iic.2 hn) hmn
  -- Step 0: `j ≤ k`.
  have step0 : ∀ {t T : ℝ}, t ≤ T → ∀ {j k : ℕ}, j ≤ N → k ≤ N →
      t ∈ I τ N j → T ∈ I τ N k → j ≤ k := by
    intro t T htT j k hj hk ht hT
    rw [mem_I_iff] at ht hT
    by_contra hjk
    have hjk : k < j := Nat.lt_of_not_le hjk
    have hkN : k < N := lt_of_lt_of_le hjk hj
    have h1 : T < τ (k + 1) := hT.2 hkN
    have h2 : τ (k + 1) ≤ τ j := mono (Nat.succ_le_of_lt hjk) hj
    linarith [ht.1]
  -- (2.3).
  have main : ∀ t T : ℝ, t ≤ T → ∀ j ≤ N, ∀ k ≤ N, t ∈ I τ N j → T ∈ I τ N k →
      ∫ u in t..T, σ u = c τ s j k t + (T - max (τ k) t) • s k := by
    intro t T htT j hj k hk ht hT
    have hjk := step0 htT hj hk ht hT
    rw [mem_I_iff] at ht hT
    rcases hjk.lt_or_eq with hlt | rfl
    · -- Step 3: `k > j`, chain `t < T_{j+1} ≤ … ≤ T_k ≤ T`.
      have hjN : j < N := lt_of_lt_of_le hlt hk
      have ht1 : t < τ (j + 1) := ht.2 hjN
      have h1k : τ (j + 1) ≤ τ k := mono (Nat.succ_le_of_lt hlt) hk
      have hkT : τ k ≤ T := hT.1
      have hmax : max (τ k) t = τ k := max_eq_left (by linarith)
      have p1 := piece hσ hj (a := t) (b := τ (j + 1)) ht1.le ht.1 (fun _ => le_rfl)
      have p3 := piece hσ hk (a := τ k) (b := T) hkT le_rfl (fun hkN => (hT.2 hkN).le)
      have pm : ∀ m, j + 1 ≤ m → m < k →
          (∫ u in τ m..τ (m + 1), σ u = (τ (m + 1) - τ m) • s m) ∧
            IntervalIntegrable σ volume (τ m) (τ (m + 1)) := by
        intro m _ hmk
        have hmN : m < N := lt_of_lt_of_le hmk hk
        exact piece hσ hmN.le (mono (Nat.le_succ m) hmN) le_rfl (fun _ => le_rfl)
      have hmid_int : IntervalIntegrable σ volume (τ (j + 1)) (τ k) :=
        IntervalIntegrable.trans_iterate_Ico (Nat.succ_le_of_lt hlt)
          (fun m hm => (pm m hm.1 hm.2).2)
      have hmid_val : ∫ u in τ (j + 1)..τ k, σ u =
          ∑ m ∈ Finset.Ico (j + 1) k, (τ (m + 1) - τ m) • s m := by
        rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (Nat.succ_le_of_lt hlt)
          (fun m hm => (pm m hm.1 hm.2).2)]
        exact Finset.sum_congr rfl fun m hm =>
          (pm m (Finset.mem_Ico.1 hm).1 (Finset.mem_Ico.1 hm).2).1
      rw [← intervalIntegral.integral_add_adjacent_intervals p1.2 (hmid_int.trans p3.2),
        ← intervalIntegral.integral_add_adjacent_intervals hmid_int p3.2,
        p1.1, hmid_val, p3.1, hmax]
      simp [c, hlt, add_assoc]
    · -- Step 2: `k = j`, so `[t, T) ⊆ I_j`.
      have hmax : max (τ j) t = t := max_eq_right ht.1
      have p := piece hσ hj htT ht.1 (fun hjN => (hT.2 hjN).le)
      rw [p.1, hmax]
      simp [c]
  refine ⟨fun t T htT j hj k hk ht hT => ⟨step0 htT hj hk ht hT, main t T htT j hj k hk ht hT⟩,
    ?_⟩
  -- Corollary (2.6): `a_{jk}(t) = ⟪s_k, c_{jk}(t)⟫ - ‖s_k‖² max (T_k, t)`.
  intro t j hj k hk ht hjk
  refine ⟨inner ℝ (s k) (c τ s j k t) - ‖s k‖ ^ 2 * max (τ k) t, fun T hT htT => ?_⟩
  rw [main t T htT j hj k hk ht hT, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

end Novel.LemmaAProof

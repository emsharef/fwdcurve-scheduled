import Standalone.PiecewiseAffineIntegral
import Novel.LemmaAProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Module

/-!
# Claim 006 (Lemma C): proof

Follows `math/claims/006-piecewise-affine-integral.md` with Claim 002's proof as the template.
Step 1, the integral of one affine piece (6.9), is `piece`: an a.e. congruence on the piece
(`intervalIntegral.integral_congr_Ioo_of_le`) to the affine function, then linearity,
`intervalIntegral.integral_const`, `intervalIntegral.integral_smul_const`,
`intervalIntegral.integral_comp_sub_right` and `integral_id`. Steps 0, 2 and 3 are `index_le`
and the case split and chain (6.10) of `integral_eq`, exactly as in
`Novel.LemmaAProof.lemmaA`; Step 4 is the rearrangement (6.5) in `integral_eq'` by the
`module` tactic. Part (b) is the subtraction argument (6.11) in `quadratic_zero` and
`affine_zero`, and (6.6), (6.7) apply them to differences. Part (a) is stated for any complete
real normed space so that later claims can use it for real-valued and for `ℝ^d`-valued data.
-/

open MeasureTheory Set

namespace Novel.PiecewiseAffineIntegralProof

open Standalone.PiecewiseAffineIntegral Standalone.LemmaA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integral of the affine function `u ↦ v + (u - c) • w` over `[p, q]`. -/
lemma integral_affine (v w : E) (c p q : ℝ) :
    ∫ u in p..q, (v + (u - c) • w) = (q - p) • v + (((q - c) ^ 2 - (p - c) ^ 2) / 2) • w := by
  have h1 : IntervalIntegrable (fun _ : ℝ => v) volume p q := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun u : ℝ => (u - c) • w) volume p q :=
    (by fun_prop : Continuous fun u : ℝ => (u - c) • w).intervalIntegrable p q
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_comp_sub_right (fun x => x) c, integral_id]

/-- (6.9): if `g = a k + (· - T_k) • b k` on `[p, q) ⊆ I_k` and `p ≤ q`, then
`∫_p^q g = (q - p) • a k + ½ [(q - T_k)² - (p - T_k)²] • b k`, and `g` is interval integrable
on `[p, q]`. -/
lemma piece {N : ℕ} {τ : ℕ → ℝ} {a b : ℕ → E} {g : ℝ → E}
    (hg : ∀ k ≤ N, ∀ u ∈ I τ N k, g u = a k + (u - τ k) • b k) {k : ℕ} (hk : k ≤ N)
    {p q : ℝ} (hpq : p ≤ q) (hp : τ k ≤ p) (hq : k < N → q ≤ τ (k + 1)) :
    (∫ u in p..q, g u = (q - p) • a k + (((q - τ k) ^ 2 - (p - τ k) ^ 2) / 2) • b k) ∧
      IntervalIntegrable g volume p q := by
  have h : ∀ u ∈ Ico p q, g u = a k + (u - τ k) • b k := fun u hu =>
    hg k hk u (LemmaAProof.mem_I_iff.2 ⟨hp.trans hu.1, fun hkN => hu.2.trans_le (hq hkN)⟩)
  constructor
  · rw [intervalIntegral.integral_congr_Ioo_of_le hpq (g := fun u => a k + (u - τ k) • b k)
      (fun u hu => h u (Ioo_subset_Ico_self hu))]
    exact integral_affine _ _ _ _ _
  · refine ((by fun_prop : Continuous fun u : ℝ => a k + (u - τ k) • b k).intervalIntegrable
      p q).congr_uIoo ?_
    rw [uIoo_of_le hpq]
    exact fun u hu => (h u (Ioo_subset_Ico_self hu)).symm

omit [CompleteSpace E] in
/-- Part (b), quadratic case: (6.11). -/
lemma quadratic_zero {c₀ c₁ c₂ : E} {x₁ x₂ x₃ : ℝ} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (e₁ : c₀ + x₁ • c₁ + x₁ ^ 2 • c₂ = 0) (e₂ : c₀ + x₂ • c₁ + x₂ ^ 2 • c₂ = 0)
    (e₃ : c₀ + x₃ • c₁ + x₃ ^ 2 • c₂ = 0) : c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have d₂ : c₁ + (x₁ + x₂) • c₂ = 0 := by
    have : (x₂ - x₁) • (c₁ + (x₁ + x₂) • c₂) =
        (c₀ + x₂ • c₁ + x₂ ^ 2 • c₂) - (c₀ + x₁ • c₁ + x₁ ^ 2 • c₂) := by module
    rw [e₁, e₂, sub_zero] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm h12))
  have d₃ : c₁ + (x₁ + x₃) • c₂ = 0 := by
    have : (x₃ - x₁) • (c₁ + (x₁ + x₃) • c₂) =
        (c₀ + x₃ • c₁ + x₃ ^ 2 • c₂) - (c₀ + x₁ • c₁ + x₁ ^ 2 • c₂) := by module
    rw [e₁, e₃, sub_zero] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm h13))
  have hc₂ : c₂ = 0 := by
    have : (x₃ - x₂) • c₂ = (c₁ + (x₁ + x₃) • c₂) - (c₁ + (x₁ + x₂) • c₂) := by module
    rw [d₂, d₃, sub_zero] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm h23))
  have hc₁ : c₁ = 0 := by
    rw [hc₂, smul_zero, add_zero] at d₂
    exact d₂
  refine ⟨?_, hc₁, hc₂⟩
  rw [hc₁, hc₂, smul_zero, smul_zero, add_zero, add_zero] at e₁
  exact e₁

omit [CompleteSpace E] in
/-- Part (b), affine case. -/
lemma affine_zero {c₀ c₁ : E} {x₁ x₂ : ℝ} (h12 : x₁ ≠ x₂) (e₁ : c₀ + x₁ • c₁ = 0)
    (e₂ : c₀ + x₂ • c₁ = 0) : c₀ = 0 ∧ c₁ = 0 := by
  have hc₁ : c₁ = 0 := by
    have : (x₂ - x₁) • c₁ = (c₀ + x₂ • c₁) - (c₀ + x₁ • c₁) := by module
    rw [e₁, e₂, sub_zero] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm h12))
  refine ⟨?_, hc₁⟩
  rw [hc₁, smul_zero, add_zero] at e₁
  exact e₁

/-- Step 0: `t ∈ I_j`, `T ∈ I_k`, `t ≤ T` force `j ≤ k`. -/
lemma index_le {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {t T : ℝ} (htT : t ≤ T)
    (hj : j ≤ N) (ht : t ∈ I τ N j) (hT : T ∈ I τ N k) : j ≤ k := by
  rw [LemmaAProof.mem_I_iff] at ht hT
  by_contra hjk
  have hjk : k < j := Nat.lt_of_not_le hjk
  have hkN : k < N := lt_of_lt_of_le hjk hj
  have h1 : T < τ (k + 1) := hT.2 hkN
  have h2 : τ (k + 1) ≤ τ j :=
    hτ.monotoneOn (mem_Iic.2 (Nat.succ_le_of_lt hkN)) (mem_Iic.2 hj) (Nat.succ_le_of_lt hjk)
  linarith [ht.1]

/-- Part (a), (6.3): for `t ≤ T`, `t ∈ I_j`, `T ∈ I_k`,
`∫_t^T g = e_{jk}(t) + (T - m_k) • a k + ½ [(T - T_k)² - (m_k - T_k)²] • b k`. -/
lemma integral_eq {N j k : ℕ} {τ : ℕ → ℝ} {a b : ℕ → E} {g : ℝ → E}
    (hτ : StrictMonoOn τ (Iic N)) (hg : ∀ k ≤ N, ∀ u ∈ I τ N k, g u = a k + (u - τ k) • b k)
    {t T : ℝ} (htT : t ≤ T) (hj : j ≤ N) (hk : k ≤ N) (ht : t ∈ I τ N j) (hT : T ∈ I τ N k) :
    ∫ u in t..T, g u = e τ a b j k t + (T - max (τ k) t) • a k +
      (((T - τ k) ^ 2 - (max (τ k) t - τ k) ^ 2) / 2) • b k := by
  have mono : ∀ {m n : ℕ}, m ≤ n → n ≤ N → τ m ≤ τ n := fun hmn hn =>
    hτ.monotoneOn (mem_Iic.2 (hmn.trans hn)) (mem_Iic.2 hn) hmn
  have hjk := index_le hτ htT hj ht hT
  rw [LemmaAProof.mem_I_iff] at ht hT
  rcases hjk.lt_or_eq with hlt | rfl
  · -- Step 3: `k > j`, the chain (6.10).
    have hjN : j < N := lt_of_lt_of_le hlt hk
    have ht1 : t < τ (j + 1) := ht.2 hjN
    have h1k : τ (j + 1) ≤ τ k := mono (Nat.succ_le_of_lt hlt) hk
    have hkT : τ k ≤ T := hT.1
    have hmax : max (τ k) t = τ k := max_eq_left (by linarith)
    have p1 := piece hg hj (p := t) (q := τ (j + 1)) ht1.le ht.1 (fun _ => le_rfl)
    have p3 := piece hg hk (p := τ k) (q := T) hkT le_rfl (fun hkN => (hT.2 hkN).le)
    have pm : ∀ m, j + 1 ≤ m → m < k →
        (∫ u in τ m..τ (m + 1), g u =
          (τ (m + 1) - τ m) • a m + ((τ (m + 1) - τ m) ^ 2 / 2) • b m) ∧
          IntervalIntegrable g volume (τ m) (τ (m + 1)) := by
      intro m _ hmk
      have hmN : m < N := lt_of_lt_of_le hmk hk
      have p := piece hg hmN.le (mono (Nat.le_succ m) hmN) le_rfl (fun _ => le_rfl)
      refine ⟨?_, p.2⟩
      rw [p.1]
      simp
    have hmid_int : IntervalIntegrable g volume (τ (j + 1)) (τ k) :=
      IntervalIntegrable.trans_iterate_Ico (Nat.succ_le_of_lt hlt)
        (fun m hm => (pm m hm.1 hm.2).2)
    have hmid_val : ∫ u in τ (j + 1)..τ k, g u = ∑ m ∈ Finset.Ico (j + 1) k,
        ((τ (m + 1) - τ m) • a m + ((τ (m + 1) - τ m) ^ 2 / 2) • b m) := by
      rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (Nat.succ_le_of_lt hlt)
        (fun m hm => (pm m hm.1 hm.2).2)]
      exact Finset.sum_congr rfl fun m hm =>
        (pm m (Finset.mem_Ico.1 hm).1 (Finset.mem_Ico.1 hm).2).1
    rw [← intervalIntegral.integral_add_adjacent_intervals p1.2 (hmid_int.trans p3.2),
      ← intervalIntegral.integral_add_adjacent_intervals hmid_int p3.2,
      p1.1, hmid_val, p3.1, hmax]
    simp only [e, hlt, ↓reduceIte]
    abel
  · -- Step 2: `k = j`, so `[t, T) ⊆ I_j`.
    have hmax : max (τ j) t = t := max_eq_right ht.1
    have p := piece hg hj htT ht.1 (fun hjN => (hT.2 hjN).le)
    rw [p.1, hmax]
    simp [e]

/-- `m_k = max (T_k, t) ∈ I_k` for `t ∈ I_j`, `T ∈ I_k`, `t ≤ T`. -/
lemma max_mem_I {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {t T : ℝ} (htT : t ≤ T)
    (hj : j ≤ N) (hk : k ≤ N) (ht : t ∈ I τ N j) (hT : T ∈ I τ N k) :
    max (τ k) t ∈ I τ N k := by
  have hjk := index_le hτ htT hj ht hT
  rw [LemmaAProof.mem_I_iff] at hT ht ⊢
  refine ⟨le_max_left _ _, fun hkN => max_lt (hτ (mem_Iic.2 hk) (mem_Iic.2 hkN)
    (Nat.lt_succ_self k)) ?_⟩
  rcases hjk.lt_or_eq with hlt | rfl
  · exact (ht.2 (lt_of_lt_of_le hlt hk)).trans_le
      (hτ.monotoneOn (mem_Iic.2 ((Nat.succ_le_of_lt hlt).trans hk))
        (mem_Iic.2 (Nat.succ_le_of_lt hkN)) (Nat.succ_le_succ hlt.le))
  · exact ht.2 hkN

/-- Part (a), (6.5): `∫_t^T g = e_{jk}(t) + τ • g(m_k) + ½ τ² • b k` with `τ = T - m_k`. -/
lemma integral_eq' {N j k : ℕ} {τ : ℕ → ℝ} {a b : ℕ → E} {g : ℝ → E}
    (hτ : StrictMonoOn τ (Iic N)) (hg : ∀ k ≤ N, ∀ u ∈ I τ N k, g u = a k + (u - τ k) • b k)
    {t T : ℝ} (htT : t ≤ T) (hj : j ≤ N) (hk : k ≤ N) (ht : t ∈ I τ N j) (hT : T ∈ I τ N k) :
    ∫ u in t..T, g u = e τ a b j k t + (T - max (τ k) t) • g (max (τ k) t) +
      ((T - max (τ k) t) ^ 2 / 2) • b k := by
  rw [integral_eq hτ hg htT hj hk ht hT, hg k hk _ (max_mem_I hτ htT hj hk ht hT)]
  module

theorem piecewiseAffineIntegral : Standalone.PiecewiseAffineIntegral.statement := by
  intro N d τ a b g _hτ0 hτ hg
  refine ⟨fun t T htT j hj k hk ht hT => ⟨index_le hτ htT hj ht hT,
    integral_eq hτ hg htT hj hk ht hT, integral_eq' hτ hg htT hj hk ht hT⟩,
    fun _ _ _ _ _ _ => quadratic_zero, fun _ _ _ _ => affine_zero, ?_, ?_⟩
  · -- (6.6).
    intro p q r p' q' r' x₁ x₂ x₃ h12 h13 h23 h
    have hx : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ →
        (p - p') + x • (q - q') + x ^ 2 • (r - r') = 0 := fun x hx => by
      have := h x (by simp [hx])
      calc (p - p') + x • (q - q') + x ^ 2 • (r - r')
          = (p + x • q + x ^ 2 • r) - (p' + x • q' + x ^ 2 • r') := by module
        _ = 0 := sub_eq_zero.2 this
    obtain ⟨h0, h1, h2⟩ := quadratic_zero h12 h13 h23 (hx x₁ (Or.inl rfl))
      (hx x₂ (Or.inr (Or.inl rfl))) (hx x₃ (Or.inr (Or.inr rfl)))
    exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩
  · -- (6.7).
    intro a' b' g' hg' htwo k hk
    obtain ⟨u₁, hu₁, u₂, hu₂, hne, e₁, e₂⟩ := htwo k hk
    have hx : ∀ u ∈ I τ N k, g u = g' u → (a k - a' k) + (u - τ k) • (b k - b' k) = 0 :=
      fun u hu he => by
        calc (a k - a' k) + (u - τ k) • (b k - b' k)
            = (a k + (u - τ k) • b k) - (a' k + (u - τ k) • b' k) := by module
          _ = 0 := by rw [← hg k hk u hu, ← hg' k hk u hu, he, sub_self]
    obtain ⟨h0, h1⟩ := affine_zero (x₁ := u₁ - τ k) (x₂ := u₂ - τ k)
      (fun h => hne (by linarith)) (hx u₁ hu₁ e₁) (hx u₂ hu₂ e₂)
    exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h1⟩

end Novel.PiecewiseAffineIntegralProof

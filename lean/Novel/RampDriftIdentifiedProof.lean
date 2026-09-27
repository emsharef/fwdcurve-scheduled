import Standalone.RampDriftIdentified
import Novel.LemmaAProof
import Novel.PiecewiseAffineIntegralProof
import Novel.Theorem1Proof

/-!
# Claim 007 (ramp drift identified): proof

Follows `math/claims/007-ramp-drift-identified.md`. Step 0 is (7.2) from Lemma A (Claim 002)
and (7.5) from Claim 006's Part (a) in the form (6.5) for real values
(`Novel.PiecewiseAffineIntegralProof.integral_eq'`), with (7.6) by bilinearity
(`norm_add_sq_real`). Step 1 is `c_succ` and `e_succ`, the recursions (7.8) and (7.7) read off
the definitions of `Standalone.LemmaA.c` and `Standalone.PiecewiseAffineIntegral.e`. Step 2
((B) ⇒ (A)) is the induction `const_eq` on the constants followed by the coefficient match on
the piece; Step 3 ((A) ⇒ (A′)) takes `M = [t, ∞)` and the points `m_k + L_k`, `m_k + L_k / 2`,
`m_k + L_k / 4` (`exists_len`); Step 4 ((A′) ⇒ (B)) is Claim 006's Part (b)
(`quadratic_zero`) on the difference of (7.5) and (7.6); Step 5 ((B) ⇔ (B′)) evaluates both
sides on the piece and uses the affine case (`affine_zero`) for the converse.
-/

open MeasureTheory Set

namespace Novel.RampDriftIdentifiedProof

open Standalone.RampDriftIdentified Standalone.LemmaA Standalone.StepDriftVanish
  Standalone.PiecewiseAffineIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `m_k = T_k` for `j < k ≤ N` when `t ∈ I_j`. -/
lemma max_eq_of_lt {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {t : ℝ}
    (ht : t ∈ I τ N j) (hjk : j < k) (hk : k ≤ N) : max (τ k) t = τ k := by
  rw [LemmaAProof.mem_I_iff] at ht
  have hjN : j < N := lt_of_lt_of_le hjk hk
  have : t < τ k := (ht.2 hjN).trans_le
    (hτ.monotoneOn (mem_Iic.2 ((Nat.succ_le_of_lt hjk).trans hk)) (mem_Iic.2 hk)
      (Nat.succ_le_of_lt hjk))
  exact max_eq_left this.le

/-- (7.8) for the constants: `C_{k+1} = C_k + (T_{k+1} - m_k) • s_k`. -/
lemma c_succ {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {s : ℕ → E} {t : ℝ}
    (ht : t ∈ I τ N j) (hjk : j ≤ k) (hk : k ≤ N) :
    c τ s j (k + 1) t = c τ s j k t + (τ (k + 1) - max (τ k) t) • s k := by
  rcases hjk.lt_or_eq with hlt | rfl
  · rw [max_eq_of_lt hτ ht hlt hk]
    have hlt' : j < k + 1 := lt_of_lt_of_le hlt (Nat.le_succ k)
    simp only [c, hlt, hlt', ↓reduceIte]
    rw [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hlt)]
    abel
  · have hmax : max (τ j) t = t := max_eq_right (LemmaAProof.mem_I_iff.1 ht).1
    simp [c, hmax]

/-- (7.7) for the constants: `e_{j,k+1}(t) = e_{jk}(t) + (T_{k+1} - m_k) • a_k
+ ½ [(T_{k+1} - T_k)² - (m_k - T_k)²] • b_k`. -/
lemma e_succ {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {a b : ℕ → E} {t : ℝ}
    (ht : t ∈ I τ N j) (hjk : j ≤ k) (hk : k ≤ N) :
    e τ a b j (k + 1) t = e τ a b j k t + (τ (k + 1) - max (τ k) t) • a k +
      (((τ (k + 1) - τ k) ^ 2 - (max (τ k) t - τ k) ^ 2) / 2) • b k := by
  rcases hjk.lt_or_eq with hlt | rfl
  · rw [max_eq_of_lt hτ ht hlt hk]
    have hlt' : j < k + 1 := lt_of_lt_of_le hlt (Nat.le_succ k)
    simp only [e, hlt, hlt', ↓reduceIte]
    rw [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hlt)]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    abel
  · have hmax : max (τ j) t = t := max_eq_right (LemmaAProof.mem_I_iff.1 ht).1
    simp [e, hmax]

/-- The piece `[m_k, T_{k+1})` has positive length: `m_k + c ∈ I_k` for `0 < c ≤ L_k`. -/
lemma exists_len {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) {t : ℝ}
    (ht : t ∈ I τ N j) (hjk : j ≤ k) (hk : k ≤ N) :
    ∃ L : ℝ, 0 < L ∧ ∀ c : ℝ, 0 < c → c ≤ L → max (τ k) t + c ∈ I τ N k := by
  have hlt : k < N → max (τ k) t < τ (k + 1) := fun hkN => by
    refine max_lt (hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)) ?_
    have ht' := LemmaAProof.mem_I_iff.1 ht
    rcases hjk.lt_or_eq with hlt | rfl
    · exact (ht'.2 (lt_of_lt_of_le hlt hk)).trans_le
        (hτ.monotoneOn (mem_Iic.2 ((Nat.succ_le_of_lt hlt).trans hk))
          (mem_Iic.2 (Nat.succ_le_of_lt hkN)) (Nat.succ_le_succ hlt.le))
    · exact ht'.2 hkN
  refine ⟨if k < N then (τ (k + 1) - max (τ k) t) / 2 else 1, ?_, ?_⟩
  · split_ifs with hkN
    · linarith [hlt hkN]
    · exact one_pos
  · intro c hc hcL
    refine LemmaAProof.mem_I_iff.2 ⟨by linarith [le_max_left (τ k) t], fun hkN => ?_⟩
    simp only [hkN, ↓reduceIte] at hcL
    linarith [hlt hkN]

theorem rampDriftIdentified : Standalone.RampDriftIdentified.statement := by
  intro N d τ s σ a b α hτ0 hτ hσ hα j hj t ht
  dsimp only
  have h0t : 0 ≤ t := by
    have := hτ.monotoneOn (mem_Iic.2 (Nat.zero_le N)) (mem_Iic.2 hj) (Nat.zero_le j)
    rw [hτ0] at this
    exact this.trans (LemmaAProof.mem_I_iff.1 ht).1
  have hα' : ∀ k ≤ N, ∀ u ∈ I τ N k, α u = a k + (u - τ k) • b k := fun k hk u hu => by
    rw [hα k hk u hu, smul_eq_mul]
  have hcs : ∀ k, inner ℝ (c τ s j k t) (s k) = inner ℝ (s k) (c τ s j k t) := fun k =>
    real_inner_comm _ _
  -- Step 0: (7.2), (7.5), (7.6) on the piece `k`.
  have h72 : ∀ k, j ≤ k → k ≤ N → ∀ T, T ∈ I τ N k → max (τ k) t ≤ T →
      ∫ u in t..T, σ u = c τ s j k t + (T - max (τ k) t) • s k := fun k hjk hk T hT hmT =>
    ((LemmaAProof.lemmaA N d τ s σ hτ0 hτ hσ).1 t T ((le_max_right _ _).trans hmT) j hj k hk
      ht hT).2
  have h75 : ∀ k, j ≤ k → k ≤ N → ∀ T, T ∈ I τ N k → max (τ k) t ≤ T →
      ∫ u in t..T, α u = e τ a b j k t +
        (T - max (τ k) t) * (a k + (max (τ k) t - τ k) * b k) +
        ((T - max (τ k) t) ^ 2 / 2) * b k := fun k hjk hk T hT hmT => by
    have htT : t ≤ T := (le_max_right _ _).trans hmT
    rw [PiecewiseAffineIntegralProof.integral_eq' hτ hα' htT hj hk ht hT,
      hα' k hk _ (PiecewiseAffineIntegralProof.max_mem_I hτ htT hj hk ht hT)]
    simp only [smul_eq_mul]
  have h76 : ∀ k, j ≤ k → k ≤ N → ∀ T, T ∈ I τ N k → max (τ k) t ≤ T →
      (1 / 2 : ℝ) * ‖∫ u in t..T, σ u‖ ^ 2 =
        (1 / 2 : ℝ) * ‖c τ s j k t‖ ^ 2 +
          (T - max (τ k) t) * inner ℝ (c τ s j k t) (s k) +
          ((T - max (τ k) t) ^ 2 / 2) * ‖s k‖ ^ 2 := fun k hjk hk T hT hmT => by
    rw [h72 k hjk hk T hT hmT, norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- Step 2, the constants: under (B), `e_{jk}(t) = ½ |C_k|²` by induction on `k`.
  have const_eq : (∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k) →
      ∀ k, j ≤ k → k ≤ N → e τ a b j k t = (1 / 2 : ℝ) * ‖c τ s j k t‖ ^ 2 := by
    intro hB k hjk
    induction k, hjk using Nat.le_induction with
    | base => intro _; simp [e, c]
    | succ k hjk ih =>
      intro hk
      have hk' : k ≤ N := (Nat.le_succ k).trans hk
      obtain ⟨ha, hb⟩ := hB k hjk hk'
      rw [e_succ hτ ht hjk hk', c_succ hτ ht hjk hk', ih hk', norm_add_sq_real,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha, hb, hcs]
      simp only [aStar, bStar, smul_eq_mul]
      ring
  -- (B) ⇒ (A).
  have hBA : (∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k) →
      ∀ T : ℝ, t ≤ T → driftCondition α σ t T := by
    intro hB T hT
    obtain ⟨k, hk, hTk⟩ := Theorem1Proof.exists_index (N := N) hτ0 (h0t.trans hT)
    have hjk := Theorem1Proof.index_mono hτ hj ht hTk hT
    have hmT : max (τ k) t ≤ T := max_le (LemmaAProof.mem_I_iff.1 hTk).1 hT
    obtain ⟨ha, hb⟩ := hB k hjk hk
    unfold driftCondition
    rw [h75 k hjk hk T hTk hmT, h76 k hjk hk T hTk hmT, const_eq hB k hjk hk, ha, hb, hcs]
    simp only [aStar, bStar]
    ring
  -- (A) ⇒ (A′): `M = [t, ∞)` and three points of each piece.
  have hAA' : (∀ T : ℝ, t ≤ T → driftCondition α σ t T) →
      ∃ M : Set ℝ, M ⊆ Ici t ∧
        (∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, ∃ T₃ ∈ M,
          T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₂ ≠ T₃ ∧
          (T₁ ∈ I τ N k ∧ max (τ k) t < T₁) ∧ (T₂ ∈ I τ N k ∧ max (τ k) t < T₂) ∧
          (T₃ ∈ I τ N k ∧ max (τ k) t < T₃)) ∧
        ∀ T ∈ M, driftCondition α σ t T := by
    intro hA
    refine ⟨Ici t, subset_rfl, fun k hjk hk => ?_, fun T hT => hA T hT⟩
    obtain ⟨L, hL, hmem⟩ := exists_len hτ ht hjk hk
    have hm : t ≤ max (τ k) t := le_max_right _ _
    refine ⟨max (τ k) t + L, by simp only [mem_Ici]; linarith,
      max (τ k) t + L / 2, by simp only [mem_Ici]; linarith,
      max (τ k) t + L / 4, by simp only [mem_Ici]; linarith,
      by intro h; linarith, by intro h; linarith, by intro h; linarith,
      ⟨hmem L hL le_rfl, by linarith⟩,
      ⟨hmem (L / 2) (by linarith) (by linarith), by linarith⟩,
      ⟨hmem (L / 4) (by linarith) (by linarith), by linarith⟩⟩
  -- (A′) ⇒ (B): three points identify the coefficients (Claim 006, Part (b)).
  have hA'B : (∃ M : Set ℝ, M ⊆ Ici t ∧
        (∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, ∃ T₃ ∈ M,
          T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₂ ≠ T₃ ∧
          (T₁ ∈ I τ N k ∧ max (τ k) t < T₁) ∧ (T₂ ∈ I τ N k ∧ max (τ k) t < T₂) ∧
          (T₃ ∈ I τ N k ∧ max (τ k) t < T₃)) ∧
        ∀ T ∈ M, driftCondition α σ t T) →
      ∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k := by
    rintro ⟨M, -, hM, h44⟩ k hjk hk
    obtain ⟨T₁, hT₁M, T₂, hT₂M, T₃, hT₃M, h12, h13, h23, ⟨hT₁, hm₁⟩, ⟨hT₂, hm₂⟩, ⟨hT₃, hm₃⟩⟩ :=
      hM k hjk hk
    have key : ∀ T, T ∈ I τ N k → max (τ k) t < T → driftCondition α σ t T →
        (e τ a b j k t - (1 / 2 : ℝ) * ‖c τ s j k t‖ ^ 2) +
          (T - max (τ k) t) • ((a k + (max (τ k) t - τ k) * b k) -
            inner ℝ (c τ s j k t) (s k)) +
          (T - max (τ k) t) ^ 2 • (b k / 2 - ‖s k‖ ^ 2 / 2) = 0 := by
      intro T hT hmT hd
      unfold driftCondition at hd
      rw [h75 k hjk hk T hT hmT.le, h76 k hjk hk T hT hmT.le] at hd
      simp only [smul_eq_mul]
      linear_combination hd
    obtain ⟨_, h1, h2⟩ := PiecewiseAffineIntegralProof.quadratic_zero (E := ℝ)
      (fun h => h12 (by linarith)) (fun h => h13 (by linarith)) (fun h => h23 (by linarith))
      (key T₁ hT₁ hm₁ (h44 T₁ hT₁M)) (key T₂ hT₂ hm₂ (h44 T₂ hT₂M))
      (key T₃ hT₃ hm₃ (h44 T₃ hT₃M))
    have hb : b k = bStar s k := by
      simp only [bStar]
      linarith
    refine ⟨?_, hb⟩
    rw [hb, hcs] at h1
    simp only [aStar, bStar] at h1 ⊢
    linear_combination h1
  -- (B) ⇔ (B′).
  have hBB' : (∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k) ↔
      ∀ u : ℝ, t ≤ u → α u = inner ℝ (σ u) (∫ v in t..u, σ v) := by
    constructor
    · intro hB u hu
      obtain ⟨k, hk, huk⟩ := Theorem1Proof.exists_index (N := N) hτ0 (h0t.trans hu)
      have hjk := Theorem1Proof.index_mono hτ hj ht huk hu
      have hmu : max (τ k) t ≤ u := max_le (LemmaAProof.mem_I_iff.1 huk).1 hu
      obtain ⟨ha, hb⟩ := hB k hjk hk
      rw [hα k hk u huk, hσ k hk u huk, h72 k hjk hk u huk hmu, inner_add_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, ha, hb]
      simp only [aStar, bStar]
      ring
    · intro hB' k hjk hk
      obtain ⟨L, hL, hmem⟩ := exists_len hτ ht hjk hk
      have hm : t ≤ max (τ k) t := le_max_right _ _
      have hval : ∀ c : ℝ, 0 < c → c ≤ L →
          (a k - aStar τ s j k t) + (max (τ k) t + c - τ k) • (b k - bStar s k) = 0 := by
        intro c hc hcL
        have hu := hmem c hc hcL
        have h1 := hB' (max (τ k) t + c) (by linarith)
        rw [hα k hk _ hu, hσ k hk _ hu, h72 k hjk hk _ hu (by linarith), inner_add_right,
          real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
        simp only [aStar, bStar, smul_eq_mul]
        linear_combination h1
      obtain ⟨h0, h1⟩ := PiecewiseAffineIntegralProof.affine_zero (E := ℝ)
        (x₁ := max (τ k) t + L - τ k) (x₂ := max (τ k) t + L / 2 - τ k)
        (by intro h; linarith) (hval L hL le_rfl) (hval (L / 2) (by linarith) (by linarith))
      exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h1⟩
  exact ⟨hAA', hA'B, hBA, hBB'⟩

end Novel.RampDriftIdentifiedProof

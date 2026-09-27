import Standalone.StepJumpsVanish
import Novel.LemmaAProof
import Novel.LemmaBProof

/-!
# Claim 003 (step jumps vanish): proof

Follows `math/claims/003-step-jumps-vanish.md`, with one simplification of Step 0: instead of
the full identity (3.6) with the constant `c_k` of (3.7), the induction step `k` uses (3.9)
directly. On the almost-sure event where `ξ(·, ω) = 0` on `[T_n, T_k)` (which is what the
inductive hypothesis gives, via `exists_mem_I`), the integral splits as
`∫_{T_n}^{T_k} + ∫_{T_k}^T = 0 + (T - T_k) X_k(ω)` for `T ∈ I_k` (`integral_eq`), using the
step-function lemmas of Claim 002's proof (`Novel.LemmaAProof.integral_eq_of_eqOn_Ico`,
`intervalIntegrable_of_eqOn_Ico`). Step 1 is `gapHalf_pos` and `maturity_mem_I` (3.8); Step 2
is the strong induction in `refinement`, closing each step with Lemma B (Claim 001) at
`λ = h_k`. The Claim follows from the Refinement, and the Corollary from the Claim by
`condExp_of_not_integrable` (integrability) and `integral_condExp` (the tower property).
-/

open MeasureTheory Real Set

namespace Novel.StepJumpsVanishProof

open Standalone.StepJumpsVanish Standalone.LemmaA

/-- Every `u ∈ [T_n, T_k)` lies in some `I_m` with `n ≤ m < k`, for `k ≤ N`. -/
lemma exists_mem_I {τ : ℕ → ℝ} {N n : ℕ} :
    ∀ k, n ≤ k → k ≤ N → ∀ u ∈ Ico (τ n) (τ k), ∃ m, n ≤ m ∧ m < k ∧ u ∈ I τ N m := by
  intro k
  induction k with
  | zero =>
    intro hn _ u hu
    obtain rfl : n = 0 := Nat.le_zero.1 hn
    simp at hu
  | succ k ih =>
    intro hn hk u hu
    rcases Nat.lt_or_ge k n with hkn | hkn
    · obtain rfl : n = k + 1 := le_antisymm hn (Nat.succ_le_of_lt hkn)
      simp at hu
    · rcases lt_or_ge u (τ k) with h | h
      · obtain ⟨m, hm1, hm2, hm3⟩ := ih hkn (Nat.le_of_succ_le hk) u ⟨hu.1, h⟩
        exact ⟨m, hm1, Nat.lt_succ_of_lt hm2, hm3⟩
      · exact ⟨k, hkn, Nat.lt_succ_self k, LemmaAProof.mem_I_iff.2 ⟨h, fun _ => hu.2⟩⟩

/-- (3.8): `h_k > 0`. -/
lemma gapHalf_pos {τ : ℕ → ℝ} {N k : ℕ} (hτ : StrictMonoOn τ (Iic N)) (hk : k ≤ N) :
    0 < gapHalf τ N k := by
  unfold gapHalf
  split_ifs with hkN
  · have := hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)
    linarith
  · exact one_pos

/-- (3.8): the maturities (3.4) lie in `I_k`. -/
lemma maturity_mem_I {τ : ℕ → ℝ} {N k : ℕ} (hτ : StrictMonoOn τ (Iic N)) (hk : k ≤ N)
    {T : ℝ} (hT : T = τ k + gapHalf τ N k ∨ T = τ k + gapHalf τ N k / 2) : T ∈ I τ N k := by
  have hpos := gapHalf_pos hτ hk
  rw [LemmaAProof.mem_I_iff]
  refine ⟨by rcases hT with rfl | rfl <;> linarith, fun hkN => ?_⟩
  have hg : gapHalf τ N k = (τ (k + 1) - τ k) / 2 := by simp [gapHalf, hkN]
  have := hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)
  rcases hT with rfl | rfl <;> linarith

/-- (3.6) after (3.9): if `ξ(·, ω) = 0` on `[T_n, T_k)`, then for `T ∈ I_k`,
`∫_{T_n}^T ξ(u, ω) du = (T - T_k) X_k(ω)`. -/
lemma integral_eq {Ω : Type} {N n k : ℕ} {τ : ℕ → ℝ} {X : ℕ → Ω → ℝ} {ξ : ℝ → Ω → ℝ}
    (hτ : StrictMonoOn τ (Iic N))
    (hξ : ∀ k ≤ N, ∀ u ∈ I τ N k, ∀ ω, ξ u ω = if n ≤ k then X k ω else 0)
    (hnk : n ≤ k) (hk : k ≤ N) {ω : Ω} (h0 : ∀ u ∈ Ico (τ n) (τ k), ξ u ω = 0)
    {T : ℝ} (hT : T ∈ I τ N k) :
    ∫ u in τ n..T, ξ u ω = (T - τ k) * X k ω := by
  have hnk' : τ n ≤ τ k := hτ.monotoneOn (mem_Iic.2 (hnk.trans hk)) (mem_Iic.2 hk) hnk
  rw [LemmaAProof.mem_I_iff] at hT
  have h1 : ∀ u ∈ Ico (τ k) T, ξ u ω = X k ω := fun u hu => by
    rw [hξ k hk u (LemmaAProof.mem_I_iff.2 ⟨hu.1, fun hkN => hu.2.trans (hT.2 hkN)⟩) ω]
    simp [hnk]
  have i1 := LemmaAProof.intervalIntegrable_of_eqOn_Ico (σ := fun u => ξ u ω) hnk' h0
  have i2 := LemmaAProof.intervalIntegrable_of_eqOn_Ico (σ := fun u => ξ u ω) hT.1 h1
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    LemmaAProof.integral_eq_of_eqOn_Ico hnk' h0, LemmaAProof.integral_eq_of_eqOn_Ico hT.1 h1]
  simp [smul_eq_mul]

theorem stepJumpsVanish : Standalone.StepJumpsVanish.statement := by
  intro Ω m₀ μ _ N n τ X ξ _hτ0 hτ _hn1 _hnN hξ
  -- Refinement: Step 2, strong induction on `k`.
  have refinement : (∀ k, n ≤ k → k ≤ N → ∀ T : ℝ,
        (T = τ k + gapHalf τ N k ∨ T = τ k + gapHalf τ N k / 2) →
        Integrable (Y τ n ξ T) μ ∧ ∫ ω, Y τ n ξ T ω ∂μ = 1) →
      ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂μ, X k ω = 0 := by
    intro hyp k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hnk hk
    -- (3.9): `ξ(·, ω) = 0` on `[T_n, T_k)` almost surely.
    have h0 : ∀ᵐ ω ∂μ, ∀ u ∈ Ico (τ n) (τ k), ξ u ω = 0 := by
      have hX : ∀ᵐ ω ∂μ, ∀ m, n ≤ m → m < k → X m ω = 0 := by
        rw [ae_all_iff]
        intro m
        by_cases hm : n ≤ m ∧ m < k
        · filter_upwards [ih m hm.2 hm.1 (hm.2.le.trans hk)] with ω hω using fun _ _ => hω
        · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hm
      filter_upwards [hX] with ω hω u hu
      obtain ⟨m, hm1, hm2, hm3⟩ := exists_mem_I k hnk hk u hu
      rw [hξ m (hm2.le.trans hk) u hm3 ω]
      simp [hm1, hω m hm1 hm2]
    -- (3.10)–(3.11): at both maturities, `Y_T = exp (-(T - T_k) X_k)` almost surely.
    have key : ∀ T : ℝ, (T = τ k + gapHalf τ N k ∨ T = τ k + gapHalf τ N k / 2) →
        Y τ n ξ T =ᵐ[μ] fun ω => exp (-(T - τ k) * X k ω) := by
      intro T hT
      filter_upwards [h0] with ω hω
      simp only [Y]
      rw [integral_eq hτ hξ hnk hk hω (maturity_mem_I hτ hk hT), neg_mul]
    obtain ⟨int1, eq1⟩ := hyp k hnk hk _ (Or.inl rfl)
    obtain ⟨int2, eq2⟩ := hyp k hnk hk _ (Or.inr rfl)
    have k1 : Y τ n ξ (τ k + gapHalf τ N k) =ᵐ[μ] fun ω => exp (-gapHalf τ N k * X k ω) := by
      refine (key _ (Or.inl rfl)).trans (Filter.Eventually.of_forall fun ω => ?_)
      show exp _ = exp _
      congr 1
      ring
    have k2 : Y τ n ξ (τ k + gapHalf τ N k / 2) =ᵐ[μ]
        fun ω => exp (-gapHalf τ N k / 2 * X k ω) := by
      refine (key _ (Or.inr rfl)).trans (Filter.Eventually.of_forall fun ω => ?_)
      show exp _ = exp _
      congr 1
      ring
    -- Lemma B (Claim 001) with `λ = h_k`.
    exact Novel.LemmaBProof.lemmaB μ (X k) (gapHalf τ N k) (gapHalf_pos hτ hk).ne'
      (int1.congr k1) ((integral_congr_ae k1).symm.trans eq1)
      (int2.congr k2) ((integral_congr_ae k2).symm.trans eq2)
  -- Claim: (3.3) for every `T ≥ T_n` restricts to the maturities (3.4).
  have claim : (∀ T : ℝ, τ n ≤ T → Integrable (Y τ n ξ T) μ ∧ ∫ ω, Y τ n ξ T ω ∂μ = 1) →
      ∀ k, n ≤ k → k ≤ N → ∀ᵐ ω ∂μ, X k ω = 0 := by
    intro hyp
    refine refinement fun k hnk hk T hT => hyp T ?_
    have hnk' : τ n ≤ τ k := hτ.monotoneOn (mem_Iic.2 (hnk.trans hk)) (mem_Iic.2 hk) hnk
    have hpos := gapHalf_pos hτ hk
    rcases hT with rfl | rfl <;> linarith
  refine ⟨refinement, claim, ?_⟩
  -- Corollary: the tower property gives (3.3) from (3.5).
  intro m hm hcond
  refine claim fun T hT => ?_
  have h := hcond T hT
  have hint : Integrable (Y τ n ξ T) μ := by
    by_contra hni
    rw [condExp_of_not_integrable hni] at h
    obtain ⟨ω, hω⟩ := h.exists
    simp at hω
  refine ⟨hint, ?_⟩
  rw [← integral_condExp (μ := μ) (f := Y τ n ξ T) hm, integral_congr_ae h]
  simp

end Novel.StepJumpsVanishProof

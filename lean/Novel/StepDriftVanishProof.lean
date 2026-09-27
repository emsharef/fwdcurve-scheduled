import Standalone.StepDriftVanish
import Novel.LemmaAProof
import Novel.StepJumpsVanishProof

/-!
# Claim 004 (step drift and volatility vanish): proof

Follows `math/claims/004-step-drift-vanish.md`, with the same simplification of Step 0 as in
Claim 003's proof file: instead of the full identity (4.6) with the constants `C_k`, `A_k` of
(4.7), the induction step `k` uses the inductive hypothesis first. Once the step values on
`I_j, …, I_{k-1}` are zero, a step function vanishes on `[t, m_k)` (`exists_mem_I` from
Claim 003's proof file), so for `T ∈ I_k` with `T ≥ m_k` the integral from `t` to `T` is
`(T - m_k) • (value on I_k)` (`integral_step_eq`, for `α` with values in `ℝ` and for `σ` with
values in `ℝ^d`, built from the step-function lemmas of Claim 002's proof file). Then (4.4) at
two distinct maturities `T₁, T₂ > m_k` of `I_k` gives (4.9) with `τ_i = T_i - m_k > 0`, and the
algebra (4.10) (`step_zero`) forces `s k = 0` and `μ k = 0`. Step 2 is the strong induction in
`refinement`; the Claim follows with `M = [t, ∞)` and the maturities `m_k + h_k`, `m_k + h_k/2`
of (4.3) (`claim`).
-/

open MeasureTheory Set

namespace Novel.StepDriftVanishProof

open Standalone.StepDriftVanish Standalone.LemmaA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- (4.6) after the inductive hypothesis: if the step values on `I_j, …, I_{k-1}` vanish,
then for `t ∈ I_j`, `T ∈ I_k` with `T ≥ m_k = max (T_k, t)`,
`∫_t^T σ = (T - m_k) • s k`. -/
lemma integral_step_eq {N j k : ℕ} {τ : ℕ → ℝ} {s : ℕ → E} {σ : ℝ → E}
    (hσ : ∀ k ≤ N, ∀ u ∈ I τ N k, σ u = s k) {t : ℝ} (ht : t ∈ I τ N j)
    (hjk : j ≤ k) (hk : k ≤ N) (h0 : ∀ m, j ≤ m → m < k → s m = 0)
    {T : ℝ} (hT : T ∈ I τ N k) (hmT : max (τ k) t ≤ T) :
    ∫ u in t..T, σ u = (T - max (τ k) t) • s k := by
  rw [LemmaAProof.mem_I_iff] at hT ht
  have htm : t ≤ max (τ k) t := le_max_right _ _
  -- on `[t, m_k)` the function vanishes
  have h1 : ∀ u ∈ Ico t (max (τ k) t), σ u = 0 := fun u hu => by
    have huk : u < τ k := by
      rcases lt_max_iff.1 hu.2 with h | h
      · exact h
      · exact absurd hu.1 (not_le.2 h)
    obtain ⟨m, hm1, hm2, hm3⟩ :=
      StepJumpsVanishProof.exists_mem_I (N := N) k hjk hk u ⟨ht.1.trans hu.1, huk⟩
    rw [hσ m (hm2.le.trans hk) u hm3, h0 m hm1 hm2]
  -- on `[m_k, T)` it equals `s k`
  have h2 : ∀ u ∈ Ico (max (τ k) t) T, σ u = s k := fun u hu =>
    hσ k hk u (LemmaAProof.mem_I_iff.2
      ⟨(le_max_left _ _).trans hu.1, fun hkN => hu.2.trans (hT.2 hkN)⟩)
  have i1 := LemmaAProof.intervalIntegrable_of_eqOn_Ico htm h1
  have i2 := LemmaAProof.intervalIntegrable_of_eqOn_Ico hmT h2
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    LemmaAProof.integral_eq_of_eqOn_Ico htm h1, LemmaAProof.integral_eq_of_eqOn_Ico hmT h2]
  simp

/-- (4.9)–(4.10): `τ μ = ½ (τ ‖s‖)²` at two distinct positive `τ` forces `s = 0` and `μ = 0`. -/
lemma step_zero {d : ℕ} {μ τ₁ τ₂ : ℝ} {s : EuclideanSpace ℝ (Fin d)}
    (h₁ : 0 < τ₁) (h₂ : 0 < τ₂) (hne : τ₁ ≠ τ₂)
    (e₁ : τ₁ * μ = (1 / 2 : ℝ) * (τ₁ * ‖s‖) ^ 2)
    (e₂ : τ₂ * μ = (1 / 2 : ℝ) * (τ₂ * ‖s‖) ^ 2) : μ = 0 ∧ s = 0 := by
  have f₁ : μ = τ₁ * ‖s‖ ^ 2 / 2 :=
    mul_left_cancel₀ h₁.ne' (e₁.trans (by ring))
  have f₂ : μ = τ₂ * ‖s‖ ^ 2 / 2 :=
    mul_left_cancel₀ h₂.ne' (e₂.trans (by ring))
  have hs : ‖s‖ ^ 2 * (τ₁ - τ₂) = 0 := by linarith
  have hs0 : ‖s‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 hs with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have hs' : s = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hs0)
  refine ⟨?_, hs'⟩
  rw [f₁, hs0]
  ring

theorem stepDriftVanish : Standalone.StepDriftVanish.statement := by
  intro N d τ μ s α σ _hτ0 hτ hα hσ j hj t ht
  -- Refinement: Step 2, strong induction on `k`.
  have refinement : ∀ M : Set ℝ,
      (∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, T₁ ≠ T₂ ∧
        T₁ ∈ I τ N k ∧ max (τ k) t < T₁ ∧ T₂ ∈ I τ N k ∧ max (τ k) t < T₂) →
      (∀ T ∈ M, driftCondition α σ t T) →
      ∀ k, j ≤ k → k ≤ N → μ k = 0 ∧ s k = 0 := by
    intro M hM h44 k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hjk hk
    have h0μ : ∀ m, j ≤ m → m < k → μ m = 0 := fun m hm1 hm2 =>
      (ih m hm2 hm1 (hm2.le.trans hk)).1
    have h0s : ∀ m, j ≤ m → m < k → s m = 0 := fun m hm1 hm2 =>
      (ih m hm2 hm1 (hm2.le.trans hk)).2
    obtain ⟨T₁, hT₁M, T₂, hT₂M, hne, hT₁, hm₁, hT₂, hm₂⟩ := hM k hjk hk
    -- (4.8) with `A_k = 0`, `C_k = 0`, at each of the two maturities
    have key : ∀ T, T ∈ I τ N k → max (τ k) t < T → driftCondition α σ t T →
        (T - max (τ k) t) * μ k = (1 / 2 : ℝ) * ((T - max (τ k) t) * ‖s k‖) ^ 2 := by
      intro T hT hmT hd
      unfold driftCondition at hd
      rw [integral_step_eq hα ht hjk hk h0μ hT hmT.le,
        integral_step_eq hσ ht hjk hk h0s hT hmT.le, norm_smul, Real.norm_eq_abs,
        abs_of_pos (sub_pos.2 hmT), smul_eq_mul] at hd
      exact hd
    exact step_zero (sub_pos.2 hm₁) (sub_pos.2 hm₂) (fun h => hne (by linarith))
      (key T₁ hT₁ hm₁ (h44 T₁ hT₁M)) (key T₂ hT₂ hm₂ (h44 T₂ hT₂M))
  refine ⟨refinement, ?_⟩
  -- Claim: `M = [t, ∞)` with the maturities `m_k + h_k` and `m_k + h_k / 2` of (4.3).
  intro h44
  refine refinement (Ici t) ?_ (fun T hT => h44 T hT)
  intro k hjk hk
  have hmono : ∀ {a b : ℕ}, a ≤ b → b ≤ N → τ a ≤ τ b := fun hab hb =>
    hτ.monotoneOn (mem_Iic.2 (hab.trans hb)) (mem_Iic.2 hb) hab
  rw [LemmaAProof.mem_I_iff] at ht
  -- `m_k < T_{k+1}` for `k < N`
  have hlt : k < N → max (τ k) t < τ (k + 1) := fun hkN => by
    refine max_lt (hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)) ?_
    rcases hjk.lt_or_eq with hlt | rfl
    · exact (ht.2 (lt_of_lt_of_le hlt hk)).trans_le
        (hmono (Nat.succ_le_succ hlt.le) (Nat.succ_le_of_lt hkN))
    · exact ht.2 hkN
  set m := max (τ k) t with hm
  set h : ℝ := if k < N then (τ (k + 1) - m) / 2 else 1 with hh
  have hpos : 0 < h := by
    rw [hh]; split_ifs with hkN
    · linarith [hlt hkN]
    · exact one_pos
  have hmem : ∀ T, m < T → (k < N → T < τ (k + 1)) → T ∈ Ici t ∧ T ∈ I τ N k ∧ m < T :=
    fun T hT hT' => ⟨(le_max_right _ _).trans hT.le,
      LemmaAProof.mem_I_iff.2 ⟨(le_max_left _ _).trans hT.le, hT'⟩, hT⟩
  have hup : ∀ c : ℝ, 0 < c → c ≤ h → k < N → m + c < τ (k + 1) := fun c _ hc hkN => by
    have : h = (τ (k + 1) - m) / 2 := by simp [hh, hkN]
    linarith
  obtain ⟨hA₁, hA₂, hA₃⟩ := hmem (m + h) (by linarith) (hup h hpos le_rfl)
  obtain ⟨hB₁, hB₂, hB₃⟩ := hmem (m + h / 2) (by linarith) (hup (h / 2) (by linarith) (by linarith))
  exact ⟨m + h, hA₁, m + h / 2, hB₁, by linarith, hA₂, hA₃, hB₂, hB₃⟩

end Novel.StepDriftVanishProof

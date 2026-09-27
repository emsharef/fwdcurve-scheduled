import Standalone.Theorem1
import Upstream.HJMScheduled
import Novel.StepJumpsVanishProof
import Novel.StepDriftVanishProof

/-!
# Claim 005 (Theorem 1): proof

Follows `math/claims/005-theorem-1-step-family.md`.

* (5.4): for each `n`, the jump `ξ n` is the step function (3.2) of Claim 003 with values
  `X n k`, and AX-02 is hypothesis (3.5) of its Corollary with `G = ℱ_(T_n)⁻`; Claim 003
  (`Novel.StepJumpsVanishProof.stepJumpsVanish`) gives `X n k = 0` a.s. for each `k`, and
  `ae_all_iff` over the finitely many `k` gives one event on which `ξ n` vanishes everywhere.
* (5.5), Step 1: AX-01 at the rational maturities `q > 0` only. For each `q`,
  `P ⊗ dt|_{[0,q]} = (P ⊗ dt|_{[0,∞)})|_{Ω × [0,q]}` (`Measure.prod_restrict`), so the
  identity holds `(P ⊗ dt|_{[0,∞)})`-a.e. on `{t ≤ q}`; `ae_all_iff` over `{q : ℚ // 0 < q}`
  gives the single null set. Step 2: for `(ω, t)` outside it, with `t ∈ I_j`, the Refinement
  of Claim 004 (`Novel.StepDriftVanishProof.stepDriftVanish`) applies to the step functions
  `α̃`, `σ̃` that agree with `α t · ω`, `σ t · ω` on `[t, ∞)` and with the step values on
  `I_j`'s part before `t`, with `M` the positive rationals `≥ t`: each `(m_k, T_{k+1})`
  contains two rationals (`exists_rat_btwn`). Step 3 reads off `α t T ω = 0`, `σ t T ω = 0`
  from (S7) for `T < t` and from (5.2) for `T ≥ t`.

`theorem1_of_HJMScheduled` is the claim's "Lean shape": the same statement for an instance
`H : Upstream.HJMScheduled Ω`, with `G n = leftLimit H.ℱ (H.τ n)`.
-/

open MeasureTheory Set

namespace Novel.Theorem1Proof

open Standalone.LemmaA

/-- Every `u ≥ 0` lies in some `I_k`, `k ≤ N`. -/
lemma exists_index {N : ℕ} {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {u : ℝ} (hu : 0 ≤ u) :
    ∃ k ≤ N, u ∈ I τ N k := by
  rcases lt_or_ge u (τ N) with h | h
  · obtain ⟨k, _, hk, hu⟩ := StepJumpsVanishProof.exists_mem_I (n := 0) N (Nat.zero_le N)
      le_rfl u ⟨by rw [hτ0]; exact hu, h⟩
    exact ⟨k, hk.le, hu⟩
  · exact ⟨N, le_rfl, LemmaAProof.mem_I_iff.2 ⟨h, fun h => absurd h (lt_irrefl N)⟩⟩

/-- `t ∈ I_j`, `u ∈ I_k`, `t ≤ u` force `j ≤ k`. -/
lemma index_mono {N j k : ℕ} {τ : ℕ → ℝ} (hτ : StrictMonoOn τ (Iic N)) (hj : j ≤ N)
    {t u : ℝ} (ht : t ∈ I τ N j) (hu : u ∈ I τ N k) (htu : t ≤ u) : j ≤ k := by
  rw [LemmaAProof.mem_I_iff] at ht hu
  by_contra hjk
  have hjk : k < j := Nat.lt_of_not_le hjk
  have hkN : k < N := lt_of_lt_of_le hjk hj
  have h1 : u < τ (k + 1) := hu.2 hkN
  have h2 : τ (k + 1) ≤ τ j :=
    hτ.monotoneOn (mem_Iic.2 (Nat.succ_le_of_lt hkN)) (mem_Iic.2 hj) (Nat.succ_le_of_lt hjk)
  linarith [ht.1]

theorem theorem1 : Standalone.Theorem1.statement := by
  intro Ω m₀ P _ N d τ α σ ξ G μ s X hτ0 hτ hG hα0 hσ0 hξ0 hAX1 hAX2 h52α h52σ h53
  have mono : ∀ {m n : ℕ}, m ≤ n → n ≤ N → τ m ≤ τ n := fun hmn hn =>
    hτ.monotoneOn (mem_Iic.2 (hmn.trans hn)) (mem_Iic.2 hn) hmn
  -- (5.4): Claim 003's Corollary, once per scheduled date.
  have jumpX : ∀ n k, 1 ≤ n → n ≤ k → k ≤ N → ∀ᵐ ω ∂P, X n k ω = 0 := by
    intro n k hn1 hnk hk
    have hstep : ∀ k ≤ N, ∀ u ∈ I τ N k, ∀ ω, ξ n u ω = if n ≤ k then X n k ω else 0 := by
      intro k' hk' u hu ω
      split_ifs with hnk'
      · exact h53 ω n k' hn1 hnk' hk' u hu
      · have hkn : k' + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_le hnk')
        rw [LemmaAProof.mem_I_iff] at hu
        have hkN : k' < N := lt_of_lt_of_le hkn (hnk.trans hk)
        exact hξ0 n hn1 (hnk.trans hk) u ω ((hu.2 hkN).trans_le (mono hkn (hnk.trans hk)))
    exact (StepJumpsVanishProof.stepJumpsVanish P N n τ (fun k => X n k) (fun u ω => ξ n u ω)
      hτ0 hτ hn1 (hnk.trans hk) hstep).2.2 (G n) (hG n) (fun T hT => hAX2 n hn1 (hnk.trans hk) T hT)
      k hnk hk
  have jumpξ : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂P, ∀ u, ξ n u ω = 0 := by
    intro n hn1 hnN
    have hall : ∀ᵐ ω ∂P, ∀ k, n ≤ k → k ≤ N → X n k ω = 0 := by
      rw [ae_all_iff]
      intro k
      by_cases hk : n ≤ k ∧ k ≤ N
      · filter_upwards [jumpX n k hn1 hk.1 hk.2] with ω hω using fun _ _ => hω
      · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hk
    filter_upwards [hall] with ω hω u
    rcases lt_or_ge u (τ n) with hu | hu
    · exact hξ0 n hn1 hnN u ω hu
    · rcases lt_or_ge u (τ N) with huN | huN
      · obtain ⟨k, hnk, hkN, huk⟩ :=
          StepJumpsVanishProof.exists_mem_I (n := n) N hnN le_rfl u ⟨hu, huN⟩
        rw [h53 ω n k hn1 hnk hkN.le u huk]
        exact hω k hnk hkN.le
      · rw [h53 ω n N hn1 hnN le_rfl u
          (LemmaAProof.mem_I_iff.2 ⟨huN, fun h => absurd h (lt_irrefl N)⟩)]
        exact hω N hnN le_rfl
  refine ⟨⟨jumpX, jumpξ⟩, ?_⟩
  -- (5.5), Step 1: one null set from AX-01 at the positive rational maturities.
  set ν : Measure (Ω × ℝ) := P.prod (volume.restrict (Ici 0)) with hν
  have hrat : ∀ q : {q : ℚ // 0 < q}, ∀ᵐ p ∂ν, p.2 ∈ Icc (0 : ℝ) q →
      ∫ u in p.2..(q : ℝ), α p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..(q : ℝ), σ p.2 u p.1‖ ^ 2 := by
    intro q
    have hq : (0 : ℝ) < q := by exact_mod_cast q.2
    have h := hAX1 q hq
    have heq : P.prod (volume.restrict (Icc (0 : ℝ) q)) = ν.restrict (univ ×ˢ Icc (0 : ℝ) q) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict
        measurableSet_Icc, inter_eq_left.2 Icc_subset_Ici_self]
    rw [heq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)] at h
    filter_upwards [h] with p hp hp2
    exact hp ⟨mem_univ _, hp2⟩
  have hall : ∀ᵐ p ∂ν, ∀ q : {q : ℚ // 0 < q}, p.2 ∈ Icc (0 : ℝ) q →
      ∫ u in p.2..(q : ℝ), α p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..(q : ℝ), σ p.2 u p.1‖ ^ 2 :=
    ae_all_iff.2 hrat
  have hpos : ∀ᵐ p ∂ν, (0 : ℝ) ≤ p.2 := by
    have : ν = (P.prod volume).restrict (univ ×ˢ Ici 0) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [this]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ici)] with p hp
    exact hp.2
  filter_upwards [hall, hpos] with p hp hp0
  obtain ⟨ω, t⟩ := p
  simp only at hp hp0 ⊢
  -- Step 2: Claim 004's Refinement for this `(ω, t)`.
  have key : ∀ j ≤ N, t ∈ I τ N j → ∀ k, j ≤ k → k ≤ N → μ k t ω = 0 ∧ s k t ω = 0 := by
    intro j hj ht k hjk hk
    -- the step functions of (4.2) agreeing with `α t · ω`, `σ t · ω` on `[t, ∞)`
    set μ' : ℕ → ℝ := fun k => if j ≤ k then μ k t ω else 0 with hμ'
    set s' : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if j ≤ k then s k t ω else 0 with hs'
    set α' : ℝ → ℝ := fun u => if t ≤ u then α t u ω else if τ j ≤ u then μ j t ω else 0
      with hα'
    set σ' : ℝ → EuclideanSpace ℝ (Fin d) :=
      fun u => if t ≤ u then σ t u ω else if τ j ≤ u then s j t ω else 0 with hσ'
    have hstep : ∀ (f : ℝ → ℝ → Ω → ℝ) (v : ℕ → ℝ → Ω → ℝ),
        (∀ ω t T, t ≤ T → ∀ k ≤ N, T ∈ I τ N k → f t T ω = v k t ω) →
        ∀ k ≤ N, ∀ u ∈ I τ N k,
          (if t ≤ u then f t u ω else if τ j ≤ u then v j t ω else 0) =
            if j ≤ k then v k t ω else 0 := by
      intro f v h52 k hk u hu
      by_cases htu : t ≤ u
      · have hjk' := index_mono hτ hj ht hu htu
        simp only [htu, hjk', ↓reduceIte]
        exact h52 ω t u htu k hk hu
      · have hut : u < t := not_le.1 htu
        have hkj : k ≤ j := index_mono hτ hk hu ht hut.le
        rcases hkj.lt_or_eq with hlt | rfl
        · rw [LemmaAProof.mem_I_iff] at hu
          have hkN : k < N := lt_of_lt_of_le hlt hj
          have h1 : ¬ τ j ≤ u :=
            not_le.2 ((hu.2 hkN).trans_le (mono (Nat.succ_le_of_lt hlt) hj))
          have h2 : ¬ j ≤ k := not_le.2 hlt
          simp only [htu, h1, h2, ↓reduceIte]
        · rw [LemmaAProof.mem_I_iff] at hu
          simp only [htu, hu.1, le_refl, ↓reduceIte]
    have hstepσ : ∀ (f : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
        (v : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)),
        (∀ ω t T, t ≤ T → ∀ k ≤ N, T ∈ I τ N k → f t T ω = v k t ω) →
        ∀ k ≤ N, ∀ u ∈ I τ N k,
          (if t ≤ u then f t u ω else if τ j ≤ u then v j t ω else 0) =
            if j ≤ k then v k t ω else 0 := by
      intro f v h52 k hk u hu
      by_cases htu : t ≤ u
      · have hjk' := index_mono hτ hj ht hu htu
        simp only [htu, hjk', ↓reduceIte]
        exact h52 ω t u htu k hk hu
      · have hut : u < t := not_le.1 htu
        have hkj : k ≤ j := index_mono hτ hk hu ht hut.le
        rcases hkj.lt_or_eq with hlt | rfl
        · rw [LemmaAProof.mem_I_iff] at hu
          have hkN : k < N := lt_of_lt_of_le hlt hj
          have h1 : ¬ τ j ≤ u :=
            not_le.2 ((hu.2 hkN).trans_le (mono (Nat.succ_le_of_lt hlt) hj))
          have h2 : ¬ j ≤ k := not_le.2 hlt
          simp only [htu, h1, h2, ↓reduceIte]
        · rw [LemmaAProof.mem_I_iff] at hu
          simp only [htu, hu.1, le_refl, ↓reduceIte]
    -- the integrals from `t` agree
    have hintα : ∀ T, t ≤ T → ∫ u in t..T, α' u = ∫ u in t..T, α t u ω := fun T hT =>
      intervalIntegral.integral_congr fun u hu => by
        rw [uIcc_of_le hT] at hu
        simp only [hα', hu.1, ↓reduceIte]
    have hintσ : ∀ T, t ≤ T → ∫ u in t..T, σ' u = ∫ u in t..T, σ t u ω := fun T hT =>
      intervalIntegral.integral_congr fun u hu => by
        rw [uIcc_of_le hT] at hu
        simp only [hσ', hu.1, ↓reduceIte]
    -- the maturity set `M`: positive rationals `≥ t`
    set M : Set ℝ := {T | 0 < T ∧ t ≤ T ∧ ∃ q : ℚ, (q : ℝ) = T} with hM
    have hM44 : ∀ T ∈ M, Standalone.StepDriftVanish.driftCondition α' σ' t T := by
      rintro T ⟨hT0, htT, q, rfl⟩
      unfold Standalone.StepDriftVanish.driftCondition
      rw [hintα _ htT, hintσ _ htT]
      exact hp ⟨q, by exact_mod_cast hT0⟩ ⟨hp0, htT⟩
    have hMtwo : ∀ k, j ≤ k → k ≤ N → ∃ T₁ ∈ M, ∃ T₂ ∈ M, T₁ ≠ T₂ ∧
        T₁ ∈ I τ N k ∧ max (τ k) t < T₁ ∧ T₂ ∈ I τ N k ∧ max (τ k) t < T₂ := by
      intro k hjk hk
      set m := max (τ k) t with hm
      set U : ℝ := if k < N then τ (k + 1) else m + 1 with hU
      have hmU : m < U := by
        rw [hU]
        split_ifs with hkN
        · refine max_lt (hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)) ?_
          rw [LemmaAProof.mem_I_iff] at ht
          rcases hjk.lt_or_eq with hlt | rfl
          · exact (ht.2 (lt_of_lt_of_le hlt hk)).trans_le
              (mono (Nat.succ_le_succ hlt.le) (Nat.succ_le_of_lt hkN))
          · exact ht.2 hkN
        · linarith
      obtain ⟨q₁, hq₁, hq₁U⟩ := exists_rat_btwn hmU
      obtain ⟨q₂, hq₂, hq₂U⟩ := exists_rat_btwn hq₁U
      have hmem : ∀ q : ℚ, m < q → (q : ℝ) < U → (q : ℝ) ∈ M ∧ (q : ℝ) ∈ I τ N k ∧ m < q :=
        fun q hq hqU => by
        have htq : t ≤ q := (le_max_right _ _).trans hq.le
        refine ⟨⟨(hp0.trans (le_max_right _ _)).trans_lt hq, htq, q, rfl⟩,
          LemmaAProof.mem_I_iff.2 ⟨(le_max_left _ _).trans hq.le, fun hkN => ?_⟩, hq⟩
        simp only [hU, hkN, ↓reduceIte] at hqU
        exact hqU
      obtain ⟨h1M, h1I, h1m⟩ := hmem q₁ hq₁ hq₁U
      obtain ⟨h2M, h2I, h2m⟩ := hmem q₂ (hq₁.trans hq₂) hq₂U
      exact ⟨q₁, h1M, q₂, h2M, ne_of_lt hq₂, h1I, h1m, h2I, h2m⟩
    have := (StepDriftVanishProof.stepDriftVanish N d τ μ' s' α' σ' hτ0 hτ
      (hstep α μ h52α) (hstepσ σ s h52σ) j hj t ht).1 M hMtwo hM44 k hjk hk
    simpa only [hμ', hs', hjk, ↓reduceIte] using this
  refine ⟨key, fun T => ?_⟩
  -- Step 3: `α t T ω = 0` and `σ t T ω = 0` for every `T`.
  rcases lt_or_ge T t with hTt | hTt
  · exact ⟨hα0 t T ω hTt, hσ0 t T ω hTt⟩
  · obtain ⟨j, hj, ht⟩ := exists_index (N := N) hτ0 hp0
    obtain ⟨k, hk, hT⟩ := exists_index (N := N) hτ0 (hp0.trans hTt)
    have hjk := index_mono hτ hj ht hT hTt
    obtain ⟨h1, h2⟩ := key j hj ht k hjk hk
    exact ⟨by rw [h52α ω t T hTt k hk hT, h1], by rw [h52σ ω t T hTt k hk hT, h2]⟩

/-- Theorem 1 for an instance of the hypothesis structure of AX-01 and AX-02, with
`ℱ_(T_n)⁻ = leftLimit H.ℱ (H.τ n)`: the claim's "Lean shape". -/
theorem theorem1_of_HJMScheduled {Ω : Type} [MeasurableSpace Ω] (H : Upstream.HJMScheduled Ω)
    (μ : ℕ → ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin H.d)) (X : ℕ → ℕ → Ω → ℝ)
    (h52α : ∀ ω t T, t ≤ T → ∀ k ≤ H.N, T ∈ I H.τ H.N k → H.α t T ω = μ k t ω)
    (h52σ : ∀ ω t T, t ≤ T → ∀ k ≤ H.N, T ∈ I H.τ H.N k → H.σ t T ω = s k t ω)
    (h53 : ∀ ω n k, 1 ≤ n → n ≤ k → k ≤ H.N → ∀ u ∈ I H.τ H.N k, H.ξ n u ω = X n k ω) :
    ((∀ n k, 1 ≤ n → n ≤ k → k ≤ H.N → ∀ᵐ ω ∂H.μ, X n k ω = 0) ∧
      (∀ n, 1 ≤ n → n ≤ H.N → ∀ᵐ ω ∂H.μ, ∀ u, H.ξ n u ω = 0)) ∧
    (∀ᵐ p ∂(H.μ.prod (volume.restrict (Set.Ici 0))),
      (∀ j ≤ H.N, p.2 ∈ I H.τ H.N j → ∀ k, j ≤ k → k ≤ H.N →
        μ k p.2 p.1 = 0 ∧ s k p.2 p.1 = 0) ∧
      ∀ T, H.α p.2 T p.1 = 0 ∧ H.σ p.2 T p.1 = 0) :=
  theorem1 H.μ H.N H.d H.τ H.α H.σ H.ξ (fun n => Upstream.leftLimit H.ℱ (H.τ n)) μ s X
    H.τ_zero H.τ_strictMono (fun _ => Upstream.leftLimit_le _ _) H.α_zero_of_lt H.σ_zero_of_lt
    H.ξ_zero_of_lt H.drift_integrated H.jump_martingale h52α h52σ h53

end Novel.Theorem1Proof

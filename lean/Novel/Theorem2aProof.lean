import Standalone.Theorem2a
import Novel.RampDriftIdentifiedProof
import Novel.JumpLawTiltedGaussianProof
import Novel.D2InstanceProof

/-! Claim 010: assembly of Claims 007 and 008. No additional hypotheses or axioms. -/

open MeasureTheory Set

namespace Novel.Theorem2aProof

open Standalone.LemmaA Standalone.RampDriftIdentified Standalone.Theorem2a

/-- Lemma 010-A: extension to all scheduled intervals, including maturities before `t`. -/
noncomputable def function_010_A {E : Type*} [AddCommMonoid E] (N : ℕ) (τ : ℕ → ℝ)
    (f : ℕ → ℝ → E) (u : ℝ) : E :=
  ∑ k ∈ Finset.range (N + 1), (I τ N k).indicator (f k) u

lemma lemma_010_A {E : Type*} [AddCommMonoid E] {N k : ℕ} {τ : ℕ → ℝ}
    (hτ : StrictMonoOn τ (Iic N)) (f : ℕ → ℝ → E) (hk : k ≤ N) {u : ℝ}
    (hu : u ∈ I τ N k) : function_010_A N τ f u = f k u := by
  classical
  unfold function_010_A
  rw [Finset.sum_eq_single k]
  · exact indicator_of_mem hu _
  · intro b hb hbk
    exact indicator_of_notMem
      (fun hub => hbk (D2InstanceProof.index_unique hτ
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)) hk hub hu)) _
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) h

/-- Lemma 010-B: Claim 007 for coefficients specified only on `[t, ∞)`. -/
lemma lemma_010_B {N d : ℕ} {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    (hτ : StrictMonoOn τ (Iic N)) (s : ℕ → EuclideanSpace ℝ (Fin d))
    (a b : ℕ → ℝ) (α : ℝ → ℝ) (σ : ℝ → EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht0 : 0 ≤ t)
    (hα : ∀ u, t ≤ u → ∀ k ≤ N, u ∈ I τ N k → α u = a k + (u - τ k) * b k)
    (hσ : ∀ u, t ≤ u → ∀ k ≤ N, u ∈ I τ N k → σ u = s k)
    {j : ℕ} (hj : j ≤ N) (ht : t ∈ I τ N j) :
    let B : Prop := ∀ k, j ≤ k → k ≤ N → a k = aStar τ s j k t ∧ b k = bStar s k
    ((∀ q : ℚ, 0 < (q : ℝ) → t ≤ q →
        ∫ u in t..(q : ℝ), α u = (1 / 2 : ℝ) * ‖∫ u in t..(q : ℝ), σ u‖ ^ 2) → B) ∧
    (B → ∀ T, t ≤ T → ∫ u in t..T, α u = (1 / 2 : ℝ) * ‖∫ u in t..T, σ u‖ ^ 2) ∧
    (B ↔ ∀ T, t ≤ T → α T = inner ℝ (σ T) (∫ u in t..T, σ u)) := by
  dsimp only
  let α' := function_010_A N τ (fun k u => a k + (u - τ k) * b k)
  let σ' := function_010_A N τ (fun k _ => s k)
  have hα' : ∀ k ≤ N, ∀ u ∈ I τ N k, α' u = a k + (u - τ k) * b k :=
    fun _ hk _ hu => lemma_010_A hτ _ hk hu
  have hσ' : ∀ k ≤ N, ∀ u ∈ I τ N k, σ' u = s k :=
    fun _ hk _ hu => lemma_010_A hτ _ hk hu
  have heα : ∀ u, t ≤ u → α' u = α u := by
    intro u hu
    obtain ⟨k, hk, huk⟩ := Theorem1Proof.exists_index (N := N) hτ0 (ht0.trans hu)
    rw [hα' k hk u huk, hα u hu k hk huk]
  have heσ : ∀ u, t ≤ u → σ' u = σ u := by
    intro u hu
    obtain ⟨k, hk, huk⟩ := Theorem1Proof.exists_index (N := N) hτ0 (ht0.trans hu)
    rw [hσ' k hk u huk, hσ u hu k hk huk]
  have hiα : ∀ T, t ≤ T → ∫ u in t..T, α' u = ∫ u in t..T, α u := by
    intro T hT
    exact intervalIntegral.integral_congr fun u hu => heα u ((uIcc_of_le hT ▸ hu).1)
  have hiσ : ∀ T, t ≤ T → ∫ u in t..T, σ' u = ∫ u in t..T, σ u := by
    intro T hT
    exact intervalIntegral.integral_congr fun u hu => heσ u ((uIcc_of_le hT ▸ hu).1)
  have h7 := RampDriftIdentifiedProof.rampDriftIdentified N d τ s σ' a b α'
    hτ0 hτ hσ' hα' j hj t ht
  dsimp only at h7
  refine ⟨?_, ?_, ?_⟩
  · intro hrat
    apply h7.2.1
    let M : Set ℝ := {T | 0 < T ∧ t ≤ T ∧ ∃ q : ℚ, (q : ℝ) = T}
    refine ⟨M, fun _ h => h.2.1, ?_, ?_⟩
    · intro k hjk hk
      obtain ⟨L, hL, hLI⟩ := RampDriftIdentifiedProof.exists_len hτ ht hjk hk
      let m := max (τ k) t
      obtain ⟨q₁, hq₁, hq₁L⟩ := exists_rat_btwn (show m < m + L by linarith)
      obtain ⟨q₂, hq₂, hq₂L⟩ := exists_rat_btwn hq₁L
      obtain ⟨q₃, hq₃, hq₃L⟩ := exists_rat_btwn hq₂L
      have hmem : ∀ q : ℚ, m < q → (q : ℝ) < m + L →
          (q : ℝ) ∈ M ∧ (q : ℝ) ∈ I τ N k ∧ m < q := by
        intro q hq hqL
        have htm : t ≤ m := le_max_right _ _
        refine ⟨⟨by linarith, by linarith, q, rfl⟩, ?_, hq⟩
        convert hLI (q - m) (by linarith) (by linarith) using 1
        dsimp [m]
        ring
      obtain ⟨h1M, h1I⟩ := hmem q₁ hq₁ hq₁L
      obtain ⟨h2M, h2I⟩ := hmem q₂ (hq₁.trans hq₂) hq₂L
      obtain ⟨h3M, h3I⟩ := hmem q₃ (hq₁.trans (hq₂.trans hq₃)) hq₃L
      exact ⟨q₁, h1M, q₂, h2M, q₃, h3M, ne_of_lt hq₂,
        ne_of_lt (hq₂.trans hq₃), ne_of_lt hq₃, h1I, h2I, h3I⟩
    · rintro T ⟨hT0, htT, q, rfl⟩
      unfold Standalone.StepDriftVanish.driftCondition
      rw [hiα _ htT, hiσ _ htT]
      exact hrat q hT0 htT
  · intro hB T hT
    have h := h7.2.2.1 hB T hT
    unfold Standalone.StepDriftVanish.driftCondition at h
    rwa [hiα _ hT, hiσ _ hT] at h
  · refine h7.2.2.2.trans ?_
    exact forall_congr' fun T => imp_congr_right fun hT => by rw [heα T hT, heσ T hT, hiσ T hT]

theorem theorem2a : Standalone.Theorem2a.statement := by
  intro Ω m₀ P _ N d τ α σ ξ G s a b X y hτ0 hτ hG hξm hξ0 hy hσ hα hξ
  dsimp only
  set ν : Measure (Ω × ℝ) := P.prod (volume.restrict (Ici 0)) with hν
  have heq : ∀ T : ℝ, P.prod (volume.restrict (Icc 0 T)) = ν.restrict (univ ×ˢ Icc 0 T) := by
    intro T
    rw [hν, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict
      measurableSet_Icc, inter_eq_left.2 Icc_subset_Ici_self]
  have hpos : ∀ᵐ p ∂ν, (0 : ℝ) ≤ p.2 := by
    have : ν = (P.prod volume).restrict (univ ×ˢ Ici 0) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [this]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ici)] with p hp
    exact hp.2
  have hpoint := fun (ω : Ω) (t : ℝ) (ht0 : 0 ≤ t) (j : ℕ) (hj : j ≤ N)
      (ht : t ∈ I τ N j) =>
    lemma_010_B hτ0 hτ (fun k => s k t) (fun k => a k t ω) (fun k => b k t ω)
      (fun u => α t u ω) (fun u => σ t u ω) ht0 (hα ω t ht0) (hσ ω t ht0) hj ht
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hAX1
    have hrat : ∀ q : {q : ℚ // 0 < q}, ∀ᵐ p ∂ν, p.2 ∈ Icc (0 : ℝ) q →
        ∫ u in p.2..(q : ℝ), α p.2 u p.1 =
          (1 / 2 : ℝ) * ‖∫ u in p.2..(q : ℝ), σ p.2 u p.1‖ ^ 2 := by
      intro q
      have hq : (0 : ℝ) < q := by exact_mod_cast q.2
      have h := hAX1 q hq
      rw [heq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)] at h
      filter_upwards [h] with p hp hp2
      exact hp ⟨mem_univ _, hp2⟩
    have hall := ae_all_iff.2 hrat
    filter_upwards [hall, hpos] with p hp hp0
    intro j hj ht
    apply (hpoint p.1 p.2 hp0 j hj ht).1
    intro q hq htq
    exact hp ⟨q, by exact_mod_cast hq⟩ ⟨hp0, htq⟩
  · intro hB T _
    rw [heq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
    filter_upwards [hB, hpos] with p hp hp0 hpT
    obtain ⟨j, hj, ht⟩ := Theorem1Proof.exists_index (N := N) hτ0 hp0
    exact (hpoint p.1 p.2 hp0 j hj ht).2.1 (hp j hj ht) T hpT.2.2
  · intro hAX2 n hn hnN
    have hmX : ∀ k, n ≤ k → k ≤ N → Measurable (X n k) := by
      intro k hnk hk
      have he : ξ n (τ k) = X n k := by
        funext ω
        simpa using hξ ω n k hn hnk hk (τ k) (D2InstanceProof.self_mem_I hτ hk)
      rw [← he]
      exact hξm n hn hnN (τ k)
    have h8 := JumpLawTiltedGaussianProof.jumpLawTiltedGaussian.1 P (G n) N n τ
      (X n) (y n) (ξ n) (hG n) hτ0 hτ hn hnN hmX
      (fun k hnk hk => hy n k hn hnk hk)
      (fun k hnk hk u hu ω => hξ ω n k hn hnk hk u hu) (hξ0 n hn hnN)
    exact h8.2.1 (hAX2 n hn hnN)
  · intro hB n hn hnN
    have hmX : ∀ k, n ≤ k → k ≤ N → Measurable (X n k) := by
      intro k hnk hk
      have he : ξ n (τ k) = X n k := by
        funext ω
        simpa using hξ ω n k hn hnk hk (τ k) (D2InstanceProof.self_mem_I hτ hk)
      rw [← he]
      exact hξm n hn hnN (τ k)
    have h8 := JumpLawTiltedGaussianProof.jumpLawTiltedGaussian.1 P (G n) N n τ
      (X n) (y n) (ξ n) (hG n) hτ0 hτ hn hnN hmX
      (fun k hnk hk => hy n k hn hnk hk)
      (fun k hnk hk u hu ω => hξ ω n k hn hnk hk u hu) (hξ0 n hn hnN)
    obtain ⟨h83, h84, h85⟩ := hB n hn hnN
    exact h8.2.2.1 h83 h84 h85
  · intro hB
    filter_upwards [hB, hpos] with p hp hp0
    obtain ⟨j, hj, ht⟩ := Theorem1Proof.exists_index (N := N) hτ0 hp0
    exact (hpoint p.1 p.2 hp0 j hj ht).2.2.1 (hp j hj ht)
  · intro hB'
    filter_upwards [hB', hpos] with p hp hp0
    intro j hj ht
    exact (hpoint p.1 p.2 hp0 j hj ht).2.2.2 hp

/-- The necessity conclusions for the audited hypothesis structure. The converse is the
axiom-free `theorem2a` above. Claim 009's `D2InstanceProof.d2` supplies instances of `H`. -/
theorem theorem2a_of_HJMScheduled {Ω : Type} [MeasurableSpace Ω] (H : Upstream.HJMScheduled Ω)
    (s : ℕ → ℝ → EuclideanSpace ℝ (Fin H.d)) (a b : ℕ → ℝ → Ω → ℝ)
    (X y : ℕ → ℕ → Ω → ℝ)
    (hy : ∀ n k, 1 ≤ n → n ≤ k → k ≤ H.N → Measurable[Upstream.leftLimit H.ℱ (H.τ n)] (y n k))
    (hσ : ∀ ω t, 0 ≤ t → ∀ T, t ≤ T → ∀ k ≤ H.N, T ∈ I H.τ H.N k → H.σ t T ω = s k t)
    (hα : ∀ ω t, 0 ≤ t → ∀ T, t ≤ T → ∀ k ≤ H.N, T ∈ I H.τ H.N k →
      H.α t T ω = a k t ω + (T - H.τ k) * b k t ω)
    (hξ : ∀ ω n k, 1 ≤ n → n ≤ k → k ≤ H.N → ∀ u ∈ I H.τ H.N k,
      H.ξ n u ω = X n k ω + y n k ω * (u - H.τ k)) :
    (∀ᵐ p ∂(H.μ.prod (volume.restrict (Ici 0))), cond104 H.N H.τ s a b p.1 p.2) ∧
    (∀ᵐ p ∂(H.μ.prod (volume.restrict (Ici 0))), ∀ T, p.2 ≤ T →
      H.α p.2 T p.1 = inner ℝ (H.σ p.2 T p.1) (∫ u in p.2..T, H.σ p.2 u p.1)) ∧
    condii H.μ (fun n => Upstream.leftLimit H.ℱ (H.τ n)) H.N H.τ X y := by
  have hξm : ∀ n, 1 ≤ n → n ≤ H.N → ∀ u, Measurable (H.ξ n u) := by
    intro n hn hnN u
    exact ((H.ξ_measurable n hn hnN).comp
      (measurable_const.prodMk measurable_id)).mono (H.ℱ.le _) le_rfl
  have h := theorem2a H.μ H.N H.d H.τ H.α H.σ H.ξ
    (fun n => Upstream.leftLimit H.ℱ (H.τ n)) s a b X y H.τ_zero H.τ_strictMono
    (fun _ => Upstream.leftLimit_le _ _) hξm H.ξ_zero_of_lt hy hσ hα hξ
  have hB := h.1.1 H.drift_integrated
  exact ⟨hB, h.2.2.1 hB, h.2.1.1 H.jump_martingale⟩

end Novel.Theorem2aProof

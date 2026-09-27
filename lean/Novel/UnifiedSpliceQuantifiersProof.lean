import Standalone.UnifiedSpliceQuantifiers
import Novel.UnifiedSpliceStep0Proof

open Matrix NormedSpace MeasureTheory Set Filter Topology
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.UnifiedSpliceQuantifiers
namespace Novel.UnifiedSpliceQuantifiersProof

variable {k r : ℕ}

/-! ### The front end between meetings -/

/-- With no meeting in `(a, v]`, `n(v) = n(a)`. -/
lemma nS_const (S : Finset ℝ) {a v : ℝ} (hav : a ≤ v) (h : ∀ τ ∈ S, τ ∉ Ioc a v) :
    nS S v = nS S a := by
  unfold nS
  congr 1
  refine Finset.filter_congr fun τ hτ => ?_
  have := h τ hτ
  simp only [mem_Ioc, not_and, not_le] at this
  exact ⟨fun hv => not_lt.1 fun ha => absurd (this ha) (not_lt.2 hv), fun ha => ha.trans hav⟩

/-- A meeting `τ` with none in `[a, τ)` adds one: `n(a) = n(τ) − 1`. -/
lemma nS_step (S : Finset ℝ) {a τ : ℝ} (hτ : τ ∈ S) (haτ : a < τ) (h : ∀ τ' ∈ S, τ' ∉ Ioo a τ) :
    nS S a = nS S τ - 1 := by
  classical
  have e : S.filter (fun x => x ≤ τ) = insert τ (S.filter fun x => x ≤ a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxτ⟩
      rcases eq_or_lt_of_le hxτ with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, not_lt.1 fun hax => h x hx ⟨hax, hlt⟩⟩
    · rintro (rfl | ⟨hx, hxa⟩)
      · exact ⟨hτ, le_rfl⟩
      · exact ⟨hx, hxa.trans haτ.le⟩
  have hn : τ ∉ S.filter fun x => x ≤ a := by
    simp only [Finset.mem_filter, not_and, not_le]; exact fun _ => haτ
  unfold nS
  rw [e, Finset.card_insert_of_notMem hn, Nat.add_sub_cancel]

/-- With no meeting in `(a, T)`, `P(u, T) = P(u, a) + (T − a) V_{n(a)}`. -/
lemma prim_lin (S : Finset ℝ) (p : Pt049 k r) (u : ℝ) {a T : ℝ} (haT : a ≤ T)
    (h : ∀ τ ∈ S, τ ∉ Ioo a T) : prim049 S p u T = prim049 S p u a + (T - a) • p.V (nS S a) := by
  funext l
  simp only [prim049, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (Novel.UnifiedSpliceStep0Proof.pc_ii (fun n => p.V n l) S u a)
    (Novel.UnifiedSpliceStep0Proof.pc_ii (fun n => p.V n l) S a T)]
  congr 1
  have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ T := by
    simpa using (countable_singleton T).ae_notMem volume
  rw [intervalIntegral.integral_congr_ae (g := fun _ => p.V (nS S a) l)]
  · simp
  · filter_upwards [hne] with v hv hvI
    rw [uIoc_of_le haT] at hvI
    rw [nS_const S hvI.1.le fun τ hτ hτI => h τ hτ ⟨hτI.1, lt_of_le_of_lt hτI.2
      (lt_of_le_of_ne hvI.2 hv)⟩]

/-- A point off a finite set has a ball meeting it at most in itself. -/
lemma exists_ball (S : Finset ℝ) (x : ℝ) : ∃ ε > 0, ∀ τ ∈ S, τ ≠ x → ε ≤ |τ - x| := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
    ((S.erase x).finite_toSet.isClosed.isOpen_compl) x (by simp)
  refine ⟨ε, hε, fun τ hτ hne => not_lt.1 fun hlt => ?_⟩
  have := hball (show τ ∈ Metric.ball x ε by rw [Metric.mem_ball, Real.dist_eq]; exact hlt)
  simp [hτ, hne] at this

/-! ### At one time and path -/

section Point
variable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (p : Pt049 k r)
  (u H : ℝ)

/-- Step 0's identity at `T`. -/
def Eid (T : ℝ) : Prop :=
  resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z (T - u) -
      (sigB p.Hp p.Hz c A d (T - u) ⬝ᵥ prim049 S p u T +
        p.V (nS S T) ⬝ᵥ SigB p.Hp p.Hz c A d (T - u)) =
    p.V (nS S T) ⬝ᵥ prim049 S p u T - p.dL (nS S T) - p.dC (nS S T) * T

variable {c A d S p u H}

/-- On a meeting-free interval `(a, b) ⊆ (u, H)`, the consistency of stage 3 holds, with the
front end's primitive `T V_{n(a)} + κ`, `κ = P(u, a) − a V_{n(a)}`. -/
lemma affine_on (hE : ∀ T ∈ Ioo u H, T ∉ S → Eid c A d S p u T) {a b : ℝ} (hua : u ≤ a)
    (hbH : b ≤ H) (hfree : ∀ τ ∈ S, τ ∉ Ioo a b) : ∀ T ∈ Ioo a b,
    resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z (T - u) -
      cross p.Hp p.Hz c A d (p.V (nS S a)) (prim049 S p u a - a • p.V (nS S a)) u T =
    (p.V (nS S a) ⬝ᵥ (prim049 S p u a - a • p.V (nS S a)) - p.dL (nS S a)) +
      (p.V (nS S a) ⬝ᵥ p.V (nS S a) - p.dC (nS S a)) * T := by
  intro T hT
  have hTS : T ∉ S := fun h => hfree T h hT
  have hn : nS S T = nS S a := nS_const S hT.1.le fun τ hτ hτI =>
    hfree τ hτ ⟨hτI.1, lt_of_le_of_lt hτI.2 hT.2⟩
  have hP := prim_lin S p u hT.1.le fun τ hτ hτI => hfree τ hτ ⟨hτI.1, hτI.2.trans hT.2⟩
  have h := hE T ⟨lt_of_le_of_lt hua hT.1, lt_of_lt_of_le hT.2 hbH⟩ hTS
  unfold Eid at h
  rw [hn, hP] at h
  simp only [cross, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h ⊢
  linarith

/-- (a) and (b)(iv) at one time and path, from Step 0's identity. -/
lemma point (hA : IsUnit A.det)
    (hobs : ∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0)
    (huH : u < H) (huS : u ∉ S) (hE : ∀ T ∈ Ioo u H, T ∉ S → Eid c A d S p u T) :
    (∀ τ ∈ S, u < τ → τ < H →
      (∀ μ', 1 ≤ μ' → μ' ≤ d → p.Hp μ' ⬝ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
      p.Hz *ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
    ∃ α β : ℝ, ∀ x, resid (sharp p.Hp (p.V (nS S u))) p.Hz c A d p.bP p.zP p.bZ p.z x =
      α + β * x := by
  have hext : ∀ (V κ : Fin k → ℝ) {a b α β : ℝ}, a < b → (∀ T ∈ Ioo a b,
      resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z (T - u) - cross p.Hp p.Hz c A d V κ u T =
        α + β * T) → ∀ T, resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z (T - u) -
          cross p.Hp p.Hz c A d V κ u T = α + β * T := fun V κ _ _ _ _ hab h =>
    Novel.UnifiedSpliceConverseProof.affine_ext
      (fun x => Novel.UnifiedSpliceConverseProof.f_an p.Hp p.Hz c A d p.bP p.zP p.bZ p.z V κ u x)
      hab h
  refine ⟨fun τ hτ huτ hτH => ?_, ?_⟩
  · -- (a) at the meeting `τ`
    obtain ⟨ε, hε, hball⟩ := exists_ball S τ
    set δ := min (ε / 2) (min ((τ - u) / 2) ((H - τ) / 2))
    have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδu : δ ≤ (τ - u) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδH : δ ≤ (H - τ) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hfreeL : ∀ τ' ∈ S, τ' ∉ Ioo (τ - δ) τ := fun τ' hτ' hI => by
      have := hball τ' hτ' hI.2.ne
      rw [abs_of_neg (by linarith [hI.2])] at this
      linarith [hI.1]
    have hfreeR : ∀ τ' ∈ S, τ' ∉ Ioo τ (τ + δ) := fun τ' hτ' hI => by
      have := hball τ' hτ' hI.1.ne'
      rw [abs_of_pos (by linarith [hI.1])] at this
      linarith [hI.2]
    have eL := affine_on hE (a := τ - δ) (b := τ) (by linarith) hτH.le hfreeL
    have eR := affine_on hE (a := τ) (b := τ + δ) huτ.le (by linarith) hfreeR
    have fL := hext _ _ (by linarith) eL
    have fR := hext _ _ (by linarith) eR
    have hstep := nS_step S hτ (show τ - δ < τ by linarith) hfreeL
    have hPτ := prim_lin S p u (show τ - δ ≤ τ by linarith) hfreeL
    have hκ : (prim049 S p u τ - τ • p.V (nS S τ)) -
        (prim049 S p u (τ - δ) - (τ - δ) • p.V (nS S (τ - δ))) =
        -τ • (p.V (nS S τ) - p.V (nS S (τ - δ))) := by
      rw [hPτ]; funext l; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    set V₀ := p.V (nS S (τ - δ))
    set V₁ := p.V (nS S τ)
    set κ₀ := prim049 S p u (τ - δ) - (τ - δ) • V₀
    set κ₁ := prim049 S p u τ - τ • V₁
    have h := Novel.UnifiedSpliceNecessityProof.necessityS k r d p.Hp p.Hz c A hA hobs V₀ V₁ κ₀ κ₁
      τ u 0 1 ((V₀ ⬝ᵥ κ₀ - p.dL (nS S (τ - δ))) - (V₁ ⬝ᵥ κ₁ - p.dL (nS S τ)))
      ((V₀ ⬝ᵥ V₀ - p.dC (nS S (τ - δ))) - (V₁ ⬝ᵥ V₁ - p.dC (nS S τ))) one_pos hκ fun T _ => by
        linear_combination fL T - fR T
    have hV₀ : V₀ = p.V (nS S τ - 1) := by simp only [V₀, hstep]
    rwa [hV₀] at h
  · -- (b)(iv) on the current interval
    obtain ⟨ε, hε, hball⟩ := exists_ball S u
    set hi := min (u + ε) H
    have hhi : u < hi := lt_min (by linarith) huH
    have hfree : ∀ τ ∈ S, τ ∉ Ioo u hi := fun τ hτ hI => by
      have := hball τ hτ (fun h => huS (h ▸ hτ))
      rw [abs_of_pos (by linarith [hI.1])] at this
      linarith [hI.2, min_le_left (u + ε) H]
    have e := affine_on hE (a := u) (b := hi) le_rfl (min_le_right _ _) hfree
    have hP0 : prim049 S p u u = 0 := by funext l; simp [prim049]
    rw [hP0, zero_sub] at e
    have hconv := Novel.UnifiedSpliceConverseProof.converseS k r d p.Hp p.Hz c A hA hobs p.bP p.zP
      p.bZ p.z p.V (fun m => -u • p.V m) (fun _ => 0) (fun _ => u) (fun _ => hi) (nS S u) (nS S u)
      u le_rfl rfl (fun m h1 h2 => absurd (h1.trans_le h2) (lt_irrefl _)) (fun _ _ _ => hhi)
    obtain ⟨-, h⟩ := hconv.1 fun m h1 h2 => by
      obtain rfl : m = nS S u := le_antisymm h2 h1
      exact ⟨_, _, fun T hT => by have := e T hT; rwa [← neg_smul] at this⟩
    exact h

end Point

/-! ### The claim's quantifiers -/

theorem quantS : quantifierStatement := by
  intro Ω _ μ _ k r d c A hA hobs S H D hax
  have h0 := Novel.UnifiedSpliceStep0Proof.step0S Ω μ k r d c A hA S H D hax
  have hX : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), q.2 ∉ ((insert H S : Finset ℝ) : Set ℝ) := by
    refine (Measure.ae_prod_iff_ae_ae (measurable_snd
      (insert H S).finite_toSet.measurableSet.compl)).2 (Filter.Eventually.of_forall fun _ => ?_)
    exact ae_restrict_of_ae ((insert H S).finite_toSet.countable.ae_notMem volume)
  have hm : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), q.2 ∈ Icc 0 H :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Icc)
  have hall : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))),
      (∀ τ ∈ S, q.2 < τ → τ < H →
        (∀ μ', 1 ≤ μ' → μ' ≤ d →
          (D q.2 q.1).Hp μ' ⬝ᵥ ((D q.2 q.1).V (nS S τ) - (D q.2 q.1).V (nS S τ - 1)) = 0) ∧
        (D q.2 q.1).Hz *ᵥ ((D q.2 q.1).V (nS S τ) - (D q.2 q.1).V (nS S τ - 1)) = 0) ∧
      ∃ α β : ℝ, ∀ x, resid (sharp (D q.2 q.1).Hp ((D q.2 q.1).V (nS S q.2))) (D q.2 q.1).Hz c A d
        (D q.2 q.1).bP (D q.2 q.1).zP (D q.2 q.1).bZ (D q.2 q.1).z x = α + β * x := by
    filter_upwards [h0, hX, hm] with q hq hx hmem
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or] at hx
    exact point hA hobs (lt_of_le_of_ne hmem.2 hx.1) hx.2 fun T hT hTS => hq T hT hTS
  exact Measure.ae_ae_of_ae_prod hall

theorem unifiedSpliceQuantifiers : Standalone.UnifiedSpliceQuantifiers.statement := quantS

end Novel.UnifiedSpliceQuantifiersProof

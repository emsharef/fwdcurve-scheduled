import Standalone.FrontEndConstructionMatching
import Novel.SpliceLocalizationConverseProof
import Novel.UnifiedSpliceQuantifiersProof
import Novel.UnifiedSpliceConverseProof

/-! # Claim 055 (d)–(f) at the coefficient level (proof)

(d): off the null set `Ω × (S ∪ {H})`, Claim 050's `explicitStatement` gives AX-01 at every
maturity with the matching drifts. Its hypothesis "R♯ affine on ℝ" comes from "affine on
`[0, H − u]`" because `R♯` is real-analytic (`resid_an`, `affine_ext`; Red's note 2).

(e): Claim 049's `quantifierStatement` gives (`eq:steporth`) and `R♯` affine in the iterated form
"almost surely, for almost every `u`". The condition set is measurable (`condSet_meas`: `R♯` is
continuous in `x`, so affinity is a countable condition), so this is the product form. Then (d)
applies, and Step 0 (`step0Statement`) holds both for the given drifts and for the matching ones.
Its left side does not involve the front-end drifts, so `dL + dC T` agrees at every `T` in the
piece; two maturities in the same piece separate `dL` and `dC`.

(f): "only if" is `quantifierStatement` in product form, and "if" is (d).

Reused, not reproved: `Novel.SpliceLocalizationConverseProof.explicitS`,
`Novel.UnifiedSpliceQuantifiersProof.quantS`, `Novel.UnifiedSpliceStep0Proof.step0S`, `nS_meas`,
`nS_eventually`, `prod_Icc`, `Novel.UnifiedSpliceConverseProof.resid_an`, `affine_ext`.
-/

open Matrix NormedSpace MeasureTheory Set Filter Topology
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse Standalone.FrontEndConstructionMatching

namespace Novel.FrontEndConstructionMatchingProof

variable {k r : ℕ}

/-! ### Measurability of the condition set -/

section Meas
variable {α : Type*} [MeasurableSpace α]

lemma resid_meas (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)
    {Hp : α → ℕ → Fin k → ℝ} {Hz : α → Matrix (Fin r) (Fin k) ℝ} {bP zP : α → ℕ → ℝ}
    {bZ z : α → Fin r → ℝ} (hHp : ∀ μ l, Measurable fun a => Hp a μ l)
    (hHz : ∀ i l, Measurable fun a => Hz a i l) (hbP : ∀ μ, Measurable fun a => bP a μ)
    (hzP : ∀ μ, Measurable fun a => zP a μ) (hbZ : ∀ i, Measurable fun a => bZ a i)
    (hz : ∀ i, Measurable fun a => z a i) (x : ℝ) :
    Measurable fun a => resid (Hp a) (Hz a) c A d (bP a) (zP a) (bZ a) (z a) x := by
  simp only [resid, sigB, SigB, dotProduct, vecMul, mulVec, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma sharp_meas {Hp : α → ℕ → Fin k → ℝ} {V : α → Fin k → ℝ}
    (hHp : ∀ μ l, Measurable fun a => Hp a μ l) (hV : ∀ l, Measurable fun a => V a l) :
    ∀ μ l, Measurable fun a => sharp (Hp a) (V a) μ l := fun μ l => by
  by_cases h : μ = 0
  · subst h
    simp only [sharp, Function.update_self, Pi.add_apply]
    exact (hHp 0 l).add (hV l)
  · simp only [sharp, Function.update_of_ne h]
    exact hHp μ l

variable {Ω : Type} [MeasurableSpace Ω]

lemma Vcur_meas {D : ℝ → Ω → Pt049 k r} (hD : FieldsMeas D) (S : Finset ℝ) (l : Fin k) :
    Measurable fun q : Ω × ℝ => (D q.2 q.1).V (nS S q.2) l := by
  have h : Measurable fun p : (Ω × ℝ) × ℕ => (D p.1.2 p.1.1).V p.2 l :=
    measurable_from_prod_countable_left fun n => hD.2.2.2.2.2.2 n l
  exact h.comp (measurable_id.prodMk ((Novel.UnifiedSpliceStep0Proof.nS_meas S).comp
    measurable_snd))

lemma Rsharp_meas {D : ℝ → Ω → Pt049 k r} (hD : FieldsMeas D) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (x : ℝ) :
    Measurable fun q : Ω × ℝ => Rsharp c A d S (D q.2 q.1) q.2 x := by
  obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, -⟩ := id hD
  exact resid_meas c A d (sharp_meas hHp (Vcur_meas hD S)) hHz hbP hzP hbZ hz x

/-- `R♯(u, ·)` is continuous. -/
lemma Rsharp_cont (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) : Continuous fun x => Rsharp c A d S p u x :=
  continuous_iff_continuousAt.2 fun x =>
    (Novel.UnifiedSpliceConverseProof.resid_an _ p.Hz c A d p.bP p.zP p.bZ p.z x).continuousAt

/-- Affinity on `ℝ` is a countable condition. -/
lemma affine_iff (f : ℝ → ℝ) (hf : Continuous f) :
    (∃ α β : ℝ, ∀ x, f x = α + β * x) ↔ ∀ q : ℚ, f q = f 0 + q * (f 1 - f 0) := by
  constructor
  · rintro ⟨α, β, h⟩ q
    rw [h, h 0, h 1]; ring
  · intro h
    refine ⟨f 0, f 1 - f 0, fun x => ?_⟩
    have hc : Continuous fun x => f 0 + (f 1 - f 0) * x := by fun_prop
    have heq : (fun x => f x) = fun x => f 0 + (f 1 - f 0) * x :=
      Rat.denseRange_cast.equalizer hf hc (funext fun q => by
        simp only [Function.comp_apply]; rw [h q]; ring)
    exact congrFun heq x

/-- The condition set of Claim 049's `quantifierStatement` is measurable. -/
lemma condSet_meas {D : ℝ → Ω → Pt049 k r} (hD : FieldsMeas D) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (H : ℝ) :
    MeasurableSet {q : Ω × ℝ | orth d S H (D q.2 q.1) q.2 ∧
      ∃ α β : ℝ, ∀ x, Rsharp c A d S (D q.2 q.1) q.2 x = α + β * x} := by
  obtain ⟨hHp, hHz, -, -, -, -, hV⟩ := id hD
  have hdot : ∀ (a b : Ω × ℝ → Fin k → ℝ), (∀ l, Measurable fun q => a q l) →
      (∀ l, Measurable fun q => b q l) → Measurable fun q => a q ⬝ᵥ b q := fun a b ha hb => by
    simp only [dotProduct]; fun_prop
  have hG : ∀ τ : ℝ, ∀ l, Measurable fun q : Ω × ℝ =>
      ((D q.2 q.1).V (nS S τ) - (D q.2 q.1).V (nS S τ - 1)) l := fun τ l => by
    simp only [Pi.sub_apply]; exact (hV _ l).sub (hV _ l)
  rw [measurableSet_setOfPred]
  refine Measurable.and ?_ ?_
  · unfold orth
    have e : (fun q : Ω × ℝ => ∀ τ ∈ S, q.2 < τ → τ < H →
        (∀ μ, 1 ≤ μ → μ ≤ d →
          (D q.2 q.1).Hp μ ⬝ᵥ ((D q.2 q.1).V (nS S τ) - (D q.2 q.1).V (nS S τ - 1)) = 0) ∧
        (D q.2 q.1).Hz *ᵥ ((D q.2 q.1).V (nS S τ) - (D q.2 q.1).V (nS S τ - 1)) = 0) =
        fun q => ∀ τ : S, q.2 < τ.1 → τ.1 < H →
        (∀ μ, 1 ≤ μ → μ ≤ d → (D q.2 q.1).Hp μ ⬝ᵥ
          ((D q.2 q.1).V (nS S τ.1) - (D q.2 q.1).V (nS S τ.1 - 1)) = 0) ∧
        ∀ i, ((D q.2 q.1).Hz *ᵥ ((D q.2 q.1).V (nS S τ.1) - (D q.2 q.1).V (nS S τ.1 - 1))) i =
          0 := by
      funext q
      simp only [Subtype.forall, funext_iff, Pi.zero_apply]
    rw [e]
    refine Measurable.forall fun τ => Measurable.imp ?_ (Measurable.imp measurable_const ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_snd measurable_const)
    · refine Measurable.and (Measurable.forall fun μ => Measurable.imp measurable_const
        (Measurable.imp measurable_const ?_)) (Measurable.forall fun i => ?_)
      · exact measurableSet_setOfPred.1 (measurableSet_eq_fun
          (hdot _ _ (fun l => hHp μ l) (hG τ.1)) measurable_const)
      · refine measurableSet_setOfPred.1 (measurableSet_eq_fun ?_ measurable_const)
        simp only [mulVec, dotProduct]
        exact Finset.measurable_sum _ fun l _ => (hHz i l).mul (hG τ.1 l)
  · have e : (fun q : Ω × ℝ => ∃ α β : ℝ, ∀ x, Rsharp c A d S (D q.2 q.1) q.2 x = α + β * x) =
        fun q => ∀ x : ℚ, Rsharp c A d S (D q.2 q.1) q.2 x = Rsharp c A d S (D q.2 q.1) q.2 0 +
          x * (Rsharp c A d S (D q.2 q.1) q.2 1 - Rsharp c A d S (D q.2 q.1) q.2 0) := by
      funext q
      exact propext (affine_iff _ (Rsharp_cont c A d S _ _))
    rw [e]
    have hR := Rsharp_meas hD c A d S
    exact Measurable.forall fun x => measurableSet_setOfPred.1 (measurableSet_eq_fun (hR x)
      ((hR 0).add (measurable_const.mul ((hR 1).sub (hR 0)))))

end Meas

/-! ### (d) -/

section Main
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

/-- Almost every `(ω, u)` has `u ∈ [0, H]`, `u ∉ S` and `u ≠ H`. -/
lemma ae_good (S : Finset ℝ) (H : ℝ) :
    ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), q.2 ∈ Icc 0 H ∧ q.2 ∉ S ∧ q.2 ≠ H := by
  have h1 : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), q.2 ∈ Icc 0 H := by
    rw [Novel.UnifiedSpliceStep0Proof.prod_Icc]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with q hq
    exact hq.2
  have h2 : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), q.2 ∉ (S : Set ℝ) ∪ {H} := by
    rw [ae_iff]
    have e : {q : Ω × ℝ | ¬ q.2 ∉ (S : Set ℝ) ∪ {H}} = univ ×ˢ ((S : Set ℝ) ∪ {H}) := by
      ext q; simp only [mem_ofPred_eq, not_not, mem_prod, mem_univ, true_and]
    have h0 : volume.restrict (Icc 0 H) ((S : Set ℝ) ∪ {H}) = 0 :=
      nonpos_iff_eq_zero.1 ((Measure.restrict_le_self (s := Icc 0 H) _).trans
        (le_of_eq ((S.finite_toSet.union (finite_singleton H)).measure_zero volume)))
    rw [e, Measure.prod_prod, h0, mul_zero]
  filter_upwards [h1, h2] with q hq hq'
  simp only [mem_union, Finset.mem_coe, mem_singleton_iff, not_or] at hq'
  exact ⟨hq, hq'⟩

theorem driftS : driftConditionStatement := by
  intro Ω _ μ _ k r d c A hA S H D hC
  have hmain : ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))),
      ∀ T ∈ Icc q.2 H, ax01At c A d S (matched c A d S (D q.2 q.1) q.2) q.2 T := by
    filter_upwards [hC, ae_good (μ := μ) S H] with q ⟨horth, α, β, hR⟩ ⟨hmem, hS, hH⟩
    have huH : q.2 < H := lt_of_le_of_ne hmem.2 hH
    have haff : ∀ x, Rsharp c A d S (D q.2 q.1) q.2 x = α + β * x :=
      Novel.UnifiedSpliceConverseProof.affine_ext
        (fun x => Novel.UnifiedSpliceConverseProof.resid_an _ _ c A d _ _ _ _ x)
        (show (0:ℝ) < H - q.2 by linarith) fun x hx => hR x ⟨hx.1.le, hx.2.le⟩
    exact Novel.SpliceLocalizationConverseProof.explicitS k r d c A hA S H q.2 (D q.2 q.1)
      hmem.1 huH hS horth ⟨α, β, haff⟩
  refine ⟨hmain, fun T _ hTH => ?_⟩
  have hac : μ.prod (volume.restrict (Icc 0 T)) ≪ μ.prod (volume.restrict (Icc 0 H)) := by
    rw [Novel.UnifiedSpliceStep0Proof.prod_Icc, Novel.UnifiedSpliceStep0Proof.prod_Icc]
    exact Measure.absolutelyContinuous_of_le (Measure.restrict_mono
      (prod_mono subset_rfl (Icc_subset_Icc_right hTH)) le_rfl)
  filter_upwards [hac.ae_le hmain, ae_good (μ := μ) S T] with q h hq
  exact h T ⟨hq.1.2, hTH⟩

/-! ### (e) -/

/-- Claim 049's conditions, in product form. -/
lemma cond_prod {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ] {k r d : ℕ}
    {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : IsUnit A.det) (hobs : Observable c A)
    {S : Finset ℝ} {H : ℝ} {D : ℝ → Ω → Pt049 k r} (hD : FieldsMeas D)
    (hax : AX01 μ c A d S H D) :
    ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), Cond c A d S H (D q.2 q.1) q.2 := by
  have hq := Novel.UnifiedSpliceQuantifiersProof.quantS Ω μ k r d c A hA hobs S H D hax
  have h := (Measure.ae_prod_iff_ae_ae (condSet_meas hD c A d S H)).2 hq
  filter_upwards [h] with q ⟨h1, α, β, h2⟩
  exact ⟨h1, α, β, fun x _ => h2 x⟩

theorem matchingS : matchingStatement := by
  intro Ω _ μ _ k r d c A hA hobs S H D hD hax
  have hM := (driftS Ω μ k r d c A hA S H D (cond_prod hA hobs hD hax)).2
  have h1 := Novel.UnifiedSpliceStep0Proof.step0S Ω μ k r d c A hA S H D hax
  have h2 := Novel.UnifiedSpliceStep0Proof.step0S Ω μ k r d c A hA S H
    (fun u ω => matched c A d S (D u ω) u) hM
  filter_upwards [h1, h2] with q e1 e2 T hT hTS
  have hp : ∀ u' T', prim049 S (matched c A d S (D q.2 q.1) q.2) u' T' =
      prim049 S (D q.2 q.1) u' T' := fun _ _ => rfl
  have key : ∀ T' ∈ Ioo q.2 H, T' ∉ S →
      (D q.2 q.1).dL (nS S T') + (D q.2 q.1).dC (nS S T') * T' =
        dL050 c A d S (D q.2 q.1) q.2 (nS S T') + dC050 c A d S (D q.2 q.1) q.2 (nS S T') * T' :=
    fun T' hT' hT'S => by
      have a := e1 T' hT' hT'S
      have b := e2 T' hT' hT'S
      simp only [hp] at b
      simp only [matched] at b
      linarith
  have f1 : ∀ᶠ y in 𝓝 T, y ∈ Ioo q.2 H := isOpen_Ioo.mem_nhds hT
  have f2 : ∀ᶠ y in 𝓝 T, y ∈ (S : Set ℝ)ᶜ :=
    S.finite_toSet.isClosed.isOpen_compl.mem_nhds (show T ∈ (S : Set ℝ)ᶜ from hTS)
  have hev : ∀ᶠ y in 𝓝[≠] T, y ∈ Ioo q.2 H ∧ y ∈ (S : Set ℝ)ᶜ ∧ nS S y = nS S T :=
    (f1.and (f2.and (Novel.UnifiedSpliceStep0Proof.nS_eventually S hTS))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨T', ⟨hT', hT'S, hn⟩, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have k1 := key T hT hTS
  have k2 := key T' hT' hT'S
  rw [hn] at k2
  have hne' : T' - T ≠ 0 := sub_ne_zero.2 hne
  have hC : (D q.2 q.1).dC (nS S T) = dC050 c A d S (D q.2 q.1) q.2 (nS S T) := by
    have : ((D q.2 q.1).dC (nS S T) - dC050 c A d S (D q.2 q.1) q.2 (nS S T)) * (T' - T) = 0 := by
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne')
  refine ⟨?_, hC⟩
  rw [hC] at k1
  linarith

/-! ### (f) -/

theorem theoremS : theoremStatement := by
  intro Ω _ μ _ k r d c A hA hobs S H D hD
  constructor
  · rintro ⟨dL, dC, hax⟩
    exact cond_prod (D := fun u ω => { D u ω with dL := dL u ω, dC := dC u ω }) hA hobs hD hax
  · intro hC
    exact ⟨fun u ω => dL050 c A d S (D u ω) u, fun u ω => dC050 c A d S (D u ω) u,
      (driftS Ω μ k r d c A hA S H D hC).2⟩

end Main

theorem frontEndConstructionMatching : Standalone.FrontEndConstructionMatching.statement :=
  ⟨driftS, matchingS, theoremS⟩

end Novel.FrontEndConstructionMatchingProof

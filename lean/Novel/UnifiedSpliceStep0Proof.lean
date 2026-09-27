import Standalone.UnifiedSpliceStep0
import Novel.UnifiedSpliceConverseProof
import Novel.RecurrentLoadingStatePProof
import Novel.MaturityShapeIdentitiesProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Matrix NormedSpace MeasureTheory Set Filter Topology
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
namespace Novel.UnifiedSpliceStep0Proof

variable {k r : ℕ}

/-! ### The interval index -/

lemma nS_meas (S : Finset ℝ) : Measurable (nS S) := by
  classical
  have e : nS S = fun T => ∑ τ ∈ S, if τ ≤ T then 1 else 0 := by
    funext T; rw [nS, Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun τ _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma nS_eventually (S : Finset ℝ) {T : ℝ} (hT : T ∉ S) : ∀ᶠ y in 𝓝 T, nS S y = nS S T := by
  have : ∀ᶠ y in 𝓝 T, ∀ τ ∈ S, (τ ≤ y ↔ τ ≤ T) := by
    refine (eventually_all_finset S).2 fun τ hτ => ?_
    have hne : T ≠ τ := fun h => hT (h ▸ hτ)
    rcases hne.lt_or_gt with h | h
    · filter_upwards [eventually_lt_nhds h] with y hy using
        iff_of_false (not_le.2 hy) (not_le.2 h)
    · filter_upwards [eventually_gt_nhds h] with y hy using iff_of_true hy.le h.le
  filter_upwards [this] with y hy
  unfold nS
  congr 1
  exact Finset.filter_congr fun τ hτ => hy τ hτ

lemma nat_bdd (g : ℕ → ℝ) (S : Finset ℝ) (v : ℝ) :
    |g (nS S v)| ≤ ∑ i ∈ Finset.range (S.card + 1), |g i| :=
  Finset.single_le_sum (f := fun i => |g i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_filter_le _ _)))

lemma pc_meas (g : ℕ → ℝ) (S : Finset ℝ) : Measurable fun v => g (nS S v) :=
  (measurable_from_nat (f := g)).comp (nS_meas S)

lemma pc_ii (g : ℕ → ℝ) (S : Finset ℝ) (a b : ℝ) :
    IntervalIntegrable (fun v => g (nS S v)) volume a b := by
  rcases le_total a b with h | h
  · exact Novel.MaturityShapeIdentitiesProof.ii_of_bound (pc_meas g S) h fun x _ => nat_bdd g S x
  · exact (Novel.MaturityShapeIdentitiesProof.ii_of_bound (pc_meas g S) h
      fun x _ => nat_bdd g S x).symm

lemma pc_contAt (g : ℕ → ℝ) (S : Finset ℝ) {T : ℝ} (hT : T ∉ S) :
    ContinuousAt (fun v => g (nS S v)) T :=
  continuousAt_const.congr (by filter_upwards [nS_eventually S hT] with y hy; rw [hy])

/-! ### The smooth parts -/

section Smooth
variable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)

lemma sigB_cont (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (l : Fin k) :
    Continuous fun x => sigB Hp Hz c A d x l :=
  continuous_iff_continuousAt.2 fun x =>
    (Novel.UnifiedSpliceConverseProof.sigB_an Hp Hz c A d l x).continuousAt

lemma driftB_cont (p : Pt049 k r) : Continuous (driftB049 c A d p) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h := fun i => Novel.UnifiedSpliceConverseProof.ephi_an c A i x
  have : AnalyticAt ℝ (fun x => driftB049 c A d p x) x := by
    unfold driftB049
    simp only [dotProduct]
    fun_prop
  exact this.continuousAt

/-- `Φ_ζ' = φ_ζ`. -/
lemma ePhi_deriv (hA : IsUnit A.det) (x : ℝ) (i : Fin r) :
    HasDerivAt (fun x => ePhi c A x i) (ephi c A x i) x := by
  have e : (fun y => ePhi c A y i) = fun y => ((c ᵥ* A⁻¹) ᵥ* exp (y • A)) i - (c ᵥ* A⁻¹) i := by
    funext y
    simp only [ePhi, mul_sub, mul_one, vecMul_sub, vecMul_vecMul, Pi.sub_apply]
  rw [e]
  have h : HasDerivAt (fun y => ((c ᵥ* A⁻¹) ᵥ* exp (y • A)) i)
      (∑ j, (c ᵥ* A⁻¹) j * (A * exp (x • A)) j i) x := by
    simp only [vecMul, dotProduct]
    exact HasDerivAt.fun_sum fun j _ =>
      (Novel.RecurrentLoadingStatePProof.exp_entry_hasDerivAt A j i x).const_mul _
  convert h.sub_const ((c ᵥ* A⁻¹) i) using 1
  have : (∑ j, (c ᵥ* A⁻¹) j * (A * exp (x • A)) j i) = ((c ᵥ* A⁻¹) ᵥ* (A * exp (x • A))) i := rfl
  rw [this, vecMul_vecMul, ← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul]
  rfl

/-- `Σ^B' = σ^B`. -/
lemma SigB_deriv (hA : IsUnit A.det) (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ)
    (x : ℝ) (l : Fin k) :
    HasDerivAt (fun x => SigB Hp Hz c A d x l) (sigB Hp Hz c A d x l) x := by
  simp only [SigB, sigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct]
  refine HasDerivAt.add (HasDerivAt.fun_sum fun μ _ => ?_) (HasDerivAt.fun_sum fun i _ => ?_)
  · have := ((hasDerivAt_pow (μ + 1) x).div_const ((μ:ℝ) + 1)).mul_const (Hp μ l)
    convert this using 1
    push_cast
    field_simp
  · exact (ePhi_deriv c A hA x i).mul_const _

lemma int_sigB (hA : IsUnit A.det) (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ)
    (u T : ℝ) (l : Fin k) :
    ∫ v in u..T, sigB Hp Hz c A d (v - u) l = SigB Hp Hz c A d (T - u) l := by
  have hd : ∀ v, HasDerivAt (fun v => SigB Hp Hz c A d (v - u) l) (sigB Hp Hz c A d (v - u) l) v :=
    fun v => by
      exact (SigB_deriv c A d hA Hp Hz (v - u) l).comp_sub_const v u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (((sigB_cont c A d Hp Hz l).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
  simp [SigB, ePhi]

end Smooth

/-! ### The drift and volatility in the maturity -/

section Coeff
variable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (p : Pt049 k r)
  (u : ℝ)

lemma alpha_eq : alpha049 c A d S p u = fun v => p.dL (nS S v) + p.dC (nS S v) * v +
    driftB049 c A d p (v - u) := rfl

lemma alpha_meas : Measurable (alpha049 c A d S p u) := by
  rw [alpha_eq]
  exact ((pc_meas p.dL S).add ((pc_meas p.dC S).mul measurable_id)).add
    ((driftB_cont c A d p).measurable.comp (measurable_id.sub_const u))

lemma alpha_ii (a b : ℝ) : IntervalIntegrable (alpha049 c A d S p u) volume a b := by
  rw [alpha_eq]
  exact ((pc_ii p.dL S a b).add ((pc_ii p.dC S a b).mul_continuousOn continuousOn_id)).add
    (((driftB_cont c A d p).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)

lemma alpha_contAt {T : ℝ} (hT : T ∉ S) : ContinuousAt (alpha049 c A d S p u) T := by
  rw [alpha_eq]
  exact ((pc_contAt p.dL S hT).add ((pc_contAt p.dC S hT).mul continuousAt_id)).add
    ((driftB_cont c A d p).comp (continuous_id.sub continuous_const)).continuousAt

lemma sig_eq (l : Fin k) : (fun v => sig049 c A d S p u v l) =
    fun v => p.V (nS S v) l + sigB p.Hp p.Hz c A d (v - u) l := rfl

lemma sig_meas (l : Fin k) : Measurable fun v => sig049 c A d S p u v l := by
  rw [sig_eq]
  exact (pc_meas (fun n => p.V n l) S).add
    ((sigB_cont c A d p.Hp p.Hz l).measurable.comp (measurable_id.sub_const u))

lemma sig_ii (l : Fin k) (a b : ℝ) :
    IntervalIntegrable (fun v => sig049 c A d S p u v l) volume a b := by
  rw [sig_eq]
  exact (pc_ii (fun n => p.V n l) S a b).add
    (((sigB_cont c A d p.Hp p.Hz l).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)

lemma sig_contAt (l : Fin k) {T : ℝ} (hT : T ∉ S) :
    ContinuousAt (fun v => sig049 c A d S p u v l) T := by
  rw [sig_eq]
  exact (pc_contAt (fun n => p.V n l) S hT).add
    ((sigB_cont c A d p.Hp p.Hz l).comp (continuous_id.sub continuous_const)).continuousAt

/-- `∫_u^T σ = P(u, T) + Σ^B(T − u)`. -/
lemma int_sig (hA : IsUnit A.det) (T : ℝ) (l : Fin k) :
    ∫ v in u..T, sig049 c A d S p u v l = prim049 S p u T l + SigB p.Hp p.Hz c A d (T - u) l := by
  have hc : IntervalIntegrable (fun v => sigB p.Hp p.Hz c A d (v - u) l) volume u T :=
    ((sigB_cont c A d p.Hp p.Hz l).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [sig_eq, intervalIntegral.integral_add (pc_ii (fun n => p.V n l) S u T) hc,
    int_sigB c A d hA]
  rfl

end Coeff

/-! ### AX-01 at every maturity, then differentiated -/

section Measure
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

/-- `Q ⊗ dt` on `Ω × [0, T]` as a restriction of `Q ⊗ dt`. -/
lemma prod_Icc (T : ℝ) :
    μ.prod (volume.restrict (Icc 0 T)) = (μ.prod volume).restrict (univ ×ˢ Icc 0 T) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

lemma rat_closure {u H : ℝ} (h : u < H) :
    Icc u H ⊆ closure (Ioo u H ∩ range ((↑) : ℚ → ℝ)) := by
  have h1 := Rat.denseRange_cast.open_subset_closure_inter (isOpen_Ioo (a := u) (b := H))
  rw [← closure_Ioo h.ne]
  exact closure_minimal h1 isClosed_closure

end Measure

/-! ### Step 0 -/

theorem step0S : step0Statement := by
  intro Ω _ μ _ k r d c A hA S H D hax
  set M := μ.prod (volume : Measure ℝ)
  have hs : MeasurableSet ((univ : Set Ω) ×ˢ Icc (0:ℝ) H) := MeasurableSet.univ.prod measurableSet_Icc
  -- AX-01 at every rational maturity, off one null set
  have hρ : ∀ ρ : ℚ, ∀ᵐ q ∂M, q ∈ (univ : Set Ω) ×ˢ Icc (0:ℝ) H → 0 < (ρ:ℝ) → (ρ:ℝ) ≤ H → q.2 ≤ ρ →
      ax01At c A d S (D q.2 q.1) q.2 ρ := fun ρ => by
    by_cases h : 0 < (ρ:ℝ) ∧ (ρ:ℝ) ≤ H
    · have := hax ρ h.1 h.2
      rw [prod_Icc, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)] at this
      filter_upwards [this] with q hq hmem _ _ hle
      exact hq ⟨mem_univ _, hmem.2.1, hle⟩
    · exact Filter.Eventually.of_forall fun q _ h1 h2 => absurd ⟨h1, h2⟩ h
  rw [prod_Icc, ae_restrict_iff' hs]
  filter_upwards [ae_all_iff.2 hρ] with q hq hmem T hT hTS
  set u := q.2
  set p := D q.2 q.1
  have huH : u < H := hT.1.trans hT.2
  -- every maturity in `[u, H]`, by continuity
  set f : Fin k → ℝ → ℝ := fun l T => ∫ v in u..T, sig049 c A d S p u v l
  set F : ℝ → ℝ := fun T => ∫ v in u..T, alpha049 c A d S p u v
  set G : ℝ → ℝ := fun T => (1 / 2 : ℝ) * ∑ l, f l T * f l T
  have hfc : ∀ l, ContinuousOn (f l) (Icc u H) := fun l => by
    have := intervalIntegral.continuousOn_primitive_interval' (sig_ii c A d S p u l u H)
      left_mem_uIcc
    rwa [uIcc_of_le huH.le] at this
  have hFG : EqOn F G (Icc u H) := by
    refine EqOn.of_subset_closure (s := Ioo u H ∩ range ((↑) : ℚ → ℝ)) ?_ ?_ ?_
      (inter_subset_left.trans Ioo_subset_Icc_self) (rat_closure huH)
    · rintro x ⟨hx, ρ, rfl⟩
      have := hq ρ hmem (by linarith [hx.1, hmem.2.1]) hx.2.le hx.1.le
      simpa only [ax01At, dotProduct] using this
    · have := intervalIntegral.continuousOn_primitive_interval' (alpha_ii c A d S p u u H)
        left_mem_uIcc
      rwa [uIcc_of_le huH.le] at this
    · exact continuousOn_const.mul (continuousOn_finsetSum _ fun l _ => (hfc l).mul (hfc l))
  -- differentiate at `T`
  have hF : HasDerivAt F (alpha049 c A d S p u T) T :=
    intervalIntegral.integral_hasDerivAt_right (alpha_ii c A d S p u u T)
      (alpha_meas c A d S p u).aestronglyMeasurable.stronglyMeasurableAtFilter
      (alpha_contAt c A d S p u hTS)
  have hf : ∀ l, HasDerivAt (f l) (sig049 c A d S p u T l) T := fun l =>
    intervalIntegral.integral_hasDerivAt_right (sig_ii c A d S p u l u T)
      (sig_meas c A d S p u l).aestronglyMeasurable.stronglyMeasurableAtFilter
      (sig_contAt c A d S p u l hTS)
  have hG : HasDerivAt G (∑ l, f l T * sig049 c A d S p u T l) T := by
    have := (HasDerivAt.fun_sum (u := Finset.univ) fun l _ => (hf l).mul (hf l)).const_mul (1 / 2 : ℝ)
    convert this using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hev : F =ᶠ[𝓝 T] G := by
    filter_upwards [isOpen_Ioo.mem_nhds hT] with y hy using hFG (Ioo_subset_Icc_self hy)
  have heq : alpha049 c A d S p u T = ∑ l, f l T * sig049 c A d S p u T l :=
    hF.unique (hG.congr_of_eventuallyEq hev)
  -- the algebra
  have hint : ∀ l, f l T = prim049 S p u T l + SigB p.Hp p.Hz c A d (T - u) l := fun l =>
    int_sig c A d S p u hA T l
  simp only [hint] at heq
  have hres : resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z (T - u) = driftB049 c A d p (T - u) -
      sigB p.Hp p.Hz c A d (T - u) ⬝ᵥ SigB p.Hp p.Hz c A d (T - u) := rfl
  set P := prim049 S p u T
  set Sg := SigB p.Hp p.Hz c A d (T - u)
  set sg := sigB p.Hp p.Hz c A d (T - u)
  set Vm := p.V (nS S T)
  have hexp : ∑ l, (P l + Sg l) * sig049 c A d S p u T l =
      Vm ⬝ᵥ P + Vm ⬝ᵥ Sg + sg ⬝ᵥ P + sg ⬝ᵥ Sg := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by simp only [sig049, Pi.add_apply]; ring
  rw [hres]
  simp only [alpha049] at heq
  linear_combination heq + hexp

theorem unifiedSpliceStep0 : Standalone.UnifiedSpliceStep0.statement := step0S

end Novel.UnifiedSpliceStep0Proof

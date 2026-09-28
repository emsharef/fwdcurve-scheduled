import Standalone.FrontEndConstructionProcess
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Novel.SpliceLocalizationConverseProof
import Novel.FrontEndConstructionMatchingProof

/-! # Claim 055 (a)–(b): the matching drifts at process level, and the front-end processes (proof)

* `driverForm_pred`: under the calculus, every coordinate of a driver-form process with (U4) rows
  and (U6) drifts is predictable (Red's note 1). Stack it with `W = driverForm(0; noise 1 on one
  driver; drift 0)` and apply AX-05 (`ito_formula`) to `f(t, (w, y)) = y_j w`. Its first conjunct
  says that `∂_w f · 1 = y_j` along the process is (U4), in particular predictable.
* `driverForm_cont`: almost surely every path is continuous. The integrals are (AX-03), and the
  time integral is a primitive of a locally integrable function.
* (a): `dL050` and `dC050` are Borel in `(u, D)` (`dL_meas`, `dC_meas`), and every field of `D` is
  progressive, so `ℓ_m`, `c_m` are progressive. Their integrability on `[0, H]` is Claim 050(c)
  (`integrabilityS`), path by path on the almost sure event where the rows are square integrable,
  the drifts integrable, and the state continuous.
* (b): `L_m`, `C_m` are driver-form processes with (U4) noises and the (U6) drifts of (a).

Reused, not reproved: `Novel.SpliceLocalizationConverseProof.integrabilityS`,
`Novel.FrontEndConstructionMatchingProof.resid_meas`, `sharp_meas`,
`Novel.UnifiedSpliceStep0Proof.nS_meas`, `Novel.ZeroMeanReversionUpstreamBridgeProof.dX_general`,
`zero_integral`, and the calculus fields `ito_formula`, `int_continuous`.
-/

open MeasureTheory Set Filter Matrix Topology
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge (ItoCalculus U4 LocallyIntegrableDrift driverForm dX)
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse Standalone.FrontEndConstructionProcess

namespace Novel.FrontEndConstructionProcessProof

/-! ### Driver-form processes -/

section Calc
variable {Ω : Type} [MeasurableSpace Ω] (IC : ItoCalculus Ω)

lemma U4_const (a : ℝ) : U4 IC.ℱ IC.μ (fun _ _ => a) :=
  ⟨stronglyMeasurable_const, fun t => Eventually.of_forall fun ω => by
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)⟩

lemma lid_zero : LocallyIntegrableDrift IC.ℱ IC.μ (fun _ _ => (0 : ℝ)) :=
  ⟨isStronglyProgressive_const _ _, fun _ => Eventually.of_forall fun _ => by simp⟩

/-- Red's note 1: a driver-form process is predictable, by AX-05's first conjunct. -/
lemma driverForm_pred (hm : 0 < IC.m) {n : ℕ} (x : Fin n → ℝ)
    (H : Fin n → Fin IC.m → ℝ≥0 → Ω → ℝ) (K : Fin n → ℝ≥0 → Ω → ℝ)
    (hH : ∀ i k, U4 IC.ℱ IC.μ (H i k)) (hK : ∀ i, LocallyIntegrableDrift IC.ℱ IC.μ (K i))
    (j : Fin n) : IsStronglyPredictable IC.ℱ (fun t ω => driverForm IC.I x H K t ω j) := by
  classical
  let k₀ : Fin IC.m := ⟨0, hm⟩
  let x' : Fin (n + 1) → ℝ := Fin.cons 0 x
  let H' : Fin (n + 1) → Fin IC.m → ℝ≥0 → Ω → ℝ :=
    Fin.cons (fun k _ _ => if k = k₀ then 1 else 0) H
  let K' : Fin (n + 1) → ℝ≥0 → Ω → ℝ := Fin.cons (fun _ _ => 0) K
  let f : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun p => p.2 j.succ * p.2 0
  have hf : ContDiff ℝ 2 f :=
    ((contDiff_apply ℝ ℝ j.succ).comp contDiff_snd).mul ((contDiff_apply ℝ ℝ 0).comp contDiff_snd)
  have hH' : ∀ i k, U4 IC.ℱ IC.μ (H' i k) := fun i k => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact U4_const IC _
    · simpa [H'] using hH i k
  have hK' : ∀ i, LocallyIntegrableDrift IC.ℱ IC.μ (K' i) := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact lid_zero IC
    · simpa [K'] using hK i
  have hdX : ∀ (s : ℝ) (y : Fin (n + 1) → ℝ), dX f (s, y) 0 = y j.succ := fun s y => by
    rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dX_general f hf s y 0]
    have e : (fun u => f (s, Function.update y 0 u)) = fun u => y j.succ * u := by
      funext u
      simp [f]
    rw [e]
    simp
  have h := ((IC.ito_formula (n + 1) x' H' K' f hH' hK' hf).1 0 k₀).1
  have e : (fun (s : ℝ≥0) ω => dX f ((s : ℝ), driverForm IC.I x' H' K' s ω) 0 * H' 0 k₀ s ω) =
      fun t ω => driverForm IC.I x H K t ω j := by
    funext s ω
    rw [hdX]
    simp [H', x', K', driverForm]
  rwa [e] at h

/-- Every time section of a progressive process is measurable. -/
lemma prog_path_meas {K : ℝ≥0 → Ω → ℝ} (hK : IsStronglyProgressive IC.ℱ K) (ω : Ω) :
    Measurable fun s : ℝ => K s.toNNReal ω := by
  have hN : ∀ N : ℕ, Measurable fun s : ℝ => K (min s (N : ℝ)).toNNReal ω := fun N => by
    have h1 : Measurable[Subtype.instMeasurableSpace.prod (IC.ℱ (N : ℝ≥0))]
        fun p : Set.Iic (N : ℝ≥0) × Ω => K p.1 p.2 := (hK (N : ℝ≥0)).measurable
    have h2 : Measurable fun q : Set.Iic (N : ℝ≥0) => K q ω :=
      h1.comp (@measurable_prodMk_right _ _ _ (IC.ℱ (N : ℝ≥0)) ω)
    have h3 : Measurable fun s : ℝ => (⟨(min s (N : ℝ)).toNNReal, by
        simp only [Set.mem_Iic]
        exact Real.toNNReal_le_iff_le_coe.2 (by simp)⟩ : Set.Iic (N : ℝ≥0)) :=
      (measurable_real_toNNReal.comp (measurable_id.min measurable_const)).subtype_mk
    exact h2.comp h3
  refine measurable_of_tendsto_metrizable hN (tendsto_pi_nhds.2 fun s => ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈s⌉₊) fun N hN => ?_
  rw [min_eq_left ((Nat.le_ceil s).trans (by exact_mod_cast hN))]

/-- Almost surely, every path of a driver-form process is continuous. -/
lemma driverForm_cont {n : ℕ} (x : Fin n → ℝ) (H : Fin n → Fin IC.m → ℝ≥0 → Ω → ℝ)
    (K : Fin n → ℝ≥0 → Ω → ℝ) (hH : ∀ i k, U4 IC.ℱ IC.μ (H i k))
    (hK : ∀ i, LocallyIntegrableDrift IC.ℱ IC.μ (K i)) :
    ∀ᵐ ω ∂IC.μ, ∀ j, Continuous fun t => driverForm IC.I x H K t ω j := by
  have hI : ∀ᵐ ω ∂IC.μ, ∀ j k, Continuous fun t => IC.I k (H j k) t ω :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => IC.int_continuous k _ (hH j k)
  have hL : ∀ᵐ ω ∂IC.μ, ∀ j (N : ℕ),
      ∫⁻ s in Set.Icc (0 : ℝ) (N : ℝ≥0), ENNReal.ofReal |K j s.toNNReal ω| < ⊤ :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun N => (hK j).2 N
  filter_upwards [hI, hL] with ω hI hL j
  set g : ℝ → ℝ := fun s => K j s.toNNReal ω
  have hg : Measurable g := prog_path_meas IC (hK j).1 ω
  have hon : ∀ N : ℕ, IntegrableOn g (Icc (-(N : ℝ)) N) := fun N => by
    have hpos : IntegrableOn g (Icc 0 (N : ℝ)) := by
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      have := hL j N
      simp only [NNReal.coe_natCast] at this
      simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using this
    have hneg : IntegrableOn g (Icc (-(N : ℝ)) 0) := by
      have e : EqOn g (fun _ => K j 0 ω) (Icc (-(N : ℝ)) 0) := fun s hs => by
        simp [g, Real.toNNReal_of_nonpos hs.2]
      exact (integrableOn_congr_fun e measurableSet_Icc).2 (integrableOn_const (by simp))
    rw [← Icc_union_Icc_eq_Icc (neg_nonpos.2 (Nat.cast_nonneg N)) (Nat.cast_nonneg N)]
    exact hneg.union hpos
  have hii : ∀ a b, IntervalIntegrable g volume a b := fun a b => by
    obtain ⟨N, hN⟩ := exists_nat_ge (max |a| |b|)
    refine (hon N).mono_set ?_ |>.intervalIntegrable
    intro s hs
    rw [mem_uIcc] at hs
    constructor <;> rcases hs with hs | hs <;>
      linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b, le_max_left |a| |b|,
        le_max_right |a| |b|, hs.1, hs.2]
  exact ((continuous_const.add (continuous_finsetSum _ fun k _ => hI j k)).add
    ((intervalIntegral.continuous_primitive hii 0).comp NNReal.continuous_coe))

end Calc

/-! ### (a): progressive measurability -/

section Meas
variable {α : Type*} {mα : MeasurableSpace α} {k r : ℕ}

lemma Vidx_meas {p : α → Pt049 k r} (hV : ∀ m l, Measurable[mα] fun a => (p a).V m l)
    {n : α → ℕ} (hn : Measurable[mα] n) (l : Fin k) : Measurable[mα] fun a => (p a).V (n a) l := by
  let _ := mα
  have h : Measurable fun q : α × ℕ => (p q.1).V q.2 l :=
    measurable_from_prod_countable_left fun n => hV n l
  exact h.comp (measurable_id.prodMk hn)

lemma kap_meas (S : Finset ℝ) {p : α → Pt049 k r} {u : α → ℝ}
    (hV : ∀ m l, Measurable[mα] fun a => (p a).V m l) (hu : Measurable[mα] u) (m : ℕ)
    (l : Fin k) : Measurable[mα] fun a => kap050 S (p a) (u a) m l := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hu
  simp only [kap050, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ite_apply,
    Pi.zero_apply]
  refine ((hu.neg).mul (Vidx_meas hV hn l)).sub (Finset.measurable_sum _ fun τ _ => ?_)
  exact Measurable.ite ((measurableSet_lt hu measurable_const).inter (MeasurableSet.const _))
    (measurable_const.mul ((hV _ l).sub (hV _ l))) measurable_const

variable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
  {p : α → Pt049 k r} {u : α → ℝ} (hHp : ∀ μ l, Measurable[mα] fun a => (p a).Hp μ l)
  (hHz : ∀ i l, Measurable[mα] fun a => (p a).Hz i l) (hbP : ∀ μ, Measurable[mα] fun a => (p a).bP μ)
  (hzP : ∀ μ, Measurable[mα] fun a => (p a).zP μ) (hbZ : ∀ i, Measurable[mα] fun a => (p a).bZ i)
  (hz : ∀ i, Measurable[mα] fun a => (p a).z i) (hV : ∀ m l, Measurable[mα] fun a => (p a).V m l)
  (hu : Measurable[mα] u)
include hHp hHz hbP hzP hbZ hz hV hu

lemma Rs_meas (x : ℝ) : Measurable[mα] fun a => Rsharp c A d S (p a) (u a) x := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hu
  exact Novel.FrontEndConstructionMatchingProof.resid_meas c A d
    (Novel.FrontEndConstructionMatchingProof.sharp_meas hHp (Vidx_meas hV hn)) hHz hbP hzP hbZ hz x

lemma dL_meas (m : ℕ) : Measurable[mα] fun a => dL050 c A d S (p a) (u a) m := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hu
  have hVc := Vidx_meas hV hn
  have hk := kap_meas S hV hu m
  have hR := Rs_meas c A d S hHp hHz hbP hzP hbZ hz hV hu
  have hVm := hV m
  have hH0 := hHp 0
  simp only [dL050, alpha050, beta050, dotProduct]
  fun_prop

lemma dC_meas (m : ℕ) : Measurable[mα] fun a => dC050 c A d S (p a) (u a) m := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hu
  have hVc := Vidx_meas hV hn
  have hR := Rs_meas c A d S hHp hHz hbP hzP hbZ hz hV hu
  have hVm := hV m
  have hH0 := hHp 0
  simp only [dC050, beta050, dotProduct]
  fun_prop

end Meas

/-! ### (a) and (b) -/

section Proc
variable {Ω : Type} [MeasurableSpace Ω] (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
  (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
  (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ)

lemma prog_coe {P : ℝ≥0 → Ω → ℝ} (hP : IsStronglyProgressive IC.ℱ P)
    (i : ℝ≥0) : Measurable[Subtype.instMeasurableSpace.prod (IC.ℱ i)]
      fun a : Set.Iic i × Ω => P ((a.1 : ℝ≥0) : ℝ).toNNReal a.2 := by
  simpa only [Real.toNNReal_coe] using (hP i).measurable

variable {IC c A S H x₀ HB KB V}

/-- The fields of `D` along `Iic i × Ω` are measurable for `σ(Iic i) ⊗ F_i`. -/
lemma pt_fields (hSet : Setting IC HB KB V) (i : ℝ≥0) :
    let mα := Subtype.instMeasurableSpace.prod (IC.ℱ i)
    let p := fun a : Set.Iic i × Ω => pt IC x₀ HB KB V ((a.1 : ℝ≥0) : ℝ) a.2
    (∀ μ l, Measurable[mα] fun a => (p a).Hp μ l) ∧ (∀ i l, Measurable[mα] fun a => (p a).Hz i l) ∧
    (∀ μ, Measurable[mα] fun a => (p a).bP μ) ∧ (∀ μ, Measurable[mα] fun a => (p a).zP μ) ∧
    (∀ i, Measurable[mα] fun a => (p a).bZ i) ∧ (∀ i, Measurable[mα] fun a => (p a).z i) ∧
    (∀ m l, Measurable[mα] fun a => (p a).V m l) ∧
    Measurable[mα] fun a : Set.Iic i × Ω => ((a.1 : ℝ≥0) : ℝ) := by
  intro mα p
  obtain ⟨hm, hHB, hKB, hV⟩ := hSet
  have hZ : ∀ j, IsStronglyProgressive IC.ℱ fun t ω => driverForm IC.I x₀ HB KB t ω j := fun j =>
    (driverForm_pred IC hm x₀ HB KB hHB hKB j).isStronglyProgressive
  have P : ∀ {Q : ℝ≥0 → Ω → ℝ}, IsStronglyProgressive IC.ℱ Q →
      Measurable[mα] fun a : Set.Iic i × Ω => Q ((a.1 : ℝ≥0) : ℝ).toNNReal a.2 :=
    fun hQ => prog_coe IC hQ i
  refine ⟨fun μ l => ?_, fun j l => ?_, fun μ => ?_, fun μ => ?_, fun j => ?_, fun j => ?_,
    fun m l => ?_, ?_⟩
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hHB _ l).1.isStronglyProgressive
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · simp only [p, pt, Matrix.of_apply]; exact P (hHB _ l).1.isStronglyProgressive
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hKB _).1
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hZ _)
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · exact P (hKB _).1
  · exact P (hZ _)
  · exact P (hV m l).1.isStronglyProgressive
  · exact measurable_coe_nnreal_real.comp
      (measurable_subtype_coe.comp (@measurable_fst _ _ _ (IC.ℱ i)))

lemma ell_prog (hSet : Setting IC HB KB V) (m : ℕ) :
    IsStronglyProgressive IC.ℱ (ell IC c A S H x₀ HB KB V m) := fun i => by
  obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, hV, hu⟩ := pt_fields (x₀ := x₀) hSet i
  let _ : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (IC.ℱ i)
  exact (Measurable.ite (measurableSet_le hu measurable_const)
    (dL_meas c A d S hHp hHz hbP hzP hbZ hz hV hu m) measurable_const).stronglyMeasurable

lemma cee_prog (hSet : Setting IC HB KB V) (m : ℕ) :
    IsStronglyProgressive IC.ℱ (cee IC c A S H x₀ HB KB V m) := fun i => by
  obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, hV, hu⟩ := pt_fields (x₀ := x₀) hSet i
  let _ : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (IC.ℱ i)
  exact (Measurable.ite (measurableSet_le hu measurable_const)
    (dC_meas c A d S hHp hHz hbP hzP hbZ hz hV hu m) measurable_const).stronglyMeasurable

omit [MeasurableSpace Ω] in
lemma memLp_of {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ}
    (h : ∫⁻ s in Icc (0 : ℝ) (T.toNNReal : ℝ), ENNReal.ofReal (g s ^ 2) < ⊤) :
    MemLp g 2 (volume.restrict (Icc 0 T)) := by
  refine (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
    ⟨(hg.pow_const 2).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_of_nonneg (sq_nonneg _)]
  exact (lintegral_mono_set (Icc_subset_Icc le_rfl (Real.le_coe_toNNReal T))).trans_lt h

omit [MeasurableSpace Ω] in
lemma integrable_of {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ}
    (h : ∫⁻ s in Icc (0 : ℝ) (T.toNNReal : ℝ), ENNReal.ofReal |g s| < ⊤) :
    Integrable g (volume.restrict (Icc 0 T)) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]
  exact (lintegral_mono_set (Icc_subset_Icc le_rfl (Real.le_coe_toNNReal T))).trans_lt h

/-- The hypotheses of Claim 050(c) hold path by path, almost surely. -/
lemma path_hyps (hSet : Setting IC HB KB V) : ∀ᵐ ω ∂IC.μ,
    let D := fun u => pt IC x₀ HB KB V u ω
    (∀ m ≤ S.card, ∀ l, MemLp (fun u => (D u).V m l) 2 (volume.restrict (Icc 0 H))) ∧
    (∀ μ ≤ d, ∀ l, MemLp (fun u => (D u).Hp μ l) 2 (volume.restrict (Icc 0 H))) ∧
    (∀ i l, MemLp (fun u => (D u).Hz i l) 2 (volume.restrict (Icc 0 H))) ∧
    (∀ μ ≤ d, Integrable (fun u => (D u).bP μ) (volume.restrict (Icc 0 H))) ∧
    (∀ i, Integrable (fun u => (D u).bZ i) (volume.restrict (Icc 0 H))) ∧
    (∀ μ ≤ d, Integrable (fun u => (D u).zP μ) (volume.restrict (Icc 0 H))) ∧
    (∀ i, Integrable (fun u => (D u).z i) (volume.restrict (Icc 0 H))) := by
  obtain ⟨hm, hHB, hKB, hV⟩ := id hSet
  have E1 : ∀ᵐ ω ∂IC.μ, ∀ m l, ∫⁻ s in Icc (0 : ℝ) (H.toNNReal : ℝ),
      ENNReal.ofReal (V m l s.toNNReal ω ^ 2) < ⊤ :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun l => (hV m l).2 H.toNNReal
  have E2 : ∀ᵐ ω ∂IC.μ, ∀ j l, ∫⁻ s in Icc (0 : ℝ) (H.toNNReal : ℝ),
      ENNReal.ofReal (HB j l s.toNNReal ω ^ 2) < ⊤ :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l => (hHB j l).2 H.toNNReal
  have E3 : ∀ᵐ ω ∂IC.μ, ∀ j, ∫⁻ s in Icc (0 : ℝ) (H.toNNReal : ℝ),
      ENNReal.ofReal |KB j s.toNNReal ω| < ⊤ :=
    ae_all_iff.2 fun j => (hKB j).2 H.toNNReal
  filter_upwards [E1, E2, E3, driverForm_cont IC x₀ HB KB hHB hKB] with ω e1 e2 e3 e4
  have mV : ∀ m l, Measurable fun s : ℝ => V m l s.toNNReal ω := fun m l =>
    prog_path_meas IC (hV m l).1.isStronglyProgressive ω
  have mH : ∀ j l, Measurable fun s : ℝ => HB j l s.toNNReal ω := fun j l =>
    prog_path_meas IC (hHB j l).1.isStronglyProgressive ω
  have mK : ∀ j, Measurable fun s : ℝ => KB j s.toNNReal ω := fun j => prog_path_meas IC (hKB j).1 ω
  have cZ : ∀ j, Continuous fun s : ℝ => driverForm IC.I x₀ HB KB s.toNNReal ω j := fun j =>
    (e4 j).comp continuous_real_toNNReal
  refine ⟨fun m _ l => memLp_of (mV m l) (e1 m l), fun μ hμ l => ?_,
    fun i l => memLp_of (mH _ l) (e2 _ l), fun μ hμ => ?_, fun i => integrable_of (mK _) (e3 _),
    fun μ hμ => ?_, fun i => by exact (cZ _).integrableOn_Icc⟩
  · have h : μ < d + 1 := Nat.lt_succ_of_le hμ
    simp only [pt, h, ↓reduceDIte]
    exact memLp_of (mH _ l) (e2 _ l)
  · have h : μ < d + 1 := Nat.lt_succ_of_le hμ
    simp only [pt, h, ↓reduceDIte]
    exact integrable_of (mK _) (e3 _)
  · have h : μ < d + 1 := Nat.lt_succ_of_le hμ
    simp only [pt, h, ↓reduceDIte]
    exact (cZ _).integrableOn_Icc

/-- Claim 050(c), path by path. -/
lemma drift_int (hSet : Setting IC HB KB V) {m : ℕ} (hmS : m ≤ S.card) :
    ∀ᵐ ω ∂IC.μ,
      Integrable (fun u => dL050 c A d S (pt IC x₀ HB KB V u ω) u m) (volume.restrict (Icc 0 H)) ∧
      Integrable (fun u => dC050 c A d S (pt IC x₀ HB KB V u ω) u m) (volume.restrict (Icc 0 H)) := by
  filter_upwards [path_hyps (S := S) (H := H) (x₀ := x₀) hSet] with ω ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact Novel.SpliceLocalizationConverseProof.integrabilityS IC.m r d c A S H
    (fun u => pt IC x₀ HB KB V u ω) h1 h2 h3 h4 h5 h6 h7 m hmS

/-- The truncation to `[0, H]` of a path integrable there has finite integral on every `[0, t]`. -/
lemma trunc_lintegral {g : ℝ → ℝ} (hg : Integrable g (volume.restrict (Icc 0 H))) (F : ℝ → ℝ)
    (hF : ∀ s, 0 ≤ s → F s = if s ≤ H then g s else 0) (t : ℝ) :
    ∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal |F s| < ⊤ := by
  have hpt : ∀ s ∈ Icc (0 : ℝ) t,
      ENNReal.ofReal |F s| ≤ (Icc 0 H).indicator (fun s => ENNReal.ofReal |g s|) s := by
    intro s hs
    rw [hF s hs.1]
    split_ifs with h
    · rw [indicator_of_mem (show s ∈ Icc (0 : ℝ) H from ⟨hs.1, h⟩)]
    · simp
  refine ((setLIntegral_mono' measurableSet_Icc hpt).trans
    ((setLIntegral_le_lintegral _ _).trans_eq (lintegral_indicator measurableSet_Icc _))).trans_lt ?_
  simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hg.2

end Proc

theorem driftS : driftStatement := by
  intro Ω _ IC d r c A S H x₀ HB KB V hSet m hmS
  have hi := drift_int (c := c) (A := A) (H := H) (x₀ := x₀) hSet hmS
  refine ⟨⟨ell_prog hSet m, fun t => ?_⟩, ⟨cee_prog hSet m, fun t => ?_⟩⟩
  · filter_upwards [hi] with ω hω
    exact trunc_lintegral hω.1 _ (fun s hs => by simp [ell, Real.coe_toNNReal _ hs]) t
  · filter_upwards [hi] with ω hω
    exact trunc_lintegral hω.2 _ (fun s hs => by simp [cee, Real.coe_toNNReal _ hs]) t

theorem processS : processStatement := by
  intro Ω _ IC d r c A S H x₀ HB KB V hSet m hmS l₀ c₀
  obtain ⟨hm, -, -, hV⟩ := id hSet
  obtain ⟨hL, hC⟩ := driftS Ω IC d r c A S H x₀ HB KB V hSet m hmS
  have hLH : ∀ (i : Fin 1) k, U4 IC.ℱ IC.μ ((fun _ => V m) i k) := fun _ k => hV m k
  have hCH : ∀ (i : Fin 1) (k : Fin IC.m), U4 IC.ℱ IC.μ
      ((fun (_ : Fin 1) (_ : Fin IC.m) (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) i k) :=
    fun _ _ => U4_const IC 0
  refine ⟨driverForm_pred IC hm _ _ _ hLH (fun _ => hL) 0,
    driverForm_pred IC hm _ _ _ hCH (fun _ => hC) 0, ?_, ?_, ?_⟩
  · filter_upwards [driverForm_cont IC _ _ _ hLH (fun _ => hL)] with ω hω
    exact hω 0
  · filter_upwards [driverForm_cont IC _ _ _ hCH (fun _ => hC)] with ω hω
    exact hω 0
  · filter_upwards [ae_all_iff.2 fun k => Novel.ZeroMeanReversionUpstreamBridgeProof.zero_integral IC k]
      with ω hω t
    simp [Cproc, driverForm, hω]

theorem frontEndConstructionProcess : Standalone.FrontEndConstructionProcess.statement := ⟨driftS, processS⟩

end Novel.FrontEndConstructionProcessProof

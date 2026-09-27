import Standalone.DiffusionMeetingConsistency
import Novel.DiffusionMeetingPricingProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.CompoundedFuturesIdentification Standalone.DiffusionMeetingIdentities
open Standalone.DiffusionMeetingGauss Standalone.DiffusionMeetingPricing
open Standalone.DiffusionMeetingConsistency
open Novel.DiffusionMeetingGaussProof Novel.DiffusionMeetingPricingProof
namespace Novel.DiffusionMeetingConsistencyProof

lemma integrand_zero {lo hi : ℝ} : Integrand (fun _ => (0:ℝ)) lo hi :=
  ⟨measurable_const, ⟨0, fun _ => by simp⟩, fun _ h => absurd rfl h⟩

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

/-- A combination of variance `0` vanishes almost surely. -/
lemma comb_ae_zero (hG : GaussLaw M Q H) {β : Fin N → ℝ} {f : ℝ → ℝ} (hf : Integrand f 0 H)
    (hv : var M H β f = 0) : ∀ᵐ ω ∂Q, comb M β f ω = 0 := by
  have hm := comb_law hG β hf
  rw [hv, Real.toNNReal_zero, gaussianReal_zero_var] at hm
  have h := congrArg (fun μ : Measure ℝ => μ {0}ᶜ) hm
  rw [Measure.map_apply (comb_meas hG hf) (measurableSet_singleton 0).compl] at h
  rw [ae_iff]
  simp at h
  exact h

/-- `Z_n = Σ e_n Z + I 0`, almost surely. -/
lemma Z_ae (hG : GaussLaw M Q H) (n : Fin N) :
    M.Z n =ᵐ[Q] comb M (Pi.single n 1) fun _ => 0 := by
  have h0 := comb_ae_zero hG (β := 0) (integrand_zero (lo := 0) (hi := H)) (by simp [var])
  filter_upwards [h0] with ω hω
  simp only [comb, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at hω
  simp [comb, Pi.single_apply, hω]

/-- The Gaussian exponential moment, given the variance's sign. -/
lemma exp_comb' [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (β : Fin N → ℝ) {f : ℝ → ℝ}
    (hf : Integrand f 0 H) (hv : 0 ≤ var M H β f) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * comb M β f ω)) Q ∧
      ∫ ω, Real.exp (c * comb M β f ω) ∂Q = Real.exp (c ^ 2 * var M H β f / 2) := by
  have hm := comb_meas hG (β := β) hf
  have hmap := comb_law hG β hf
  refine ⟨?_, ?_⟩
  · have := integrable_exp_mul_gaussianReal (μ := 0) (v := (var M H β f).toNNReal) c
    rw [← hmap] at this
    exact (integrable_map_measure (by fun_prop) hm.aemeasurable).1 this
  · rw [← integral_map (f := fun x => Real.exp (c * x)) hm.aemeasurable (by fun_prop), hmap]
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := (var M H β f).toNNReal)) c
    simp only [mgf, id] at this
    rw [this, Real.coe_toNNReal _ hv]
    ring_nf

omit m₀ in
lemma var_single (n : Fin N) : var M H (Pi.single n 1) (fun _ => 0) = M.v n := by
  simp [var, Pi.single_apply]

/-- Assumption 2.2. -/
lemma jump_martingale [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (n : Fin N) {T : ℝ}
    (hT : M.T n ≤ T) :
    Q[fun ω => Real.exp (-∫ u in M.T n..T, xi M n u ω) | leftLim M (M.T n)] =ᵐ[Q] 1 := by
  obtain ⟨-, hv, -, -, -, -, -, -, -, -, -, -, -, -, hmono, hFle, -, -, hind⟩ := id hG
  set c := T - M.T n
  set X := comb M (Pi.single n 1) fun _ => 0
  have hXm : Measurable X := comb_meas hG (integrand_zero (lo := 0) (hi := H))
  have hint : ∀ ω, ∫ u in M.T n..T, xi M n u ω = M.Z n ω * c + M.v n * (c ^ 2 / 2) := fun ω => by
    have := int_step hT (M.T n) (M.Z n ω) (M.v n)
    simp only [xi]
    rw [this, w, d, sub_self, max_self]
    rw [max_eq_left (sub_nonneg.2 hT)]
    ring
  have hle : leftLim M (M.T n) ≤ m₀ := iSup₂_le fun s _ => hFle s
  have hind' : Indep (MeasurableSpace.comap X inferInstance) (leftLim M (M.T n)) Q := by
    refine Indep.symm ?_
    rw [leftLim, iSup_subtype']
    refine indep_iSup_of_directed_le (fun s => (hind s _ _ (fun i hi => ?_)
      integrand_zero (fun _ h => absurd rfl h)).symm) (fun s => hFle s) hXm.comap_le
      (Monotone.directed_le fun a b hab => hmono hab)
    rw [Pi.single_apply] at hi
    split_ifs at hi with h
    · subst h; exact s.2
    · exact absurd rfl hi
  have he : (fun ω => Real.exp (-∫ u in M.T n..T, xi M n u ω)) =ᵐ[Q]
      fun ω => Real.exp (-(M.v n * (c ^ 2 / 2))) * Real.exp (-c * X ω) := by
    filter_upwards [Z_ae hG n] with ω hω
    rw [hint, hω, ← Real.exp_add]
    simp only [X]
    ring_nf
  have hc := condExp_indep_eq (f := fun ω => Real.exp (-(M.v n * (c ^ 2 / 2))) *
      Real.exp (-c * X ω)) hXm.comap_le hle
    ((measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (comap_measurable X)))).stronglyMeasurable) hind'
  have hE := (exp_comb' hG (Pi.single n 1) (integrand_zero (lo := 0) (hi := H))
    (by rw [var_single]; exact hv n) (-c)).2
  filter_upwards [condExp_congr_ae (m := leftLim M (M.T n)) he, hc] with ω h1 h2
  rw [h1, h2, integral_const_mul, hE, var_single, ← Real.exp_add, Pi.one_apply,
    Real.exp_eq_one_iff]
  ring

/-- The meeting weights `(T − T_n) 1{T_n ≤ t}`. -/
noncomputable def bet (M : DiffModel Ω N) (t T : ℝ) (i : Fin N) : ℝ :=
  if M.T i ≤ t then T - M.T i else 0

/-- The integrand `(T − s) 1_{[0, t]}`. -/
noncomputable def Kf (t T : ℝ) : ℝ → ℝ := (Icc 0 t).indicator fun s => T - s

lemma Kf_integrand {t T lo hi : ℝ} (hlo : lo ≤ 0) (hhi : t ≤ hi) : Integrand (Kf t T) lo hi := by
  refine ⟨(measurable_const.sub measurable_id).indicator measurableSet_Icc,
    ⟨|T| + |t|, fun s => ?_⟩, fun s hs => ?_⟩
  · by_cases h : s ∈ Icc 0 t
    · rw [Kf, indicator_of_mem h]
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
      exact h.2
    · rw [Kf, indicator_of_notMem h]; simp; positivity
  · by_cases h : s ∈ Icc 0 t
    · exact ⟨hlo.trans h.1, h.2.trans hhi⟩
    · rw [Kf, indicator_of_notMem h] at hs; exact absurd rfl hs

/-- Pull out the known part and integrate the independent Gaussian rest. -/
lemma condExp_split [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (hH : 0 ≤ H) {s : ℝ}
    {Y : Ω → ℝ} (hY : Measurable[M.F s] Y) {β : Fin N → ℝ} {f : ℝ → ℝ} (hf : Integrand f 0 H)
    (hβ : ∀ i, β i ≠ 0 → s < M.T i) (hfs : ∀ u, f u ≠ 0 → s < u) (c : ℝ)
    (hint : Integrable (fun ω => Real.exp (Y ω + c * comb M β f ω)) Q) :
    Q[fun ω => Real.exp (Y ω + c * comb M β f ω) | M.F s] =ᵐ[Q]
      fun ω => Real.exp (Y ω + c ^ 2 * var M H β f / 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -, -, hind⟩ := id hG
  set X := comb M β f
  have hXm : Measurable X := comb_meas hG hf
  have hint2 := (exp_comb hG hH β hf c).1
  have hc := condExp_indep_eq (f := fun ω => Real.exp (c * X ω)) hXm.comap_le (hFle s)
    (Real.measurable_exp.comp (measurable_const.mul (comap_measurable X))).stronglyMeasurable
    (hind s β f hβ hf hfs)
  have e : (fun ω => Real.exp (Y ω + c * X ω)) =
      (fun ω => Real.exp (Y ω)) * fun ω => Real.exp (c * X ω) := by
    funext ω; simp [Real.exp_add]
  have hpull := condExp_mul_of_stronglyMeasurable_left (f := fun ω => Real.exp (Y ω))
    (g := fun ω => Real.exp (c * X ω)) (m := M.F s)
    (Real.measurable_exp.comp hY).stronglyMeasurable (e ▸ hint) hint2
  rw [e]
  filter_upwards [hpull, hc] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, (exp_comb hG hH β hf c).2, ← Real.exp_add]

omit m₀ in
lemma Vm_eq (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {t T : ℝ} (ht : 0 ≤ t)
    (htH : t ≤ H) :
    var M H (bet M t T) (Kf t T) = ∑ n, (if M.T n ≤ t then (T - M.T n) ^ 2 * M.v n else 0) +
      ∫ s in (0:ℝ)..t, M.g s * (T - s) ^ 2 := by
  unfold var
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by simp only [bet]; split_ifs <;> ring
  · have i1 : ∀ x y, IntervalIntegrable (fun s => Kf t T s ^ 2 * M.g s) volume x y := fun x y => by
      simpa only [sq] using prod_ii hσ hB (Kf_integrand (T := T) le_rfl htH)
        (Kf_integrand (T := T) le_rfl htH) x y
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 t) (i1 t H)]
    have z : ∫ s in t..H, Kf t T s ^ 2 * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le htH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [Kf, indicator, not_le.2 hs.1]]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only [Kf, indicator_of_mem hs]
    ring

/-- `P(t, T)/B_t = exp(−A_{0,T} − Σ_{T_n ≤ t} (T − T_n) Z_n − I((T − ·) 1_{[0,t]}) − V/2)`. -/
lemma disc_eq (hG : GaussLaw M Q H) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    discBond M t T =ᵐ[Q] fun ω => Real.exp (-Aint M 0 T - comb M (bet M t T) (Kf t T) ω -
      var M H (bet M t T) (Kf t T) / 2) := by
  obtain ⟨hT, hv, hσ, ⟨B, hB⟩, -, hf0, ⟨C, hC⟩, -, hlin, -, -, -, hY, hfub, -⟩ := id hG
  have htH : t ≤ H := htT.trans hTH
  have ii := fun (φ : ℝ → ℝ) (hφ : Continuous φ) (x y : ℝ) =>
    Novel.DiffusionMeetingIdentitiesProof.ii hσ hB φ hφ x y
  have hone : Integrand ((Icc (0:ℝ) t).indicator 1) 0 H := by
    refine ⟨measurable_const.indicator measurableSet_Icc, ⟨1, fun s => ?_⟩, fun s hs => ?_⟩
    · by_cases h : s ∈ Icc (0:ℝ) t <;> simp [h]
    · by_cases h : s ∈ Icc (0:ℝ) t
      · exact ⟨h.1, h.2.trans htH⟩
      · simp [h] at hs
  have hK : (fun s => Wf 0 t s + (T - t) * (Icc (0:ℝ) t).indicator 1 s) = Kf t T := by
    funext s
    by_cases h : s ∈ Icc (0:ℝ) t
    · rw [Kf, indicator_of_mem h, indicator_of_mem h, Wf_eq ht h.1, w,
        max_eq_left (sub_nonneg.2 h.2), max_eq_right (by linarith [h.1] : (0:ℝ) - s ≤ 0)]
      simp only [Pi.one_apply]
      ring
    · rw [Kf, indicator_of_notMem h, indicator_of_notMem h]
      simp [Wf, h]
  have hlin' := hlin (Wf 0 t) _ (T - t) (Wf_integrand (a := 0) htH) hone
  rw [hK] at hlin'
  -- the integrals in `u` of the forward curve
  have hK' : ∀ u, ∫ v in (0:ℝ)..t, M.g v * (u - v) =
      u * (∫ v in (0:ℝ)..t, M.g v) - ∫ v in (0:ℝ)..t, M.g v * v := fun u => by
    have h1 : IntervalIntegrable (fun v => M.g v * u) volume 0 t := ii (fun _ => u) continuous_const 0 t
    have h2 : IntervalIntegrable (fun v => M.g v * v) volume 0 t := ii id continuous_id 0 t
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_mul_const]
    ring
  have i4 : IntervalIntegrable (fun u => ∫ v in (0:ℝ)..t, M.g v * (u - v)) volume t T := by
    simp only [hK']
    exact (by fun_prop : Continuous fun u : ℝ => u * (∫ v in (0:ℝ)..t, M.g v) -
      ∫ v in (0:ℝ)..t, M.g v * v).intervalIntegrable _ _
  have hA : Aint M 0 t + ∫ u in t..T, M.f0 u = Aint M 0 T :=
    intervalIntegral.integral_add_adjacent_intervals
      (Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC 0 t)
      (Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC t T)
  have hbr := Novel.DiffusionMeetingIdentitiesProof.bracketS M.g hσ ⟨B, hB⟩ t T ht htT
  have hdr := Novel.DiffusionMeetingIdentitiesProof.driftS M.g hσ ⟨B, hB⟩ 0 t le_rfl ht
  have hV := Vm_eq (T := T) hσ hB ht htH
  have hdiv : ∫ v in (0:ℝ)..t, M.g v * (T - v) ^ 2 / 2 =
      (∫ v in (0:ℝ)..t, M.g v * (T - v) ^ 2) / 2 := intervalIntegral.integral_div _ _
  filter_upwards [hfub 0 t le_rfl ht htH, hY t ht htH, hlin'] with ω h1 h2 h3
  have h1' : ∫ u in (0:ℝ)..t, M.Y u ω = M.I (Wf 0 t) ω := h1
  have hr := rate_int hG ω le_rfl ht
  have hf : ∫ u in t..T, fwd M t u ω = (∫ u in t..T, M.f0 u) +
      (∑ n, if M.T n ≤ t then M.Z n ω * (T - t) +
        M.v n * (((T - M.T n) ^ 2 - (t - M.T n) ^ 2) / 2) else 0) +
      (T - t) * M.Y t ω + ∫ u in t..T, ∫ v in (0:ℝ)..t, M.g v * (u - v) := by
    have i1 := Novel.SpliceCrossTermDriftProof.ii_bdd hf0 C hC t T
    have i2 : IntervalIntegrable (fun u => ∑ n, (if M.T n ≤ t then M.Z n ω + M.v n * (u - M.T n)
        else 0)) volume t T := by
      refine Continuous.intervalIntegrable (continuous_finsetSum _ fun n _ => ?_) _ _
      split_ifs <;> fun_prop
    unfold fwd
    rw [intervalIntegral.integral_add ((i1.add i2).add intervalIntegrable_const) i4,
      intervalIntegral.integral_add (i1.add i2) intervalIntegrable_const,
      intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_finsetSum fun n _ => by
        split_ifs
        · exact (by fun_prop : Continuous fun u : ℝ => M.Z n ω + M.v n * (u - M.T n)).intervalIntegrable _ _
        · exact intervalIntegrable_const]
    congr 3
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun u : ℝ => M.v n * (u - M.T n)).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
        intervalIntegral.integral_comp_sub_right (fun x => x) (M.T n), integral_id]
      ring
    · simp
  have hJ : (∑ n, (M.Z n ω * w 0 t (M.T n) + M.v n * d 0 t (M.T n))) +
      (∑ n, if M.T n ≤ t then M.Z n ω * (T - t) +
        M.v n * (((T - M.T n) ^ 2 - (t - M.T n) ^ 2) / 2) else 0) =
      ∑ n, bet M t T n * M.Z n ω +
        (∑ n, if M.T n ≤ t then (T - M.T n) ^ 2 * M.v n else 0) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [bet, w, d]
    rw [max_eq_right (by linarith [hT n] : (0:ℝ) - M.T n ≤ 0)]
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith [not_le.1 h])]; ring
  have hc : comb M (bet M t T) (Kf t T) ω = ∑ n, bet M t T n * M.Z n ω + M.I (Kf t T) ω := rfl
  rw [h2] at hf
  simp only [discBond]
  congr 1
  rw [hc, hV]
  linarith

/-- One step of the martingale property of the closed form. -/
lemma cond_step [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {s t T : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    Q[fun ω => Real.exp (-Aint M 0 T - comb M (bet M t T) (Kf t T) ω -
        var M H (bet M t T) (Kf t T) / 2) | M.F s] =ᵐ[Q]
      fun ω => Real.exp (-Aint M 0 T - comb M (bet M s T) (Kf s T) ω -
        var M H (bet M s T) (Kf s T) / 2) := by
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -, -, -, -, -, -, -, -, -, -, -, -, hZF, hIF, -⟩ := id hG
  have htH := htT.trans hTH
  have hsH := hst.trans htH
  have hH : 0 ≤ H := hs.trans hsH
  set Δβ : Fin N → ℝ := fun i => bet M t T i + (-1) * bet M s T i
  set ΔK : ℝ → ℝ := fun u => Kf t T u + (-1) * Kf s T u
  have hKt : Integrand (Kf t T) 0 H := Kf_integrand le_rfl htH
  have hKs : Integrand (Kf s T) 0 H := Kf_integrand le_rfl hsH
  have hΔK : Integrand ΔK 0 H := integrand_add hKt hKs (-1)
  have hsplit := comb_add hG (bet M s T) Δβ hKs hΔK 1
  have e1 : (fun i => bet M s T i + 1 * Δβ i) = bet M t T := by funext i; simp only [Δβ]; ring
  have e2 : (fun u => Kf s T u + 1 * ΔK u) = Kf t T := by funext u; simp only [ΔK]; ring
  rw [e1, e2] at hsplit
  have hcov : cov M H (bet M s T) (Kf s T) Δβ ΔK = 0 := by
    have z1 : ∀ i, bet M s T i * Δβ i * M.v i = 0 := fun i => by
      by_cases h2 : M.T i ≤ s
      · simp only [Δβ, bet, h2, h2.trans hst, ite_true]; ring
      · simp only [Δβ, bet, h2, ite_false]; ring
    have z2 : ∀ u, Kf s T u * ΔK u * M.g u = 0 := fun u => by
      by_cases hu : u ∈ Icc 0 s
      · have hu' : u ∈ Icc 0 t := ⟨hu.1, hu.2.trans hst⟩
        simp only [ΔK, Kf, indicator_of_mem hu, indicator_of_mem hu']; ring
      · simp only [ΔK, Kf, indicator_of_notMem hu]; ring
    unfold cov
    rw [Finset.sum_eq_zero fun i _ => z1 i,
      intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun u _ => z2 u]
    simp
  have hVt : var M H (bet M t T) (Kf t T) = var M H (bet M s T) (Kf s T) + var M H Δβ ΔK := by
    have := var_add hσ hB (bet M s T) Δβ hKs hΔK 1
    rw [e1, e2, hcov] at this
    linarith
  have hXs : Measurable[M.F s] (comb M (bet M s T) (Kf s T)) := by
    show Measurable[M.F s] fun ω => ∑ i, bet M s T i * M.Z i ω + M.I (Kf s T) ω
    refine (Finset.measurable_sum _ fun n _ => ?_).add (hIF _ s (Kf_integrand le_rfl le_rfl))
    by_cases h : M.T n ≤ s
    · simp only [bet, h, ite_true]; exact measurable_const.mul (hZF n s h)
    · simp only [bet, h, ite_false, zero_mul]; exact measurable_const
  have hY : Measurable[M.F s] fun ω => -Aint M 0 T - comb M (bet M s T) (Kf s T) ω -
      var M H (bet M t T) (Kf t T) / 2 := (measurable_const.sub hXs).sub measurable_const
  have he : (fun ω => Real.exp (-Aint M 0 T - comb M (bet M t T) (Kf t T) ω -
      var M H (bet M t T) (Kf t T) / 2)) =ᵐ[Q] fun ω => Real.exp ((-Aint M 0 T -
      comb M (bet M s T) (Kf s T) ω - var M H (bet M t T) (Kf t T) / 2) +
        -1 * comb M Δβ ΔK ω) := by
    filter_upwards [hsplit] with ω h
    rw [← h]
    ring_nf
  have hint : Integrable (fun ω => Real.exp ((-Aint M 0 T - comb M (bet M s T) (Kf s T) ω -
      var M H (bet M t T) (Kf t T) / 2) + -1 * comb M Δβ ΔK ω)) Q := by
    refine (((exp_comb hG hH (bet M t T) hKt (-1)).1).const_mul
      (Real.exp (-Aint M 0 T - var M H (bet M t T) (Kf t T) / 2))).congr ?_
    filter_upwards [hsplit] with ω h
    rw [← Real.exp_add, ← h]
    ring_nf
  have hΔβ : ∀ i, Δβ i ≠ 0 → s < M.T i := fun i hi => by
    by_contra h
    push Not at h
    apply hi
    simp only [Δβ, bet, h, h.trans hst, ite_true]
    ring
  have hΔK' : ∀ u, ΔK u ≠ 0 → s < u := fun u hu => by
    by_contra h
    push Not at h
    apply hu
    by_cases h0 : 0 ≤ u
    · have m1 : u ∈ Icc 0 t := ⟨h0, h.trans hst⟩
      have m2 : u ∈ Icc 0 s := ⟨h0, h⟩
      simp only [ΔK, Kf, indicator_of_mem m1, indicator_of_mem m2]
      ring
    · have m1 : u ∉ Icc 0 t := fun m => h0 m.1
      have m2 : u ∉ Icc 0 s := fun m => h0 m.1
      simp only [ΔK, Kf, indicator_of_notMem m1, indicator_of_notMem m2]
      ring
  have hc := condExp_split hG hH hY hΔK hΔβ hΔK' (-1) hint
  filter_upwards [condExp_congr_ae (m := M.F s) he, hc] with ω h1 h2
  rw [h1, h2, hVt]
  congr 1
  ring

end

lemma consistencyS : Standalone.DiffusionMeetingConsistency.consistencyStatement := by
  intro Ω _ N Q _ M H hG
  obtain ⟨-, -, hg, -, hg0, -, -, -, -, -, -, -, hY, -, -, -, hZF, -⟩ := id hG
  refine ⟨?_, ?_, fun t T h => ⟨by simp [alpha, not_le.2 h], by simp [sigma, not_le.2 h]⟩,
    fun n => ?_, fun n u ω h => by simp [xi, not_le.2 h], fun t T htT => ?_,
    fun n T hT => jump_martingale hG n hT, fun t T ht htT htH => ?_⟩
  · exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      ((hg.comp measurable_fst).mul (measurable_snd.sub measurable_fst)) measurable_const
  · exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (hg.comp measurable_fst).sqrt measurable_const
  · have hZ : Measurable[MeasurableSpace.prod inferInstance (M.F (M.T n))]
        fun p : ℝ × Ω => M.Z n p.2 :=
      (hZF n (M.T n) le_rfl).comp (@measurable_snd ℝ Ω inferInstance (M.F (M.T n)))
    have hfst : Measurable[MeasurableSpace.prod inferInstance (M.F (M.T n))]
        fun p : ℝ × Ω => p.1 := @measurable_fst ℝ Ω inferInstance (M.F (M.T n))
    exact Measurable.ite (measurableSet_le measurable_const hfst)
      (hZ.add (measurable_const.mul (hfst.sub measurable_const))) measurable_const
  · have e1 : ∫ u in t..T, alpha M t u = M.g t * ((T - t) ^ 2 / 2) := by
      rw [intervalIntegral.integral_congr (g := fun u => M.g t * (u - t)) fun u hu => by
        rw [uIcc_of_le htT] at hu
        simp [alpha, hu.1], intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x => x) t, integral_id]
      ring
    have e2 : ∫ u in t..T, sigma M t u = Real.sqrt (M.g t) * (T - t) := by
      rw [intervalIntegral.integral_congr (g := fun _ => Real.sqrt (M.g t)) fun u hu => by
        rw [uIcc_of_le htT] at hu
        simp [sigma, hu.1], intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [e1, e2, mul_pow, Real.sq_sqrt (hg0 t)]
    ring
  · filter_upwards [hY t ht htH] with ω hω
    have e1 : ∫ s in (0:ℝ)..t, alpha M s T = ∫ s in (0:ℝ)..t, M.g s * (T - s) :=
      intervalIntegral.integral_congr fun s hs => by
        rw [uIcc_of_le ht] at hs
        simp [alpha, hs.2.trans htT]
    have e2 : ∀ n, (if M.T n ≤ t then xi M n T ω else 0) =
        if M.T n ≤ t then M.Z n ω + M.v n * (T - M.T n) else 0 := fun n => by
      split_ifs with h
      · simp [xi, h.trans htT]
      · rfl
    simp only [fwd, e1, e2, hω]
    ring

lemma martingaleS : Standalone.DiffusionMeetingConsistency.martingaleStatement := by
  intro Ω _ N Q _ M H hG T hT hTH
  obtain ⟨-, hv, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hT.trans hTH
  have hint : ∀ t, 0 ≤ t → t ≤ T → Integrable (discBond M t T) Q := fun t ht htT => by
    refine (((exp_comb hG hH (bet M t T) (Kf_integrand (T := T) le_rfl (htT.trans hTH)) (-1)).1).const_mul
      (Real.exp (-Aint M 0 T - var M H (bet M t T) (Kf t T) / 2))).congr ?_
    filter_upwards [disc_eq hG ht htT hTH] with ω h
    rw [h, ← Real.exp_add]
    ring_nf
  refine ⟨hint, fun s t hs hst htT => ?_, fun t ht htT => ?_⟩
  · filter_upwards [condExp_congr_ae (m := M.F s) (disc_eq hG (hs.trans hst) htT hTH),
      cond_step hG hs hst htT hTH, disc_eq hG hs (hst.trans htT) hTH] with ω h1 h2 h3
    rw [h1, h2, h3]
  · filter_upwards [disc_eq hG ht htT hTH] with ω h
    have htau : ∀ i : Fin N, tau M (i.val + 1) = M.T i := fun i => by simp [tau]
    have hvN : ∀ i, ((vN M i : NNReal) : ℝ) = M.v i := fun i => Real.coe_toNNReal _ (hv i)
    rw [h, P0, Dfac, Standalone.D3EventVariances.discounted, Standalone.D3EventVariances.past]
    simp only [Standalone.D3EventVariances.factor, htau, hvN]
    rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add, Finset.sum_filter,
      Vm_eq hσ hB ht (htT.trans hTH)]
    congr 1
    have e3 : ∑ i, (if M.T i ≤ t then -((T - M.T i) * M.Z i ω + M.v i * (T - M.T i) ^ 2 / 2)
        else 0) = -(∑ i, bet M t T i * M.Z i ω) -
          (∑ i, (if M.T i ≤ t then (T - M.T i) ^ 2 * M.v i else 0)) / 2 := by
      rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [bet]; split_ifs <;> ring
    rw [e3]
    simp only [comb, Kf]
    ring

theorem diffusionMeetingConsistency : Standalone.DiffusionMeetingConsistency.statement :=
  ⟨consistencyS, martingaleS⟩

end Novel.DiffusionMeetingConsistencyProof

import Standalone.DiffusionMeetingPricing
import Novel.DiffusionMeetingGaussProof
import Novel.MGFUniqueness
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Novel.CompoundedFuturesIdentificationProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.CompoundedFuturesIdentification Standalone.DiffusionMeetingIdentities
open Standalone.DiffusionMeetingGauss Standalone.DiffusionMeetingPricing
open Novel.DiffusionMeetingGaussProof
namespace Novel.DiffusionMeetingPricingProof

lemma bdd_of_integrand {f : ℝ → ℝ} {lo hi : ℝ} (hf : Integrand f lo hi) :
    ∃ C, 0 ≤ C ∧ ∀ s, |f s| ≤ C := by
  obtain ⟨-, ⟨C, hC⟩, -⟩ := hf
  exact ⟨C, (abs_nonneg _).trans (hC 0), hC⟩

lemma integrand_add {f g : ℝ → ℝ} {lo hi : ℝ} (hf : Integrand f lo hi) (hg : Integrand g lo hi)
    (c : ℝ) : Integrand (fun s => f s + c * g s) lo hi := by
  obtain ⟨hfm, ⟨A, hA⟩, hfs⟩ := hf
  obtain ⟨hgm, ⟨B, hB⟩, hgs⟩ := hg
  refine ⟨hfm.add (measurable_const.mul hgm), ⟨A + |c| * B, fun s => ?_⟩, fun s hs => ?_⟩
  · calc |f s + c * g s| ≤ |f s| + |c * g s| := abs_add_le _ _
      _ ≤ A + |c| * B := by rw [abs_mul]; gcongr; exacts [hA s, hB s]
  · by_contra h
    have h1 : f s = 0 := by by_contra h'; exact h (hfs s h')
    have h2 : g s = 0 := by by_contra h'; exact h (hgs s h')
    exact hs (by simp [h1, h2])

lemma integrand_indicator {f : ℝ → ℝ} {lo hi lo' hi' : ℝ} (hf : Integrand f lo hi) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : ∀ s ∈ A, lo ≤ s → s ≤ hi → lo' ≤ s ∧ s ≤ hi') :
    Integrand (A.indicator f) lo' hi' := by
  obtain ⟨hfm, ⟨C, hC⟩, hfs⟩ := hf
  refine ⟨hfm.indicator hA, ⟨|C|, fun s => ?_⟩, fun s hs => ?_⟩
  · by_cases h : s ∈ A
    · rw [indicator_of_mem h]; exact (hC s).trans (le_abs_self C)
    · rw [indicator_of_notMem h]; simp
  · by_cases h : s ∈ A
    · rw [indicator_of_mem h] at hs; exact hsub s h (hfs s hs).1 (hfs s hs).2
    · rw [indicator_of_notMem h] at hs; exact absurd rfl hs

lemma Wf_eq {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) : Wf a b s = w a b s := by
  by_cases h : s ≤ b
  · simp [Wf, indicator, hs, h, w]
  · have h' : b < s := not_le.1 h
    simp [Wf, indicator, h, w, max_eq_right (by linarith : b - s ≤ 0),
      max_eq_right (by linarith : a - s ≤ 0)]

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : DiffModel Ω N} {H : ℝ}

omit m₀ in
lemma prod_ii (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {f g : ℝ → ℝ} {lo hi : ℝ}
    (hf : Integrand f lo hi) (hg : Integrand g lo hi) (x y : ℝ) :
    IntervalIntegrable (fun s => f s * g s * M.g s) volume x y := by
  obtain ⟨A, hA0, hA⟩ := bdd_of_integrand hf
  obtain ⟨C, hC0, hC⟩ := bdd_of_integrand hg
  refine Novel.SpliceCrossTermDriftProof.ii_bdd ((hf.1.mul hg.1).mul hσ) (A * C * B)
    (fun s => ?_) x y
  simp only [Pi.mul_apply]
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hA s) (hC s) (abs_nonneg _) hA0) (hB s) (abs_nonneg _)
    (mul_nonneg hA0 hC0)

/-- The covariance `Σ β_i γ_i v_i + ∫_0^H f g σ²`. -/
noncomputable def cov (M : DiffModel Ω N) (H : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ) (γ : Fin N → ℝ)
    (g : ℝ → ℝ) : ℝ :=
  ∑ i, β i * γ i * M.v i + ∫ s in (0:ℝ)..H, f s * g s * M.g s

omit m₀ in
lemma var_add (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) (β γ : Fin N → ℝ)
    {f g : ℝ → ℝ} (hf : Integrand f 0 H) (hg : Integrand g 0 H) (c : ℝ) :
    var M H (fun i => β i + c * γ i) (fun s => f s + c * g s) =
      var M H β f + 2 * c * cov M H β f γ g + c ^ 2 * var M H γ g := by
  have i1 := prod_ii hσ hB hf hf 0 H
  have i2 := prod_ii hσ hB hf hg 0 H
  have i3 := prod_ii hσ hB hg hg 0 H
  have sq' : ∀ φ : ℝ → ℝ, ∫ s in (0:ℝ)..H, φ s ^ 2 * M.g s = ∫ s in (0:ℝ)..H, φ s * φ s * M.g s :=
    fun φ => by simp only [sq]
  have e1 : ∫ s in (0:ℝ)..H, (f s + c * g s) ^ 2 * M.g s =
      (∫ s in (0:ℝ)..H, f s * f s * M.g s) + 2 * c * (∫ s in (0:ℝ)..H, f s * g s * M.g s) +
        c ^ 2 * ∫ s in (0:ℝ)..H, g s * g s * M.g s := by
    rw [intervalIntegral.integral_congr (g := fun s => (f s * f s * M.g s +
        2 * c * (f s * g s * M.g s)) + c ^ 2 * (g s * g s * M.g s)) fun s _ => by ring,
      intervalIntegral.integral_add (i1.add (i2.const_mul _)) (i3.const_mul _),
      intervalIntegral.integral_add i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have e2 : ∑ i, (β i + c * γ i) ^ 2 * M.v i = ∑ i, β i ^ 2 * M.v i +
      2 * c * ∑ i, β i * γ i * M.v i + c ^ 2 * ∑ i, γ i ^ 2 * M.v i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [var, cov]
  rw [e1, e2, sq' f, sq' g]
  ring

lemma comb_add (hG : GaussLaw M Q H) (β γ : Fin N → ℝ) {f g : ℝ → ℝ} (hf : Integrand f 0 H)
    (hg : Integrand g 0 H) (c : ℝ) :
    (fun ω => comb M β f ω + c * comb M γ g ω) =ᵐ[Q]
      comb M (fun i => β i + c * γ i) (fun s => f s + c * g s) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlin, -⟩ := hG
  filter_upwards [hlin f g c hf hg] with ω hω
  have e : ∑ i, (β i + c * γ i) * M.Z i ω = ∑ i, β i * M.Z i ω + c * ∑ i, γ i * M.Z i ω := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [comb, hω, e]
  ring

/-- The law of a combination under the tilt by another: the Gaussian shift. -/
lemma tilt [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) (hH : 0 ≤ H) (β γ : Fin N → ℝ)
    {f g : ℝ → ℝ} (hf : Integrand f 0 H) (hg : Integrand g 0 H) {c : ℝ} (hc : c ≠ 0) :
    (Q.tilted fun ω => c * comb M β f ω).map (comb M γ g) =
      gaussianReal (c * cov M H β f γ g) (var M H γ g).toNNReal := by
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hint := (exp_comb hG hH β hf c).1
  have := isProbabilityMeasure_tilted hint
  have hf' := fun t : ℝ => integrand_add hf hg (t / c)
  have hj : ∀ t, (fun ω => Real.exp (c * comb M β f ω) * Real.exp (t * comb M γ g ω)) =ᵐ[Q]
      fun ω => Real.exp (c * comb M (fun i => β i + t / c * γ i)
        (fun s => f s + t / c * g s) ω) := fun t => by
    filter_upwards [comb_add hG β γ hf hg (t / c)] with ω hω
    rw [← hω, ← Real.exp_add]
    congr 1
    field_simp
  refine Novel.MGFUniqueness.map_eq_gaussianReal_of_mgf_eqOn (comb_meas hG hg).aemeasurable
    one_pos (fun t _ => ?_) (fun t _ => ?_)
  · rw [integrable_tilted_iff hint]
    simp only [smul_eq_mul]
    exact (exp_comb hG hH _ (hf' t) c).1.congr (hj t).symm
  · simp only [mgf]
    rw [integral_tilted]
    simp only [smul_eq_mul, div_mul_eq_mul_div]
    rw [integral_div, integral_congr_ae (hj t), (exp_comb hG hH _ (hf' t) c).2,
      (exp_comb hG hH β hf c).2, ← Real.exp_sub, var_add hσ hB β γ hf hg,
      Real.coe_toNNReal _ (var_nonneg hG hH γ g)]
    congr 1
    field_simp
    ring

/-- The meeting weights revealed by `t`, and the rest. -/
noncomputable def β1 (M : DiffModel Ω N) (a b t : ℝ) (i : Fin N) : ℝ :=
  if M.T i ≤ t then w a b (M.T i) else 0
noncomputable def β2 (M : DiffModel Ω N) (a b t : ℝ) (i : Fin N) : ℝ :=
  if M.T i ≤ t then 0 else w a b (M.T i)

/-- The Fubini integrand before `t`, and after. -/
noncomputable def W1 (a b t : ℝ) : ℝ → ℝ := (Iic t).indicator (Wf a b)
noncomputable def W2 (a b t : ℝ) : ℝ → ℝ := (Ioi t).indicator (Wf a b)

lemma W1_integrand (a : ℝ) {b H : ℝ} (hbH : b ≤ H) (t : ℝ) : Integrand (W1 a b t) 0 H :=
  integrand_indicator (Wf_integrand hbH) measurableSet_Iic fun _ _ h1 h2 => ⟨h1, h2⟩

lemma W1_integrand' (a : ℝ) {b H : ℝ} (hbH : b ≤ H) (t : ℝ) : Integrand (W1 a b t) 0 t :=
  integrand_indicator (Wf_integrand hbH) measurableSet_Iic fun _ hs h1 _ => ⟨h1, hs⟩

lemma W2_integrand (a : ℝ) {b H : ℝ} (hbH : b ≤ H) (t : ℝ) : Integrand (W2 a b t) 0 H :=
  integrand_indicator (Wf_integrand hbH) measurableSet_Ioi fun _ _ h1 h2 => ⟨h1, h2⟩

lemma comb_split (hG : GaussLaw M Q H) {a b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    comb M (fun n => w a b (M.T n)) (Wf a b) =ᵐ[Q]
      fun ω => comb M (β1 M a b t) (W1 a b t) ω + 1 * comb M (β2 M a b t) (W2 a b t) ω := by
  have h := comb_add hG (β1 M a b t) (β2 M a b t) (W1_integrand a hbH t) (W2_integrand a hbH t) 1
  have e1 : (fun i => β1 M a b t i + 1 * β2 M a b t i) = fun n => w a b (M.T n) := by
    funext i; simp only [β1, β2]; split_ifs <;> ring
  have e2 : (fun s => W1 a b t s + 1 * W2 a b t s) = Wf a b := by
    funext s
    by_cases hs : s ≤ t
    · simp [W1, W2, indicator, hs, not_lt.2 hs]
    · simp [W1, W2, indicator, hs, not_le.1 hs]
  rw [e1, e2] at h
  exact h.symm

lemma var_split (hG : GaussLaw M Q H) {a b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    var M H (β1 M a b t) (W1 a b t) + var M H (β2 M a b t) (W2 a b t) =
      var M H (fun n => w a b (M.T n)) (Wf a b) := by
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := hG
  have i1 := prod_ii hσ hB (W1_integrand a hbH t) (W1_integrand a hbH t) 0 H
  have i2 := prod_ii hσ hB (W2_integrand a hbH t) (W2_integrand a hbH t) 0 H
  have sq' : ∀ φ : ℝ → ℝ, ∫ s in (0:ℝ)..H, φ s ^ 2 * M.g s = ∫ s in (0:ℝ)..H, φ s * φ s * M.g s :=
    fun φ => by simp only [sq]
  simp only [var, sq']
  rw [add_add_add_comm, ← Finset.sum_add_distrib, ← intervalIntegral.integral_add i1 i2]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp only [β1, β2]; split_ifs <;> ring
  · refine intervalIntegral.integral_congr fun s _ => ?_
    by_cases hs : s ≤ t
    · simp [W1, W2, indicator, hs, not_lt.2 hs]
    · simp [W1, W2, indicator, hs, not_le.1 hs]

lemma integrable_rate [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbH : b ≤ H) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ∫ u in a..b, rate M u ω)) Q := by
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  refine (((exp_comb hG hH (fun n => w a b (M.T n)) (Wf_integrand (a := a) hbH) c).1).const_mul
    (Real.exp (c * Cst M a b))).congr ?_
  filter_upwards [rate_ae hG ha hab hbH] with ω h
  simp only [h, ← Real.exp_add]
  ring_nf

/-- `G_t = exp(Cst + Σ_{T_i ≤ t} w_i Z_i + I(w 1_{≤ t}) + ½ Var(the rest))`. -/
lemma G_eq [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) (t : ℝ) :
    Standalone.DiffusionMeetingPricing.G M Q t a b =ᵐ[Q] fun ω => Real.exp (Cst M a b + comb M (β1 M a b t) (W1 a b t) ω +
      var M H (β2 M a b t) (W2 a b t) / 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, hZF, hIF, hind⟩ := id hG
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  set X1 := comb M (β1 M a b t) (W1 a b t)
  set X2 := comb M (β2 M a b t) (W2 a b t)
  have hX1 : StronglyMeasurable[M.F t] (fun ω => Real.exp (Cst M a b + X1 ω)) := by
    refine Measurable.stronglyMeasurable (Real.measurable_exp.comp (measurable_const.add ?_))
    refine (Finset.measurable_sum _ fun n _ => ?_).add (hIF _ t (W1_integrand' a hbH t))
    by_cases h : M.T n ≤ t
    · simp only [β1, h, ite_true]; exact measurable_const.mul (hZF n t h)
    · simp only [β1, h, ite_false, zero_mul]; exact measurable_const
  have hX2m : Measurable X2 := comb_meas hG (W2_integrand a hbH t)
  have hind2 : Indep (MeasurableSpace.comap X2 inferInstance) (M.F t) Q := by
    refine hind t _ _ (fun i hi => ?_) (W2_integrand a hbH t) (fun s hs => ?_)
    · simp only [β2] at hi
      split_ifs at hi with h
      · exact absurd rfl hi
      · exact not_le.1 h
    · simp only [W2, indicator] at hs
      split_ifs at hs with h
      · exact h
      · exact absurd rfl hs
  have he : (fun ω => Real.exp (∫ u in a..b, rate M u ω)) =ᵐ[Q]
      (fun ω => Real.exp (Cst M a b + X1 ω)) * fun ω => Real.exp (X2 ω) := by
    filter_upwards [rate_ae hG ha hab hbH, comb_split hG (a := a) hbH t] with ω h1 h2
    simp only [X1, X2, Pi.mul_apply, h1, h2, ← Real.exp_add]
    ring_nf
  have hint : Integrable (fun ω => Real.exp (∫ u in a..b, rate M u ω)) Q := by
    simpa using integrable_rate hG ha hab hbH 1
  have hint2 : Integrable (fun ω => Real.exp (X2 ω)) Q := by
    simpa using (exp_comb hG hH (β2 M a b t) (W2_integrand a hbH t) 1).1
  have hE2 : ∫ ω, Real.exp (X2 ω) ∂Q = Real.exp (var M H (β2 M a b t) (W2 a b t) / 2) := by
    simpa using (exp_comb hG hH (β2 M a b t) (W2_integrand a hbH t) 1).2
  have hc := condExp_indep_eq (f := fun ω => Real.exp (X2 ω))
    (m₁ := MeasurableSpace.comap X2 inferInstance) hX2m.comap_le
    (hFle t) (Real.measurable_exp.comp (comap_measurable X2)).stronglyMeasurable hind2
  have hpull := condExp_mul_of_stronglyMeasurable_left hX1 (hint.congr he) hint2
  filter_upwards [condExp_congr_ae (m := M.F t) he, hpull, hc] with ω h1 h2 h3
  rw [Standalone.DiffusionMeetingPricing.G, h1, h2, Pi.mul_apply, h3, hE2, ← Real.exp_add]

lemma futures_eq [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) :
    ∫ ω, Real.exp (∫ u in a..b, rate M u ω) ∂Q = Real.exp (Aint M a b + pdiff M a b) := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -⟩ := id hG
  have hE := (exp_comb hG (ha.trans (hab.trans hbH)) (fun n => w a b (M.T n))
    (Wf_integrand (a := a) hbH) 1).2
  simp only [one_mul, one_pow] at hE
  rw [integral_congr_ae (g := fun ω => Real.exp (Cst M a b) *
      Real.exp (comb M (fun n => w a b (M.T n)) (Wf a b) ω))
    ((rate_ae hG ha hab hbH).mono fun ω h => by simp only [h, Real.exp_add]),
    integral_const_mul, hE, ← Real.exp_add, key hg hB ha hab hbH]

/-- `G_0 = exp(A + p)`. -/
lemma G_zero [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) :
    Standalone.DiffusionMeetingPricing.G M Q 0 a b =ᵐ[Q]
      fun _ => Real.exp (Aint M a b + pdiff M a b) := by
  obtain ⟨hT, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -⟩ := id hG
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  have hv0 : var M H (β1 M a b 0) (W1 a b 0) = 0 := by
    have e1 : ∀ i, β1 M a b 0 i = 0 := fun i => by simp [β1, not_le.2 (hT i)]
    have e2 : ∫ s in (0:ℝ)..H, W1 a b 0 s ^ 2 * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    simp [var, e1, e2]
  have hX0 : ∀ᵐ ω ∂Q, comb M (β1 M a b 0) (W1 a b 0) ω = 0 := by
    have hm := comb_law hG (β1 M a b 0) (W1_integrand a hbH 0)
    rw [hv0, Real.toNNReal_zero, gaussianReal_zero_var] at hm
    have h := congrArg (fun μ : Measure ℝ => μ {0}ᶜ) hm
    rw [Measure.map_apply (comb_meas hG (W1_integrand a hbH 0))
      (measurableSet_singleton 0).compl] at h
    rw [ae_iff]
    simp at h
    exact h
  set c := Real.exp (Cst M a b + 0 + var M H (β2 M a b 0) (W2 a b 0) / 2)
  have hGc : Standalone.DiffusionMeetingPricing.G M Q 0 a b =ᵐ[Q] fun _ => c := by
    filter_upwards [G_eq hG ha hab hbH 0, hX0] with ω h1 h2
    rw [h1, h2]
  have hmean : ∫ ω, Standalone.DiffusionMeetingPricing.G M Q 0 a b ω ∂Q = c := by
    rw [integral_congr_ae hGc]; simp
  rw [Standalone.DiffusionMeetingPricing.G, integral_condExp (hFle 0), futures_eq hG ha hab hbH]
    at hmean
  rw [hmean]
  exact hGc

omit m₀ in
lemma pdiff_zero (hT : ∀ i, 0 < M.T i) (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B)
    {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    pdiff M 0 S = var M H (fun n => w 0 S (M.T n)) (Wf 0 S) := by
  unfold pdiff var
  rw [int_Wf hσ hB le_rfl hS hSH]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [h, d, w, max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
    ring
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [h, d, w, max_eq_right (by linarith [hs.1] : (0:ℝ) - s ≤ 0)]
    ring

/-- `B_S⁻¹ = exp(−Cst) exp(−U)`, `U = Σ (S − T_n)⁺ Z_n + I (S − ·)⁺`. -/
lemma disc_ae (hG : GaussLaw M Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    disc M S =ᵐ[Q] fun ω => Real.exp (-Cst M 0 S) *
      Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω) := by
  filter_upwards [rate_ae hG le_rfl hS hSH] with ω h
  simp only [disc, h, ← Real.exp_add]
  ring_nf

lemma disc_mean [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {S : ℝ} (hS : 0 ≤ S)
    (hSH : S ≤ H) :
    ∫ ω, disc M S ω ∂Q = Real.exp (-Cst M 0 S) *
        ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω) ∂Q ∧
      ∫ ω, disc M S ω ∂Q = P0 M S := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hS.trans hSH
  have e1 : ∫ ω, disc M S ω ∂Q = Real.exp (-Cst M 0 S) *
      ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω) ∂Q := by
    rw [integral_congr_ae (disc_ae hG hS hSH), integral_const_mul]
  refine ⟨e1, ?_⟩
  rw [e1, (exp_comb hG hH _ (Wf_integrand (a := 0) hSH) (-1)).2, ← Real.exp_add, P0]
  have k := key (a := 0) hσ hB le_rfl hS hSH
  rw [← pdiff_zero hT hσ hB hS hSH] at k
  congr 1
  rw [pdiff_zero hT hσ hB hS hSH] at k
  linarith

/-- The density of `Q^S` is the tilt by `−U`. -/
lemma dens_ae [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    (fun ω => Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω) /
      ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω) ∂Q) =ᵐ[Q]
      fun ω => disc M S ω / P0 M S := by
  obtain ⟨e1, e2⟩ := disc_mean hG hS hSH
  filter_upwards [disc_ae hG hS hSH] with ω h
  rw [h, ← e2, e1, mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma QS_eq [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    Standalone.DiffusionMeetingPricing.QS M Q S =
      Q.tilted fun ω => -1 * comb M (fun n => w 0 S (M.T n)) (Wf 0 S) ω := by
  unfold Standalone.DiffusionMeetingPricing.QS Measure.tilted
  refine withDensity_congr_ae ?_
  filter_upwards [dens_ae hG hS hSH] with ω h
  rw [h]

omit m₀ in
lemma q_eq (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B) {S a b : ℝ} (hS : 0 ≤ S)
    (hSH : S ≤ H) (hab : a ≤ b) (hbH : b ≤ H) :
    var M H (β1 M a b S) (W1 a b S) = qdiff M S a b := by
  unfold var qdiff
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [β1, k]
    split_ifs <;> ring
  · have i1 : ∀ x y, IntervalIntegrable (fun s => W1 a b S s ^ 2 * M.g s) volume x y := fun x y => by
      simpa only [sq] using prod_ii hσ hB (W1_integrand a hbH S) (W1_integrand a hbH S) x y
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 S) (i1 S H)]
    have z : ∫ s in S..H, W1 a b S s ^ 2 * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hSH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [W1, indicator_of_mem (show s ∈ Iic S from hs.2), Wf_eq hab hs.1]
    ring

omit m₀ in
lemma z_eq (hT : ∀ i, 0 < M.T i) (hσ : Measurable M.g) {B : ℝ} (hB : ∀ s, |M.g s| ≤ B)
    {S a b : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) (hab : a ≤ b) (hbH : b ≤ H) :
    cov M H (fun n => w 0 S (M.T n)) (Wf 0 S) (β1 M a b S) (W1 a b S) = zdiff M S a b := by
  unfold cov zdiff
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [β1, j]
    split_ifs with h
    · rw [w, max_eq_left (sub_nonneg.2 h), max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
      ring
    · ring
  · have i1 : ∀ x y, IntervalIntegrable (fun s => Wf 0 S s * W1 a b S s * M.g s) volume x y :=
      prod_ii hσ hB (Wf_integrand (a := 0) hSH) (W1_integrand a hbH S)
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 S) (i1 S H)]
    have z : ∫ s in S..H, Wf 0 S s * W1 a b S s * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hSH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [W1, indicator_of_mem (show s ∈ Iic S from hs.2), Wf_eq hab hs.1, Wf_eq hS hs.1]
    have hw : w 0 S s = S - s := by
      rw [w, max_eq_left (sub_nonneg.2 hs.2), max_eq_right (by linarith [hs.1] : (0:ℝ) - s ≤ 0)]
      ring
    rw [hw]
    ring

/-- Under `Q^S`, `log G_S ~ N(log m − q/2, q)`. -/
lemma law_logG [IsProbabilityMeasure Q] (hG : GaussLaw M Q H) {S a b : ℝ} (hS : 0 ≤ S)
    (hSH : S ≤ H) (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H) :
    HasLaw (fun ω => Real.log (Standalone.DiffusionMeetingPricing.G M Q S a b ω))
      (gaussianReal (Real.log (mdiff M S a b) - qdiff M S a b / 2) (qdiff M S a b).toNNReal)
      (Standalone.DiffusionMeetingPricing.QS M Q S) := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hS.trans hSH
  set c := Cst M a b + var M H (β2 M a b S) (W2 a b S) / 2
  set X1 := comb M (β1 M a b S) (W1 a b S)
  have hX1 : Measurable X1 := comb_meas hG (W1_integrand a hbH S)
  have hlog : (fun ω => Real.log (Standalone.DiffusionMeetingPricing.G M Q S a b ω)) =ᵐ[Q]
      fun ω => c + X1 ω := by
    filter_upwards [G_eq hG ha hab hbH S] with ω h
    rw [h, Real.log_exp]
    ring
  have hac : Standalone.DiffusionMeetingPricing.QS M Q S ≪ Q :=
    withDensity_absolutelyContinuous _ _
  have hlog' : (fun ω => Real.log (Standalone.DiffusionMeetingPricing.G M Q S a b ω)) =ᵐ[
      Standalone.DiffusionMeetingPricing.QS M Q S] fun ω => c + X1 ω := hac.ae_le hlog
  have hmap : (Standalone.DiffusionMeetingPricing.QS M Q S).map X1 =
      gaussianReal (-1 * cov M H (fun n => w 0 S (M.T n)) (Wf 0 S) (β1 M a b S) (W1 a b S))
        (var M H (β1 M a b S) (W1 a b S)).toNNReal := by
    rw [QS_eq hG hS hSH]
    exact tilt hG hH _ _ (Wf_integrand (a := 0) hSH) (W1_integrand a hbH S) (by norm_num)
  refine ⟨(measurable_const.add hX1).aemeasurable.congr hlog'.symm, ?_⟩
  rw [Measure.map_congr hlog', show (fun ω => c + X1 ω) = (fun x => c + x) ∘ X1 from rfl,
    ← Measure.map_map (measurable_const_add c) hX1, hmap, gaussianReal_map_const_add,
    q_eq hσ hB hS hSH hab hbH, z_eq hT hσ hB hS hSH hab hbH]
  congr 1
  have k1 := key hσ hB ha hab hbH
  have k2 := var_split hG (a := a) hbH S
  rw [q_eq hσ hB hS hSH hab hbH] at k2
  simp only [mdiff, Real.log_exp, c]
  linarith

lemma pricingS : Standalone.DiffusionMeetingPricing.pricingStatement := by
  intro Ω _ N Q _ M H hG a b ha hab hbH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmono, hFle, -⟩ := id hG
  refine ⟨by simpa using integrable_rate hG ha hab hbH 1, fun t => integrable_condExp,
    fun s t hst => condExp_condExp_of_le (hmono hst) (hFle t), G_zero hG ha hab hbH,
    fun S hS hSH => ?_⟩
  have hH : 0 ≤ H := hS.trans hSH
  have hprob : IsProbabilityMeasure (Standalone.DiffusionMeetingPricing.QS M Q S) := by
    rw [QS_eq hG hS hSH]
    exact isProbabilityMeasure_tilted (exp_comb hG hH _ (Wf_integrand (a := 0) hSH) (-1)).1
  have hlaw := law_logG hG hS hSH ha hab hbH
  refine ⟨(disc_mean hG hS hSH).2, hprob, hlaw, fun K => ?_⟩
  have hq : 0 ≤ qdiff M S a b := by
    obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
    rw [← q_eq hσ hB hS hSH hab hbH]
    exact var_nonneg hG hH _ _
  have hi := hlaw.integral_comp (f := fun x => max (Real.exp x - K) 0) (by fun_prop)
  rw [C0177, Real.coe_toNNReal _ hq, ← hi, QS_eq hG hS hSH, integral_tilted]
  have hP : 0 < P0 M S := Real.exp_pos _
  have hpos : ∀ᵐ ω ∂Q, 0 < Standalone.DiffusionMeetingPricing.G M Q S a b ω := by
    filter_upwards [G_eq hG ha hab hbH S] with ω h
    rw [h]; exact Real.exp_pos _
  rw [integral_congr_ae (g := fun ω => (disc M S ω *
      max (Standalone.DiffusionMeetingPricing.G M Q S a b ω - K) 0) / P0 M S), integral_div,
    call]
  · field_simp
  · filter_upwards [dens_ae hG hS hSH, hpos] with ω h1 h2
    simp only [Function.comp_apply, smul_eq_mul, Real.exp_log h2]
    rw [h1]
    ring

end

open Filter Topology in
lemma surfaceS : Standalone.DiffusionMeetingPricing.surfaceStatement := by
  intro P m q hP hm
  open Novel.CompoundedFuturesIdentificationProof in
  -- `−∂_K (P · C0177 m q) → P` as `K ↓ 0`
  have hlim : ∀ (P m : ℝ) (q : NNReal), 0 < P → 0 < m →
      Tendsto (fun K => -deriv (fun K => P * C0177 m q K) K) (𝓝[>] 0) (𝓝 P) := by
    intro P m q hP hm
    rcases (zero_le : 0 ≤ q).eq_or_lt with hq | hq
    · subst hq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hm] with K hK
      have hd : HasDerivAt (fun K => P * C0177 m 0 K) (P * (-1)) K := by
        refine ((hasDerivAt_id K).const_sub m |>.const_mul P).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds hK.2] with x hx
        rw [C0177_zero hm, max_eq_left (by linarith [mem_Iio.1 hx])]
        rfl
      rw [hd.deriv]; ring
    · have hD : Tendsto (D01713 m q) (𝓝[>] 0) atTop := by
        have hl : Tendsto (fun K => -Real.log K) (𝓝[>] 0) atTop :=
          tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
        have := (tendsto_atTop_add_const_left _ (Real.log m - (q : ℝ) / 2) hl).atTop_div_const
          (Real.sqrt_pos.2 (NNReal.coe_pos.2 hq))
        refine this.congr fun K => ?_
        simp only [D01713]; ring
      have hΦ := (tendsto_cdf_atTop (μ := gaussianReal 0 1)).comp hD
      have : Tendsto (fun K => P * Φ (D01713 m q K)) (𝓝[>] 0) (𝓝 P) := by
        have h := hΦ.const_mul P
        rw [mul_one] at h
        exact h
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with K hK
      rw [((C0177_deriv hm hK q hq).const_mul P).deriv]
      ring
  refine ⟨fun K hK hq => ?_, fun K hq => ?_, hlim P m q hP hm,
    (Novel.CompoundedFuturesIdentificationProof.C0177_limit hm q).const_mul P, ?_,
    fun P' m' q' hP' hm' => ⟨fun he => ?_, ?_⟩⟩
  · rw [Novel.CompoundedFuturesIdentificationProof.C0177_pos hm hK q hq]
  · subst hq; rw [Novel.CompoundedFuturesIdentificationProof.C0177_zero hm]
  · have := Novel.CompoundedFuturesIdentificationProof.C0177_recover_q hm q
    rw [q0178] at this
    rwa [mul_div_mul_left _ _ hP.ne']
  · have hev : (fun K => P * C0177 m q K) =ᶠ[𝓝[>] 0] fun K => P' * C0177 m' q' K := by
      filter_upwards [self_mem_nhdsWithin] with K hK using he K hK
    have hd : (fun K => -deriv (fun K => P * C0177 m q K) K) =ᶠ[𝓝[>] 0]
        fun K => -deriv (fun K => P' * C0177 m' q' K) K := by
      filter_upwards [self_mem_nhdsWithin] with K hK
      rw [Filter.EventuallyEq.deriv_eq]
      filter_upwards [Ioi_mem_nhds hK] with x hx using he x hx
    have hPP : P = P' := tendsto_nhds_unique ((hlim P m q hP hm).congr' hd) (hlim P' m' q' hP' hm')
    subst hPP
    have := (Novel.CompoundedFuturesIdentificationProof.C0177_surface hm hm' q q').1
      fun K hK => mul_left_cancel₀ hP.ne' (he K hK)
    exact ⟨rfl, this⟩
  · rintro ⟨rfl, rfl, rfl⟩ K _; rfl

lemma accumulationS : Standalone.DiffusionMeetingPricing.accumulationStatement := by
  intro Ω N M S a b hT hσ ⟨B, hB⟩ hS hSa hab
  have hw : ∀ s, s ≤ S → w a b s = b - a := fun s hs => by
    rw [w, max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  have hstep : ∀ i, ∫ x in (0:ℝ)..S, (if M.T i ≤ x then M.v i else 0) =
      if M.T i ≤ S then (S - M.T i) * M.v i else 0 := fun i => by
    have := int_step hS (M.T i) (M.v i) 0
    simp only [zero_mul, add_zero] at this
    rw [this, w, max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith [not_le.1 h])]; ring
  have iprim : IntervalIntegrable (fun x => ∫ s in (0:ℝ)..x, M.g s) volume 0 S :=
    (intervalIntegral.continuous_primitive
      (fun x y => Novel.SpliceCrossTermDriftProof.ii_bdd hσ B hB x y) 0).intervalIntegrable 0 S
  have istep : ∀ i, IntervalIntegrable (fun x => if M.T i ≤ x then M.v i else 0) volume 0 S :=
    fun i => by simpa using step_ii (M.T i) (M.v i) 0 0 S
  have hz1 : zdiff M S a b = (b - a) * (∑ i, (if M.T i ≤ S then (S - M.T i) * M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * (S - s)) := by
    unfold zdiff
    rw [mul_add, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [j]
      split_ifs with h
      · rw [hw _ h]; ring
      · ring
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hS] at hs
      simp only [hw s hs.2]; ring
  refine ⟨?_, hz1, ?_, ?_⟩
  · unfold qdiff Qacc
    rw [mul_add, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [k]
      split_ifs with h
      · rw [hw _ h]
      · simp
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hS] at hs
      simp only [hw s hs.2]; ring
  · rw [hz1]
    congr 1
    unfold Qacc
    have isum : IntervalIntegrable (fun x => ∑ i, (if M.T i ≤ x then M.v i else 0)) volume 0 S := by
      have := IntervalIntegrable.sum Finset.univ fun i _ => istep i
      convert this using 1
      funext x
      simp [Finset.sum_apply]
    rw [intervalIntegral.integral_add isum iprim,
      intervalIntegral.integral_finsetSum fun i _ => istep i,
      Novel.DiffusionMeetingIdentitiesProof.accumulatedS M.g hσ ⟨B, hB⟩ S hS]
    simp only [hstep]
  · rw [mdiff, Real.log_exp]; ring

theorem diffusionMeetingPricing : Standalone.DiffusionMeetingPricing.statement :=
  ⟨pricingS, surfaceS, accumulationS⟩

end Novel.DiffusionMeetingPricingProof

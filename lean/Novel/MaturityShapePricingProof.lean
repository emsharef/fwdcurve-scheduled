import Standalone.MaturityShapePricing
import Novel.MaturityShapeGaussProof
import Novel.DiffusionMeetingPricingProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Standalone.CompoundedFuturesIdentification Standalone.MaturityShapeIdentities
open Standalone.MaturityShapeGauss Standalone.MaturityShapePricing
open Standalone.DiffusionMeetingGauss (Integrand)
open Novel.MaturityShapeGaussProof
open Novel.DiffusionMeetingPricingProof (bdd_of_integrand integrand_add integrand_indicator)
namespace Novel.MaturityShapePricingProof

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {N : ℕ} {Q : Measure Ω} {M : ShapeModel Ω N} {φ : ℝ → ℝ → ℝ} {H : ℝ}

lemma WtI (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (hbH : b ≤ H) : Integrand (Wt φ a b) 0 H := by
  obtain ⟨-, -, -, -, -, -, -, hφ, ⟨C, hC⟩, -⟩ := hG
  exact Wt_integrand hφ hC hbH

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
noncomputable def cov (M : ShapeModel Ω N) (H : ℝ) (β : Fin N → ℝ) (f : ℝ → ℝ) (γ : Fin N → ℝ)
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

lemma comb_add (hG : ShapeGaussLaw M φ Q H) (β γ : Fin N → ℝ) {f g : ℝ → ℝ} (hf : Integrand f 0 H)
    (hg : Integrand g 0 H) (c : ℝ) :
    (fun ω => comb M β f ω + c * comb M γ g ω) =ᵐ[Q]
      comb M (fun i => β i + c * γ i) (fun s => f s + c * g s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlin, -⟩ := hG
  filter_upwards [hlin f g c hf hg] with ω hω
  have e : ∑ i, (β i + c * γ i) * M.Z i ω = ∑ i, β i * M.Z i ω + c * ∑ i, γ i * M.Z i ω := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [comb, hω, e]
  ring

/-- The law of a combination under the tilt by another: the Gaussian shift. -/
lemma tilt [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) (hH : 0 ≤ H) (β γ : Fin N → ℝ)
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
noncomputable def β1 (M : ShapeModel Ω N) (a b t : ℝ) (i : Fin N) : ℝ :=
  if M.T i ≤ t then w a b (M.T i) else 0
noncomputable def β2 (M : ShapeModel Ω N) (a b t : ℝ) (i : Fin N) : ℝ :=
  if M.T i ≤ t then 0 else w a b (M.T i)

/-- The Fubini integrand before `t`, and after. -/
noncomputable def W1 (φ : ℝ → ℝ → ℝ) (a b t : ℝ) : ℝ → ℝ := (Iic t).indicator (Wt φ a b)
noncomputable def W2 (φ : ℝ → ℝ → ℝ) (a b t : ℝ) : ℝ → ℝ := (Ioi t).indicator (Wt φ a b)

lemma W1_integrand (hG : ShapeGaussLaw M φ Q H) (a : ℝ) {b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    Integrand (W1 φ a b t) 0 H :=
  integrand_indicator (WtI hG hbH) measurableSet_Iic fun _ _ h1 h2 => ⟨h1, h2⟩

lemma W1_integrand' (hG : ShapeGaussLaw M φ Q H) (a : ℝ) {b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    Integrand (W1 φ a b t) 0 t :=
  integrand_indicator (WtI hG hbH) measurableSet_Iic fun _ hs h1 _ => ⟨h1, hs⟩

lemma W2_integrand (hG : ShapeGaussLaw M φ Q H) (a : ℝ) {b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    Integrand (W2 φ a b t) 0 H :=
  integrand_indicator (WtI hG hbH) measurableSet_Ioi fun _ _ h1 h2 => ⟨h1, h2⟩

lemma comb_split (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    comb M (fun n => w a b (M.T n)) (Wt φ a b) =ᵐ[Q]
      fun ω => comb M (β1 M a b t) (W1 φ a b t) ω + 1 * comb M (β2 M a b t) (W2 φ a b t) ω := by
  have h := comb_add hG (β1 M a b t) (β2 M a b t) (W1_integrand hG a hbH t) (W2_integrand hG a hbH t) 1
  have e1 : (fun i => β1 M a b t i + 1 * β2 M a b t i) = fun n => w a b (M.T n) := by
    funext i; simp only [β1, β2]; split_ifs <;> ring
  have e2 : (fun s => W1 φ a b t s + 1 * W2 φ a b t s) = Wt φ a b := by
    funext s
    by_cases hs : s ≤ t
    · simp [W1, W2, indicator, hs, not_lt.2 hs]
    · simp [W1, W2, indicator, hs, not_le.1 hs]
  rw [e1, e2] at h
  exact h.symm

lemma var_split (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (hbH : b ≤ H) (t : ℝ) :
    var M H (β1 M a b t) (W1 φ a b t) + var M H (β2 M a b t) (W2 φ a b t) =
      var M H (fun n => w a b (M.T n)) (Wt φ a b) := by
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have i1 := prod_ii hσ hB (W1_integrand hG a hbH t) (W1_integrand hG a hbH t) 0 H
  have i2 := prod_ii hσ hB (W2_integrand hG a hbH t) (W2_integrand hG a hbH t) 0 H
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

lemma integrable_rate [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbH : b ≤ H) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ∫ u in a..b, rate M φ u ω)) Q := by
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  refine (((exp_comb hG hH (fun n => w a b (M.T n)) (WtI hG (a := a) hbH) c).1).const_mul
    (Real.exp (c * Cst M φ a b))).congr ?_
  filter_upwards [rate_ae hG ha hab hbH] with ω h
  simp only [h, ← Real.exp_add]
  ring_nf

/-- `G_t = exp(Cst + Σ_{T_i ≤ t} w_i Z_i + I(w 1_{≤ t}) + ½ Var(the rest))`. -/
lemma G_eq [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) (t : ℝ) :
    Standalone.MaturityShapePricing.G M φ Q t a b =ᵐ[Q] fun ω => Real.exp (Cst M φ a b + comb M (β1 M a b t) (W1 φ a b t) ω +
      var M H (β2 M a b t) (W2 φ a b t) / 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, hZF, hIF, hind⟩ := id hG
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  set X1 := comb M (β1 M a b t) (W1 φ a b t)
  set X2 := comb M (β2 M a b t) (W2 φ a b t)
  have hX1 : StronglyMeasurable[M.F t] (fun ω => Real.exp (Cst M φ a b + X1 ω)) := by
    refine Measurable.stronglyMeasurable (Real.measurable_exp.comp (measurable_const.add ?_))
    refine (Finset.measurable_sum _ fun n _ => ?_).add (hIF _ t (W1_integrand' hG a hbH t))
    by_cases h : M.T n ≤ t
    · simp only [β1, h, ite_true]; exact measurable_const.mul (hZF n t h)
    · simp only [β1, h, ite_false, zero_mul]; exact measurable_const
  have hX2m : Measurable X2 := comb_meas hG (W2_integrand hG a hbH t)
  have hind2 : Indep (MeasurableSpace.comap X2 inferInstance) (M.F t) Q := by
    refine hind t _ _ (fun i hi => ?_) (W2_integrand hG a hbH t) (fun s hs => ?_)
    · simp only [β2] at hi
      split_ifs at hi with h
      · exact absurd rfl hi
      · exact not_le.1 h
    · simp only [W2, indicator] at hs
      split_ifs at hs with h
      · exact h
      · exact absurd rfl hs
  have he : (fun ω => Real.exp (∫ u in a..b, rate M φ u ω)) =ᵐ[Q]
      (fun ω => Real.exp (Cst M φ a b + X1 ω)) * fun ω => Real.exp (X2 ω) := by
    filter_upwards [rate_ae hG ha hab hbH, comb_split hG (a := a) hbH t] with ω h1 h2
    simp only [X1, X2, Pi.mul_apply, h1, h2, ← Real.exp_add]
    ring_nf
  have hint : Integrable (fun ω => Real.exp (∫ u in a..b, rate M φ u ω)) Q := by
    simpa using integrable_rate hG ha hab hbH 1
  have hint2 : Integrable (fun ω => Real.exp (X2 ω)) Q := by
    simpa using (exp_comb hG hH (β2 M a b t) (W2_integrand hG a hbH t) 1).1
  have hE2 : ∫ ω, Real.exp (X2 ω) ∂Q = Real.exp (var M H (β2 M a b t) (W2 φ a b t) / 2) := by
    simpa using (exp_comb hG hH (β2 M a b t) (W2_integrand hG a hbH t) 1).2
  have hc := condExp_indep_eq (f := fun ω => Real.exp (X2 ω))
    (m₁ := MeasurableSpace.comap X2 inferInstance) hX2m.comap_le
    (hFle t) (Real.measurable_exp.comp (comap_measurable X2)).stronglyMeasurable hind2
  have hpull := condExp_mul_of_stronglyMeasurable_left hX1 (hint.congr he) hint2
  filter_upwards [condExp_congr_ae (m := M.F t) he, hpull, hc] with ω h1 h2 h3
  rw [Standalone.MaturityShapePricing.G, h1, h2, Pi.mul_apply, h3, hE2, ← Real.exp_add]

lemma futures_eq [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) :
    ∫ ω, Real.exp (∫ u in a..b, rate M φ u ω) ∂Q = Real.exp (Aint M a b + ptil M φ a b) := by
  obtain ⟨-, -, hg, ⟨B, hB⟩, -⟩ := id hG
  have hE := (exp_comb hG (ha.trans (hab.trans hbH)) (fun n => w a b (M.T n))
    (WtI hG (a := a) hbH) 1).2
  simp only [one_mul, one_pow] at hE
  rw [integral_congr_ae (g := fun ω => Real.exp (Cst M φ a b) *
      Real.exp (comb M (fun n => w a b (M.T n)) (Wt φ a b) ω))
    ((rate_ae hG ha hab hbH).mono fun ω h => by simp only [h, Real.exp_add]),
    integral_const_mul, hE, ← Real.exp_add, key hG ha hab hbH]

/-- `G_0 = exp(A + p)`. -/
lemma G_zero [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ H) :
    Standalone.MaturityShapePricing.G M φ Q 0 a b =ᵐ[Q]
      fun _ => Real.exp (Aint M a b + ptil M φ a b) := by
  obtain ⟨hT, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFle, -⟩ := id hG
  have hH : 0 ≤ H := ha.trans (hab.trans hbH)
  have hv0 : var M H (β1 M a b 0) (W1 φ a b 0) = 0 := by
    have e1 : ∀ i, β1 M a b 0 i = 0 := fun i => by simp [β1, not_le.2 (hT i)]
    have e2 : ∫ s in (0:ℝ)..H, W1 φ a b 0 s ^ 2 * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    simp [var, e1, e2]
  have hX0 : ∀ᵐ ω ∂Q, comb M (β1 M a b 0) (W1 φ a b 0) ω = 0 := by
    have hm := comb_law hG (β1 M a b 0) (W1_integrand hG a hbH 0)
    rw [hv0, Real.toNNReal_zero, gaussianReal_zero_var] at hm
    have h := congrArg (fun μ : Measure ℝ => μ {0}ᶜ) hm
    rw [Measure.map_apply (comb_meas hG (W1_integrand hG a hbH 0))
      (measurableSet_singleton 0).compl] at h
    rw [ae_iff]
    simp at h
    exact h
  set c := Real.exp (Cst M φ a b + 0 + var M H (β2 M a b 0) (W2 φ a b 0) / 2)
  have hGc : Standalone.MaturityShapePricing.G M φ Q 0 a b =ᵐ[Q] fun _ => c := by
    filter_upwards [G_eq hG ha hab hbH 0, hX0] with ω h1 h2
    rw [h1, h2]
  have hmean : ∫ ω, Standalone.MaturityShapePricing.G M φ Q 0 a b ω ∂Q = c := by
    rw [integral_congr_ae hGc]; simp
  rw [Standalone.MaturityShapePricing.G, integral_condExp (hFle 0), futures_eq hG ha hab hbH]
    at hmean
  rw [hmean]
  exact hGc

lemma ptil_zero (hG : ShapeGaussLaw M φ Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    ptil M φ 0 S = var M H (fun n => w 0 S (M.T n)) (Wt φ 0 S) := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -, -, -, hφ, ⟨C, hC⟩, -⟩ := hG
  unfold ptil var
  rw [int_Wt hφ hC hσ hB hS hSH]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [h, d, w, max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
    ring
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [Wt_eq hs, dtil, max_eq_right hs.1, Phi, intervalIntegral.integral_same]
    ring

/-- `B_S⁻¹ = exp(−Cst) exp(−U)`, `U = Σ (S − T_n)⁺ Z_n + I (S − ·)⁺`. -/
lemma disc_ae (hG : ShapeGaussLaw M φ Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    disc M φ S =ᵐ[Q] fun ω => Real.exp (-Cst M φ 0 S) *
      Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω) := by
  filter_upwards [rate_ae hG le_rfl hS hSH] with ω h
  simp only [disc, h, ← Real.exp_add]
  ring_nf

lemma disc_mean [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {S : ℝ} (hS : 0 ≤ S)
    (hSH : S ≤ H) :
    ∫ ω, disc M φ S ω ∂Q = Real.exp (-Cst M φ 0 S) *
        ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω) ∂Q ∧
      ∫ ω, disc M φ S ω ∂Q = P0 M S := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hS.trans hSH
  have e1 : ∫ ω, disc M φ S ω ∂Q = Real.exp (-Cst M φ 0 S) *
      ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω) ∂Q := by
    rw [integral_congr_ae (disc_ae hG hS hSH), integral_const_mul]
  refine ⟨e1, ?_⟩
  rw [e1, (exp_comb hG hH _ (WtI hG (a := 0) hSH) (-1)).2, ← Real.exp_add, P0]
  have k := key (a := 0) hG le_rfl hS hSH
  rw [← ptil_zero hG hS hSH] at k
  congr 1
  rw [ptil_zero hG hS hSH] at k
  linarith

/-- The density of `Q^S` is the tilt by `−U`. -/
lemma dens_ae [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    (fun ω => Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω) /
      ∫ ω, Real.exp (-1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω) ∂Q) =ᵐ[Q]
      fun ω => disc M φ S ω / P0 M S := by
  obtain ⟨e1, e2⟩ := disc_mean hG hS hSH
  filter_upwards [disc_ae hG hS hSH] with ω h
  rw [h, ← e2, e1, mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma QS_eq [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {S : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) :
    Standalone.MaturityShapePricing.QS M φ Q S =
      Q.tilted fun ω => -1 * comb M (fun n => w 0 S (M.T n)) (Wt φ 0 S) ω := by
  unfold Standalone.MaturityShapePricing.QS Measure.tilted
  refine withDensity_congr_ae ?_
  filter_upwards [dens_ae hG hS hSH] with ω h
  rw [h]

lemma q_eq (hG : ShapeGaussLaw M φ Q H) {S a b : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) (_hab : a ≤ b)
    (hbH : b ≤ H) : var M H (β1 M a b S) (W1 φ a b S) = qtil M φ S a b := by
  obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  unfold var qtil
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [β1, k]
    split_ifs <;> ring
  · have i1 : ∀ x y, IntervalIntegrable (fun s => W1 φ a b S s ^ 2 * M.g s) volume x y :=
      fun x y => by
        simpa only [sq] using prod_ii hσ hB (W1_integrand hG a hbH S) (W1_integrand hG a hbH S) x y
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 S) (i1 S H)]
    have z : ∫ s in S..H, W1 φ a b S s ^ 2 * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hSH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [W1, indicator_of_mem (show s ∈ Iic S from hs.2)]
    ring

lemma z_eq (hG : ShapeGaussLaw M φ Q H) {S a b : ℝ} (hS : 0 ≤ S) (hSH : S ≤ H) (_hab : a ≤ b)
    (hbH : b ≤ H) :
    cov M H (fun n => w 0 S (M.T n)) (Wt φ 0 S) (β1 M a b S) (W1 φ a b S) = ztil M φ S a b := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  unfold cov ztil
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [β1, j]
    split_ifs with h
    · rw [w, max_eq_left (sub_nonneg.2 h), max_eq_right (by linarith [hT i] : (0:ℝ) - M.T i ≤ 0)]
      ring
    · ring
  · have i1 : ∀ x y, IntervalIntegrable (fun s => Wt φ 0 S s * W1 φ a b S s * M.g s) volume x y :=
      prod_ii hσ hB (WtI hG (a := 0) hSH) (W1_integrand hG a hbH S)
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1 0 S) (i1 S H)]
    have z : ∫ s in S..H, Wt φ 0 S s * W1 φ a b S s * M.g s = 0 := by
      rw [intervalIntegral.integral_of_le hSH, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0:ℝ)) fun s hs => by simp [W1, indicator, not_le.2 hs.1]]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    simp only [W1, indicator_of_mem (show s ∈ Iic S from hs.2), Wt_eq hs, max_eq_right hs.1, Phi]
    ring

/-- Under `Q^S`, `log G_S ~ N(log m − q/2, q)`. -/
lemma law_logG [IsProbabilityMeasure Q] (hG : ShapeGaussLaw M φ Q H) {S a b : ℝ} (hS : 0 ≤ S)
    (hSH : S ≤ H) (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ H) :
    HasLaw (fun ω => Real.log (Standalone.MaturityShapePricing.G M φ Q S a b ω))
      (gaussianReal (Real.log (mtil M φ S a b) - qtil M φ S a b / 2) (qtil M φ S a b).toNNReal)
      (Standalone.MaturityShapePricing.QS M φ Q S) := by
  obtain ⟨hT, -, hσ, ⟨B, hB⟩, -⟩ := id hG
  have hH : 0 ≤ H := hS.trans hSH
  set c := Cst M φ a b + var M H (β2 M a b S) (W2 φ a b S) / 2
  set X1 := comb M (β1 M a b S) (W1 φ a b S)
  have hX1 : Measurable X1 := comb_meas hG (W1_integrand hG a hbH S)
  have hlog : (fun ω => Real.log (Standalone.MaturityShapePricing.G M φ Q S a b ω)) =ᵐ[Q]
      fun ω => c + X1 ω := by
    filter_upwards [G_eq hG ha hab hbH S] with ω h
    rw [h, Real.log_exp]
    ring
  have hac : Standalone.MaturityShapePricing.QS M φ Q S ≪ Q :=
    withDensity_absolutelyContinuous _ _
  have hlog' : (fun ω => Real.log (Standalone.MaturityShapePricing.G M φ Q S a b ω)) =ᵐ[
      Standalone.MaturityShapePricing.QS M φ Q S] fun ω => c + X1 ω := hac.ae_le hlog
  have hmap : (Standalone.MaturityShapePricing.QS M φ Q S).map X1 =
      gaussianReal (-1 * cov M H (fun n => w 0 S (M.T n)) (Wt φ 0 S) (β1 M a b S) (W1 φ a b S))
        (var M H (β1 M a b S) (W1 φ a b S)).toNNReal := by
    rw [QS_eq hG hS hSH]
    exact tilt hG hH _ _ (WtI hG (a := 0) hSH) (W1_integrand hG a hbH S) (by norm_num)
  refine ⟨(measurable_const.add hX1).aemeasurable.congr hlog'.symm, ?_⟩
  rw [Measure.map_congr hlog', show (fun ω => c + X1 ω) = (fun x => c + x) ∘ X1 from rfl,
    ← Measure.map_map (measurable_const_add c) hX1, hmap, gaussianReal_map_const_add,
    q_eq hG hS hSH hab hbH, z_eq hG hS hSH hab hbH]
  congr 1
  have k1 := key hG ha hab hbH
  have k2 := var_split hG (a := a) hbH S
  rw [q_eq hG hS hSH hab hbH] at k2
  simp only [mtil, Real.log_exp, c]
  linarith

lemma pricingS : Standalone.MaturityShapePricing.pricingStatement := by
  intro Ω _ N Q _ M φ H hG a b ha hab hbH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmono, hFle, -⟩ := id hG
  refine ⟨by simpa using integrable_rate hG ha hab hbH 1, fun t => integrable_condExp,
    fun s t hst => condExp_condExp_of_le (hmono hst) (hFle t), G_zero hG ha hab hbH,
    fun S hS hSH => ?_⟩
  have hH : 0 ≤ H := hS.trans hSH
  have hprob : IsProbabilityMeasure (Standalone.MaturityShapePricing.QS M φ Q S) := by
    rw [QS_eq hG hS hSH]
    exact isProbabilityMeasure_tilted (exp_comb hG hH _ (WtI hG (a := 0) hSH) (-1)).1
  have hlaw := law_logG hG hS hSH ha hab hbH
  refine ⟨(disc_mean hG hS hSH).2, hprob, hlaw, fun K => ?_⟩
  have hq : 0 ≤ qtil M φ S a b := by
    obtain ⟨-, -, hσ, ⟨B, hB⟩, -⟩ := id hG
    rw [← q_eq hG hS hSH hab hbH]
    exact var_nonneg hG hH _ _
  have hi := hlaw.integral_comp (f := fun x => max (Real.exp x - K) 0) (by fun_prop)
  rw [C0177, Real.coe_toNNReal _ hq, ← hi, QS_eq hG hS hSH, integral_tilted]
  have hP : 0 < P0 M S := Real.exp_pos _
  have hpos : ∀ᵐ ω ∂Q, 0 < Standalone.MaturityShapePricing.G M φ Q S a b ω := by
    filter_upwards [G_eq hG ha hab hbH S] with ω h
    rw [h]; exact Real.exp_pos _
  rw [integral_congr_ae (g := fun ω => (disc M φ S ω *
      max (Standalone.MaturityShapePricing.G M φ Q S a b ω - K) 0) / P0 M S), integral_div,
    call]
  · field_simp
  · filter_upwards [dens_ae hG hS hSH, hpos] with ω h1 h2
    simp only [Function.comp_apply, smul_eq_mul, Real.exp_log h2]
    rw [h1]
    ring

end

lemma accumulationS : Standalone.MaturityShapePricing.accumulationStatement := by
  intro Ω N M φ S a b hT hS hSa hab
  have hδ : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hw : ∀ s, s ≤ S → w a b s = b - a := fun s hs => by
    rw [w, max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  have hW : ∀ s ∈ uIcc 0 S, Wt φ a b s = (b - a) * betaW φ a b s := fun s hs => by
    rw [uIcc_of_le hS] at hs
    rw [Wt_eq ⟨hs.1, by linarith [hs.2]⟩, max_eq_left (by linarith [hs.2]), betaW]
    field_simp
  have hq : qtil M φ S a b = (b - a) ^ 2 * (∑ i, (if M.T i ≤ S then M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * betaW φ a b s ^ 2) := by
    unfold qtil
    rw [mul_add, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [k]
      split_ifs with h
      · rw [hw _ h]
      · simp
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hW s hs]; ring
  have hz : ztil M φ S a b = (b - a) * (∑ i, (if M.T i ≤ S then (S - M.T i) * M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * (Phi φ s S * betaW φ a b s)) := by
    unfold ztil
    rw [mul_add, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [j]
      split_ifs with h
      · rw [hw _ h]; ring
      · ring
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hW s hs]; ring
  exact ⟨hq, hz, by rw [mtil, Real.log_exp]; ring⟩

theorem maturityShapePricing : Standalone.MaturityShapePricing.statement :=
  ⟨pricingS, accumulationS⟩

end Novel.MaturityShapePricingProof

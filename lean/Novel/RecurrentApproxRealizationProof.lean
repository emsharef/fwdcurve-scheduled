import Standalone.RecurrentApproxRealization
import Novel.RecurrentApproxBondProof
import Novel.RecurrentLoadingAssemblyProof

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
  Standalone.RecurrentLoadingAssembly Standalone.ExternalScaleConditions
  Standalone.RecurrentApproxEstimates Standalone.RecurrentApproxMeanSquare
  Standalone.RecurrentApproxBond Standalone.RecurrentApproxRealization
  Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingDiffusion
namespace Novel.RecurrentApproxRealizationProof

section Ito
variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)

/-- A Borel integrand bounded on compacts and zero on `[0, t]` has `I_t = 0` a.s. -/
lemma I_null (G : ℝ≥0 → ℝ) (hG : Measurable G) (hloc : ∀ T' : ℝ≥0, ∃ B, ∀ s ≤ T', |G s| ≤ B)
    (t : ℝ≥0) (h0 : ∀ s ≤ t, G s = 0) : S.I k (fun s _ => G s) t =ᵐ[S.μ] 0 := by
  have := S.isProbabilityMeasure
  have hU4 : U4 S.ℱ S.μ (fun s (_ : Ω) => G s) := by
    simpa using Novel.RecurrentLoadingDiffusionProof.U4_scaled S (fun _ _ => (1:ℝ))
      stronglyMeasurable_const 1 (fun _ _ => by simp) G hG hloc
  have hz : ∀ s ∈ Icc (0:ℝ) t, G (Real.toNNReal s) = 0 := fun s hs =>
    h0 _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hU5 : U5 S.ℱ S.μ (fun s (_ : Ω) => G s) t := by
    refine ⟨hU4, ?_⟩
    have e : ∫⁻ s in Icc (0:ℝ) t, ENNReal.ofReal (G (Real.toNNReal s) ^ 2) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => (0:ℝ≥0∞))
        (fun s hs => by simp [hz s hs])]
      simp
    simp only [e, lintegral_const, zero_mul, ENNReal.zero_lt_top]
  set H : ℝ≥0 → Ω → ℝ := fun s _ => G s
  have hM := S.int_product_martingale k k H H t hU5 hU5
  set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k H (min u t) ω * S.I k H (min u t) ω -
    ∫ s in (0 : ℝ)..(min u t : ℝ≥0), H (Real.toNNReal s) ω * H (Real.toNNReal s) ω *
      S.c k k (Real.toNNReal s) with hMdef
  have hcond : S.μ[M t | S.ℱ 0] =ᵐ[S.μ] M 0 := hM.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t)
  have hM0 : M 0 =ᵐ[S.μ] 0 := by
    filter_upwards [S.int_zero k H hU5.1] with ω hω
    simp [hMdef, hω]
  have hD : ∫ s in (0:ℝ)..t, G (Real.toNNReal s) * G (Real.toNNReal s) * S.c k k (Real.toNNReal s)
      = 0 := by
    have hEq : EqOn (fun s : ℝ => G (Real.toNNReal s) * G (Real.toNNReal s) * S.c k k (Real.toNNReal s))
        (fun _ => (0:ℝ)) (uIcc 0 (t:ℝ)) := fun s hs => by
      rw [uIcc_of_le t.coe_nonneg] at hs
      simp [hz s hs]
    rw [intervalIntegral.integral_congr hEq]; simp
  have hMt : M t = fun ω => (S.I k H t ω) ^ 2 := by
    funext ω
    simp only [hMdef, min_self, sq, H, hD, sub_zero]
  have hL2 : MemLp (S.I k H t) 2 S.μ := (S.int_martingale k H t hU5).2 t le_rfl
  have hint : ∫ ω, M t ω ∂S.μ = 0 := by
    calc ∫ ω, M t ω ∂S.μ = ∫ ω, (S.μ[M t | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
      _ = ∫ ω, M 0 ω ∂S.μ := integral_congr_ae hcond
      _ = 0 := by rw [integral_congr_ae hM0]; simp
  rw [hMt] at hint
  have hsq := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hL2.integrable_sq).1 hint
  filter_upwards [hsq] with ω hω
  simpa using hω

end Ito

section MS
open Novel.RecurrenceNecessityGaussianProof (det_U4 det_U5 isometry)
open Novel.RecurrentApproxMeanSquareProof (sigT_meas sigT_bound alpha_ii mean_zero)
open Novel.RecurrentApproxEstimatesProof (meanS)

/-- (48.5) for a Brownian driver: as `RecurrentApproxMeanSquare`, with the isometry in place of
`c_kk ≡ 1`. -/
theorem meanSquare_brownian {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (hBr : IsPreBrownianReal (S.B k) S.μ) {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam f0 : ℝ → ℝ}
    {H Λ ε Abar : ℝ} (h : Hyp048 Tm a a' lam H Λ ε Abar) (t : ℝ≥0) {T : ℝ} (htT : (t:ℝ) ≤ T)
    (hTH : T ≤ H) :
    ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ ≤
      ε ^ 2 * (Λ ^ 2 * H + Abar ^ 2 * Λ ^ 4 * H ^ 4) := by
  have := S.isProbabilityMeasure
  have ht : (0:ℝ) ≤ t := t.2
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (htT.trans hTH)⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hb := sigT_bound h hTH (mul_nonneg hA0 hl0) (mul_nonneg hε0 hl0)
  set G := sigT Tm a lam T
  set G' := sigT Tm a' lam T
  set D : ℝ≥0 → ℝ := fun s => G s - G' s with hD
  have mG := sigT_meas Tm a h.1 T
  have mG' := sigT_meas Tm a' h.1 T
  have mD : Measurable D := mG.sub mG'
  have hU := det_U4 S G mG _ fun s => (hb s).1
  have hU' := det_U4 S G' mG' _ fun s => (hb s).2.1
  have hU5 := det_U5 S D mD _ (fun s => (hb s).2.2) t
  -- the difference
  have hlin := S.int_linear k (fun s _ => G s) (fun s _ => G' s) 1 (-1) hU hU' t
  have hfun : ((1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => G s) + (-1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => G' s) :
      ℝ≥0 → Ω → ℝ) = fun s _ => D s := by
    funext s ω; simp [hD, sub_eq_add_neg]
  rw [hfun] at hlin
  have hm : m048 Tm a a' lam t T =
      (∫ s in (0:ℝ)..t, alpha048 Tm a lam s T) - ∫ s in (0:ℝ)..t, alpha048 Tm a' lam s T :=
    intervalIntegral.integral_sub (alpha_ii h a (Or.inl rfl) ht htT hTH hA0 hl0)
      (alpha_ii h a' (Or.inr rfl) ht htT hTH hA0 hl0)
  have hae : (fun ω => fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) =ᵐ[S.μ]
      (fun ω => m048 Tm a a' lam t T + S.I k (fun s _ => sigT Tm a lam T s - sigT Tm a' lam T s) t ω) := by
    filter_upwards [hlin] with ω hω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul] at hω
    simp only [fwd048, hm]
    change _ = _ + S.I k (fun s _ => D s) t ω
    rw [hω]; ring
  -- the second moment
  set X := S.I k (fun s _ => D s) t
  have hL2 : MemLp X 2 S.μ := (S.int_martingale k _ t hU5).2 t le_rfl
  have hX1 : Integrable X S.μ := hL2.integrable one_le_two
  have hmean : ∫ ω, X ω ∂S.μ = 0 := mean_zero S k _ t hU5
  have hsec := isometry S k hBr D mD _ (fun s => (hb s).2.2) t
  have hint : ∫ s in (0:ℝ)..t, D (Real.toNNReal s) ^ 2 =
      ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have hs' : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    have hsT : s ≤ T := hs.2.trans htT
    simp only [hD, G, G', sigT, hs', hsT, ite_true]
  have heq : ∫ ω, (fwd048 S k f0 Tm a lam t T ω - fwd048 S k f0 Tm a' lam t T ω) ^ 2 ∂S.μ =
      m048 Tm a a' lam t T ^ 2 +
        ∫ s in (0:ℝ)..t, (sig048 Tm a lam s T - sig048 Tm a' lam s T) ^ 2 := by
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only at hω ⊢; rw [hω])]
    change ∫ ω, (m048 Tm a a' lam t T + X ω) ^ 2 ∂S.μ = _
    have e : (fun ω => (m048 Tm a a' lam t T + X ω) ^ 2) =
        fun ω => (m048 Tm a a' lam t T ^ 2 + 2 * m048 Tm a a' lam t T * X ω) + X ω ^ 2 := by
      funext ω; ring
    set mm := m048 Tm a a' lam t T
    rw [e, integral_add (f := fun ω => mm ^ 2 + 2 * mm * X ω) (g := fun ω => X ω ^ 2)
      ((integrable_const _).add (hX1.const_mul _)) hL2.integrable_sq,
      integral_add (f := fun _ => mm ^ 2) (g := fun ω => 2 * mm * X ω) (integrable_const _)
        (hX1.const_mul _), integral_const, integral_const_mul, hmean, ← hint, ← hsec]
    simp [X]
  obtain ⟨-, -, h3, h4⟩ := meanS Tm a a' lam H Λ ε Abar h t T ht htT hTH
  exact heq ▸ h3.trans h4

end MS

/-! ### Integrals of versions -/

/-- Two jointly measurable processes that agree a.s. at each `y ∈ [a, b]` have a.s. equal
integrals over `[a, b]` (Tonelli). -/
lemma ae_int_eq {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ] {F G : Ω × ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Icc a b, (fun ω => F (ω, y)) =ᵐ[μ] fun ω => G (ω, y)) :
    ∀ᵐ ω ∂μ, ∫ y in a..b, F (ω, y) = ∫ y in a..b, G (ω, y) := by
  set φ : Ω × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal |F q - G q|
  have hφ : Measurable φ := (continuous_abs.measurable.comp (hF.sub hG)).ennreal_ofReal
  have h1 : ∫⁻ ω, (∫⁻ y in Ioc a b, φ (ω, y)) ∂μ = 0 := by
    rw [lintegral_lintegral_swap (f := fun ω y => φ (ω, y)) hφ.aemeasurable,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) fun y hy => ?_]
    · simp
    · refine (lintegral_eq_zero_iff (hφ.comp (measurable_id.prodMk measurable_const))).2 ?_
      filter_upwards [h y ⟨hy.1.le, hy.2⟩] with ω hω
      simp [φ, hω]
  have h2 := (lintegral_eq_zero_iff hφ.lintegral_prod_right').1 h1
  filter_upwards [h2] with ω hω
  have h3 := (lintegral_eq_zero_iff (hφ.comp measurable_prodMk_left)).1 hω
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le hab]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 h3] with y hy hyI
  have := hy hyI
  simp only [φ, Function.comp_apply, Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
  linarith [abs_nonneg (F (ω, y) - G (ω, y)), le_abs_self (F (ω, y) - G (ω, y)),
    neg_abs_le (F (ω, y) - G (ω, y))]

/-! ### The realized curve -/

section Curve
variable {p r : ℕ}

lemma idx_meas (D : Finset ℝ) : Measurable fun x => idx030 x D := by
  classical
  have e : (fun x => idx030 x D) = fun x => ∑ d ∈ D, if d ≤ x then 1 else 0 := by
    funext x; rw [idx030, Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun d _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma k_meas (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (D : Finset ℝ) (ab : Fin p × Fin r) :
    Measurable fun x => k030 u M c A x D ab := by
  unfold k030
  refine ((measurable_from_nat (f := fun n => (u ᵥ* (M ^ n)) ab.1)).comp (idx_meas D)).mul ?_
  refine Continuous.measurable ?_
  simp only [vecMul, dotProduct]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (Novel.RecurrenceNecessityReductionProof.exp_entry_cont A i ab.2)

lemma K_meas (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (D : Finset ℝ) (ab : Fin p × Fin r) :
    Measurable fun x => Kvec030 u M c A x D ab :=
  Novel.MaturityShapeIdentitiesProof.meas_param measurable_const measurable_id
    (K := fun _ y => k030 u M c A y D ab) ((k_meas u M c A D ab).comp measurable_snd)

variable {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)

lemma xi_meas (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (ab : Fin p × Fin r) :
    Measurable (S.I k (xiInt Tm v M b A (fun _ _ => 1) t ab) t) := by
  have e : xiInt (Ω := Ω) Tm v M b A (fun _ _ => 1) t ab = fun s _ => (1:ℝ) *
      (Set.indicator {s | s ≤ t} (fun _ => (1:ℝ)) s * w030 Tm v M b A s t ab) := by
    funext s ω; simp only [Standalone.RecurrentLoadingDiffusion.xiInt]; ring
  rw [e]
  exact Novel.RecurrenceNecessityGaussianProof.I_measurable S k _
    (Novel.RecurrentLoadingDiffusionProof.U4_scaled S (fun _ _ => (1:ℝ)) stronglyMeasurable_const 1
      (fun _ _ => by simp) _ (Novel.RecurrentLoadingDiffusionProof.w_time_measurable Tm v M b A t ab)
      (Novel.RecurrentLoadingDiffusionProof.w_time_bounded Tm v M b A t ab)) t

lemma curve_meas (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) :
    Measurable fun q : Ω × ℝ =>
      curve031 u M c A (state030 S k Tm u v M c b A t q.1) (dist030 Tm t) (q.2 - t) := by
  unfold curve031 state030
  simp only [dotProduct, mulVec, Pi.add_apply]
  refine Finset.measurable_sum _ fun ab _ =>
    ((k_meas u M c A _ ab).comp (measurable_snd.sub_const _)).mul
      ((((xi_meas S k Tm v M b A t ab).comp measurable_fst)).add ?_ |>.add measurable_const)
  exact Finset.measurable_sum _ fun cd _ =>
    measurable_const.mul ((K_meas u M c A _ cd).comp (measurable_snd.sub_const _))

end Curve

/-! ### Claim 030's curve is the approximating curve -/

section Link
variable {p r : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
open Novel.RecurrenceNecessityGaussianProof (det_U4)
open Novel.RecurrentApproxMeanSquareProof (sigT_meas sigT_bound)

/-- For `t + x ≤ H`, the curve (48.2) with `ã` and `f_0 = 0` is Claim 030's HJM curve a.s. -/
lemma fwd_hjm {Tm : Finset ℝ} {u v : Fin p → ℝ} {M : Matrix (Fin p) (Fin p) ℝ} {c b : Fin r → ℝ}
    {A : Matrix (Fin r) (Fin r) ℝ} {a : ℕ → ℝ} {H Λ ε Abar : ℝ}
    (h : Hyp048 Tm a (loading030 u v M) (shape030 c b A) H Λ ε Abar) (t : ℝ≥0) {x : ℝ}
    (hx : 0 ≤ x) (hxH : (t:ℝ) + x ≤ H) :
    fwd048 S k (fun _ => 0) Tm (loading030 u v M) (shape030 c b A) t (t + x) =ᵐ[S.μ]
      hjm030 S k Tm u v M c b A t x := by
  set T : ℝ := (t:ℝ) + x
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, (t.coe_nonneg.trans (by linarith)).trans hxH⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hb := sigT_bound h hxH (mul_nonneg hA0 hl0) (mul_nonneg hε0 hl0)
  have hσU := (Novel.RecurrentLoadingAssemblyProof.curve Ω inferInstance S k p r Tm u v M c b A).1 T
  have hTU := det_U4 S (sigT Tm (loading030 u v M) (shape030 c b A) T) (sigT_meas _ _ h.1 T) _
    fun s => (hb s).2.1
  have hlin := S.int_linear k (fun s _ => sigma030 Tm u v M c b A s T)
    (fun s _ => sigT Tm (loading030 u v M) (shape030 c b A) T s) 1 (-1) hσU hTU t
  set Gd : ℝ≥0 → ℝ := fun s => sigma030 Tm u v M c b A s T -
    sigT Tm (loading030 u v M) (shape030 c b A) T s
  have hfun : ((1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => sigma030 Tm u v M c b A s T) +
      (-1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => sigT Tm (loading030 u v M) (shape030 c b A) T s) :
      ℝ≥0 → Ω → ℝ) = fun s _ => Gd s := by
    funext s ω; simp [Gd, sub_eq_add_neg]
  rw [hfun] at hlin
  have hnull := I_null S k Gd
    ((Novel.RecurrentLoadingDiffusionProof.sigma_time_measurable Tm u v M c b A T).sub
      (sigT_meas _ _ h.1 T))
    (fun T' => by
      obtain ⟨B1, hB1⟩ := Novel.RecurrentLoadingDiffusionProof.sigma_time_bounded Tm u v M c b A T T'
      exact ⟨B1 + Abar * Λ, fun s hs => (abs_sub _ _).trans (add_le_add (hB1 s hs) (hb s).2.1)⟩)
    t (fun s hs => by
      have hsT : (s:ℝ) ≤ T := (show (s:ℝ) ≤ t by exact_mod_cast hs).trans (by linarith)
      simp only [Gd, sigT, hsT, ite_true]
      exact sub_self _)
  filter_upwards [hlin, hnull] with ω h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul, Pi.zero_apply] at h1 h2
  simp only [fwd048, hjm030, zero_add]
  have : alpha030 Tm u v M c b A = alpha048 Tm (loading030 u v M) (shape030 c b A) := rfl
  rw [this]
  linarith

end Link

/-! ### (c) -/

theorem realizationS : realizationStatement := by
  intro Ω _ S k hBr p r u v M c b A Tm a H Λ ε Abar h
  refine ⟨fun s T => ⟨rfl, rfl⟩, fun t T htT hTH => ?_⟩
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have hcurve := (Novel.RecurrentLoadingAssemblyProof.curve Ω inferInstance S k p r Tm u v M c b A).2
  have hi : ∀ x, 0 ≤ x → (t:ℝ) + x ≤ H →
      fwd048 S k (fun _ => 0) Tm (loading030 u v M) (shape030 c b A) t (t + x) =ᵐ[S.μ]
        fun ω => curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) x :=
    fun x hx hxH => (fwd_hjm S k h t hx hxH).trans (hcurve t x hx)
  obtain ⟨hver, -, h487⟩ := Novel.RecurrentApproxBondProof.bondS Ω S k hBr r c b A Tm a
    (loading030 u v M) H Λ ε Abar h (fun _ => 0) 0 measurable_const (fun _ _ => by simp) t T htT hTH
  obtain ⟨hVm, -, hVae⟩ := hver (loading030 u v M) (Or.inr rfl)
  have hPr : Preal048 S k Tm u v M c b A t T =ᵐ[S.μ]
      P048 S k (fun _ => 0) Tm (loading030 u v M) c b A t T := by
    have := ae_int_eq (μ := S.μ)
      (F := fun q => curve031 u M c A (state030 S k Tm u v M c b A t q.1) (dist030 Tm t) (q.2 - t))
      (G := fun q => V048 S k (fun _ => 0) Tm (loading030 u v M) c b A t q.2 q.1)
      (curve_meas S k Tm u v M c b A t) hVm htT fun y hy => by
        have e1 := hi (y - t) (by linarith [hy.1]) (by linarith [hy.2])
        rw [show (t:ℝ) + (y - t) = y by ring] at e1
        exact e1.symm.trans (hVae y ⟨hy.1, hy.2.trans hTH⟩).symm
    filter_upwards [this] with ω hω
    simp only [Preal048, P048]
    rw [hω]
  refine ⟨hi, hPr, ?_, ?_⟩
  · have hT := hi (T - t) (by linarith) (by linarith)
    rw [show (t:ℝ) + (T - t) = T by ring] at hT
    have e : (fun ω => (fwd048 S k (fun _ => 0) Tm a (shape030 c b A) t T ω -
        curve031 u M c A (state030 S k Tm u v M c b A t ω) (dist030 Tm t) (T - t)) ^ 2) =ᵐ[S.μ]
        fun ω => (fwd048 S k (fun _ => 0) Tm a (shape030 c b A) t T ω -
          fwd048 S k (fun _ => 0) Tm (loading030 u v M) (shape030 c b A) t T ω) ^ 2 := by
      filter_upwards [hT] with ω hω
      rw [hω]
    rw [integral_congr_ae e]
    exact meanSquare_brownian S k hBr h t htT hTH
  · have e : (fun ω => (P048 S k (fun _ => 0) Tm a c b A t T ω -
        Preal048 S k Tm u v M c b A t T ω) ^ 2) =ᵐ[S.μ]
        fun ω => (P048 S k (fun _ => 0) Tm a c b A t T ω -
          P048 S k (fun _ => 0) Tm (loading030 u v M) c b A t T ω) ^ 2 := by
      filter_upwards [hPr] with ω hω
      rw [hω]
    rw [integral_congr_ae e]
    simpa using h487

theorem recurrentApproxRealization : Standalone.RecurrentApproxRealization.statement := realizationS

end Novel.RecurrentApproxRealizationProof

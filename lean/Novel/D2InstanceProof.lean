import Standalone.D2Instance
import Upstream.HJMScheduled
import Novel.LemmaAProof
import Novel.PiecewiseAffineIntegralProof
import Novel.RampDriftIdentifiedProof
import Novel.Theorem1Proof
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Claim 009: proof

`Standalone.D2Instance.statement`, and the instance packaged as `Upstream.HJMScheduled` (`d2`).

The proof follows `math/claims/009-d2-instance.md`, Part (a).

* (S7). `step` is a finite sum of indicators of the Borel sets `I_k`, hence Borel and bounded
  by `S = ∑_k ‖s k‖`; `∫_t^T step = F T - F t` with `F` the continuous primitive
  (`intervalIntegral.continuous_primitive`), so `(t, T) ↦ α t T` and `(t, T) ↦ σ t T` are
  Borel functions of `(t, T)`, and a deterministic Borel function is progressively measurable
  for any filtration (`isStronglyProgressive_of_measurable`). The bounds `‖σ‖ ≤ S` and
  `|α(s, u)| ≤ S² T` on `0 ≤ s ≤ u ≤ T` give the integrability fields. `ξ n` is a finite sum
  of `1_{I_k}(u) (X_{n,k} + y (u - τ k))` with `X_{n,k}` measurable for `F_{τ n}`.
* AX-01 (`drift_pointwise`). For `0 ≤ t ∈ I_j` and `T ≥ t`, Claim 007's (B) ⇒ (A)
  (`Novel.RampDriftIdentifiedProof.rampDriftIdentified`) applied to the step function
  `step` and to `α'' u = ⟪step u, ∫_t^u step⟫` for `u ≥ τ j` (and `0` below `τ j`), which is
  piecewise affine with the data `a* b*` of (7.4) on `I_k`, `k ≥ j`, by Lemma A
  (`Novel.LemmaAProof.lemmaA`) for `k > j` and by the constancy of `step` on `I_j` for `k = j`.
  `α t · = α''` and `σ t · = step` on `(t, ∞)`, so the interval integrals agree.
* AX-02 (`jump_martingale`). For `T ∈ I_k`, `k ≥ n`, Lemma C's (6.3)
  (`Novel.PiecewiseAffineIntegralProof.integral_eq`) gives (9.4), so
  `exp (-∫_{τ n}^T ξ_n) = ∏_{m=n}^k exp (-(c_m X_{n,m} + ½ y_{n,m} c_m²))` with
  `c_m = τ (m+1) - τ m` for `m < k` and `c_k = T - τ k` (9.5). This is measurable for the
  σ-algebra of the coordinates `(n, ·)`, which is independent of `F_{τ n -} ⊆ σ(X_p : p.1 ≠ n)`
  (`indep_iSup_of_disjoint` on the independent coordinates of `Measure.infinitePi`), so
  `condExp_indep_eq` reduces the conditional expectation to the expectation, which
  `iIndepFun.integral_fun_prod_comp` and `mgf_gaussianReal` evaluate to `1` (9.6).
-/

open MeasureTheory ProbabilityTheory Set
open Standalone.LemmaA Standalone.D2Instance

namespace Novel.D2InstanceProof

variable {N d : ℕ} {τ : ℕ → ℝ} {s : ℕ → EuclideanSpace ℝ (Fin d)} {y : ℕ → ℕ → NNReal}

/-! ### Intervals and the step function -/

lemma measurableSet_I (τ : ℕ → ℝ) (N k : ℕ) : MeasurableSet (I τ N k) := by
  unfold I
  split_ifs
  · exact measurableSet_Ico
  · exact measurableSet_Ici

lemma ordConnected_I (τ : ℕ → ℝ) (N k : ℕ) : (I τ N k).OrdConnected := by
  unfold I
  split_ifs
  · exact ordConnected_Ico
  · exact ordConnected_Ici

lemma self_mem_I (hτ : StrictMonoOn τ (Iic N)) {n : ℕ} (hn : n ≤ N) : τ n ∈ I τ N n :=
  LemmaAProof.mem_I_iff.2 ⟨le_rfl, fun hnN => hτ (mem_Iic.2 hn) (mem_Iic.2 hnN) (Nat.lt_succ_self n)⟩

lemma τ_mono (hτ : StrictMonoOn τ (Iic N)) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ N) :
    τ m ≤ τ n :=
  hτ.monotoneOn (mem_Iic.2 (hmn.trans hn)) (mem_Iic.2 hn) hmn

/-- The intervals are disjoint: `u ∈ I_k ∩ I_k'` forces `k = k'`. -/
lemma index_unique (hτ : StrictMonoOn τ (Iic N)) {k k' : ℕ} (hk : k ≤ N) (hk' : k' ≤ N) {u : ℝ}
    (hu : u ∈ I τ N k) (hu' : u ∈ I τ N k') : k = k' :=
  le_antisymm (PiecewiseAffineIntegralProof.index_le hτ le_rfl hk hu hu')
    (PiecewiseAffineIntegralProof.index_le hτ le_rfl hk' hu' hu)

lemma step_eq (hτ : StrictMonoOn τ (Iic N)) {k : ℕ} (hk : k ≤ N) {u : ℝ} (hu : u ∈ I τ N k) :
    step τ N s u = s k := by
  unfold step
  rw [Finset.sum_eq_single k]
  · exact indicator_of_mem hu _
  · intro b hb hbk
    exact indicator_of_notMem
      (fun hub => hbk (index_unique hτ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)) hk hub hu)) _
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) h

/-- `S = ∑_{k ≤ N} ‖s k‖` bounds the step. -/
noncomputable def S (N : ℕ) (s : ℕ → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ‖s k‖

lemma S_nonneg : 0 ≤ S N s := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_step_le (u : ℝ) : ‖step τ N s u‖ ≤ S N s :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_indicator_le_norm_self _ _)

lemma measurable_step : Measurable (step τ N s) :=
  Finset.measurable_sum _ fun k _ => measurable_const.indicator (measurableSet_I τ N k)

lemma intervalIntegrable_step (a b : ℝ) : IntervalIntegrable (step τ N s) volume a b := by
  have h : ∀ a b : ℝ, IntegrableOn (step τ N s) (Ioc a b) volume := fun a b =>
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne measurable_step.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => norm_step_le u)
  exact ⟨h a b, h b a⟩

/-- `∫_t^T step = F T - F t` with `F` the primitive from `0`, a continuous function. -/
lemma measurable_integral_step :
    Measurable fun q : ℝ × ℝ => ∫ u in q.1..q.2, step τ N s u := by
  have hF : Continuous fun x : ℝ => ∫ u in (0 : ℝ)..x, step τ N s u :=
    intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_step a b) 0
  have h : (fun q : ℝ × ℝ => ∫ u in q.1..q.2, step τ N s u) =
      fun q => (∫ u in (0 : ℝ)..q.2, step τ N s u) - ∫ u in (0 : ℝ)..q.1, step τ N s u := by
    funext q
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_step _ _)
      (intervalIntegrable_step _ _)]
  rw [h]
  exact (hF.measurable.comp measurable_snd).sub (hF.measurable.comp measurable_fst)

lemma norm_integral_step_le (t T : ℝ) : ‖∫ u in t..T, step τ N s u‖ ≤ S N s * |T - t| :=
  intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => norm_step_le u

/-! ### The coefficients `σ` and `α` -/

lemma σ_eq {t u : ℝ} (h : t ≤ u) (ω : Ω N) : σ τ N s t u ω = step τ N s u := by
  simp [σ, not_lt.2 h]

lemma σ_zero {t u : ℝ} (h : u < t) (ω : Ω N) : σ τ N s t u ω = 0 := by
  simp [σ, h]

lemma norm_σ_le (t u : ℝ) (ω : Ω N) : ‖σ τ N s t u ω‖ ≤ S N s := by
  unfold σ
  split_ifs
  · simpa using S_nonneg
  · exact norm_step_le u

lemma integral_σ {t T : ℝ} (h : t ≤ T) (ω : Ω N) :
    ∫ u in t..T, σ τ N s t u ω = ∫ u in t..T, step τ N s u :=
  intervalIntegral.integral_congr_Ioo_of_le h fun _ hu => σ_eq hu.1.le ω

lemma α_eq (t T : ℝ) (ω : Ω N) :
    α τ N s t T ω = if T < t then 0 else inner ℝ (step τ N s T) (∫ u in t..T, step τ N s u) := by
  unfold α
  split_ifs with h
  · rfl
  · rw [σ_eq (not_lt.1 h), integral_σ (not_lt.1 h)]

lemma α_zero {t T : ℝ} (h : T < t) (ω : Ω N) : α τ N s t T ω = 0 := by
  simp [α, h]

/-- `|α(s, u)| ≤ S² T` for `0 ≤ s`, `0 ≤ u ≤ T`. -/
lemma abs_α_le {t u T : ℝ} (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu : u ≤ T) (ω : Ω N) :
    |α τ N s t u ω| ≤ S N s * (S N s * T) := by
  have hS := S_nonneg (N := N) (s := s)
  rw [α_eq]
  split_ifs with h
  · simp only [abs_zero]
    exact mul_nonneg hS (mul_nonneg hS (hu0.trans hu))
  · calc |inner ℝ (step τ N s u) (∫ v in t..u, step τ N s v)|
        ≤ ‖step τ N s u‖ * ‖∫ v in t..u, step τ N s v‖ := abs_real_inner_le_norm _ _
      _ ≤ S N s * (S N s * T) := by
          refine mul_le_mul (norm_step_le u) ((norm_integral_step_le t u).trans ?_)
            (norm_nonneg _) hS
          refine mul_le_mul_of_nonneg_left ?_ hS
          rw [abs_of_nonneg (by linarith [not_lt.1 h])]
          linarith

/-- A deterministic Borel function of `(t, T)` is progressively measurable for any
filtration. -/
lemma isStronglyProgressive_of_measurable {Ω' : Type*} {m₀ : MeasurableSpace Ω'}
    (ℱ : Filtration ℝ m₀) {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {g : ℝ → ℝ → E}
    (hg : Measurable fun q : ℝ × ℝ => g q.1 q.2) :
    IsStronglyProgressive (Upstream.paramFiltration ℱ) fun t (p : ℝ × Ω') => g t p.1 := by
  intro i
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (Upstream.paramFiltration ℱ i)]
      fun p : Set.Iic i × (ℝ × Ω') => ((p.1 : ℝ), p.2.1) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_subtype_coe.comp (@measurable_fst _ _ _ (Upstream.paramFiltration ℱ i))
    · exact (@measurable_fst ℝ Ω' _ (ℱ i)).comp (@measurable_snd _ _ _ (Upstream.paramFiltration ℱ i))
  exact (hg.comp h1).stronglyMeasurable

lemma α_progMeasurable (ℱ : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N))) :
    IsStronglyProgressive (Upstream.paramFiltration ℱ) fun t (p : ℝ × Ω N) => α τ N s t p.1 p.2 := by
  have h : (fun t (p : ℝ × Ω N) => α τ N s t p.1 p.2) = fun t (p : ℝ × Ω N) =>
      if p.1 < t then (0 : ℝ) else inner ℝ (step τ N s p.1) (∫ u in t..p.1, step τ N s u) := by
    funext t p
    exact α_eq t p.1 p.2
  rw [h]
  exact isStronglyProgressive_of_measurable ℱ
    (g := fun t T => if T < t then (0 : ℝ) else inner ℝ (step τ N s T) (∫ u in t..T, step τ N s u))
    (Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
      ((measurable_step.comp measurable_snd).inner measurable_integral_step))

lemma σ_progMeasurable (ℱ : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N))) :
    IsStronglyProgressive (Upstream.paramFiltration ℱ) fun t (p : ℝ × Ω N) => σ τ N s t p.1 p.2 := by
  refine isStronglyProgressive_of_measurable ℱ (g := fun t T => if T < t then 0 else step τ N s T) ?_
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
    (measurable_step.comp measurable_snd)

lemma α_integrable (T : ℝ) (ω : Ω N) :
    ∫⁻ u in Icc 0 T, ∫⁻ t in Icc 0 u, ENNReal.ofReal |α τ N s t u ω| < ⊤ := by
  calc ∫⁻ u in Icc 0 T, ∫⁻ t in Icc 0 u, ENNReal.ofReal |α τ N s t u ω|
      ≤ ∫⁻ _ in Icc 0 T, ENNReal.ofReal (S N s * (S N s * T)) * ENNReal.ofReal T := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_)
        calc ∫⁻ t in Icc 0 u, ENNReal.ofReal |α τ N s t u ω|
            ≤ ENNReal.ofReal (S N s * (S N s * T)) * ENNReal.ofReal u :=
              Upstream.HJMScheduled.setLIntegral_Icc_le fun t ht => abs_α_le ht.1 hu.1 hu.2 ω
          _ ≤ ENNReal.ofReal (S N s * (S N s * T)) * ENNReal.ofReal T :=
              mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hu.2)
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top

lemma σ_integrable (T : ℝ) (ω : Ω N) :
    ∑ i, ∫⁻ u in Icc 0 T,
      (∫⁻ t in Icc 0 u, ENNReal.ofReal ((σ τ N s t u ω i) ^ 2)) ^ (1 / 2 : ℝ) < ⊤ := by
  have hb : ∀ t u : ℝ, ∀ i, (σ τ N s t u ω i) ^ 2 ≤ S N s ^ 2 := by
    intro t u i
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (norm_σ_le t u ω)
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  calc ∫⁻ u in Icc 0 T, (∫⁻ t in Icc 0 u, ENNReal.ofReal ((σ τ N s t u ω i) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ _ in Icc 0 T, (ENNReal.ofReal (S N s ^ 2) * ENNReal.ofReal T) ^ (1 / 2 : ℝ) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_)
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        calc ∫⁻ t in Icc 0 u, ENNReal.ofReal ((σ τ N s t u ω i) ^ 2)
            ≤ ENNReal.ofReal (S N s ^ 2) * ENNReal.ofReal u :=
              Upstream.HJMScheduled.setLIntegral_Icc_le fun t _ => hb t u i
          _ ≤ ENNReal.ofReal (S N s ^ 2) * ENNReal.ofReal T :=
              mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hu.2)
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne)
          ENNReal.ofReal_lt_top

/-! ### The coordinates and the jumps `ξ` -/

instance (N : ℕ) (y : ℕ → ℕ → NNReal) : IsProbabilityMeasure (Q N y) := by
  unfold Q
  infer_instance

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by the coordinates in `A`. -/
def coordAlg (N : ℕ) (A : Set (P N)) : MeasurableSpace (Ω N) :=
  ⨆ p ∈ A, MeasurableSpace.comap (fun ω : Ω N => ω p) inferInstance

lemma filt_apply (N : ℕ) (τ : ℕ → ℝ) (t : ℝ) :
    filt N τ t = coordAlg N {p | τ p.1.1 ≤ t} := rfl

lemma coordAlg_le (A : Set (P N)) : coordAlg N A ≤ MeasurableSpace.pi :=
  iSup₂_le fun p _ => (measurable_pi_apply p).comap_le

lemma measurable_eval_coordAlg {A : Set (P N)} {p : P N} (hp : p ∈ A) :
    Measurable[coordAlg N A] fun ω : Ω N => ω p :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun (p : P N) (_ : p ∈ A) =>
    MeasurableSpace.comap (fun ω : Ω N => ω p) inferInstance) p hp)

lemma X_eq {n k : ℕ} (h : 1 ≤ n ∧ n ≤ k ∧ k ≤ N) (ω : Ω N) : X N n k ω = ω ⟨(n, k), h⟩ := by
  simp [X, h]

lemma measurable_X_coordAlg {A : Set (P N)} {n k : ℕ} (h : 1 ≤ n ∧ n ≤ k ∧ k ≤ N)
    (hA : (⟨(n, k), h⟩ : P N) ∈ A) : Measurable[coordAlg N A] (X N n k) := by
  have : X N n k = fun ω : Ω N => ω ⟨(n, k), h⟩ := funext fun ω => X_eq h ω
  rw [this]
  exact measurable_eval_coordAlg hA

lemma measurable_X (n k : ℕ) : Measurable (X N n k) := by
  by_cases h : 1 ≤ n ∧ n ≤ k ∧ k ≤ N
  · have : X N n k = fun ω : Ω N => ω ⟨(n, k), h⟩ := funext fun ω => X_eq h ω
    rw [this]
    exact measurable_pi_apply _
  · have : X N n k = fun _ => 0 := funext fun ω => by simp [X, h]
    rw [this]
    exact measurable_const

lemma ξ_zero_of_lt (hτ : StrictMonoOn τ (Iic N)) {n : ℕ} {u : ℝ} (hu : u < τ n) (ω : Ω N) :
    ξ τ N y n u ω = 0 := by
  unfold ξ
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  refine indicator_of_notMem (fun huk => ?_) _
  have := (LemmaAProof.mem_I_iff.1 huk).1
  linarith [τ_mono hτ hk'.1 (Nat.lt_succ_iff.1 hk'.2)]

lemma ξ_eq (hτ : StrictMonoOn τ (Iic N)) {n k : ℕ} (hk : k ≤ N) (hnk : n ≤ k) {u : ℝ}
    (hu : u ∈ I τ N k) (ω : Ω N) : ξ τ N y n u ω = X N n k ω + y n k * (u - τ k) := by
  unfold ξ
  rw [Finset.sum_eq_single k]
  · exact indicator_of_mem hu _
  · intro b hb hbk
    have hb' := Finset.mem_Ico.1 hb
    exact indicator_of_notMem
      (fun hub => hbk (index_unique hτ (Nat.lt_succ_iff.1 hb'.2) hk hub hu)) _
  · intro h
    exact absurd (Finset.mem_Ico.2 ⟨hnk, Nat.lt_succ_of_le hk⟩) h

lemma ξ_measurable (hn : 1 ≤ n) :
    Measurable[MeasurableSpace.prod inferInstance (filt N τ (τ n))]
      fun p : ℝ × Ω N => ξ τ N y n p.1 p.2 := by
  let _i : MeasurableSpace (Ω N) := filt N τ (τ n)
  have hX : ∀ k, n ≤ k → k ≤ N → Measurable (X N n k) := fun k hnk hkN =>
    measurable_X_coordAlg (A := {p | τ p.1.1 ≤ τ n}) ⟨hn, hnk, hkN⟩ (le_refl (τ n))
  show Measurable fun p : ℝ × Ω N => ξ τ N y n p.1 p.2
  unfold ξ
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  have : (fun p : ℝ × Ω N => (I τ N k).indicator (fun u => X N n k p.2 + y n k * (u - τ k)) p.1)
      = (Prod.fst ⁻¹' I τ N k).indicator fun p => X N n k p.2 + y n k * (p.1 - τ k) := by
    funext p
    rfl
  rw [this]
  exact (((hX k hk'.1 (Nat.lt_succ_iff.1 hk'.2)).comp measurable_snd).add
    (measurable_const.mul (measurable_fst.sub measurable_const))).indicator
    (measurable_fst (measurableSet_I τ N k))

lemma abs_ξ_le (T : ℝ) (n : ℕ) (ω : Ω N) {u : ℝ} (hu : u ∈ Icc 0 T) :
    |ξ τ N y n u ω| ≤ ∑ k ∈ Finset.Ico n (N + 1), (|X N n k ω| + y n k * (T + |τ k|)) := by
  unfold ξ
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have h1 : |(I τ N k).indicator (fun u => X N n k ω + y n k * (u - τ k)) u| ≤
      |X N n k ω + y n k * (u - τ k)| := by
    classical
    rw [indicator_apply]
    split_ifs
    · exact le_rfl
    · simp only [abs_zero]
      exact abs_nonneg _
  refine h1.trans ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
  rw [abs_mul, NNReal.abs_eq]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ le_rfl)) (y n k).2
  rw [abs_of_nonneg hu.1]
  exact hu.2

lemma ξ_integrable (T : ℝ) (n : ℕ) (ω : Ω N) :
    ∫⁻ u in Icc 0 T, ENNReal.ofReal |ξ τ N y n u ω| < ⊤ :=
  calc ∫⁻ u in Icc 0 T, ENNReal.ofReal |ξ τ N y n u ω|
      ≤ ENNReal.ofReal (∑ k ∈ Finset.Ico n (N + 1), (|X N n k ω| + y n k * (T + |τ k|))) *
          ENNReal.ofReal T :=
        Upstream.HJMScheduled.setLIntegral_Icc_le fun _ hu => abs_ξ_le T n ω hu
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ### AX-01 -/

/-- AX-01 pointwise: for every `ω`, `0 ≤ t` and `T ≥ t`,
`∫_t^T α(t, u) du = ½ ‖∫_t^T σ(t, u) du‖²`, by Claim 007's (B) ⇒ (A). -/
lemma drift_pointwise (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (ω : Ω N) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ u in t..T, α τ N s t u ω = (1 / 2 : ℝ) * ‖∫ u in t..T, σ τ N s t u ω‖ ^ 2 := by
  obtain ⟨j, hj, htj⟩ := Theorem1Proof.exists_index (N := N) hτ0 ht
  have hτjt : τ j ≤ t := (LemmaAProof.mem_I_iff.1 htj).1
  -- Claim 007 applied to `step` and to `α''`
  set α'' : ℝ → ℝ := fun u =>
    if u < τ j then 0 else inner ℝ (step τ N s u) (∫ v in t..u, step τ N s v) with hα''
  set a : ℕ → ℝ := fun k =>
    if j ≤ k then Standalone.RampDriftIdentified.aStar τ s j k t else 0 with ha
  set b : ℕ → ℝ := fun k => if j ≤ k then Standalone.RampDriftIdentified.bStar s k else 0 with hb
  have hstep : ∀ k ≤ N, ∀ u ∈ I τ N k, step τ N s u = s k := fun k hk u hu => step_eq hτ hk hu
  have hpiece : ∀ k ≤ N, ∀ u ∈ I τ N k, α'' u = a k + (u - τ k) * b k := by
    intro k hk u hu
    have huk := LemmaAProof.mem_I_iff.1 hu
    rcases lt_or_ge k j with hkj | hjk
    · have hkN : k < N := lt_of_lt_of_le hkj hj
      have hu' : u < τ j := (huk.2 hkN).trans_le (τ_mono hτ (Nat.succ_le_of_lt hkj) hj)
      simp [hα'', ha, hb, hu', not_le.2 hkj]
    · have hu' : ¬ u < τ j := not_lt.2 ((τ_mono hτ hjk hk).trans huk.1)
      simp only [hα'', ha, hb, hu', ↓reduceIte, hjk, Standalone.RampDriftIdentified.aStar,
        Standalone.RampDriftIdentified.bStar, hstep k hk u hu]
      rcases hjk.lt_or_eq with hlt | rfl
      · -- `k > j`: Lemma A
        have htu : t ≤ u := by
          have hjN : j < N := lt_of_lt_of_le hlt hk
          exact ((LemmaAProof.mem_I_iff.1 htj).2 hjN).le.trans
            ((τ_mono hτ (Nat.succ_le_of_lt hlt) hk).trans huk.1)
        have hA := (LemmaAProof.lemmaA N d τ s (step τ N s) hτ0 hτ hstep).1 t u htu j hj k hk
          htj hu
        rw [hA.2, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
        ring
      · -- `k = j`: `step = s j` on `I_j ⊇ [t, u]`
        have hc : c τ s j j t = 0 := by simp [c]
        have hint : ∫ v in t..u, step τ N s v = (u - t) • s j := by
          rw [intervalIntegral.integral_congr (g := fun _ => s j)
            (fun v hv => hstep j hj v ((ordConnected_I τ N j).uIcc_subset htj hu hv))]
          exact intervalIntegral.integral_const _
        rw [hint, hc, inner_smul_right, real_inner_self_eq_norm_sq, max_eq_right hτjt]
        simp only [inner_zero_right]
        ring
  have h007 := RampDriftIdentifiedProof.rampDriftIdentified N d τ s (step τ N s) a b α'' hτ0 hτ
    hstep hpiece j hj t htj
  obtain ⟨-, -, hBA, -⟩ := h007
  have hB : ∀ k, j ≤ k → k ≤ N → a k = Standalone.RampDriftIdentified.aStar τ s j k t ∧
      b k = Standalone.RampDriftIdentified.bStar s k := fun k hjk _ => by simp [ha, hb, hjk]
  have hA := hBA hB T htT
  unfold Standalone.StepDriftVanish.driftCondition at hA
  rw [integral_σ htT, ← hA]
  refine intervalIntegral.integral_congr_Ioo_of_le htT fun u hu => ?_
  rw [α_eq, hα'']
  simp only [not_lt.2 hu.1.le, ↓reduceIte, not_lt.2 (hτjt.trans hu.1.le)]

/-- AX-01 in the field's form. -/
lemma drift_integrated (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) (T : ℝ) :
    ∀ᵐ p ∂((Q N y).prod (volume.restrict (Icc 0 T))),
      ∫ u in p.2..T, α τ N s p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..T, σ τ N s p.2 u p.1‖ ^ 2 := by
  rw [← Measure.restrict_univ (μ := Q N y), Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun p hp => ?_
  exact drift_pointwise hτ0 hτ p.1 hp.2.1 hp.2.2

/-! ### AX-02 -/

/-- The coordinates are independent under `Q`. -/
lemma iIndepFun_coord (N : ℕ) (y : ℕ → ℕ → NNReal) :
    iIndepFun (fun (p : P N) (ω : Ω N) => ω p) (Q N y) :=
  iIndepFun_infinitePi (X := fun (_ : P N) (x : ℝ) => x) fun _ => measurable_id

lemma hasLaw_coord (N : ℕ) (y : ℕ → ℕ → NNReal) (p : P N) :
    HasLaw (fun ω : Ω N => ω p) (gaussianReal 0 (y p.1.1 p.1.2)) (Q N y) :=
  ⟨(measurable_pi_apply p).aemeasurable, Measure.infinitePi_map_eval _ p⟩

/-- `F_{τ n -} ⊆ σ(X_p : p.1 ≠ n)`. -/
lemma leftLimit_le (τ : ℕ → ℝ) (n : ℕ) :
    Upstream.leftLimit (filt N τ) (τ n) ≤ coordAlg N {p | p.1.1 ≠ n} := by
  refine iSup₂_le fun t ht => ?_
  rw [filt_apply]
  refine iSup₂_le fun p hp => ?_
  refine le_iSup₂_of_le (f := fun (p : P N) (_ : p ∈ {p : P N | p.1.1 ≠ n}) =>
    MeasurableSpace.comap (fun ω : Ω N => ω p) inferInstance) p ?_ le_rfl
  intro hpn
  have : τ p.1.1 ≤ t := hp
  rw [hpn] at this
  exact absurd (this.trans_lt ht) (lt_irrefl _)

lemma indep_block (τ : ℕ → ℝ) (n : ℕ) :
    Indep (coordAlg N {p | p.1.1 = n}) (Upstream.leftLimit (filt N τ) (τ n)) (Q N y) := by
  refine indep_of_indep_of_le_right ?_ (leftLimit_le τ n)
  refine indep_iSup_of_disjoint (fun p => (measurable_pi_apply p).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_coord N y)) ?_
  rw [Set.disjoint_left]
  intro p hp hp'
  exact hp' hp

/-- (9.4)–(9.5): for `T ∈ I_k`, `k ≥ n`, the exponent is `∑_{m=n}^k (c_m X_{n,m} + ½ y c_m²)`
with `c_m = τ (m+1) - τ m` for `m < k` and `c_k = T - τ k`. -/
noncomputable def coef (τ : ℕ → ℝ) (k : ℕ) (T : ℝ) (m : ℕ) : ℝ :=
  if m < k then τ (m + 1) - τ m else T - τ k

lemma integral_ξ (hτ : StrictMonoOn τ (Iic N)) {n k : ℕ} (hnk : n ≤ k) (hk : k ≤ N)
    {T : ℝ} (hT : T ∈ I τ N k) (ω : Ω N) :
    ∫ u in τ n..T, ξ τ N y n u ω =
      ∑ m ∈ Finset.Ico n (k + 1),
        (coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2) := by
  have hnN : n ≤ N := hnk.trans hk
  set a : ℕ → ℝ := fun m => if n ≤ m then X N n m ω else 0 with ha
  set b : ℕ → ℝ := fun m => if n ≤ m then (y n m : ℝ) else 0 with hb
  have hg : ∀ m ≤ N, ∀ u ∈ I τ N m, ξ τ N y n u ω = a m + (u - τ m) • b m := by
    intro m hm u hu
    rcases le_or_gt n m with hnm | hmn
    · rw [ξ_eq hτ hm hnm hu]
      simp [ha, hb, hnm, mul_comm]
    · have hmN : m < N := lt_of_lt_of_le hmn hnN
      have hu' : u < τ n :=
        ((LemmaAProof.mem_I_iff.1 hu).2 hmN).trans_le (τ_mono hτ (Nat.succ_le_of_lt hmn) hnN)
      rw [ξ_zero_of_lt hτ hu']
      simp [ha, hb, not_le.2 hmn]
  have hτnT : τ n ≤ T := (τ_mono hτ hnk hk).trans (LemmaAProof.mem_I_iff.1 hT).1
  rw [PiecewiseAffineIntegralProof.integral_eq hτ hg hτnT hnN hk (self_mem_I hτ hnN) hT]
  have hmax : max (τ k) (τ n) = τ k := max_eq_left (τ_mono hτ hnk hk)
  rw [hmax, Finset.sum_Ico_succ_top hnk]
  have hlast : coef τ k T k = T - τ k := by simp [coef]
  have hsum : ∑ m ∈ Finset.Ico n k,
      (coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2) =
      Standalone.PiecewiseAffineIntegral.e τ a b n k (τ n) := by
    rcases hnk.lt_or_eq with hlt | rfl
    · simp only [Standalone.PiecewiseAffineIntegral.e, hlt, ↓reduceIte]
      rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      have h1 : ∀ m ∈ Finset.Ico (n + 1) k,
          coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2 =
          (τ (m + 1) - τ m) • a m + ((τ (m + 1) - τ m) ^ 2 / 2) • b m := by
        intro m hm
        have hm' := Finset.mem_Ico.1 hm
        simp only [coef, hm'.2, ↓reduceIte, ha, hb, (Nat.le_succ n).trans hm'.1, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl h1]
      simp only [coef, hlt, ↓reduceIte, ha, hb, le_refl, smul_eq_mul, sub_self]
      ring
    · simp [Standalone.PiecewiseAffineIntegral.e]
  rw [hsum, hlast]
  simp only [ha, hb, hnk, ↓reduceIte, smul_eq_mul, sub_self]
  ring

/-- (9.6): the expectation of the exponential factor is `1`. -/
lemma integral_exp_eq_one (hn : 1 ≤ n) (hk : k ≤ N) (T : ℝ) :
    ∫ ω, ∏ m ∈ Finset.Ico n (k + 1),
        Real.exp (-(coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2)) ∂(Q N y)
      = 1 := by
  -- the coordinates of the block, indexed by `Finset.Ico n (k + 1)`
  let g : ↥(Finset.Ico n (k + 1)) → P N := fun m =>
    ⟨(n, m.1), ⟨hn, (Finset.mem_Ico.1 m.2).1, (Nat.lt_succ_iff.1 (Finset.mem_Ico.1 m.2).2).trans hk⟩⟩
  have hg : Function.Injective g := by
    intro m m' h
    have := congrArg (fun p : P N => p.1.2) h
    exact Subtype.ext this
  have hind : iIndepFun (fun (m : ↥(Finset.Ico n (k + 1))) (ω : Ω N) => X N n m ω) (Q N y) := by
    have h := (iIndepFun_coord N y).precomp hg
    convert h using 2 with m
    funext ω
    exact X_eq _ ω
  let f : ↥(Finset.Ico n (k + 1)) → ℝ → ℝ := fun m x =>
    Real.exp (-(coef τ k T m * x + (y n m : ℝ) * coef τ k T m ^ 2 / 2))
  have hf : ∀ m, Continuous (f m) := fun m => by fun_prop
  have hprod : ∀ ω : Ω N, (∏ m ∈ Finset.Ico n (k + 1),
      Real.exp (-(coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2))) =
      ∏ m : ↥(Finset.Ico n (k + 1)), f m (X N n m ω) := fun ω =>
    (Finset.prod_coe_sort (Finset.Ico n (k + 1)) fun m =>
      Real.exp (-(coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2))).symm
  simp_rw [hprod]
  rw [hind.integral_fun_prod_comp (fun m => (measurable_X n m).aemeasurable)
    (fun m => (hf m).aestronglyMeasurable)]
  refine Finset.prod_eq_one fun m _ => ?_
  -- one factor: `exp (-½ y c²) · mgf (-c) = 1`
  have hlaw : HasLaw (X N n m) (gaussianReal 0 (y n m)) (Q N y) := by
    have h := hasLaw_coord N y (g m)
    have hX : (fun ω : Ω N => ω (g m)) = X N n m := funext fun ω => (X_eq _ ω).symm
    rwa [hX] at h
  have hmgf := mgf_gaussianReal hlaw (-coef τ k T m)
  unfold mgf at hmgf
  have h1 : (fun ω => f m (X N n m ω)) = fun ω =>
      Real.exp (-((y n m : ℝ) * coef τ k T m ^ 2 / 2)) *
        Real.exp (-coef τ k T m * X N n m ω) := by
    funext ω
    simp only [f]
    rw [← Real.exp_add]
    ring_nf
  rw [h1, integral_const_mul, hmgf, ← Real.exp_add]
  simp only [zero_mul, zero_add]
  rw [Real.exp_eq_one_iff]
  ring

/-- AX-02: `E[exp (-∫_{τ n}^T ξ_n) | F_{τ n -}] = 1` for `1 ≤ n ≤ N`, `T ≥ τ n`. -/
lemma jump_martingale (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Iic N)) {n : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) {T : ℝ} (hT : τ n ≤ T) :
    (Q N y)[fun ω => Real.exp (-(∫ u in τ n..T, ξ τ N y n u ω)) |
        Upstream.leftLimit (filt N τ) (τ n)] =ᵐ[Q N y] 1 := by
  have hτn : 0 ≤ τ n := hτ0 ▸ τ_mono hτ (Nat.zero_le n) hnN
  obtain ⟨k, hk, hTk⟩ := Theorem1Proof.exists_index (N := N) hτ0 (hτn.trans hT)
  have hnk : n ≤ k :=
    PiecewiseAffineIntegralProof.index_le hτ hT hnN (self_mem_I hτ hnN) hTk
  -- the integrand as a product over the block `(n, m)`, `n ≤ m ≤ k`
  have hY : (fun ω : Ω N => Real.exp (-(∫ u in τ n..T, ξ τ N y n u ω))) = fun ω =>
      ∏ m ∈ Finset.Ico n (k + 1),
        Real.exp (-(coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2)) := by
    funext ω
    rw [integral_ξ hτ hnk hk hTk, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  rw [hY]
  -- measurability for the block σ-algebra
  have hmeas : StronglyMeasurable[coordAlg N {p | p.1.1 = n}] fun ω : Ω N =>
      ∏ m ∈ Finset.Ico n (k + 1),
        Real.exp (-(coef τ k T m * X N n m ω + (y n m : ℝ) * coef τ k T m ^ 2 / 2)) := by
    let _i : MeasurableSpace (Ω N) := coordAlg N {p | p.1.1 = n}
    refine Measurable.stronglyMeasurable ?_
    refine Finset.measurable_prod _ fun m hm => ?_
    have hm' := Finset.mem_Ico.1 hm
    have hX : Measurable (X N n m) :=
      measurable_X_coordAlg (A := {p | p.1.1 = n}) ⟨hn, hm'.1, (Nat.lt_succ_iff.1 hm'.2).trans hk⟩ rfl
    exact (measurable_const.mul hX |>.add measurable_const).neg.exp
  have h := condExp_indep_eq (μ := Q N y) (coordAlg_le _) (Upstream.leftLimit_le (filt N τ) (τ n))
    hmeas (indep_block τ n)
  rw [integral_exp_eq_one hn hk T] at h
  exact h

/-! ### The instance -/

/-- The instance of Claim 009 as a value of `Upstream.HJMScheduled`. -/
noncomputable def d2 (N d : ℕ) (τ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d))
    (y : ℕ → ℕ → NNReal) (f₀ : ℝ → ℝ) (hτ0 : τ 0 = 0) (hτ : StrictMonoOn τ (Set.Iic N))
    (hf₀ : Measurable f₀) (hbd : ∀ T : ℝ, 0 < T → ∃ C : ℝ, ∀ u ∈ Set.Icc 0 T, |f₀ u| ≤ C) :
    Upstream.HJMScheduled (Ω N) where
  μ := Q N y
  ℱ := filt N τ
  d := d
  N := N
  τ := τ
  τ_zero := hτ0
  τ_strictMono := hτ
  f₀ := f₀
  α := α τ N s
  σ := σ τ N s
  ξ := ξ τ N y
  f₀_measurable := hf₀
  f₀_locallyIntegrable := fun T hT => by
    obtain ⟨C, hC⟩ := hbd T hT
    exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne hf₀.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => by
        rw [Real.norm_eq_abs]; exact hC u hu)
  α_progMeasurable := α_progMeasurable _
  α_zero_of_lt := fun _ _ ω h => α_zero h ω
  α_integrable := fun T _ => Filter.Eventually.of_forall fun ω => α_integrable T ω
  σ_progMeasurable := σ_progMeasurable _
  σ_zero_of_lt := fun _ _ ω h => σ_zero h ω
  σ_integrable := fun T _ => Filter.Eventually.of_forall fun ω => σ_integrable T ω
  ξ_measurable := fun _ hn _ => ξ_measurable hn
  ξ_zero_of_lt := fun _ _ _ _ ω hu => ξ_zero_of_lt hτ hu ω
  ξ_integrable := fun n _ _ T _ => Filter.Eventually.of_forall fun ω => ξ_integrable T n ω
  drift_integrated := fun T _ => drift_integrated hτ0 hτ T
  jump_martingale := fun _ hn hnN _ hT => jump_martingale hτ0 hτ hn hnN hT

theorem d2Instance : Standalone.D2Instance.statement := by
  intro N d τ s y f₀ hτ0 hτ hf₀ hbd μ ℱ α σ ξ
  let H := d2 N d τ s y f₀ hτ0 hτ hf₀ hbd
  exact ⟨H.isProbabilityMeasure, hτ0, hτ, hf₀, H.f₀_locallyIntegrable, H.α_progMeasurable,
    H.α_zero_of_lt, H.α_integrable, H.σ_progMeasurable, H.σ_zero_of_lt, H.σ_integrable,
    H.ξ_measurable, H.ξ_zero_of_lt, H.ξ_integrable,
    fun ω t T ht htT => drift_pointwise hτ0 hτ ω ht htT, H.drift_integrated, H.jump_martingale⟩

end Novel.D2InstanceProof

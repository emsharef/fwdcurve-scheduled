import Standalone.ZeroMeanReversionUpstreamBridge
import Upstream.ItoCalculus
import Novel.ZeroMeanReversionVarianceSupportProof
import Mathlib.Analysis.Calculus.Deriv.Pi

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
open Standalone.ZeroMeanReversionVarianceSupport
open Standalone.ZeroMeanReversionUpstreamBridge

namespace Novel.ZeroMeanReversionUpstreamBridgeProof

/-! ### The globally `C²` extension of the backward exponential -/

lemma g_eq_of_le (T δ s : ℝ) (hδ : 0 < δ) (hs : s ≤ T) : g0155 T δ s = T - s := by
  unfold g0155
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring

lemma g_ge (T δ s : ℝ) (hδ : 0 < δ) : -δ ≤ g0155 T δ s := by
  unfold g0155
  have h0 := Real.smoothTransition.nonneg ((s - T) / δ)
  have h1 := Real.smoothTransition.le_one ((s - T) / δ)
  by_cases hs : s ≤ T
  · nlinarith
  · by_cases hs' : T + δ ≤ s
    · rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))]
      linarith
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_of_not_ge hs))]

lemma δ_pos {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) : 0 < δ0155 α l := by
  unfold δ0155
  have : 0 ≤ ∑ j, (α j) ^ 2 * l j := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hl j)
  positivity

lemma δ_small {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (j : Fin d) :
    (α j) ^ 2 * l j * δ0155 α l < 1 := by
  unfold δ0155
  have hsum : 0 ≤ ∑ i, (α i) ^ 2 * l i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hl i)
  have hle : (α j) ^ 2 * l j ≤ ∑ i, (α i) ^ 2 * l i :=
    Finset.single_le_sum (f := fun i => (α i) ^ 2 * l i)
      (fun i _ => mul_nonneg (sq_nonneg _) (hl i)) (Finset.mem_univ j)
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

lemma denom_pos {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T : ℝ) (j : Fin d) (s : ℝ) :
    0 < 1 + ((α j) ^ 2 * g0155 T (δ0155 α l) s / 2) * l j := by
  have hδ := δ_pos α l hl
  have hg := g_ge T (δ0155 α l) s hδ
  have hsmall := δ_small α l hl j
  have h1 : (α j) ^ 2 * (-δ0155 α l) / 2 * l j ≤ (α j) ^ 2 * g0155 T (δ0155 α l) s / 2 * l j := by
    have := mul_le_mul_of_nonneg_left hg (sq_nonneg (α j))
    have := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right this (hl j)
  nlinarith

lemma g_contDiff (T δ : ℝ) : ContDiff ℝ 2 (g0155 T δ) := by
  unfold g0155
  exact (contDiff_const.sub contDiff_id).mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)))

lemma qExt_contDiff {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T : ℝ) (j : Fin d) :
    ContDiff ℝ 2 (fun s => qExt (α j) T (δ0155 α l) (l j) s) := by
  unfold qExt
  refine contDiff_const.div ?_ (fun s => (denom_pos α l hl T j s).ne')
  exact contDiff_const.add
    (((contDiff_const.mul (g_contDiff T _)).div_const 2).mul contDiff_const)

lemma EExt_contDiff {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T : ℝ) :
    ContDiff ℝ 2 (EExt α l T (δ0155 α l)) := by
  unfold EExt
  refine Real.contDiff_exp.comp (ContDiff.neg (ContDiff.sum fun j _ => ?_))
  exact ((qExt_contDiff α l hl T j).comp contDiff_fst).mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)

lemma EExt_eq {d : ℕ} (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T s : ℝ) (x : Fin d → ℝ)
    (hs : s ≤ T) : EExt α l T (δ0155 α l) (s, x) = E0152 α l T s x := by
  simp only [EExt, E0152, qExt, q0152, g_eq_of_le T _ s (δ_pos α l hl) hs]

lemma extension : extensionStatement := by
  intro d α l T hl
  exact ⟨EExt α l T (δ0155 α l), EExt_contDiff α l hl T, fun s x hs => EExt_eq α l hl T s x hs⟩

/-! ### The integral of the zero integrand -/

lemma U4_zero {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) :
    U4 S.ℱ S.μ (fun _ _ => (0 : ℝ)) :=
  ⟨stronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => by simp⟩

lemma zero_integral {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun _ _ => (0 : ℝ)) t ω = 0 := by
  let z : ℝ≥0 → Ω → ℝ := fun _ _ => 0
  have hlin := S.int_linear k z z 0 0 (U4_zero S) (U4_zero S)
  have hz : (0 : ℝ) • z + (0 : ℝ) • z = z := by
    funext s ω
    simp [z]
  rw [hz] at hlin
  have hpt : ∀ t, ∀ᵐ ω ∂S.μ, S.I k (fun _ _ => (0 : ℝ)) t ω = 0 := fun t => by
    filter_upwards [hlin t] with ω hω
    simpa using hω
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂S.μ, ∀ t ∈ D, S.I k (fun _ _ => (0 : ℝ)) t ω = 0 :=
    (ae_ball_iff hDc).2 fun t _ => hpt t
  filter_upwards [hD, S.int_continuous k _ (U4_zero S)] with ω hω hc
  intro t
  have hclosed : IsClosed {s : ℝ≥0 | S.I k (fun _ _ => (0 : ℝ)) s ω = 0} :=
    isClosed_eq hc continuous_const
  have hsub : D ⊆ {s : ℝ≥0 | S.I k (fun _ _ => (0 : ℝ)) s ω = 0} := fun s hs => hω s hs
  have := closure_minimal hsub hclosed
  rw [hDd.closure_eq] at this
  exact this (Set.mem_univ t)

lemma zeroIntegral : zeroIntegralStatement := fun _ _ S k => zero_integral S k

/-- The Upstream structure, viewed as the restated structure of the standalone file. -/
def ofUpstream {Ω : Type*} [m₀ : MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω) :
    ItoCalculus Ω where
  μ := S.μ
  isProbabilityMeasure := S.isProbabilityMeasure
  ℱ := S.ℱ
  m := S.m
  B := S.B
  c := S.c
  I := S.I
  usual_null := S.usual_null
  usual_rightContinuous := S.usual_rightContinuous
  c_measurable := S.c_measurable
  c_bounded_on_compacts := S.c_bounded_on_compacts
  c_symm := S.c_symm
  B_adapted := S.B_adapted
  B_zero := S.B_zero
  B_continuous := S.B_continuous
  B_memLp_two := S.B_memLp_two
  B_martingale := S.B_martingale
  B_covariation := S.B_covariation
  int_elementary := S.int_elementary
  int_linear := S.int_linear
  int_adapted := S.int_adapted
  int_zero := S.int_zero
  int_continuous := S.int_continuous
  int_martingale := S.int_martingale
  int_product_martingale := S.int_product_martingale
  stopped_martingale := S.stopped_martingale
  int_stopped := S.int_stopped
  ito_formula := S.ito_formula

/-- The zero-integral identity for an actual `Upstream.ItoCalculus` structure. -/
lemma upstream_zero_integral {Ω : Type} [mΩ : MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (k : Fin S.m) : ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun _ _ => (0 : ℝ)) t ω = 0 :=
  zero_integral (ofUpstream S) k

/-! ### The Itô representation of the backward exponential from the field AX-05 -/

section Ito
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma Hdrv_U4 (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) (i : Fin d) (k' : Fin S.m) :
    U4 S.ℱ S.μ (Hdrv k α X i k') := by
  unfold Hdrv
  split_ifs
  · exact hU i
  · exact U4_zero S

lemma zeroDrift : LocallyIntegrableDrift S.ℱ S.μ (fun _ _ => (0 : ℝ)) :=
  ⟨isStronglyProgressive_const _ _, fun _ => Eventually.of_forall fun _ => by simp⟩

lemma driverForm_eq (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) t ω =
      fun i => (X t ω i : ℝ) := by
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hs : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω := ae_all_iff.2 hsde
  filter_upwards [hz, hs, hx0] with ω hz hs hx0
  intro t
  funext i
  have hx0i : X 0 ω i = x0 i := congrFun hx0 i
  simp only [driverForm, intervalIntegral.integral_zero, add_zero]
  rw [Finset.sum_eq_single (k i)]
  · simp only [Hdrv, eq_self_iff_true, ite_true]
    rw [hs i t, hx0i]
  · intro k' _ hk'
    simp only [Hdrv, ite_eq_right hk']
    exact hz k' t
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma dT_eq (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T s : ℝ) (hs : s < T) (x : Fin d → ℝ) :
    dT (EExt α l T (δ0155 α l)) (s, x) = deriv (fun u => E0152 α l T u x) s := by
  have hf := (EExt_contDiff α l hl T).differentiable (by norm_num)
  have hL : HasDerivAt (fun u : ℝ => (u, x)) ((1 : ℝ), (0 : Fin d → ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h := (hf (s, x)).hasFDerivAt.comp_hasDerivAt s hL
  have heq : (EExt α l T (δ0155 α l) ∘ fun u : ℝ => (u, x)) =ᶠ[𝓝 s]
      fun u => E0152 α l T u x := by
    filter_upwards [Iio_mem_nhds hs] with u hu
    exact EExt_eq α l hl T u x (le_of_lt hu)
  rw [dT, ← h.deriv]
  exact heq.deriv_eq

lemma dXX_eq (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T s : ℝ) (hs : s ≤ T) (x : Fin d → ℝ)
    (i : Fin d) :
    dXX (EExt α l T (δ0155 α l)) (s, x) i i =
      deriv (deriv (fun u => E0152 α l T s (Function.update x i u))) (x i) := by
  classical
  have hf : ContDiff ℝ 2 (EExt α l T (δ0155 α l)) := EExt_contDiff α l hl T
  have hfd : Differentiable ℝ (EExt α l T (δ0155 α l)) := hf.differentiable (by norm_num)
  have hf' : Differentiable ℝ (fderiv ℝ (EExt α l T (δ0155 α l))) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hL : ∀ u, HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)) u :=
    fun u => (hasDerivAt_const u s).prodMk (hasDerivAt_update x i u)
  have hg : ∀ u, HasDerivAt (fun u => EExt α l T (δ0155 α l) (s, Function.update x i u))
      (fderiv ℝ (EExt α l T (δ0155 α l)) (s, Function.update x i u) (0, Pi.single i 1)) u :=
    fun u => (hfd _).hasFDerivAt.comp_hasDerivAt u (hL u)
  have hgE : (fun u => EExt α l T (δ0155 α l) (s, Function.update x i u)) =
      fun u => E0152 α l T s (Function.update x i u) :=
    funext fun u => EExt_eq α l hl T s _ hs
  have hderiv : deriv (fun u => E0152 α l T s (Function.update x i u)) =
      fun u => fderiv ℝ (EExt α l T (δ0155 α l)) (s, Function.update x i u) (0, Pi.single i 1) := by
    rw [← hgE]
    funext u
    exact (hg u).deriv
  have h2 : HasDerivAt (fun u => fderiv ℝ (EExt α l T (δ0155 α l)) (s, Function.update x i u)
        (0, Pi.single i 1))
      (fderiv ℝ (fderiv ℝ (EExt α l T (δ0155 α l))) (s, Function.update x i (x i))
        (0, Pi.single i 1) (0, Pi.single i 1)) (x i) := by
    have hc : HasDerivAt (fun u => fderiv ℝ (EExt α l T (δ0155 α l)) (s, Function.update x i u))
        (fderiv ℝ (fderiv ℝ (EExt α l T (δ0155 α l))) (s, Function.update x i (x i))
          (0, Pi.single i 1)) (x i) :=
      (hf' _).hasFDerivAt.comp_hasDerivAt (x i) (hL (x i))
    have := hc.clm_apply (hasDerivAt_const (x i) ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)))
    simpa using this
  rw [dXX, hderiv, h2.deriv, Function.update_eq_self]

lemma quad_sum (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (D : Fin d → Fin d → ℝ) (i j : Fin d) (s : ℝ≥0) (ω : Ω) :
    (∑ k', ∑ l', D i j * Hdrv k α X i k' s ω * Hdrv k α X j l' s ω * S.c k' l' s) =
      D i j * (α i * Real.sqrt (X s ω i)) * (α j * Real.sqrt (X s ω j)) * S.c (k i) (k j) s := by
  classical
  rw [Finset.sum_eq_single (k i)]
  · rw [Finset.sum_eq_single (k j)]
    · simp only [Hdrv, eq_self_iff_true, ite_true]
    · intro l' _ hl'
      simp [Hdrv, ite_eq_right hl']
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k' _ hk'
    simp [Hdrv, ite_eq_right hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma drift_pointwise (k : Fin d → Fin S.m) (α l : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) (hl : ∀ j, 0 ≤ l j)
    (T s : ℝ) (hs : s < T) (ω : Ω) :
    dT (EExt α l T (δ0155 α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l',
        dXX (EExt α l T (δ0155 α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i j *
          Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s) = 0 := by
  classical
  set x : Fin d → ℝ := fun i => (X (Real.toNNReal s) ω i : ℝ) with hx
  have hq : ∀ i j, (∑ k', ∑ l', dXX (EExt α l T (δ0155 α l)) (s, x) i j *
      Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
        S.c k' l' (Real.toNNReal s)) =
      if i = j then dXX (EExt α l T (δ0155 α l)) (s, x) i i * ((α i) ^ 2 * x i) else 0 := by
    intro i j
    rw [quad_sum S k α X (fun i j => dXX (EExt α l T (δ0155 α l)) (s, x) i j) i j, hc]
    split_ifs with hij
    · subst hij
      simp only [hx, mul_one]
      have hsq : Real.sqrt (X (Real.toNNReal s) ω i : ℝ) * Real.sqrt (X (Real.toNNReal s) ω i : ℝ) =
          (X (Real.toNNReal s) ω i : ℝ) := Real.mul_self_sqrt (NNReal.coe_nonneg _)
      linear_combination (dXX (EExt α l T (δ0155 α l)) (s, x) i i * (α i) ^ 2) * hsq
    · simp
  simp_rw [hq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [dT_eq α l hl T s hs x]
  simp_rw [dXX_eq α l hl T s hs.le x]
  have hg := Novel.ZeroMeanReversionVarianceSupportProof.E0152_generator α l T s x hl hs.le
  rw [Finset.mul_sum]
  have hterm : (∑ i, (1 / 2 : ℝ) * (deriv (deriv (fun u => E0152 α l T s (Function.update x i u)))
      (x i) * ((α i) ^ 2 * x i))) =
      ∑ j, ((α j) ^ 2 * x j / 2) *
        deriv (deriv (fun u => E0152 α l T s (Function.update x j u))) (x j) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hterm]
  exact hg

lemma ito_representation (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (T : ℝ) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    (∀ i, U4 S.ℱ S.μ (Gint S k α l T x0 X i)) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      E0152 α l T t (fun i => (X t ω i : ℝ)) =
        E0152 α l T 0 (fun i => (x0 i : ℝ)) + ∑ i, S.I (k i) (Gint S k α l T x0 X i) t ω := by
  classical
  obtain ⟨hU4, hae⟩ := S.ito_formula d (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0)
    (EExt α l T (δ0155 α l)) (fun i k' => Hdrv_U4 S k α X hU i k') (fun _ => zeroDrift S)
    (EExt_contDiff α l hl T)
  refine ⟨fun i => hU4 i (k i), ?_⟩
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  filter_upwards [hae, driverForm_eq S k α X x0 hx0 hsde, hz] with ω hω hdf hz
  intro t ht
  have h0T : (0 : ℝ) ≤ T := t.coe_nonneg.trans ht
  have h := hω t
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at h
  have hsum : ∀ i, (∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (EExt α l T (δ0155 α l))
      ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) i *
        Hdrv k α X i k' s ω) t ω) = S.I (k i) (Gint S k α l T x0 X i) t ω := by
    intro i
    rw [Finset.sum_eq_single (k i)]
    · rfl
    · intro k' _ hk'
      have hzero : (fun (s : ℝ≥0) ω => dX (EExt α l T (δ0155 α l))
          ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) i *
            Hdrv k α X i k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        simp [Hdrv, ite_eq_right hk']
      rw [hzero]
      exact hz k' t
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  simp only [hsum] at h
  have hdrift : (∫ s in (0 : ℝ)..t, (dT (EExt α l T (δ0155 α l))
      (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) (Real.toNNReal s) ω) +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l', dXX (EExt α l T (δ0155 α l))
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) (Real.toNNReal s) ω)
          i j * Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s))) = 0 := by
    refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
    have hT : ∀ᵐ s : ℝ, s ∉ ({T} : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton T)
    filter_upwards [hT] with s hsT hsI
    rw [Set.uIoc_of_le t.coe_nonneg] at hsI
    have hsT' : s < T := lt_of_le_of_ne (hsI.2.trans ht) (fun h => hsT (by simp [h]))
    rw [hdf (Real.toNNReal s)]
    exact drift_pointwise S k α l X hc hl T s hsT' ω
  rw [hdrift, add_zero, hdf t, EExt_eq α l hl T _ _ ht, EExt_eq α l hl T 0 _ h0T] at h
  exact h

lemma ito : itoStatement := by
  intro d Ω mΩ S k α X x0 hc hx0 hU hsde T l hl
  exact ito_representation S k α X x0 hc hx0 hU hsde T l hl

end Ito

/-! ### Localization: `H0152` from the Itô representation, AX-04b and AX-03c -/

section Localization
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- `∂_i` of the extended exponential on the horizon. -/
lemma dX_eq (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T s : ℝ) (hs : s ≤ T) (x : Fin d → ℝ)
    (i : Fin d) :
    dX (EExt α l T (δ0155 α l)) (s, x) i = -q0152 (α i) T (l i) s * E0152 α l T s x := by
  classical
  have hfd : Differentiable ℝ (EExt α l T (δ0155 α l)) :=
    (EExt_contDiff α l hl T).differentiable (by norm_num)
  have hL : HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)) (x i) :=
    (hasDerivAt_const _ s).prodMk (hasDerivAt_update x i (x i))
  have hg : HasDerivAt (fun u => EExt α l T (δ0155 α l) (s, Function.update x i u))
      (fderiv ℝ (EExt α l T (δ0155 α l)) (s, Function.update x i (x i)) (0, Pi.single i 1))
      (x i) :=
    (hfd _).hasFDerivAt.comp_hasDerivAt (x i) hL
  rw [Function.update_eq_self] at hg
  have hgE : (fun u => EExt α l T (δ0155 α l) (s, Function.update x i u)) =
      fun u => E0152 α l T s (Function.update x i u) :=
    funext fun u => EExt_eq α l hl T s _ hs
  rw [hgE] at hg
  have h2 := E0152_coordinate_derivative α l T s x i (x i)
  rw [Function.update_eq_self] at h2
  unfold dX
  exact hg.unique h2

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The Itô integrand of the backward exponential is bounded where the state is. -/
lemma Gint_bound (k : Fin d → Fin S.m) (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (T : ℝ)
    (x0 : Fin d → NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) (s : ℝ≥0) (ω : Ω)
    (hdf : driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω =
      fun j => (X s ω j : ℝ))
    (hs : (s : ℝ) ≤ T) (C : ℝ) (hX : (X s ω i : ℝ) ≤ C) :
    |Gint S k α l T x0 X i s ω| ≤ l i * |α i| * Real.sqrt C := by
  simp only [Gint, hdf, Hdrv, eq_self_iff_true, ite_true]
  rw [dX_eq α l hl T s hs]
  have hq := q0152_bounds (α i) T (l i) s (hl i) hs
  have hE := E0152_bounds α l T s (fun j => (X s ω j : ℝ)) hl hs (fun j => NNReal.coe_nonneg _)
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hq.1, abs_of_pos hE.1,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : Real.sqrt (X s ω i : ℝ) ≤ Real.sqrt C := Real.sqrt_le_sqrt hX
  calc q0152 (α i) T (l i) s * E0152 α l T s (fun j => (X s ω j : ℝ)) *
        (|α i| * Real.sqrt (X s ω i : ℝ))
      ≤ l i * 1 * (|α i| * Real.sqrt C) :=
        mul_le_mul (mul_le_mul hq.2 hE.2 hE.1.le (hl i))
          (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg (hl i) zero_le_one)
    _ = l i * |α i| * Real.sqrt C := by ring

/-- The stopped integrand of AX-04b. -/
noncomputable def stoppedInt (τ : Ω → ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => Set.indicator {s | s ≤ τ ω} (fun _ => (1 : ℝ)) s * G s ω

/-- The stochastic interval `[0, τ]` of a stopping time is predictable. -/
lemma stoppingSet_predictable (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    MeasurableSet[S.ℱ.predictable] {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} := by
  have h : {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} =
      (⋃ q : ℚ, Set.Ioi (Real.toNNReal q) ×ˢ {ω | τ ω ≤ Real.toNNReal q})ᶜ := by
    ext ⟨s, ω⟩
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi,
      not_exists, not_and]
    constructor
    · intro h q hq hτq
      exact absurd (hτq.trans_lt hq) (not_lt.mpr h)
    · intro h
      by_contra hlt
      have hlt' : τ ω < s := not_le.mp hlt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.mpr hlt')
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
      refine h q ?_ ?_
      · have := (Real.toNNReal_lt_toNNReal_iff_of_nonneg hq0).mpr hq2
        rwa [Real.toNNReal_coe] at this
      · exact (Real.le_toNNReal_iff_coe_le hq0).mpr hq1.le
  rw [h]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun q => measurableSet_predictable_Ioi_prod ?_)
  convert hτ.measurableSet_le (Real.toNNReal q) using 1
  ext ω
  constructor <;> intro h <;>
    first | exact WithTop.coe_le_coe.mpr h | exact WithTop.coe_le_coe.mp h

lemma stoppedInt_predictable (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (G : ℝ≥0 → Ω → ℝ) (hG : IsStronglyPredictable S.ℱ G) :
    IsStronglyPredictable S.ℱ (stoppedInt τ G) := by
  have h1 : StronglyMeasurable[S.ℱ.predictable]
      (fun p : ℝ≥0 × Ω => Set.indicator {s | s ≤ τ p.2} (fun _ => (1 : ℝ)) p.1) := by
    have : (fun p : ℝ≥0 × Ω => Set.indicator {s | s ≤ τ p.2} (fun _ => (1 : ℝ)) p.1) =
        Set.indicator {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} (fun _ => (1 : ℝ)) := by
      funext p
      simp only [Set.indicator, Set.mem_ofPred_eq]
    rw [this]
    exact stronglyMeasurable_const.indicator (stoppingSet_predictable S τ hτ)
  exact h1.mul hG

/-- A bounded stopped (U4) integrand is (U5) on every horizon. -/
lemma stoppedInt_U5 (τ : Ω → ℝ≥0) (hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (G : ℝ≥0 → Ω → ℝ) (hG : U4 S.ℱ S.μ G) (C : ℝ)
    (hbound : ∀ᵐ ω ∂S.μ, ∀ s, s ≤ τ ω → |G s ω| ≤ C) (T : ℝ≥0) :
    U5 S.ℱ S.μ (stoppedInt τ G) T := by
  have hpt : ∀ᵐ ω ∂S.μ, ∀ s, (stoppedInt τ G s ω) ^ 2 ≤ C ^ 2 := by
    filter_upwards [hbound] with ω hω s
    by_cases hs : s ≤ τ ω
    · simp only [stoppedInt, Set.indicator_of_mem (show s ∈ {s | s ≤ τ ω} from hs), one_mul]
      exact sq_le_sq' (abs_le.mp (hω s hs)).1 (abs_le.mp (hω s hs)).2
    · have h0 : stoppedInt τ G s ω = 0 := by
        simp only [stoppedInt, Set.indicator_of_notMem (show s ∉ {s | s ≤ τ ω} from hs), zero_mul]
      rw [h0, zero_pow two_ne_zero]
      exact sq_nonneg C
  have hint : ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
      ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((stoppedInt τ G (Real.toNNReal s) ω) ^ 2) ≤
        ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (t : ℝ) := by
    filter_upwards [hpt] with ω hω t
    calc ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((stoppedInt τ G (Real.toNNReal s) ω) ^ 2)
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (C ^ 2) :=
          lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hω _)
      _ = ENNReal.ofReal (C ^ 2) * volume (Set.Icc (0 : ℝ) t) := setLIntegral_const _ _
      _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (t : ℝ) := by rw [Real.volume_Icc, sub_zero]
  refine ⟨⟨stoppedInt_predictable S τ hτ G hG.1, fun t => ?_⟩, ?_⟩
  · filter_upwards [hint] with ω hω
    exact (hω t).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  · calc ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal ((stoppedInt τ G (Real.toNNReal s) ω) ^ 2)) ∂S.μ
        ≤ ∫⁻ _, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (T : ℝ) ∂S.μ :=
          lintegral_mono_ae (hint.mono fun ω hω => hω T)
      _ < ⊤ := by
          rw [lintegral_const, measure_univ, mul_one]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- A finite sum of martingales is a martingale. -/
lemma martingale_finsum {ι : Type*} [Preorder ι] {n : ℕ} (f : Fin n → ι → Ω → ℝ)
    (ℱ : Filtration ι mΩ) (μ : Measure Ω) (hf : ∀ i, Martingale (f i) ℱ μ) :
    Martingale (fun t ω => ∑ i, f i t ω) ℱ μ := by
  classical
  have key : ∀ s : Finset (Fin n), Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ μ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      convert martingale_zero ℝ ℱ μ using 1
      funext t ω
      simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a).add ih
  exact key Finset.univ

lemma coe_min_Icc {T : NNReal} (a b : Set.Icc (0 : ℝ) T) :
    ((min a b : Set.Icc (0 : ℝ) T) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Subtype.coe_le_coe.mpr h)]
  · rw [min_eq_right h, min_eq_right (Subtype.coe_le_coe.mpr h)]

/-- The frozen development's localizers, read as `ℝ≥0`-valued stopping times of the
structure's filtration. -/
lemma localizer_stoppingTime (T : NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (n : ℕ) :
    IsStoppingTime S.ℱ (fun ω =>
      ((Real.toNNReal (σ01521 T (stateR X) n ω).val : ℝ≥0) : WithTop ℝ≥0)) := by
  have hst := Novel.ZeroMeanReversionVarianceSupportProof.localizer_stopping (filtR S.ℱ) T
    (stateR X) (fun s _ => hadapt _)
    (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)) n
  intro t
  have h := hst ⟨min (t : ℝ) T, le_min t.coe_nonneg T.coe_nonneg, min_le_right _ _⟩
  have hset : {ω | ((Real.toNNReal (σ01521 T (stateR X) n ω).val : ℝ≥0) : WithTop ℝ≥0) ≤ ↑t} =
      {ω | ((σ01521 T (stateR X) n ω : Set.Icc (0 : ℝ) T) : WithTop (Set.Icc (0 : ℝ) T)) ≤
        ↑(⟨min (t : ℝ) T, le_min t.coe_nonneg T.coe_nonneg, min_le_right _ _⟩ :
          Set.Icc (0 : ℝ) T)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    rw [← Subtype.coe_le_coe]
    simp only [le_min_iff]
    constructor
    · intro h
      refine ⟨?_, (σ01521 T (stateR X) n ω).2.2⟩
      rw [← Real.toNNReal_coe (r := t)] at h
      exact (Real.toNNReal_le_toNNReal_iff t.coe_nonneg).mp h
    · rintro ⟨h, -⟩
      exact (Real.toNNReal_le_toNNReal h).trans_eq Real.toNNReal_coe
  rw [hset]
  have hle : Real.toNNReal (min (t : ℝ) T) ≤ t :=
    (Real.toNNReal_le_toNNReal (min_le_left _ _)).trans_eq Real.toNNReal_coe
  exact S.ℱ.mono hle _ h

/-- The stopped backward exponential is adapted to the real-time filtration. -/
lemma stopped_adapted (T : NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (α l : Fin d → ℝ) (n : ℕ) (s : Set.Icc (0 : ℝ) T) :
    StronglyMeasurable[filt0152 (filtR S.ℱ) T s]
      (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ)) ω) := by
  have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  let u : Set.Icc (0 : ℝ) T → Ω → ℝ × (Fin d → ℝ) :=
    fun s ω => ((s : ℝ), fun j => (stateR X (s : ℝ) ω j : ℝ))
  have hu_ad : StronglyAdapted (filt0152 (filtR S.ℱ) T) u := by
    intro s
    refine (measurable_const.prodMk ?_).stronglyMeasurable
    have hcoe : Measurable (fun v : Fin d → NNReal => fun j => (v j : ℝ)) :=
      measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp (measurable_pi_apply j)
    exact hcoe.comp (hadapt (Real.toNNReal (s : ℝ)))
  have hu_cont : ∀ ω, Continuous fun s => u s ω := fun ω =>
    continuous_subtype_val.prodMk (continuous_pi fun j =>
      (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val))
  have hprog := hu_ad.isStronglyProgressive_of_continuous hu_cont
  have hτ := Novel.ZeroMeanReversionVarianceSupportProof.localizer_stopping (filtR S.ℱ) T
    (stateR X) (fun s _ => hadapt _)
    (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)) n
  have hsp := (hprog.stoppedProcess hτ).stronglyAdapted s
  have hE : Measurable (fun p : ℝ × (Fin d → ℝ) => E0152 α l T p.1 p.2) := by
    unfold E0152 q0152
    fun_prop
  have heq : (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ)) ω) =
      fun ω => E0152 α l T
        (stoppedProcess u (fun ω => (σ01521 T (stateR X) n ω : WithTop (Set.Icc (0 : ℝ) T))) s ω).1
        (stoppedProcess u (fun ω => (σ01521 T (stateR X) n ω : WithTop (Set.Icc (0 : ℝ) T))) s ω).2 := by
    funext ω
    simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopD_coe, u, M0152, coe_min_Icc]
  rw [heq]
  exact (hE.comp hsp.measurable).stronglyMeasurable

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The stopped backward exponential along the frozen development's localizers is a
martingale, from the fields. -/
lemma localization_martingale (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (T : NNReal) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (n : ℕ) :
    Martingale (fun (s : Set.Icc (0 : ℝ) T) ω =>
      M0152 α l T (stateR X) (min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ)) ω)
      (filt0152 (filtR S.ℱ) T) S.μ := by
  classical
  have hc' : ∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) T => (stateR X s.val ω j : ℝ)) :=
    fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  obtain ⟨hU4G, hito⟩ := ito_representation S k α X x0 hc hx0 hU hsde T l hl
  set τ : Ω → ℝ≥0 := fun ω => Real.toNNReal (σ01521 T (stateR X) n ω).val with hτdef
  have hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0)) :=
    localizer_stoppingTime S T X hcont hadapt n
  have hτT : ∀ ω, τ ω ≤ T := fun ω =>
    (Real.toNNReal_le_toNNReal (σ01521 T (stateR X) n ω).2.2).trans_eq Real.toNNReal_coe
  set G := Gint S k α l T x0 X with hGdef
  have hGb : ∀ i, ∀ᵐ ω ∂S.μ, ∀ s, s ≤ τ ω →
      |G i s ω| ≤ l i * |α i| * Real.sqrt ((n : ℝ) + 2) := by
    intro i
    filter_upwards [driverForm_eq S k α X x0 hx0 hsde, hx0] with ω hdf hx0ω s hs
    have hsT : (s : ℝ) ≤ T := by exact_mod_cast hs.trans (hτT ω)
    have h0 : ∀ j, stateR X 0 ω j ≤ 1 := fun j => by
      have hx : X 0 ω j = x0 j := congrFun hx0ω j
      simp only [stateR, Real.toNNReal_zero, hx]
      exact hx0le j
    have hsσ : (⟨(s : ℝ), s.coe_nonneg, hsT⟩ : Set.Icc (0 : ℝ) T) ≤ σ01521 T (stateR X) n ω :=
      (Real.le_toNNReal_iff_coe_le (σ01521 T (stateR X) n ω).2.1).mp hs
    have hXb := localizer_coordinate_bound T (stateR X) hc' ω h0 n
      ⟨(s : ℝ), s.coe_nonneg, hsT⟩ hsσ i
    have hXb' : (X s ω i : ℝ) ≤ (n : ℝ) + 2 := by
      simp only [stateR, Real.toNNReal_coe] at hXb
      exact_mod_cast hXb
    exact Gint_bound S k α l hl T x0 X i s ω (hdf s) hsT _ hXb'
  have hU5 : ∀ i, U5 S.ℱ S.μ (stoppedInt τ (G i)) T := fun i =>
    stoppedInt_U5 S τ hτ (G i) (hU4G i) _ (hGb i) T
  set c0 : ℝ := E0152 α l T 0 (fun i => (x0 i : ℝ)) with hc0
  have hg : Martingale (fun t ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min t T) ω)
      S.ℱ S.μ :=
    (martingale_const S.ℱ S.μ c0).add
      (martingale_finsum _ S.ℱ S.μ fun i => (S.int_martingale (k i) _ T (hU5 i)).1)
  have hid : ∀ s : Set.Icc (0 : ℝ) T,
      (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ)) ω) =ᵐ[S.μ]
        fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s) T) ω := by
    intro s
    have hst : ∀ᵐ ω ∂S.μ, ∀ i, S.I (k i) (G i) (min (Real.toNNReal s) (τ ω)) ω =
        S.I (k i) (stoppedInt τ (G i)) (Real.toNNReal s) ω :=
      ae_all_iff.2 fun i => S.int_stopped (k i) (G i) τ (hU4G i) hτ (Real.toNNReal s)
    filter_upwards [hito, hst] with ω hω hst
    have hmin : Real.toNNReal (min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ)) =
        min (Real.toNNReal s) (τ ω) := by
      rcases le_total (s : ℝ) (σ01521 T (stateR X) n ω : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.toNNReal_le_toNNReal h)]
      · rw [min_eq_right h, min_eq_right (Real.toNNReal_le_toNNReal h)]
    have hle : ((min (Real.toNNReal s) (τ ω) : ℝ≥0) : ℝ) ≤ T := by
      have : min (Real.toNNReal s) (τ ω) ≤ τ ω := min_le_right _ _
      exact_mod_cast this.trans (hτT ω)
    have hcoe : ((min (Real.toNNReal s) (τ ω) : ℝ≥0) : ℝ) =
        min (s : ℝ) (σ01521 T (stateR X) n ω : ℝ) := by
      rw [← hmin, Real.coe_toNNReal _ (le_min s.2.1 (σ01521 T (stateR X) n ω).2.1)]
    have hsT : min (Real.toNNReal s) T = Real.toNNReal s :=
      min_eq_left ((Real.toNNReal_le_toNNReal s.2.2).trans_eq Real.toNNReal_coe)
    simp only [M0152, stateR, hmin, hsT]
    rw [← hcoe, hω _ hle]
    simp only [hst]
  refine ⟨fun s => stopped_adapted S T X hcont hadapt α l n s, fun s s' hss' => ?_⟩
  have hts : Real.toNNReal (s : ℝ) ≤ Real.toNNReal (s' : ℝ) :=
    Real.toNNReal_le_toNNReal (Subtype.coe_le_coe.mpr hss')
  have h1 : S.μ[(fun ω => M0152 α l T (stateR X) (min (s' : ℝ) (σ01521 T (stateR X) n ω : ℝ)) ω)
      | filt0152 (filtR S.ℱ) T s] =ᵐ[S.μ]
      S.μ[(fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s') T) ω)
      | filt0152 (filtR S.ℱ) T s] := condExp_congr_ae (hid s')
  have h2 : S.μ[(fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s') T) ω)
      | filt0152 (filtR S.ℱ) T s] =ᵐ[S.μ]
      fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s) T) ω :=
    hg.condExp_ae_eq hts
  exact h1.trans (h2.trans (hid s).symm)

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- `H0152` for the actual variance states under the fields. -/
lemma localization (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (T : NNReal) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    H0152 S.μ (filtR S.ℱ) α l T (stateR X) :=
  ⟨σ01521 T (stateR X), Eventually.of_forall fun ω => localizer_eventually T (stateR X)
    (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)) ω,
    fun n => localization_martingale S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl n⟩

/-- The integral operator respects integrands that agree almost surely at all times: from
AX-03b, the diagonal case of AX-03c, and AX-03a's zero and continuity clauses. -/
lemma int_congr_ae (k : Fin S.m) (H H' : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H)
    (hH' : U4 S.ℱ S.μ H') (hHH' : ∀ᵐ ω ∂S.μ, ∀ s, H s ω = H' s ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k H t ω = S.I k H' t ω := by
  set K : ℝ≥0 → Ω → ℝ := (1 : ℝ) • H + (-1 : ℝ) • H' with hKdef
  have hK0 : ∀ᵐ ω ∂S.μ, ∀ s, K s ω = 0 := by
    filter_upwards [hHH'] with ω hω s
    simp [hKdef, hω s]
  have hKU4 : U4 S.ℱ S.μ K := by
    refine ⟨?_, fun t => ?_⟩
    · have h1 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H) := hH.1
      have h2 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H') := hH'.1
      exact (h1.const_smul (1 : ℝ)).add (h2.const_smul (-1 : ℝ))
    · filter_upwards [hK0] with ω hω
      simp [hω]
  have hKU5 : ∀ T, U5 S.ℱ S.μ K T := fun T => ⟨hKU4, by
    have hz : ∀ᵐ ω ∂S.μ,
        (∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((K (Real.toNNReal s) ω) ^ 2)) = 0 := by
      filter_upwards [hK0] with ω hω
      simp [hω]
    rw [lintegral_congr_ae hz, lintegral_zero]
    exact ENNReal.zero_lt_top⟩
  have hzero : ∀ t, S.I k K t =ᵐ[S.μ] 0 := by
    intro t
    have hM := S.int_product_martingale k k K K t (hKU5 t) (hKU5 t)
    set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k K (min u t) ω * S.I k K (min u t) ω -
      ∫ s in (0 : ℝ)..(min u t : ℝ≥0), K (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
        S.c k k (Real.toNNReal s) with hMdef
    have hcond : S.μ[M t | S.ℱ 0] =ᵐ[S.μ] M 0 := hM.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t)
    have hM0 : M 0 =ᵐ[S.μ] 0 := by
      filter_upwards [S.int_zero k K hKU4] with ω hω
      simp [hMdef, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t), hω]
    have hMt : M t =ᵐ[S.μ] fun ω => (S.I k K t ω) ^ 2 := by
      filter_upwards [hK0] with ω hω
      simp [hMdef, hω, sq]
    have hL2 : MemLp (S.I k K t) 2 S.μ := (S.int_martingale k K t (hKU5 t)).2 t le_rfl
    have hint : ∫ ω, (S.I k K t ω) ^ 2 ∂S.μ = 0 := by
      calc ∫ ω, (S.I k K t ω) ^ 2 ∂S.μ = ∫ ω, M t ω ∂S.μ := integral_congr_ae hMt.symm
        _ = ∫ ω, (S.μ[M t | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
        _ = ∫ ω, M 0 ω ∂S.μ := integral_congr_ae hcond
        _ = 0 := by rw [integral_congr_ae hM0]; simp
    have hsq := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      hL2.integrable_sq).mp hint
    filter_upwards [hsq] with ω hω
    exact pow_eq_zero_iff two_ne_zero |>.mp hω
  have heach : ∀ t, S.I k H t =ᵐ[S.μ] S.I k H' t := by
    intro t
    filter_upwards [hzero t, S.int_linear k H H' 1 (-1) hH hH' t] with ω h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul, Pi.zero_apply] at h1 h2
    linarith
  have hdense : DenseRange (Real.toNNReal ∘ ((↑) : ℚ → ℝ)) :=
    (Function.Surjective.denseRange (f := Real.toNNReal)
      fun r => ⟨(r : ℝ), Real.toNNReal_coe⟩).comp Rat.denseRange_cast continuous_real_toNNReal
  have hq : ∀ᵐ ω ∂S.μ, ∀ q : ℚ, S.I k H (Real.toNNReal q) ω = S.I k H' (Real.toNNReal q) ω :=
    ae_all_iff.2 fun q => heach _
  filter_upwards [hq, S.int_continuous k H hH, S.int_continuous k H' hH'] with ω hq hc hc'
  have := Continuous.ext_on hdense hc hc' (fun x hx => by
    obtain ⟨q, rfl⟩ := hx
    exact hq q)
  intro t
  exact congrFun this t

/-- The null-set replacement used in Claim 015: continuous adapted paths everywhere,
with one initial measurable null set outside which the whole process is unchanged. -/
lemma continuousVersionData (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t)) :
    ∃ (N : Set Ω) (X' : ℝ≥0 → Ω → Fin d → NNReal),
      MeasurableSet[S.ℱ 0] N ∧ S.μ N = 0 ∧
      (∀ t ω, ω ∈ N → X' t ω = x0) ∧ (∀ t ω, ω ∉ N → X' t ω = X t ω) ∧
      (∀ ω j, Continuous fun t => (X' t ω j : ℝ)) ∧
      (∀ t, Measurable[S.ℱ t] (X' t)) := by
  classical
  have hae : ∀ᵐ ω ∂S.μ, ∀ j, Continuous fun t => (X t ω j : ℝ) := ae_all_iff.2 hcont
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hN0 : MeasurableSet[S.ℱ 0] N := S.usual_null N hNmeas hNnull
  have hNt : ∀ t, MeasurableSet[S.ℱ t] N := fun t => S.ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN0
  set X' : ℝ≥0 → Ω → Fin d → NNReal := fun t => N.piecewise (fun _ => x0) (X t) with hX'def
  have hX'N : ∀ t ω, ω ∈ N → X' t ω = x0 := fun t ω hω => Set.piecewise_eq_of_mem _ _ _ hω
  have hX'nN : ∀ t ω, ω ∉ N → X' t ω = X t ω := fun t ω hω => Set.piecewise_eq_of_notMem _ _ _ hω
  have hcont' : ∀ ω j, Continuous fun t => (X' t ω j : ℝ) := by
    intro ω j
    by_cases hω : ω ∈ N
    · simp only [hX'N _ ω hω]
      exact continuous_const
    · simp only [hX'nN _ ω hω]
      have : ω ∉ {ω | ¬ ∀ j, Continuous fun t => (X t ω j : ℝ)} := fun h => hω (hNsub h)
      simp only [Set.mem_ofPred_eq, not_not] at this
      exact this j
  have hadapt' : ∀ t, Measurable[S.ℱ t] (X' t) := fun t =>
    Measurable.piecewise (hNt t) measurable_const (hadapt t)
  exact ⟨N,X',hN0,hNnull,hX'N,hX'nN,hcont',hadapt'⟩

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- `H0152` under the fields' almost-sure path continuity, by modifying the state on a null
set of the initial σ-algebra. -/
lemma localizationAe (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (T : NNReal) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    H0152 S.μ (filtR S.ℱ) α l T (stateR X) := by
  classical
  obtain ⟨N,X',hN0,hNnull,hX'N,hX'nN,hcont',hadapt'⟩ :=
    continuousVersionData S X x0 hcont hadapt
  have hNt : ∀ t, MeasurableSet[S.ℱ t] N := fun t => S.ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN0
  have hNae : ∀ᵐ ω ∂S.μ, ω ∉ N := compl_mem_ae_iff.2 hNnull
  have hx0' : X' 0 =ᵐ[S.μ] fun _ => x0 := by
    filter_upwards [hx0, hNae] with ω hω hN
    rw [hX'nN _ ω hN]
    exact hω
  have hset : MeasurableSet[S.ℱ.predictable] (Set.univ ×ˢ N) := by
    have : (Set.univ ×ˢ N : Set (ℝ≥0 × Ω)) = {⊥} ×ˢ N ∪ Set.Ioi ⊥ ×ˢ N := by
      ext ⟨s, ω⟩
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_Ioi]
      constructor
      · intro h
        rcases eq_or_lt_of_le (bot_le : ⊥ ≤ s) with h' | h'
        · exact Or.inl ⟨h'.symm, h⟩
        · exact Or.inr ⟨h', h⟩
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    rw [this]
    exact (MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨N, hN0, rfl⟩)).union
      (measurableSet_predictable_Ioi_prod hN0)
  have hU' : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X' s ω j)) := by
    intro j
    refine ⟨?_, fun t => ?_⟩
    · have huncurry : Function.uncurry (fun s ω => α j * Real.sqrt (X' s ω j)) =
          (Set.univ ×ˢ N).piecewise (fun _ => α j * Real.sqrt (x0 j))
            (Function.uncurry fun s ω => α j * Real.sqrt (X s ω j)) := by
        funext p
        by_cases hp : p.2 ∈ N
        · rw [Set.piecewise_eq_of_mem _ _ _ (by simp [hp])]
          simp [Function.uncurry, hX'N _ _ hp]
        · rw [Set.piecewise_eq_of_notMem _ _ _ (by simp [hp])]
          simp [Function.uncurry, hX'nN _ _ hp]
      show StronglyMeasurable[S.ℱ.predictable]
        (Function.uncurry fun s ω => α j * Real.sqrt (X' s ω j))
      rw [huncurry]
      exact stronglyMeasurable_const.piecewise hset (hU j).1
    · filter_upwards [(hU j).2 t, hNae] with ω hω hN
      simpa only [hX'nN _ ω hN] using hω
  have hsde' : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X' t ω j : ℝ) =
      X' 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X' s ω j)) t ω := by
    intro j
    have hI := int_congr_ae S (k j) (fun s ω => α j * Real.sqrt (X s ω j))
      (fun s ω => α j * Real.sqrt (X' s ω j)) (hU j) (hU' j)
      (by filter_upwards [hNae] with ω hN s; rw [hX'nN _ ω hN])
    filter_upwards [hsde j, hI, hNae] with ω hω hI hN t
    rw [hX'nN _ ω hN, hX'nN _ ω hN, ← hI t]
    exact hω t
  have hM := fun n => localization_martingale S k α X' x0 hc hcont' hadapt' hx0' hx0le hU' hsde'
    T l hl n
  have hc'' : ∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) T => (stateR X' s.val ω j : ℝ)) :=
    fun ω j => (hcont' ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  let σ' : ℕ → Ω → Set.Icc (0 : ℝ) T := fun n ω =>
    if ω ∈ N then ⟨T, T.coe_nonneg, le_rfl⟩ else σ01521 T (stateR X') n ω
  have hf : ∀ n (s : Set.Icc (0 : ℝ) T),
      (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ' n ω : ℝ)) ω) =ᵐ[S.μ]
        fun ω => M0152 α l T (stateR X') (min (s : ℝ) (σ01521 T (stateR X') n ω : ℝ)) ω := by
    intro n s
    filter_upwards [hNae] with ω hN
    simp only [σ', hN, ite_false, M0152, stateR, hX'nN _ ω hN]
  refine ⟨σ', Eventually.of_forall fun ω => ?_, fun n => ⟨fun s => ?_, fun s s' hss' => ?_⟩⟩
  · by_cases hω : ω ∈ N
    · exact Eventually.of_forall fun n => by simp [σ', hω]
    · filter_upwards [localizer_eventually T (stateR X') hc'' ω] with n hn
      simp [σ', hω, hn]
  · have hE : Measurable (fun x : Fin d → ℝ => E0152 α l T s x) := by
      unfold E0152 q0152
      fun_prop
    have hcoe : Measurable (fun v : Fin d → NNReal => fun j => (v j : ℝ)) :=
      measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp (measurable_pi_apply j)
    have hg : StronglyMeasurable[filt0152 (filtR S.ℱ) T s]
        (fun ω => E0152 α l T s (fun j => (X (Real.toNNReal (s : ℝ)) ω j : ℝ))) :=
      (hE.comp (hcoe.comp (hadapt (Real.toNNReal (s : ℝ))))).stronglyMeasurable
    have heq : (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ' n ω : ℝ)) ω) =
        N.piecewise (fun ω => E0152 α l T s (fun j => (X (Real.toNNReal (s : ℝ)) ω j : ℝ)))
          (fun ω => M0152 α l T (stateR X') (min (s : ℝ) (σ01521 T (stateR X') n ω : ℝ)) ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · rw [Set.piecewise_eq_of_mem _ _ _ hω]
        simp only [σ', hω, ite_true, M0152, stateR, min_eq_left s.2.2]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
        simp only [σ', hω, ite_false, M0152, stateR, hX'nN _ ω hω]
    change StronglyMeasurable[filt0152 (filtR S.ℱ) T s]
      (fun ω => M0152 α l T (stateR X) (min (s : ℝ) (σ' n ω : ℝ)) ω)
    rw [heq]
    exact hg.piecewise (hNt _) (stopped_adapted S T X' hcont' hadapt' α l n s)
  · have h1 := condExp_congr_ae (m := filt0152 (filtR S.ℱ) T s) (μ := S.μ) (hf n s')
    have h2 := (hM n).condExp_ae_eq hss'
    exact h1.trans (h2.trans (hf n s).symm)

lemma localizationAeProp : localizationAeStatement := by
  intro d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl
  exact localizationAe S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The frozen development's transform, law and moment conclusions from the fields. -/
lemma transform : transformStatement := by
  intro d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) T, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l T (stateR X) :=
    fun l hl => localizationAe S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  refine ⟨localized_state_law S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0', fun s hs => ?_, ?_, ?_⟩
  · exact ⟨fun l hl => localized_conditional_transform S.μ (filtR S.ℱ) α l T (stateR X) hl hX
      (hH l hl) s hs, localized_conditional_state_law S.μ (filtR S.ℱ) α T (stateR X) hX hH s hs⟩
  · exact localized_state_independence S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0'
  · intro j
    have hi := localized_state_memLp S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' j
    have hm := localized_state_moments S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' j
    refine ⟨hi, hm.1, hm.2, localized_state_martingale S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' j,
      localized_state_constant S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' j, fun s hs => ?_⟩
    have hcm := localized_state_conditional_moments S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' s hs j
    have his : MemLp (fun ω => (stateR X s ω j : ℝ)) 2 S.μ := (hi.condExp one_le_two).ae_eq hcm.1
    exact ⟨his, hcm.1, hcm.2.1, hcm.2.2,
      localized_state_absorption S.μ (filtR S.ℱ) α T (stateR X) hX hH x0 hx0' s hs j⟩

/-! ### Conditional isometry and orthogonality of increments -/

section Increments
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- A predictable integrand dominated in square by a (U5) integrand is (U5). -/
lemma U5_of_sq_le (H H' : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (hH : U5 S.ℱ S.μ H T)
    (hpred : IsStronglyPredictable S.ℱ H') (hle : ∀ s ω, (H' s ω) ^ 2 ≤ (H s ω) ^ 2) :
    U5 S.ℱ S.μ H' T := by
  refine ⟨⟨hpred, fun t => ?_⟩, ?_⟩
  · filter_upwards [hH.1.2 t] with ω hω
    exact (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hle _ ω)).trans_lt hω
  · exact (lintegral_mono fun ω => lintegral_mono fun s =>
      ENNReal.ofReal_le_ofReal (hle _ ω)).trans_lt hH.2

/-- The part of an integrand after the deterministic time `t`. -/
noncomputable def after (t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => H s ω - stoppedInt (fun _ => t) H s ω

lemma after_of_le (t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (hs : s ≤ t) (ω : Ω) :
    after t H s ω = 0 := by
  simp [after, stoppedInt, Set.indicator_of_mem (show s ∈ {s | s ≤ (fun _ : Ω => t) ω} from hs)]

lemma after_of_lt (t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (hs : t < s) (ω : Ω) :
    after t H s ω = H s ω := by
  simp [after, stoppedInt,
    Set.indicator_of_notMem (show s ∉ {s | s ≤ (fun _ : Ω => t) ω} from not_le.mpr hs)]

lemma stopped_const (t : ℝ≥0) :
    IsStoppingTime S.ℱ (fun ω => (((fun _ : Ω => t) ω : ℝ≥0) : WithTop ℝ≥0)) :=
  isStoppingTime_const S.ℱ _

lemma after_U5 (t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (hH : U5 S.ℱ S.μ H T) :
    U5 S.ℱ S.μ (after t H) T := by
  refine U5_of_sq_le S H (after t H) T hH ?_ fun s ω => ?_
  · have h1 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H) := hH.1.1
    have h2 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry (stoppedInt (fun _ => t) H)) :=
      stoppedInt_predictable S (fun _ => t) (stopped_const S t) H hH.1.1
    exact h1.sub h2
  · rcases le_or_gt s t with hs | hs
    · rw [after_of_le t H s hs, zero_pow two_ne_zero]
      exact sq_nonneg _
    · rw [after_of_lt t H s hs]

lemma int_after (k : Fin S.m) (t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (s : ℝ≥0) :
    S.I k (after t H) s =ᵐ[S.μ] fun ω => S.I k H s ω - S.I k H (min s t) ω := by
  have hb : U4 S.ℱ S.μ (stoppedInt (fun _ => t) H) := by
    refine ⟨stoppedInt_predictable S (fun _ => t) (stopped_const S t) H hH.1, fun u => ?_⟩
    filter_upwards [hH.2 u] with ω hω
    refine (lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_).trans_lt hω
    show (Set.indicator {s | s ≤ (fun _ : Ω => t) ω} (fun _ => (1 : ℝ)) (Real.toNNReal s) *
      H (Real.toNNReal s) ω) ^ 2 ≤ (H (Real.toNNReal s) ω) ^ 2
    by_cases hs : Real.toNNReal s ≤ t
    · rw [Set.indicator_of_mem (show Real.toNNReal s ∈ {s | s ≤ (fun _ : Ω => t) ω} from hs),
        one_mul]
    · rw [Set.indicator_of_notMem (show Real.toNNReal s ∉ {s | s ≤ (fun _ : Ω => t) ω} from hs),
        zero_mul, zero_pow two_ne_zero]
      exact sq_nonneg _
  have ha : U4 S.ℱ S.μ (after t H) := by
    refine ⟨?_, fun u => ?_⟩
    · have h1 : StronglyMeasurable[S.ℱ.predictable] (Function.uncurry H) := hH.1
      exact h1.sub hb.1
    · filter_upwards [hH.2 u] with ω hω
      refine (lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_).trans_lt hω
      rcases le_or_gt (Real.toNNReal s) t with hs | hs
      · rw [after_of_le t H _ hs, zero_pow two_ne_zero]
        exact sq_nonneg _
      · rw [after_of_lt t H _ hs]
  have hsplit : (1 : ℝ) • stoppedInt (fun _ => t) H + (1 : ℝ) • after t H = H := by
    funext s ω
    simp [after]
  have hlin := S.int_linear k (stoppedInt (fun _ => t) H) (after t H) 1 1 hb ha s
  rw [hsplit] at hlin
  have hst := S.int_stopped k H (fun _ => t) hH (stopped_const S t) s
  filter_upwards [hlin, hst] with ω h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at h1
  change S.I k H (min s t) ω = S.I k (stoppedInt (fun _ => t) H) s ω at h2
  linarith

/-- The horizon-`T` product integrals over `(t, T]` as an indicator integral. -/
lemma after_product_integral (t T : ℝ≥0) (ht : t ≤ T) (H K : ℝ≥0 → Ω → ℝ) (c : ℝ≥0 → ℝ)
    (ω : Ω) :
    (∫ s in (0 : ℝ)..T, after t H (Real.toNNReal s) ω * after t K (Real.toNNReal s) ω *
        c (Real.toNNReal s)) =
      ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω * c (Real.toNNReal s) := by
  have hind : (fun s : ℝ => after t H (Real.toNNReal s) ω * after t K (Real.toNNReal s) ω *
      c (Real.toNNReal s)) = Set.indicator (Set.Ioi (t : ℝ))
        (fun s => H (Real.toNNReal s) ω * K (Real.toNNReal s) ω * c (Real.toNNReal s)) := by
    funext s
    by_cases hs : (t : ℝ) < s
    · have hs' : t < Real.toNNReal s := by
        have := (Real.toNNReal_lt_toNNReal_iff_of_nonneg t.coe_nonneg).mpr hs
        rwa [Real.toNNReal_coe] at this
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hs), after_of_lt t H _ hs', after_of_lt t K _ hs']
    · have hs' : Real.toNNReal s ≤ t := by
        have := Real.toNNReal_le_toNNReal (not_lt.mp hs)
        rwa [Real.toNNReal_coe] at this
      rw [Set.indicator_of_notMem (fun h => hs (Set.mem_Ioi.mp h)), after_of_le t H _ hs',
        zero_mul, zero_mul]
  have hset : Set.Ioc (0 : ℝ) T ∩ Set.Ioi (t : ℝ) = Set.Ioc (t : ℝ) T := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨t.coe_nonneg.trans_lt h1, h2⟩, h1⟩
  rw [hind, intervalIntegral.integral_of_le T.coe_nonneg, intervalIntegral.integral_of_le
    (NNReal.coe_le_coe.mpr ht), setIntegral_indicator measurableSet_Ioi, hset]

/-- Conditional isometry and orthogonality of increments. -/
lemma increments (k l : Fin S.m) (H K : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (hH : U5 S.ℱ S.μ H T) (hK : U5 S.ℱ S.μ K T) :
    MemLp (fun ω => S.I k H T ω - S.I k H t ω) 2 S.μ ∧
    S.μ[fun ω => (S.I k H T ω - S.I k H t ω) * (S.I l K T ω - S.I l K t ω) | S.ℱ t] =ᵐ[S.μ]
      S.μ[fun ω => ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
        S.c k l (Real.toNNReal s) | S.ℱ t] := by
  have hA := after_U5 S t H T hH
  have hA' := after_U5 S t K T hK
  have hIT : S.I k (after t H) T =ᵐ[S.μ] fun ω => S.I k H T ω - S.I k H t ω := by
    filter_upwards [int_after S k t H hH.1 T] with ω hω
    rw [hω, min_eq_right ht]
  have hIT' : S.I l (after t K) T =ᵐ[S.μ] fun ω => S.I l K T ω - S.I l K t ω := by
    filter_upwards [int_after S l t K hK.1 T] with ω hω
    rw [hω, min_eq_right ht]
  have hIt : S.I k (after t H) t =ᵐ[S.μ] 0 := by
    filter_upwards [int_after S k t H hH.1 t] with ω hω
    rw [hω, min_self, sub_self]
    rfl
  have hIt' : S.I l (after t K) t =ᵐ[S.μ] 0 := by
    filter_upwards [int_after S l t K hK.1 t] with ω hω
    rw [hω, min_self, sub_self]
    rfl
  have hL2 : MemLp (S.I k (after t H) T) 2 S.μ := (S.int_martingale k _ T hA).2 T le_rfl
  have hL2' : MemLp (S.I l (after t K) T) 2 S.μ := (S.int_martingale l _ T hA').2 T le_rfl
  refine ⟨hL2.ae_eq hIT, ?_⟩
  have hM := S.int_product_martingale k l (after t H) (after t K) T hA hA'
  set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k (after t H) (min u T) ω * S.I l (after t K) (min u T) ω -
    ∫ s in (0 : ℝ)..(min u T : ℝ≥0), after t H (Real.toNNReal s) ω *
      after t K (Real.toNNReal s) ω * S.c k l (Real.toNNReal s) with hMdef
  have hcond : S.μ[M T | S.ℱ t] =ᵐ[S.μ] M t := hM.condExp_ae_eq ht
  have hMt : M t =ᵐ[S.μ] 0 := by
    filter_upwards [hIt, hIt'] with ω h1 h2
    have hz : (∫ s in (0 : ℝ)..(t : ℝ), after t H (Real.toNNReal s) ω *
        after t K (Real.toNNReal s) ω * S.c k l (Real.toNNReal s)) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans
        intervalIntegral.integral_zero
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      have hs' : Real.toNNReal s ≤ t :=
        (Real.toNNReal_le_toNNReal hs.2).trans_eq Real.toNNReal_coe
      simp [after_of_le t H _ hs']
    simp only [hMdef, min_eq_left ht, hz, sub_zero]
    rw [show S.I k (after t H) t ω = 0 from h1, zero_mul]
    rfl
  set J : Ω → ℝ := fun ω => ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
    S.c k l (Real.toNNReal s) with hJdef
  have hMT : M T = fun ω => S.I k (after t H) T ω * S.I l (after t K) T ω - J ω := by
    funext ω
    simp only [hMdef, hJdef, min_self]
    rw [after_product_integral t T ht H K (S.c k l) ω]
  have hprod : Integrable (fun ω => S.I k (after t H) T ω * S.I l (after t K) T ω) S.μ :=
    hL2.integrable_mul hL2'
  have hJ : Integrable J S.μ := by
    have := hprod.sub (hM.integrable T)
    rw [hMT] at this
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  have hpair : (fun ω => (S.I k H T ω - S.I k H t ω) * (S.I l K T ω - S.I l K t ω)) =ᵐ[S.μ]
      fun ω => M T ω + J ω := by
    filter_upwards [hIT, hIT'] with ω h1 h2
    rw [hMT]
    simp only [h1, h2]
    ring
  calc S.μ[fun ω => (S.I k H T ω - S.I k H t ω) * (S.I l K T ω - S.I l K t ω) | S.ℱ t]
      =ᵐ[S.μ] S.μ[fun ω => M T ω + J ω | S.ℱ t] := condExp_congr_ae hpair
    _ =ᵐ[S.μ] S.μ[M T | S.ℱ t] + S.μ[J | S.ℱ t] := condExp_add (hM.integrable T) hJ _
    _ =ᵐ[S.μ] (0 : Ω → ℝ) + S.μ[J | S.ℱ t] := (hcond.trans hMt).add (ae_eq_refl _)
    _ = S.μ[J | S.ℱ t] := zero_add _

/-- The `[t, T]` product integral is integrable. -/
lemma increments_integrable (k l : Fin S.m) (H K : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (hH : U5 S.ℱ S.μ H T) (hK : U5 S.ℱ S.μ K T) :
    Integrable (fun ω => ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
      S.c k l (Real.toNNReal s)) S.μ := by
  have hA := after_U5 S t H T hH
  have hA' := after_U5 S t K T hK
  have hL2 : MemLp (S.I k (after t H) T) 2 S.μ := (S.int_martingale k _ T hA).2 T le_rfl
  have hL2' : MemLp (S.I l (after t K) T) 2 S.μ := (S.int_martingale l _ T hA').2 T le_rfl
  have hM := S.int_product_martingale k l (after t H) (after t K) T hA hA'
  have hprod : Integrable (fun ω => S.I k (after t H) T ω * S.I l (after t K) T ω) S.μ :=
    hL2.integrable_mul hL2'
  have := hprod.sub (hM.integrable T)
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, min_self]
  rw [after_product_integral t T ht H K (S.c k l) ω]
  ring

lemma incrementsProp : incrementStatement := by
  intro Ω mΩ S k l H K T t ht hH hK
  exact increments S k l H K T t ht hH hK

end Increments

/-! ### Two-driver increments: the conditional isometry (15.28) and cross-factor orthogonality -/

section TwoDriver
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma twoDriverIsometry (kw ku : Fin S.m) (Hw Hu : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (hHw : U5 S.ℱ S.μ Hw T) (hHu : U5 S.ℱ S.μ Hu T) :
    MemLp (twoDriverIncrement S kw ku Hw Hu T t) 2 S.μ ∧
    S.μ[fun ω => twoDriverIncrement S kw ku Hw Hu T t ω ^ 2 | S.ℱ t] =ᵐ[S.μ]
      S.μ[fun ω =>
        (∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hw (Real.toNNReal s) ω *
          S.c kw kw (Real.toNNReal s)) +
        2 * (∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
          S.c kw ku (Real.toNNReal s)) +
        (∫ s in (t : ℝ)..T, Hu (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
          S.c ku ku (Real.toNNReal s)) | S.ℱ t] := by
  set ΔW : Ω → ℝ := fun ω => S.I kw Hw T ω - S.I kw Hw t ω with hΔW
  set ΔU : Ω → ℝ := fun ω => S.I ku Hu T ω - S.I ku Hu t ω with hΔU
  set Jww : Ω → ℝ := fun ω => ∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hw (Real.toNNReal s) ω *
    S.c kw kw (Real.toNNReal s) with hJww
  set Jwu : Ω → ℝ := fun ω => ∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
    S.c kw ku (Real.toNNReal s) with hJwu
  set Juu : Ω → ℝ := fun ω => ∫ s in (t : ℝ)..T, Hu (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
    S.c ku ku (Real.toNNReal s) with hJuu
  obtain ⟨hW2, hWW⟩ := increments S kw kw Hw Hw T t ht hHw hHw
  obtain ⟨hU2, hUU⟩ := increments S ku ku Hu Hu T t ht hHu hHu
  have hWU := (increments S kw ku Hw Hu T t ht hHw hHu).2
  have hJww_int := increments_integrable S kw kw Hw Hw T t ht hHw hHw
  have hJwu_int := increments_integrable S kw ku Hw Hu T t ht hHw hHu
  have hJuu_int := increments_integrable S ku ku Hu Hu T t ht hHu hHu
  have hZ : twoDriverIncrement S kw ku Hw Hu T t = ΔW + ΔU := rfl
  refine ⟨by rw [hZ]; exact hW2.add hU2, ?_⟩
  -- the left side, expanded
  have hsq : (fun ω => twoDriverIncrement S kw ku Hw Hu T t ω ^ 2) =
      (fun ω => ΔW ω * ΔW ω) + (fun ω => 2 * (ΔW ω * ΔU ω)) + fun ω => ΔU ω * ΔU ω := by
    funext ω
    simp only [twoDriverIncrement, Pi.add_apply, hΔW, hΔU]
    ring
  have iWW : Integrable (fun ω => ΔW ω * ΔW ω) S.μ := hW2.integrable_mul hW2
  have iWU : Integrable (fun ω => ΔW ω * ΔU ω) S.μ := hW2.integrable_mul hU2
  have iUU : Integrable (fun ω => ΔU ω * ΔU ω) S.μ := hU2.integrable_mul hU2
  have iWU2 : Integrable (fun ω => 2 * (ΔW ω * ΔU ω)) S.μ := iWU.const_mul 2
  have hL1 := condExp_add (μ := S.μ) (iWW.add iWU2) iUU (S.ℱ t)
  have hL2 := condExp_add (μ := S.μ) iWW iWU2 (S.ℱ t)
  have hL3 : S.μ[fun ω => 2 * (ΔW ω * ΔU ω) | S.ℱ t] =ᵐ[S.μ]
      fun ω => 2 * (S.μ[fun ω => ΔW ω * ΔU ω | S.ℱ t]) ω := by
    have hf : (fun ω => 2 * (ΔW ω * ΔU ω)) = (2 : ℝ) • fun ω => ΔW ω * ΔU ω := by
      funext ω
      simp [smul_eq_mul]
    rw [hf]
    have h := condExp_smul (μ := S.μ) (m := S.ℱ t) (2 : ℝ) (fun ω => ΔW ω * ΔU ω)
    filter_upwards [h] with ω hω
    simpa [smul_eq_mul] using hω
  -- the right side, expanded
  have hR1 := condExp_add (μ := S.μ) (hJww_int.add (hJwu_int.const_mul 2)) hJuu_int (S.ℱ t)
  have hR2 := condExp_add (μ := S.μ) hJww_int (hJwu_int.const_mul 2) (S.ℱ t)
  have hR3 : S.μ[fun ω => 2 * Jwu ω | S.ℱ t] =ᵐ[S.μ] fun ω => 2 * (S.μ[Jwu | S.ℱ t]) ω := by
    have hf : (fun ω => 2 * Jwu ω) = (2 : ℝ) • Jwu := by
      funext ω
      simp [smul_eq_mul]
    rw [hf]
    have h := condExp_smul (μ := S.μ) (m := S.ℱ t) (2 : ℝ) Jwu
    filter_upwards [h] with ω hω
    simpa [smul_eq_mul] using hω
  rw [hsq]
  have hRfun : (fun ω => Jww ω + 2 * Jwu ω + Juu ω) = Jww + (fun ω => 2 * Jwu ω) + Juu := by
    funext ω
    simp only [Pi.add_apply]
  show S.μ[(fun ω => ΔW ω * ΔW ω) + (fun ω => 2 * (ΔW ω * ΔU ω)) + (fun ω => ΔU ω * ΔU ω)
    | S.ℱ t] =ᵐ[S.μ] S.μ[fun ω => Jww ω + 2 * Jwu ω + Juu ω | S.ℱ t]
  rw [hRfun]
  filter_upwards [hL1, hL2, hL3, hR1, hR2, hR3, hWW, hUU, hWU] with ω h1 h2 h3 r1 r2 r3 hww huu hwu
  rw [h1, r1]
  simp only [Pi.add_apply] at h2 r2 ⊢
  rw [h2, r2, h3, r3]
  have hww' : (S.μ[fun ω => ΔW ω * ΔW ω | S.ℱ t]) ω = (S.μ[Jww | S.ℱ t]) ω := hww
  have huu' : (S.μ[fun ω => ΔU ω * ΔU ω | S.ℱ t]) ω = (S.μ[Juu | S.ℱ t]) ω := huu
  have hwu' : (S.μ[fun ω => ΔW ω * ΔU ω | S.ℱ t]) ω = (S.μ[Jwu | S.ℱ t]) ω := hwu
  rw [hww', huu', hwu']

lemma twoDriverIsometryProp : twoDriverIsometryStatement := by
  intro Ω mΩ S kw ku Hw Hu T t ht hHw hHu
  exact twoDriverIsometry S kw ku Hw Hu T t ht hHw hHu

/-- A product of increments on drivers with zero covariation has zero conditional
expectation. -/
lemma crossTerm (k l : Fin S.m) (H K : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (hH : U5 S.ℱ S.μ H T) (hK : U5 S.ℱ S.μ K T) (hc : ∀ s, S.c k l s = 0) :
    S.μ[fun ω => (S.I k H T ω - S.I k H t ω) * (S.I l K T ω - S.I l K t ω) | S.ℱ t] =ᵐ[S.μ]
      0 := by
  have h := (increments S k l H K T t ht hH hK).2
  have hz : (fun ω => ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
      S.c k l (Real.toNNReal s)) = (0 : Ω → ℝ) := by
    funext ω
    simp [hc]
  rw [hz, condExp_zero] at h
  exact h

lemma crossFactor (kw ku kw' ku' : Fin S.m) (Hw Hu Hw' Hu' : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0)
    (ht : t ≤ T) (hHw : U5 S.ℱ S.μ Hw T) (hHu : U5 S.ℱ S.μ Hu T) (hHw' : U5 S.ℱ S.μ Hw' T)
    (hHu' : U5 S.ℱ S.μ Hu' T) (c1 : ∀ s, S.c kw kw' s = 0) (c2 : ∀ s, S.c kw ku' s = 0)
    (c3 : ∀ s, S.c ku kw' s = 0) (c4 : ∀ s, S.c ku ku' s = 0) :
    Integrable (fun ω => twoDriverIncrement S kw ku Hw Hu T t ω *
      twoDriverIncrement S kw' ku' Hw' Hu' T t ω) S.μ ∧
    S.μ[fun ω => twoDriverIncrement S kw ku Hw Hu T t ω *
      twoDriverIncrement S kw' ku' Hw' Hu' T t ω | S.ℱ t] =ᵐ[S.μ] 0 := by
  set ΔW : Ω → ℝ := fun ω => S.I kw Hw T ω - S.I kw Hw t ω with hΔW
  set ΔU : Ω → ℝ := fun ω => S.I ku Hu T ω - S.I ku Hu t ω with hΔU
  set ΔW' : Ω → ℝ := fun ω => S.I kw' Hw' T ω - S.I kw' Hw' t ω with hΔW'
  set ΔU' : Ω → ℝ := fun ω => S.I ku' Hu' T ω - S.I ku' Hu' t ω with hΔU'
  have hW2 := (increments S kw kw Hw Hw T t ht hHw hHw).1
  have hU2 := (increments S ku ku Hu Hu T t ht hHu hHu).1
  have hW2' := (increments S kw' kw' Hw' Hw' T t ht hHw' hHw').1
  have hU2' := (increments S ku' ku' Hu' Hu' T t ht hHu' hHu').1
  have hprod : (fun ω => twoDriverIncrement S kw ku Hw Hu T t ω *
      twoDriverIncrement S kw' ku' Hw' Hu' T t ω) =
      (fun ω => ΔW ω * ΔW' ω) + (fun ω => ΔW ω * ΔU' ω) +
        (fun ω => ΔU ω * ΔW' ω) + fun ω => ΔU ω * ΔU' ω := by
    funext ω
    simp only [twoDriverIncrement, Pi.add_apply, hΔW, hΔU, hΔW', hΔU']
    ring
  have i1 : Integrable (fun ω => ΔW ω * ΔW' ω) S.μ := hW2.integrable_mul hW2'
  have i2 : Integrable (fun ω => ΔW ω * ΔU' ω) S.μ := hW2.integrable_mul hU2'
  have i3 : Integrable (fun ω => ΔU ω * ΔW' ω) S.μ := hU2.integrable_mul hW2'
  have i4 : Integrable (fun ω => ΔU ω * ΔU' ω) S.μ := hU2.integrable_mul hU2'
  rw [hprod]
  refine ⟨((i1.add i2).add i3).add i4, ?_⟩
  have e1 := crossTerm S kw kw' Hw Hw' T t ht hHw hHw' c1
  have e2 := crossTerm S kw ku' Hw Hu' T t ht hHw hHu' c2
  have e3 := crossTerm S ku kw' Hu Hw' T t ht hHu hHw' c3
  have e4 := crossTerm S ku ku' Hu Hu' T t ht hHu hHu' c4
  have a1 := condExp_add (μ := S.μ) ((i1.add i2).add i3) i4 (S.ℱ t)
  have a2 := condExp_add (μ := S.μ) (i1.add i2) i3 (S.ℱ t)
  have a3 := condExp_add (μ := S.μ) i1 i2 (S.ℱ t)
  filter_upwards [a1, a2, a3, e1, e2, e3, e4] with ω h1 h2 h3 g1 g2 g3 g4
  rw [h1]
  simp only [Pi.add_apply] at h2 h3 ⊢
  rw [h2, h3]
  have g1' : (S.μ[fun ω => ΔW ω * ΔW' ω | S.ℱ t]) ω = (0 : Ω → ℝ) ω := g1
  have g2' : (S.μ[fun ω => ΔW ω * ΔU' ω | S.ℱ t]) ω = (0 : Ω → ℝ) ω := g2
  have g3' : (S.μ[fun ω => ΔU ω * ΔW' ω | S.ℱ t]) ω = (0 : Ω → ℝ) ω := g3
  have g4' : (S.μ[fun ω => ΔU ω * ΔU' ω | S.ℱ t]) ω = (0 : Ω → ℝ) ω := g4
  rw [g1', g2', g3', g4']
  simp

lemma crossFactorProp : crossFactorStatement := by
  intro Ω mΩ S kw ku kw' ku' Hw Hu Hw' Hu' T t ht hHw hHu hHw' hHu' c1 c2 c3 c4
  exact crossFactor S kw ku kw' ku' Hw Hu Hw' Hu' T t ht hHw hHu hHw' hHu' c1 c2 c3 c4

end TwoDriver

/-! ### Square integrability of the coefficient integrands from the state mean -/

section Coefficients
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- The predictable σ-algebra is coarser than the product σ-algebra. -/
lemma predictable_le_prod (ℱ : Filtration ℝ≥0 mΩ) :
    ℱ.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact (measurableSet_singleton _).prod (ℱ.le _ _ hA)
  · exact measurableSet_Ioi.prod (ℱ.le _ _ hA)

/-- Joint measurability of a predictable process in real time. -/
lemma predictable_joint_measurable (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable S.ℱ H) :
    Measurable (fun p : ℝ × Ω => H (Real.toNNReal p.1) p.2) := by
  have h1 : Measurable[S.ℱ.predictable] (Function.uncurry H) := hH.measurable
  have h2 : Measurable (Function.uncurry H) := h1.mono (predictable_le_prod S.ℱ) le_rfl
  exact h2.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

lemma sq_integrand_bound (K : ℝ≥0 → ℝ) (C : ℝ) (T : ℝ≥0) (hK : ∀ s, s ≤ T → |K s| ≤ C)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (j : Fin d) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) ≤
      ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (X (Real.toNNReal s) ω j) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hsT : Real.toNNReal s ≤ T := (Real.toNNReal_le_toNNReal hs.2).trans_eq Real.toNNReal_coe
  have hK2 : (K (Real.toNNReal s)) ^ 2 ≤ C ^ 2 :=
    sq_le_sq' (abs_le.mp (hK _ hsT)).1 (abs_le.mp (hK _ hsT)).2
  exact mul_le_mul_of_nonneg_right hK2 (NNReal.coe_nonneg _)

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The coefficient integrand `K √v_j` is (U5) on every horizon. -/
lemma coefficient_U5 (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (j : Fin d) (K : ℝ≥0 → ℝ) (hKm : Measurable K)
    (hKb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) (T : ℝ≥0) :
    U5 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) T := by
  have hpred : IsStronglyPredictable S.ℱ (fun s ω => K s * Real.sqrt (X s ω j)) :=
    Upstream.ItoCalculus.predictable_const_mul S.ℱ K hKm _ (hsq j)
  have hjm : Measurable (fun p : ℝ × Ω =>
      ENNReal.ofReal ((K (Real.toNNReal p.1) * Real.sqrt (X (Real.toNNReal p.1) p.2 j)) ^ 2)) :=
    ((predictable_joint_measurable S _ hpred).pow_const 2).ennreal_ofReal
  have hmean : ∀ s : ℝ,
      ∫⁻ ω, ENNReal.ofReal (X (Real.toNNReal s) ω j) ∂S.μ = ENNReal.ofReal (x0 j) := by
    intro s
    obtain ⟨-, -, -, hj⟩ :=
      transform d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde (Real.toNNReal s)
    obtain ⟨hL2, hm, -⟩ := hj j
    simp only [stateR, Real.toNNReal_coe] at hL2 hm
    have hint : Integrable (fun ω => (X (Real.toNNReal s) ω j : ℝ)) S.μ := hL2.integrable one_le_two
    rw [← hm, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => NNReal.coe_nonneg _)]
  have hbound : ∀ T' : ℝ≥0, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T',
      ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2)) ∂S.μ
        < ⊤ := by
    intro T'
    obtain ⟨C, hC⟩ := hKb T'
    have hswap := lintegral_lintegral_swap (μ := S.μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
      (f := fun ω s => ENNReal.ofReal
        ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2))
      (hjm.comp measurable_swap).aemeasurable
    rw [hswap]
    calc ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ ω, ENNReal.ofReal
          ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) ∂S.μ
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T', ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x0 j) := by
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          calc ∫⁻ ω, ENNReal.ofReal
                ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) ∂S.μ
              ≤ ∫⁻ ω, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (X (Real.toNNReal s) ω j) ∂S.μ :=
                lintegral_mono fun ω => sq_integrand_bound K C T' hC X j s hs ω
            _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x0 j) := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmean s]
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
  refine ⟨⟨hpred, fun t => ?_⟩, hbound T⟩
  have hmeas : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2)) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      (hjm.comp measurable_swap)
  exact ae_lt_top' hmeas.aemeasurable (hbound t).ne

lemma coefficientProp : coefficientStatement := by
  intro d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j K hKm hKb T
  exact coefficient_U5 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j K hKm hKb T

lemma sqrt_integrand_eq (K₁ K₂ : ℝ≥0 → ℝ) (c : ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (j : Fin d)
    (s : ℝ≥0) (ω : Ω) :
    (K₁ s * Real.sqrt (X s ω j)) * (K₂ s * Real.sqrt (X s ω j)) * c =
      K₁ s * K₂ s * c * (X s ω j : ℝ) := by
  have h := Real.mul_self_sqrt (NNReal.coe_nonneg (X s ω j))
  linear_combination (K₁ s * K₂ s * c) * h

lemma actualIncrement : actualIncrementStatement := by
  intro d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq kw K₁ K₂ hK₁m hK₂m hK₁b hK₂b
    T t ht
  have hU5 : ∀ (j : Fin d) (K : ℝ≥0 → ℝ), Measurable K →
      (∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) →
      U5 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) T :=
    fun j K hKm hKb => coefficient_U5 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j K hKm hKb T
  refine ⟨fun j => ?_, fun i j c1 c2 c3 c4 => ?_⟩
  · obtain ⟨h1, h2⟩ := twoDriverIsometry S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
      (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ht (hU5 j (K₁ j) (hK₁m j) (hK₁b j))
      (hU5 j (K₂ j) (hK₂m j) (hK₂b j))
    refine ⟨h1, ?_⟩
    have e1 : ∀ (s : ℝ) (ω : Ω), (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (kw j) (kw j) (Real.toNNReal s) =
        K₁ j (Real.toNNReal s) ^ 2 * S.c (kw j) (kw j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := by
      intro s ω
      rw [sqrt_integrand_eq, sq]
    have e2 : ∀ (s : ℝ) (ω : Ω), (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (kw j) (k j) (Real.toNNReal s) =
        K₁ j (Real.toNNReal s) * K₂ j (Real.toNNReal s) * S.c (kw j) (k j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := fun s ω => sqrt_integrand_eq _ _ _ X j _ ω
    have e3 : ∀ (s : ℝ) (ω : Ω), (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (k j) (k j) (Real.toNNReal s) =
        K₂ j (Real.toNNReal s) ^ 2 * S.c (k j) (k j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := by
      intro s ω
      rw [sqrt_integrand_eq, sq]
    simp only [e1, e2, e3] at h2
    exact h2
  · exact crossFactor S (kw i) (k i) (kw j) (k j) _ _ _ _ T t ht
      (hU5 i (K₁ i) (hK₁m i) (hK₁b i)) (hU5 i (K₂ i) (hK₂m i) (hK₂b i))
      (hU5 j (K₁ j) (hK₁m j) (hK₁b j)) (hU5 j (K₂ j) (hK₂m j) (hK₂b j)) c1 c2 c3 c4

end Coefficients

/-! ### The full kernel: combining the covariation integrals along continuous paths -/

section Kernel
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- A bounded measurable product of three functions is interval integrable. -/
lemma intervalIntegrable_bounded (F G K : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (h0 : 0 ≤ a)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) (CF CG CK : ℝ)
    (hCF : ∀ u ∈ Set.Icc (0 : ℝ) b, |F u| ≤ CF) (hCG : ∀ u ∈ Set.Icc (0 : ℝ) b, |G u| ≤ CG)
    (hCK : ∀ u ∈ Set.Icc (0 : ℝ) b, |K u| ≤ CK) :
    IntervalIntegrable (fun u => F u * G u * K u) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := CF * CG * CK) measure_Ioc_lt_top.ne
    ((hF.mul hG).mul hK).aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc
      fun u hu => ?_)
  have hu' : u ∈ Set.Icc (0 : ℝ) b := by
    rw [min_eq_left hab, max_eq_right hab] at hu
    exact ⟨h0.trans hu.1.le, hu.2⟩
  have hab' : a ∈ Set.Icc (0 : ℝ) b := ⟨h0, hab⟩
  have hCF0 : 0 ≤ CF := (abs_nonneg _).trans (hCF a hab')
  have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hCG a hab')
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hCF u hu') (hCG u hu') (abs_nonneg _) hCF0) (hCK u hu')
    (abs_nonneg _) (mul_nonneg hCF0 hCG0)

/-- The kernel identity (15.28) along a continuous path: the three covariation integrals
combine into the full-kernel integral. -/
lemma kernel_combine {m d : ℕ} (k kw : Fin d → Fin S.m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ)
    (T : Fin m → ℝ) (n : Fin m) (j : Fin d)
    (hg : Measurable (g n j)) (hgb : ∀ T' : ℝ, ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C)
    (hR : Measurable (fun u : ℝ => ∫ s in u..T n, b n j s))
    (hRb : ∀ T' : ℝ, ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |∫ s in u..T n, b n j s| ≤ C)
    (hcww : ∀ s, S.c (kw j) (kw j) s = 1) (hcuu : ∀ s, S.c (k j) (k j) s = 1)
    (hcwu : ∀ s, S.c (kw j) (k j) s = ρ j s) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T n) (ω : Ω)
    (hcont : Continuous fun u => (X u ω j : ℝ)) :
    (∫ s in ((Real.toNNReal t : ℝ≥0) : ℝ)..((Real.toNNReal (T n) : ℝ≥0) : ℝ),
        g n j ((Real.toNNReal s : ℝ≥0) : ℝ) ^ 2 * S.c (kw j) (kw j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ)) +
      2 * (∫ s in ((Real.toNNReal t : ℝ≥0) : ℝ)..((Real.toNNReal (T n) : ℝ≥0) : ℝ),
        g n j ((Real.toNNReal s : ℝ≥0) : ℝ) *
          (α j * ∫ u in ((Real.toNNReal s : ℝ≥0) : ℝ)..T n, b n j u) *
          S.c (kw j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) +
      (∫ s in ((Real.toNNReal t : ℝ≥0) : ℝ)..((Real.toNNReal (T n) : ℝ≥0) : ℝ),
        (α j * ∫ u in ((Real.toNNReal s : ℝ≥0) : ℝ)..T n, b n j u) ^ 2 *
          S.c (k j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) =
    I0154 g b ρ α T t (stateR X) n j ω := by
  have hT0 : 0 ≤ T n := ht0.trans htT
  rw [Real.coe_toNNReal t ht0, Real.coe_toNNReal (T n) hT0]
  -- bounds on `[0, T n]`
  obtain ⟨Cg, hCg⟩ := hgb (T n)
  obtain ⟨CR, hCR⟩ := hRb (T n)
  obtain ⟨Cc, hCc⟩ := S.c_bounded_on_compacts (kw j) (kw j) (Real.toNNReal (T n))
  obtain ⟨Cc', hCc'⟩ := S.c_bounded_on_compacts (kw j) (k j) (Real.toNNReal (T n))
  obtain ⟨Cc'', hCc''⟩ := S.c_bounded_on_compacts (k j) (k j) (Real.toNNReal (T n))
  have hcontR : Continuous fun u : ℝ => (X (Real.toNNReal u) ω j : ℝ) :=
    hcont.comp continuous_real_toNNReal
  obtain ⟨CX, hCX⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T n)).exists_bound_of_continuousOn
    hcontR.continuousOn
  have hXm : Measurable fun u : ℝ => (X (Real.toNNReal u) ω j : ℝ) := hcontR.measurable
  have hgm : Measurable fun u : ℝ => g n j ((Real.toNNReal u : ℝ≥0) : ℝ) :=
    hg.comp (NNReal.continuous_coe.measurable.comp measurable_real_toNNReal)
  have hRm : Measurable fun u : ℝ => α j * ∫ s in ((Real.toNNReal u : ℝ≥0) : ℝ)..T n, b n j s :=
    (hR.comp (NNReal.continuous_coe.measurable.comp measurable_real_toNNReal)).const_mul _
  have hcoe : ∀ u ∈ Set.Icc (0 : ℝ) (T n), ((Real.toNNReal u : ℝ≥0) : ℝ) = u :=
    fun u hu => Real.coe_toNNReal u hu.1
  have hle : ∀ u ∈ Set.Icc (0 : ℝ) (T n), Real.toNNReal u ≤ Real.toNNReal (T n) :=
    fun u hu => Real.toNNReal_le_toNNReal hu.2
  have hgb' : ∀ u ∈ Set.Icc (0 : ℝ) (T n), |g n j ((Real.toNNReal u : ℝ≥0) : ℝ)| ≤ Cg :=
    fun u hu => by rw [hcoe u hu]; exact hCg u hu
  have hRb' : ∀ u ∈ Set.Icc (0 : ℝ) (T n),
      |α j * ∫ s in ((Real.toNNReal u : ℝ≥0) : ℝ)..T n, b n j s| ≤ |α j| * CR :=
    fun u hu => by
      rw [hcoe u hu, abs_mul]
      exact mul_le_mul_of_nonneg_left (hCR u hu) (abs_nonneg _)
  have hXb : ∀ u ∈ Set.Icc (0 : ℝ) (T n), |(X (Real.toNNReal u) ω j : ℝ)| ≤ CX :=
    fun u hu => by rw [← Real.norm_eq_abs]; exact hCX u hu
  have hsq : ∀ (F : ℝ → ℝ) (C : ℝ), (∀ u ∈ Set.Icc (0 : ℝ) (T n), |F u| ≤ C) →
      ∀ u ∈ Set.Icc (0 : ℝ) (T n), |F u ^ 2| ≤ C ^ 2 := fun F C hF u hu => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF u hu) 2
  have hprod : ∀ (F G : ℝ → ℝ) (CF CG : ℝ), (∀ u ∈ Set.Icc (0 : ℝ) (T n), |F u| ≤ CF) →
      (∀ u ∈ Set.Icc (0 : ℝ) (T n), |G u| ≤ CG) →
      ∀ u ∈ Set.Icc (0 : ℝ) (T n), |F u * G u| ≤ CF * CG := fun F G CF CG hF hG u hu => by
    rw [abs_mul]
    exact mul_le_mul (hF u hu) (hG u hu) (abs_nonneg _)
      ((abs_nonneg _).trans (hF 0 ⟨le_rfl, hT0⟩))
  have hi1 := intervalIntegrable_bounded (fun u => g n j ((Real.toNNReal u : ℝ≥0) : ℝ) ^ 2)
    (fun u => S.c (kw j) (kw j) (Real.toNNReal u)) (fun u => (X (Real.toNNReal u) ω j : ℝ))
    t (T n) htT ht0 (hgm.pow_const 2) ((S.c_measurable _ _).comp measurable_real_toNNReal) hXm
    _ _ _ (hsq _ _ hgb') (fun u hu => hCc _ (hle u hu)) hXb
  have hi2 := intervalIntegrable_bounded (fun u => g n j ((Real.toNNReal u : ℝ≥0) : ℝ) *
      (α j * ∫ s in ((Real.toNNReal u : ℝ≥0) : ℝ)..T n, b n j s))
    (fun u => S.c (kw j) (k j) (Real.toNNReal u)) (fun u => (X (Real.toNNReal u) ω j : ℝ))
    t (T n) htT ht0 (hgm.mul hRm) ((S.c_measurable _ _).comp measurable_real_toNNReal) hXm
    _ _ _ (hprod _ _ _ _ hgb' hRb') (fun u hu => hCc' _ (hle u hu)) hXb
  have hi3 := intervalIntegrable_bounded
    (fun u => (α j * ∫ s in ((Real.toNNReal u : ℝ≥0) : ℝ)..T n, b n j s) ^ 2)
    (fun u => S.c (k j) (k j) (Real.toNNReal u)) (fun u => (X (Real.toNNReal u) ω j : ℝ))
    t (T n) htT ht0 (hRm.pow_const 2) ((S.c_measurable _ _).comp measurable_real_toNNReal) hXm
    _ _ _ (hsq _ _ hRb') (fun u hu => hCc'' _ (hle u hu)) hXb
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 (hi2.const_mul 2),
    ← intervalIntegral.integral_add (hi1.add (hi2.const_mul 2)) hi3]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le htT] at hu
  have hu' : u ∈ Set.Icc (0 : ℝ) (T n) := ⟨ht0.trans hu.1, hu.2⟩
  simp only [hcoe u hu', hcww, hcuu, hcwu, K0154, stateR]
  ring

lemma kernelIsometry : kernelIsometryStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T n hg hgb hR hRb
    hcww hcuu hcwu t ht0 htT
  have hK₁m : ∀ j, Measurable (fun s : ℝ≥0 => g n j s) :=
    fun j => (hg j).comp NNReal.continuous_coe.measurable
  have hK₂m : ∀ j, Measurable (fun s : ℝ≥0 => α j * ∫ u in (s : ℝ)..T n, b n j u) :=
    fun j => ((hR j).comp NNReal.continuous_coe.measurable).const_mul _
  have hK₁b : ∀ j (T' : ℝ≥0), ∃ C, ∀ s, s ≤ T' → |g n j s| ≤ C := fun j T' => by
    obtain ⟨C, hC⟩ := hgb j T'
    exact ⟨C, fun s hs => hC s ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩⟩
  have hK₂b : ∀ j (T' : ℝ≥0), ∃ C, ∀ s, s ≤ T' →
      |α j * ∫ u in (s : ℝ)..T n, b n j u| ≤ |α j| * C := fun j T' => by
    obtain ⟨C, hC⟩ := hRb j T'
    exact ⟨C, fun s hs => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC s ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩)
        (abs_nonneg _)⟩
  have hK₂b' : ∀ j (T' : ℝ≥0), ∃ C, ∀ s, s ≤ T' →
      |α j * ∫ u in (s : ℝ)..T n, b n j u| ≤ C := fun j T' =>
    let ⟨C, hC⟩ := hK₂b j T'; ⟨|α j| * C, hC⟩
  have htT' : Real.toNNReal t ≤ Real.toNNReal (T n) := Real.toNNReal_le_toNNReal htT
  obtain ⟨hiso, hcross⟩ := actualIncrement d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde
    hsq kw (fun j s => g n j s) (fun j s => α j * ∫ u in (s : ℝ)..T n, b n j u) hK₁m hK₂m hK₁b
    hK₂b' (Real.toNNReal (T n)) (Real.toNNReal t) htT'
  refine ⟨fun i j => (hiso i).1.integrable_mul (hiso j).1, fun j => ?_, fun i j c1 c2 c3 c4 =>
    (hcross i j c1 c2 c3 c4).2⟩
  refine (hiso j).2.trans (condExp_congr_ae ?_)
  filter_upwards [hcont j] with ω hω
  exact kernel_combine S k kw α X g b ρ T n j (hg j) (hgb j) (hR j) (hRb j) (hcww j) (hcuu j)
    (hcwu j) t ht0 htT ω hω

end Kernel

/-! ### The product rule (15.26) from the Itô-formula field -/

section ProductRule
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma dT_general {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (s : ℝ)
    (x : Fin n → ℝ) : dT f (s, x) = deriv (fun u => f (u, x)) s := by
  have hL : HasDerivAt (fun u : ℝ => (u, x)) ((1 : ℝ), (0 : Fin n → ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h := ((hf.differentiable (by norm_num)) (s, x)).hasFDerivAt.comp_hasDerivAt s hL
  rw [dT, ← h.deriv]
  rfl

lemma dX_general {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (s : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    dX f (s, x) i = deriv (fun u => f (s, Function.update x i u)) (x i) := by
  classical
  have hL : HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)) (x i) :=
    (hasDerivAt_const _ s).prodMk (hasDerivAt_update x i (x i))
  have h := ((hf.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt (x i) hL
  rw [Function.update_eq_self] at h
  rw [dX, ← h.deriv]
  rfl

lemma dXX_general {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (s : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    dXX f (s, x) i i = deriv (deriv (fun u => f (s, Function.update x i u))) (x i) := by
  classical
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hL : ∀ u, HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)) u :=
    fun u => (hasDerivAt_const u s).prodMk (hasDerivAt_update x i u)
  have hg : ∀ u, HasDerivAt (fun u => f (s, Function.update x i u))
      (fderiv ℝ f (s, Function.update x i u) (0, Pi.single i 1)) u :=
    fun u => (hfd _).hasFDerivAt.comp_hasDerivAt u (hL u)
  have hderiv : deriv (fun u => f (s, Function.update x i u)) =
      fun u => fderiv ℝ f (s, Function.update x i u) (0, Pi.single i 1) :=
    funext fun u => (hg u).deriv
  have h2 : HasDerivAt (fun u => fderiv ℝ f (s, Function.update x i u) (0, Pi.single i 1))
      (fderiv ℝ (fderiv ℝ f) (s, Function.update x i (x i)) (0, Pi.single i 1)
        (0, Pi.single i 1)) (x i) := by
    have hc : HasDerivAt (fun u => fderiv ℝ f (s, Function.update x i u))
        (fderiv ℝ (fderiv ℝ f) (s, Function.update x i (x i)) (0, Pi.single i 1)) (x i) :=
      (hf' _).hasFDerivAt.comp_hasDerivAt (x i) (hL (x i))
    have := hc.clm_apply (hasDerivAt_const (x i) ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)))
    simpa using this
  rw [dXX, hderiv, h2.deriv, Function.update_eq_self]

/-- The weighted coordinate `f(s, x) = R(s) x_j`. -/
def fprod (R : ℝ → ℝ) (j : Fin d) (p : ℝ × (Fin d → ℝ)) : ℝ := R p.1 * p.2 j

lemma fprod_contDiff (R : ℝ → ℝ) (hR : ContDiff ℝ 2 R) (j : Fin d) :
    ContDiff ℝ 2 (fprod R j) :=
  (hR.comp contDiff_fst).mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)

lemma fprod_dT (R : ℝ → ℝ) (hR : ContDiff ℝ 2 R) (j : Fin d) (s : ℝ) (x : Fin d → ℝ) :
    dT (fprod R j) (s, x) = deriv R s * x j := by
  rw [dT_general _ (fprod_contDiff R hR j)]
  exact deriv_mul_const (hR.differentiable (by norm_num) s) (x j)

lemma fprod_dX (R : ℝ → ℝ) (hR : ContDiff ℝ 2 R) (j : Fin d) (s : ℝ) (x : Fin d → ℝ)
    (i : Fin d) : dX (fprod R j) (s, x) i = if i = j then R s else 0 := by
  classical
  rw [dX_general _ (fprod_contDiff R hR j)]
  show deriv (fun u => R s * Function.update x i u j) (x i) = _
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, if_true]
    rw [deriv_const_mul _ differentiableAt_id, deriv_id'']
    ring
  · simp only [Function.update_of_ne (Ne.symm hij), if_neg hij]
    exact deriv_const _ _

lemma fprod_dXX (R : ℝ → ℝ) (hR : ContDiff ℝ 2 R) (j : Fin d) (s : ℝ) (x : Fin d → ℝ)
    (i : Fin d) : dXX (fprod R j) (s, x) i i = 0 := by
  classical
  rw [dXX_general _ (fprod_contDiff R hR j)]
  show deriv (deriv (fun u => R s * Function.update x i u j)) (x i) = 0
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    have : deriv (fun u : ℝ => R s * u) = fun _ => R s := by
      funext u
      rw [deriv_const_mul _ differentiableAt_id, deriv_id'']
      ring
    rw [this]
    exact deriv_const _ _
  · simp only [Function.update_of_ne (Ne.symm hij)]
    have : deriv (fun _ : ℝ => R s * x j) = fun _ => (0 : ℝ) := funext fun u => deriv_const _ _
    rw [this]
    exact deriv_const _ _

/-- The drift of the Itô formula for the weighted coordinate: `R'(s) x_j`. -/
lemma fprod_drift (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 2 R) (j : Fin d) (s : ℝ) (ω : Ω) :
    dT (fprod R j) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      ∑ i, dX (fprod R j) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i * (0 : ℝ) +
      (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ k', ∑ l',
        dXX (fprod R j) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i' *
          Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X i' l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s) =
    deriv R s * (X (Real.toNNReal s) ω j : ℝ) := by
  classical
  set x : Fin d → ℝ := fun i => (X (Real.toNNReal s) ω i : ℝ) with hx
  have hq : ∀ i i', (∑ k', ∑ l', dXX (fprod R j) (s, x) i i' *
      Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X i' l' (Real.toNNReal s) ω *
        S.c k' l' (Real.toNNReal s)) = 0 := by
    intro i i'
    rw [quad_sum S k α X (fun i i' => dXX (fprod R j) (s, x) i i') i i', hc]
    split_ifs with hii'
    · subst hii'
      rw [fprod_dXX R hR j s x i]
      ring
    · simp
  simp only [hq, Finset.sum_const_zero, mul_zero, add_zero, fprod_dT R hR j s x]
  rfl

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The product rule (15.26) from the field AX-05. -/
lemma productRule (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (j : Fin d) (R b : ℝ → ℝ) (hR : ContDiff ℝ 2 R) (hb : ∀ u, HasDerivAt R (-(b u)) u) :
    U4 S.ℱ S.μ (fun (s : ℝ≥0) ω => R (s : ℝ) * (α j * Real.sqrt (X s ω j))) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, R t * (X t ω j : ℝ) =
      R 0 * (x0 j : ℝ) - (∫ u in (0 : ℝ)..t, b u * (X (Real.toNNReal u) ω j : ℝ)) +
        S.I (k j) (fun (s : ℝ≥0) ω => R (s : ℝ) * (α j * Real.sqrt (X s ω j))) t ω := by
  classical
  obtain ⟨hU4, hae⟩ := S.ito_formula d (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0)
    (fprod R j) (fun i k' => Hdrv_U4 S k α X hU i k') (fun _ => zeroDrift S)
    (fprod_contDiff R hR j)
  have hint : (fun (s : ℝ≥0) ω => dX (fprod R j)
      ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) j *
        Hdrv k α X j (k j) s ω) = fun (s : ℝ≥0) ω => R (s : ℝ) * (α j * Real.sqrt (X s ω j)) := by
    funext s ω
    rw [fprod_dX R hR j]
    simp [Hdrv]
  refine ⟨hint ▸ hU4 j (k j), ?_⟩
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  filter_upwards [hae, driverForm_eq S k α X x0 hx0 hsde, hz] with ω hω hdf hz
  intro t
  have h := hω t
  have hsum : (∑ i, ∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (fprod R j)
      ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) i *
        Hdrv k α X i k' s ω) t ω) =
      S.I (k j) (fun (s : ℝ≥0) ω => R (s : ℝ) * (α j * Real.sqrt (X s ω j))) t ω := by
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single (k j)]
      · rw [hint]
      · intro k' _ hk'
        have hzero : (fun (s : ℝ≥0) ω => dX (fprod R j)
            ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) j *
              Hdrv k α X j k' s ω) = fun _ _ => (0 : ℝ) := by
          funext s ω
          simp [Hdrv, ite_eq_right hk']
        rw [hzero]
        exact hz k' t
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · intro i _ hij
      refine Finset.sum_eq_zero fun k' _ => ?_
      have hzero : (fun (s : ℝ≥0) ω => dX (fprod R j)
          ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) i *
            Hdrv k α X i k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        rw [fprod_dX R hR j, if_neg hij, zero_mul]
      rw [hzero]
      exact hz k' t
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  rw [hsum] at h
  have hdrift : (∫ s in (0 : ℝ)..t, (dT (fprod R j)
      (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) (Real.toNNReal s) ω) +
      ∑ i, dX (fprod R j)
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) (Real.toNNReal s) ω)
          i * (0 : ℝ) +
      (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ k', ∑ l', dXX (fprod R j)
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) (Real.toNNReal s) ω)
          i i' * Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X i' l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s))) =
      -(∫ u in (0 : ℝ)..t, b u * (X (Real.toNNReal u) ω j : ℝ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hdf (Real.toNNReal s), fprod_drift S k α X hc R hR j s ω, (hb s).deriv]
    ring
  rw [hdrift, hdf t] at h
  have h0 : fprod R j (0, fun j => (x0 j : ℝ)) = R 0 * (x0 j : ℝ) := rfl
  have ht : fprod R j ((t : ℝ), fun i => (X t ω i : ℝ)) = R t * (X t ω j : ℝ) := rfl
  rw [h0, ht] at h
  rw [h]
  ring

lemma productRuleProp : productRuleStatement := by
  intro d Ω mΩ S k α X x0 hc hx0 hU hsde j R b hR hb
  obtain ⟨hU4, hae⟩ := productRule S k α X x0 hc hx0 hU hsde j R b hR hb
  refine ⟨hU4, hae, fun hcont T hRT => ?_⟩
  have hbc : Continuous b := by
    have h1 : Continuous (deriv R) := hR.continuous_deriv (by norm_num)
    have h2 : deriv R = fun u => -(b u) := funext fun u => (hb u).deriv
    rw [h2] at h1
    have h3 : b = fun u => -(-(b u)) := funext fun u => (neg_neg _).symm
    rw [h3]
    exact h1.neg
  filter_upwards [hae, hcont] with ω hω hcω
  intro t ht
  have hX : Continuous fun u : ℝ => (X (Real.toNNReal u) ω j : ℝ) :=
    hcω.comp continuous_real_toNNReal
  have hi : ∀ a c : ℝ, IntervalIntegrable (fun u => b u * (X (Real.toNNReal u) ω j : ℝ))
      volume a c := fun a c => (hbc.mul hX).intervalIntegrable a c
  have hT := hω T
  have htt := hω t
  rw [hRT, zero_mul] at hT
  have hsplit := intervalIntegral.integral_interval_sub_left (hi 0 T) (hi 0 t)
  rw [← hsplit]
  linarith

end ProductRule

/-! ### The product rule for an absolutely continuous weight -/

section ProductRuleAC
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- The product of the state coordinate `j` with the appended weight coordinate. -/
def fpair (j : Fin d) (p : ℝ × (Fin (d+1) → ℝ)) : ℝ := p.2 (Fin.castSucc j) * p.2 (Fin.last d)

lemma fpair_contDiff (j : Fin d) : ContDiff ℝ 2 (fpair (d := d) j) := by
  unfold fpair
  fun_prop

lemma fpair_dT (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) : dT (fpair j) (s, z) = 0 := by
  rw [dT_general (n := d+1) (fpair j) (fpair_contDiff j)]
  show deriv (fun _ : ℝ => z (Fin.castSucc j) * z (Fin.last d)) s = 0
  exact deriv_const _ _

/-- The coordinate derivatives of `fpair` as functions of the moving coordinate. -/
lemma fpair_deriv (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    deriv (fun u => fpair j (s, Function.update z i u)) =
      fun _ => if i = Fin.castSucc j then z (Fin.last d)
        else if i = Fin.last d then z (Fin.castSucc j) else 0 := by
  classical
  funext u
  simp only [fpair]
  by_cases h1 : i = Fin.castSucc j
  · subst h1
    simp only [Function.update_self, Function.update_of_ne (Fin.castSucc_ne_last j).symm,
      ite_true]
    rw [deriv_mul_const differentiableAt_id, deriv_id'']
    ring
  · by_cases h2 : i = Fin.last d
    · subst h2
      simp only [Function.update_self, Function.update_of_ne (Fin.castSucc_ne_last j), h1,
        ite_false, ite_true]
      rw [deriv_const_mul _ differentiableAt_id, deriv_id'']
      ring
    · simp only [Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h2), h1, h2,
        ite_false]
      exact deriv_const _ _

lemma fpair_dX (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    dX (fpair j) (s, z) i = if i = Fin.castSucc j then z (Fin.last d)
      else if i = Fin.last d then z (Fin.castSucc j) else 0 := by
  rw [dX_general (n := d+1) (fpair j) (fpair_contDiff j), fpair_deriv]

lemma fpair_dXX (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    dXX (fpair j) (s, z) i i = 0 := by
  rw [dXX_general (n := d+1) (fpair j) (fpair_contDiff j), fpair_deriv]
  exact deriv_const _ _

/-- The extended integrand family: the drivers of the state and none for the weight. -/
noncomputable def Hext (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) :
    Fin (d+1) → Fin S.m → ℝ≥0 → Ω → ℝ :=
  Fin.snoc (fun a => Hdrv k α X a) (fun _ _ _ => 0)
/-- The extended drift family: none for the state and `−b` for the weight. -/
noncomputable def Kext (b : ℝ → ℝ) : Fin (d+1) → ℝ≥0 → Ω → ℝ :=
  Fin.snoc (fun _ => fun _ _ => 0) (fun (s : ℝ≥0) _ => -(b s))
/-- The extended initial value. -/
noncomputable def xext (x0 : Fin d → NNReal) (R0 : ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc (fun a => (x0 a : ℝ)) R0

lemma Hext_castSucc (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (a : Fin d) : Hext S k α X (Fin.castSucc a) = Hdrv k α X a := Fin.snoc_castSucc _ _ _
lemma Hext_last (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) :
    Hext S k α X (Fin.last d) = fun _ _ _ => 0 := Fin.snoc_last _ _
lemma Kext_castSucc (b : ℝ → ℝ) (a : Fin d) :
    Kext (Ω := Ω) (d := d) b (Fin.castSucc a) = fun _ _ => 0 := Fin.snoc_castSucc _ _ _
lemma Kext_last (b : ℝ → ℝ) : Kext (Ω := Ω) (d := d) b (Fin.last d) = fun (s : ℝ≥0) _ => -(b s) :=
  Fin.snoc_last _ _

lemma Hext_U4 (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) (i : Fin (d+1))
    (k' : Fin S.m) : U4 S.ℱ S.μ (Hext S k α X i k') := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · rw [Hext_last]
    exact U4_zero S
  · rw [Hext_castSucc]
    exact Hdrv_U4 S k α X hU a k'

lemma Kext_drift (b : ℝ → ℝ) (hb : Measurable b)
    (hbint : ∀ t : ℝ, IntervalIntegrable b volume 0 t) (i : Fin (d+1)) :
    LocallyIntegrableDrift S.ℱ S.μ (Kext (Ω := Ω) b i) := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · rw [Kext_last]
    refine ⟨fun t => ?_, fun t => ?_⟩
    · exact ((hb.comp (NNReal.continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst))).neg).stronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      have hI : IntegrableOn b (Set.Icc (0 : ℝ) t) volume :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg).mp (hbint t)
      have h2 := hI.2
      rw [HasFiniteIntegral] at h2
      refine lt_of_eq_of_lt ?_ h2
      refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      show ENNReal.ofReal |-(b ((Real.toNNReal s : ℝ≥0) : ℝ))| = ‖b s‖ₑ
      rw [Real.coe_toNNReal s hs.1, abs_neg, Real.enorm_eq_ofReal_abs]
  · rw [Kext_castSucc]
    exact zeroDrift S

/-- The extended driver-form process is the state with the weight appended. -/
lemma driverFormExt_eq (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (b : ℝ → ℝ) (R0 : ℝ) :
    ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) t ω =
      Fin.snoc (fun a => (X t ω a : ℝ)) (weightAC b R0 t) := by
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hs : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω := ae_all_iff.2 hsde
  filter_upwards [hz, hs, hx0] with ω hz hs hx0
  intro t
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · rw [Fin.snoc_last]
    show xext x0 R0 (Fin.last d) + (∑ k', S.I k' (Hext S k α X (Fin.last d) k') t ω) +
      (∫ s in (0 : ℝ)..(t : ℝ), Kext b (Fin.last d) (Real.toNNReal s) ω) = weightAC b R0 t
    rw [Hext_last, Kext_last]
    have hx : xext x0 R0 (Fin.last d) = R0 := Fin.snoc_last _ _
    have hI0 : (∑ k', S.I k' (fun _ _ => (0 : ℝ)) t ω) = 0 :=
      Finset.sum_eq_zero fun k' _ => hz k' t
    have hneg : (∫ s in (0 : ℝ)..(t : ℝ), (fun (s : ℝ≥0) (_ : Ω) => -(b s)) (Real.toNNReal s) ω) =
        -(∫ u in (0 : ℝ)..(t : ℝ), b u) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le t.coe_nonneg] at hu
      show -(b ((Real.toNNReal u : ℝ≥0) : ℝ)) = -(b u)
      rw [Real.coe_toNNReal u hu.1]
    rw [hx, hI0, hneg, weightAC]
    ring
  · rw [Fin.snoc_castSucc]
    show xext x0 R0 (Fin.castSucc a) + (∑ k', S.I k' (Hext S k α X (Fin.castSucc a) k') t ω) +
      (∫ s in (0 : ℝ)..(t : ℝ), Kext b (Fin.castSucc a) (Real.toNNReal s) ω) = (X t ω a : ℝ)
    rw [Hext_castSucc, Kext_castSucc]
    have hK0 : (∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (Real.toNNReal s) ω)
        = 0 := intervalIntegral.integral_zero
    have hx : xext x0 R0 (Fin.castSucc a) = (x0 a : ℝ) := Fin.snoc_castSucc _ _ _
    rw [hK0, add_zero, hx]
    have hx0i : X 0 ω a = x0 a := congrFun hx0 a
    rw [Finset.sum_eq_single (k a)]
    · simp only [Hdrv, eq_self_iff_true, ite_true]
      rw [hs a t, hx0i]
    · intro k' _ hk'
      simp only [Hdrv, ite_eq_right hk']
      exact hz k' t
    · intro h
      exact absurd (Finset.mem_univ _) h

lemma weightAC_continuous (b : ℝ → ℝ) (hbint : ∀ t : ℝ, IntervalIntegrable b volume 0 t)
    (R0 : ℝ) : Continuous (weightAC b R0) := by
  unfold weightAC
  refine continuous_const.sub ?_
  refine intervalIntegral.continuous_primitive (fun a c => ?_) 0
  exact (hbint a).symm.trans (hbint c)

lemma weightAC_U4 (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) (j : Fin d) (b : ℝ → ℝ)
    (hbint : ∀ t : ℝ, IntervalIntegrable b volume 0 t) (R0 : ℝ) :
    U4 S.ℱ S.μ (fun (s : ℝ≥0) ω => weightAC b R0 s * (α j * Real.sqrt (X s ω j))) := by
  have hRc := weightAC_continuous b hbint R0
  refine ⟨Upstream.ItoCalculus.predictable_const_mul S.ℱ (fun s : ℝ≥0 => weightAC b R0 s)
    (hRc.measurable.comp NNReal.continuous_coe.measurable) _ (hU j).1, fun t => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hRc.continuousOn
  filter_upwards [(hU j).2 t] with ω hω
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, t.coe_nonneg⟩)
  calc ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal
        ((weightAC b R0 ((Real.toNNReal s : ℝ≥0) : ℝ) *
          (α j * Real.sqrt (X (Real.toNNReal s) ω j))) ^ 2)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (C ^ 2) *
          ENNReal.ofReal ((α j * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_pow]
        have hR : |weightAC b R0 ((Real.toNNReal s : ℝ≥0) : ℝ)| ≤ C := by
          rw [Real.coe_toNNReal s hs.1, ← Real.norm_eq_abs]
          exact hC s hs
        have hR2 : (weightAC b R0 ((Real.toNNReal s : ℝ≥0) : ℝ)) ^ 2 ≤ C ^ 2 :=
          sq_le_sq' (abs_le.mp hR).1 (abs_le.mp hR).2
        exact mul_le_mul_of_nonneg_right hR2 (sq_nonneg _)
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((α j * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω

/-- The quadratic term of the Itô formula for the extended process vanishes. -/
lemma quad_ext (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) (j : Fin d) (s : ℝ)
    (z : Fin (d+1) → ℝ) (u : ℝ≥0) (ω : Ω) :
    (∑ i, ∑ i', ∑ k', ∑ l', dXX (fpair j) (s, z) i i' * Hext S k α X i k' u ω *
      Hext S k α X i' l' u ω * S.c k' l' u) = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
  refine Fin.lastCases ?_ (fun a' => ?_) i'
  · simp [Hext_last]
  · refine Fin.lastCases ?_ (fun a => ?_) i
    · simp [Hext_last]
    · rw [Hext_castSucc, Hext_castSucc,
        quad_sum S k α X (fun a a' => dXX (fpair j) (s, z) (Fin.castSucc a) (Fin.castSucc a'))
          a a' u ω, hc]
      split_ifs with haa
      · subst haa
        rw [fpair_dXX]
        ring
      · simp

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma productRuleAC : productRuleACStatement := by
  intro d Ω mΩ S k α X x0 hc hx0 hU hsde j b R0 hb hbint
  refine ⟨weightAC_U4 S k α X hU j b hbint R0, ?_⟩
  obtain ⟨hU4, hae⟩ := S.ito_formula (d+1) (xext x0 R0) (Hext S k α X) (Kext b) (fpair j)
    (Hext_U4 S k α X hU) (Kext_drift S b hb hbint) (fpair_contDiff j)
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hdfae := driverFormExt_eq S k α X x0 hx0 hsde b R0
  have hint : ∀ᵐ ω ∂S.μ, ∀ t, S.I (k j) (fun (s : ℝ≥0) ω => dX (fpair j)
      ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω) (Fin.castSucc j) *
        Hext S k α X (Fin.castSucc j) (k j) s ω) t ω =
      S.I (k j) (fun (s : ℝ≥0) ω => weightAC b R0 s * (α j * Real.sqrt (X s ω j))) t ω := by
    refine int_congr_ae S (k j) _ _ (hU4 (Fin.castSucc j) (k j))
      (weightAC_U4 S k α X hU j b hbint R0) ?_
    filter_upwards [hdfae] with ω hdf s
    rw [fpair_dX, hdf s, if_pos rfl, Fin.snoc_last, Hext_castSucc]
    simp [Hdrv]
  filter_upwards [hae, hdfae, hz, hint] with ω hω hdf hz hint
  intro t
  have h := hω t
  have hsum : (∑ i, ∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (fpair j)
      ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω) i *
        Hext S k α X i k' s ω) t ω) =
      S.I (k j) (fun (s : ℝ≥0) ω => weightAC b R0 s * (α j * Real.sqrt (X s ω j))) t ω := by
    rw [Fin.sum_univ_castSucc]
    have hlast : (∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (fpair j)
        ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω) (Fin.last d) *
          Hext S k α X (Fin.last d) k' s ω) t ω) = 0 := by
      refine Finset.sum_eq_zero fun k' _ => ?_
      have hzero : (fun (s : ℝ≥0) ω => dX (fpair j)
          ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω) (Fin.last d) *
            Hext S k α X (Fin.last d) k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        rw [Hext_last]
        simp
      rw [hzero]
      exact hz k' t
    rw [hlast, add_zero, Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single (k j)]
      · exact hint t
      · intro k' _ hk'
        have hzero : (fun (s : ℝ≥0) ω => dX (fpair j)
            ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω)
              (Fin.castSucc j) * Hext S k α X (Fin.castSucc j) k' s ω) = fun _ _ => (0 : ℝ) := by
          funext s ω
          rw [Hext_castSucc]
          simp [Hdrv, ite_eq_right hk']
        rw [hzero]
        exact hz k' t
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · intro a _ haj
      refine Finset.sum_eq_zero fun k' _ => ?_
      have hzero : (fun (s : ℝ≥0) ω => dX (fpair j)
          ((s : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) s ω) (Fin.castSucc a) *
            Hext S k α X (Fin.castSucc a) k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        rw [fpair_dX, if_neg (Fin.castSucc_inj.not.mpr haj), if_neg (Fin.castSucc_ne_last a),
          zero_mul]
      rw [hzero]
      exact hz k' t
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  rw [hsum] at h
  have hdrift : (∫ s in (0 : ℝ)..t, (dT (fpair j)
      (s, driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) (Real.toNNReal s) ω) +
      ∑ i, dX (fpair j)
        (s, driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) (Real.toNNReal s) ω) i *
          Kext b i (Real.toNNReal s) ω +
      (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ k', ∑ l', dXX (fpair j)
        (s, driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) (Real.toNNReal s) ω) i i' *
          Hext S k α X i k' (Real.toNNReal s) ω * Hext S k α X i' l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s))) =
      -(∫ u in (0 : ℝ)..t, b u * (X (Real.toNNReal u) ω j : ℝ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    rw [hdf (Real.toNNReal s), fpair_dT, quad_ext S k α X hc j]
    have hd : (∑ i, dX (fpair j) (s, Fin.snoc (fun a => (X (Real.toNNReal s) ω a : ℝ))
        (weightAC b R0 ((Real.toNNReal s : ℝ≥0) : ℝ))) i * Kext b i (Real.toNNReal s) ω) =
        -(b s * (X (Real.toNNReal s) ω j : ℝ)) := by
      rw [Fin.sum_univ_castSucc]
      have h1 : (∑ a : Fin d, dX (fpair j) (s, Fin.snoc (fun a => (X (Real.toNNReal s) ω a : ℝ))
          (weightAC b R0 ((Real.toNNReal s : ℝ≥0) : ℝ))) (Fin.castSucc a) *
            Kext b (Fin.castSucc a) (Real.toNNReal s) ω) = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [Kext_castSucc]; simp
      rw [h1, zero_add, fpair_dX, if_neg (Fin.castSucc_ne_last j).symm, if_pos rfl, Kext_last,
        Fin.snoc_castSucc]
      show (X (Real.toNNReal s) ω j : ℝ) * -(b ((Real.toNNReal s : ℝ≥0) : ℝ)) = _
      rw [Real.coe_toNNReal s hs.1]
      ring
    rw [hd]
    ring
  rw [hdrift] at h
  have hL : fpair j ((t : ℝ), driverForm S.I (xext x0 R0) (Hext S k α X) (Kext b) t ω) =
      weightAC b R0 t * (X t ω j : ℝ) := by
    rw [hdf t]
    simp only [fpair, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have h0 : fpair j (0, xext x0 R0) = R0 * (x0 j : ℝ) := by
    simp only [fpair, xext, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [hL, h0] at h
  rw [h]
  ring

end ProductRuleAC

/-! ### The centered representation of the meeting jump -/

section Centered
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma backwardWeight : backwardWeightStatement := by
  intro b T hb
  have hbc : Continuous b := hb.continuous
  have hd : ∀ u, HasDerivAt (fun u => ∫ s in u..T, b s) (-(b u)) u := fun u =>
    intervalIntegral.integral_hasDerivAt_left (hbc.intervalIntegrable _ _)
      (hbc.stronglyMeasurableAtFilter _ _) hbc.continuousAt
  refine ⟨?_, hd, intervalIntegral.integral_same⟩
  have hderiv : deriv (fun u => ∫ s in u..T, b s) = fun u => -(b u) := funext fun u => (hd u).deriv
  have h22 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h22]
  refine (contDiff_succ_iff_deriv (n := 1)).mpr ⟨fun u => (hd u).differentiableAt, ?_, ?_⟩
  · intro h
    exact absurd h WithTop.one_ne_top
  · rw [hderiv]
    exact hb.neg

/-- Conditional expectation of a finite sum. -/
lemma condExp_finsum {n : ℕ} (f : Fin n → Ω → ℝ) (t : ℝ≥0)
    (hf : ∀ i, Integrable (f i) S.μ) :
    S.μ[fun ω => ∑ i, f i ω | S.ℱ t] =ᵐ[S.μ] fun ω => ∑ i, (S.μ[f i | S.ℱ t]) ω := by
  classical
  have key : ∀ s : Finset (Fin n), S.μ[fun ω => ∑ i ∈ s, f i ω | S.ℱ t] =ᵐ[S.μ]
      fun ω => ∑ i ∈ s, (S.μ[f i | S.ℱ t]) ω := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Ω => (0 : ℝ)) = (0 : Ω → ℝ) from rfl, condExp_zero]
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have h := condExp_add (μ := S.μ) (hf a) (integrable_finset_sum s fun i _ => hf i) (S.ℱ t)
      have h' : S.μ[fun ω => f a ω + ∑ i ∈ s, f i ω | S.ℱ t] =ᵐ[S.μ]
          S.μ[f a | S.ℱ t] + S.μ[fun ω => ∑ i ∈ s, f i ω | S.ℱ t] := h
      filter_upwards [h', ih] with ω h1 h2
      rw [h1, Pi.add_apply, h2]
  exact key Finset.univ

lemma increment_condExp_zero (k : Fin S.m) (H : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (hH : U5 S.ℱ S.μ H T) :
    S.μ[fun ω => S.I k H T ω - S.I k H t ω | S.ℱ t] =ᵐ[S.μ] 0 := by
  have hM := (S.int_martingale k H T hH).1
  have h1 : S.μ[fun ω => S.I k H (min T T) ω | S.ℱ t] =ᵐ[S.μ] fun ω => S.I k H (min t T) ω :=
    hM.condExp_ae_eq ht
  simp only [min_self, min_eq_left ht] at h1
  have hint : Integrable (S.I k H t) S.μ :=
    ((S.int_martingale k H T hH).2 t ht).integrable one_le_two
  have hmeas : StronglyMeasurable[S.ℱ t] (S.I k H t) :=
    (S.int_adapted k H hH.1 t).stronglyMeasurable
  have h2 := condExp_sub (μ := S.μ) (((S.int_martingale k H T hH).2 T le_rfl).integrable
    one_le_two) hint (S.ℱ t)
  have h3 : S.μ[S.I k H t | S.ℱ t] = S.I k H t :=
    condExp_of_stronglyMeasurable (S.ℱ.le t) hmeas hint
  have h2' : S.μ[fun ω => S.I k H T ω - S.I k H t ω | S.ℱ t] =ᵐ[S.μ]
      S.μ[S.I k H T | S.ℱ t] - S.μ[S.I k H t | S.ℱ t] := h2
  filter_upwards [h2', h1] with ω h2 h1
  rw [h2, Pi.sub_apply, h3, Pi.zero_apply]
  have h1' : (S.μ[S.I k H T | S.ℱ t]) ω = S.I k H t ω := h1
  rw [h1', sub_self]

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The centered representation for continuous weights satisfying the product rule at the
horizon. -/
lemma centered_core {m d : ℕ} (k kw : Fin d → Fin S.m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m) (R : Fin d → ℝ → ℝ)
    (hg : ∀ j, Measurable (g n j))
    (hgb : ∀ j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C)
    (hRc : ∀ j, Continuous (R j))
    (hprod : ∀ j, ∀ᵐ ω ∂S.μ,
      (∫ u in (0 : ℝ)..T n, b n j u * (X (Real.toNNReal u) ω j : ℝ)) =
        R j 0 * (x0 j : ℝ) + S.I (k j) (fun (s : ℝ≥0) ω => R j (s : ℝ) * (α j * Real.sqrt (X s ω j)))
          (Real.toNNReal (T n)) ω)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T n) :
    Integrable (Yactual S kw X g b T n) S.μ ∧
    Yactual S kw X g b T n - S.μ[Yactual S kw X g b T n | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
      fun ω => ∑ j, twoDriverIncrement S (kw j) (k j)
        (fun s ω => g n j s * Real.sqrt (X s ω j))
        (fun s ω => R j s * (α j * Real.sqrt (X s ω j)))
        (Real.toNNReal (T n)) (Real.toNNReal t) ω := by
  have htT' : Real.toNNReal t ≤ Real.toNNReal (T n) := Real.toNNReal_le_toNNReal htT
  -- the integrands
  set Hw : Fin d → ℝ≥0 → Ω → ℝ := fun j s ω => g n j s * Real.sqrt (X s ω j) with hHw
  set Hu : Fin d → ℝ≥0 → Ω → ℝ := fun j (s : ℝ≥0) ω => R j (s : ℝ) * (α j * Real.sqrt (X s ω j))
    with hHu
  have hU5w : ∀ j, U5 S.ℱ S.μ (Hw j) (Real.toNNReal (T n)) := fun j =>
    coefficient_U5 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j (fun s => g n j s)
      ((hg j).comp NNReal.continuous_coe.measurable) (fun T' => by
        obtain ⟨C, hC⟩ := hgb j T'
        exact ⟨C, fun s hs => hC s ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩⟩) _
  have hU5u : ∀ j, U5 S.ℱ S.μ (Hu j) (Real.toNNReal (T n)) := by
    intro j
    have hRc : Continuous (R j) := hRc j
    have hK : Measurable (fun s : ℝ≥0 => R j (s : ℝ) * α j) :=
      (hRc.measurable.comp NNReal.continuous_coe.measurable).mul_const _
    have hKb : ∀ T' : ℝ≥0, ∃ C, ∀ s : ℝ≥0, s ≤ T' → |R j (s : ℝ) * α j| ≤ C := fun T' => by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T')).exists_bound_of_continuousOn
        hRc.continuousOn
      exact ⟨C * |α j|, fun s hs => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by
          rw [← Real.norm_eq_abs]; exact hC s ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩)
          (abs_nonneg _)⟩
    have h := coefficient_U5 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j
      (fun s : ℝ≥0 => R j (s : ℝ) * α j) hK hKb (Real.toNNReal (T n))
    have he : (fun (s : ℝ≥0) ω => (R j (s : ℝ) * α j) * Real.sqrt (X s ω j)) = Hu j := by
      funext s ω
      simp only [hHu]
      ring
    rw [he] at h
    exact h
  have hall : ∀ᵐ ω ∂S.μ, ∀ j, (∫ u in (0 : ℝ)..T n, b n j u * (X (Real.toNNReal u) ω j : ℝ)) =
      R j 0 * (x0 j : ℝ) + S.I (k j) (Hu j) (Real.toNNReal (T n)) ω := ae_all_iff.2 hprod
  -- decomposition Y = A + Z
  set A : Fin d → Ω → ℝ := fun j ω => R j 0 * (x0 j : ℝ) + S.I (k j) (Hu j) (Real.toNNReal t) ω +
    S.I (kw j) (Hw j) (Real.toNNReal t) ω with hA
  set Z : Fin d → Ω → ℝ := fun j => twoDriverIncrement S (kw j) (k j) (Hw j) (Hu j)
    (Real.toNNReal (T n)) (Real.toNNReal t) with hZ
  have hY : Yactual S kw X g b T n =ᵐ[S.μ] fun ω => ∑ j, (A j ω + Z j ω) := by
    filter_upwards [hall] with ω hω
    simp only [Yactual, hA, hZ, twoDriverIncrement]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω j]
    ring
  have hL2 : ∀ (k' : Fin S.m) (H : ℝ≥0 → Ω → ℝ), U5 S.ℱ S.μ H (Real.toNNReal (T n)) →
      ∀ u, u ≤ Real.toNNReal (T n) → Integrable (S.I k' H u) S.μ := fun k' H hH u hu =>
    ((S.int_martingale k' H _ hH).2 u hu).integrable one_le_two
  have hAint : ∀ j, Integrable (A j) S.μ := fun j =>
    ((integrable_const _).add (hL2 (k j) (Hu j) (hU5u j) _ htT')).add (hL2 (kw j) (Hw j) (hU5w j) _ htT')
  have hZint : ∀ j, Integrable (Z j) S.μ := fun j =>
    ((hL2 (kw j) (Hw j) (hU5w j) _ le_rfl).sub (hL2 (kw j) (Hw j) (hU5w j) _ htT')).add
      ((hL2 (k j) (Hu j) (hU5u j) _ le_rfl).sub (hL2 (k j) (Hu j) (hU5u j) _ htT'))
  have hYint : Integrable (Yactual S kw X g b T n) S.μ :=
    (integrable_finset_sum Finset.univ fun j _ => (hAint j).add (hZint j)).congr hY.symm
  refine ⟨hYint, ?_⟩
  -- conditional expectations
  have hAcond : ∀ j, S.μ[A j | S.ℱ (Real.toNNReal t)] = A j := fun j =>
    condExp_of_stronglyMeasurable (S.ℱ.le _)
      ((stronglyMeasurable_const.add (S.int_adapted _ _ (hU5u j).1 _).stronglyMeasurable).add
        (S.int_adapted _ _ (hU5w j).1 _).stronglyMeasurable) (hAint j)
  have hZcond : ∀ j, S.μ[Z j | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] 0 := by
    intro j
    have h1 := increment_condExp_zero S (kw j) (Hw j) _ _ htT' (hU5w j)
    have h2 := increment_condExp_zero S (k j) (Hu j) _ _ htT' (hU5u j)
    have h := condExp_add (μ := S.μ) ((hL2 (kw j) (Hw j) (hU5w j) _ le_rfl).sub (hL2 (kw j) (Hw j) (hU5w j) _ htT'))
      ((hL2 (k j) (Hu j) (hU5u j) _ le_rfl).sub (hL2 (k j) (Hu j) (hU5u j) _ htT')) (S.ℱ (Real.toNNReal t))
    have h' : S.μ[Z j | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
        S.μ[fun ω => S.I (kw j) (Hw j) (Real.toNNReal (T n)) ω - S.I (kw j) (Hw j) (Real.toNNReal t) ω
          | S.ℱ (Real.toNNReal t)] +
        S.μ[fun ω => S.I (k j) (Hu j) (Real.toNNReal (T n)) ω - S.I (k j) (Hu j) (Real.toNNReal t) ω
          | S.ℱ (Real.toNNReal t)] := h
    filter_upwards [h', h1, h2] with ω h' h1 h2
    rw [h', Pi.add_apply]
    have h1' : (S.μ[fun ω => S.I (kw j) (Hw j) (Real.toNNReal (T n)) ω -
        S.I (kw j) (Hw j) (Real.toNNReal t) ω | S.ℱ (Real.toNNReal t)]) ω = 0 := h1
    have h2' : (S.μ[fun ω => S.I (k j) (Hu j) (Real.toNNReal (T n)) ω -
        S.I (k j) (Hu j) (Real.toNNReal t) ω | S.ℱ (Real.toNNReal t)]) ω = 0 := h2
    rw [h1', h2', add_zero]
    rfl
  have hsum := condExp_finsum S (fun j ω => A j ω + Z j ω) (Real.toNNReal t)
    fun j => (hAint j).add (hZint j)
  have hterm : ∀ j, S.μ[fun ω => A j ω + Z j ω | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] A j := by
    intro j
    have h := condExp_add (μ := S.μ) (hAint j) (hZint j) (S.ℱ (Real.toNNReal t))
    have h' : S.μ[fun ω => A j ω + Z j ω | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
        S.μ[A j | S.ℱ (Real.toNNReal t)] + S.μ[Z j | S.ℱ (Real.toNNReal t)] := h
    filter_upwards [h', hZcond j] with ω h' hz
    rw [h', Pi.add_apply, hAcond j]
    have hz' : (S.μ[Z j | S.ℱ (Real.toNNReal t)]) ω = 0 := hz
    rw [hz', add_zero]
  have hterms : ∀ᵐ ω ∂S.μ, ∀ j, (S.μ[fun ω => A j ω + Z j ω | S.ℱ (Real.toNNReal t)]) ω = A j ω :=
    ae_all_iff.2 hterm
  have hcondY : S.μ[Yactual S kw X g b T n | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] fun ω => ∑ j, A j ω := by
    refine (condExp_congr_ae hY).trans ?_
    filter_upwards [hsum, hterms] with ω h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  filter_upwards [hY, hcondY] with ω hY hcondY
  rw [Pi.sub_apply, hY, hcondY, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma centered : centeredStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b T n R hg hgb hR hR'
    hRT t ht0 htT
  have hT0 : 0 ≤ T n := ht0.trans htT
  refine centered_core S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b T n R hg hgb
    (fun j => (hR j).continuous) (fun j => ?_) t ht0 htT
  obtain ⟨-, hae⟩ := productRule S k α X x0 hc hx0 hU hsde j (R j) (b n j) (hR j) (hR' j)
  filter_upwards [hae] with ω hω
  have h := hω (Real.toNNReal (T n))
  rw [Real.coe_toNNReal _ hT0, hRT j, zero_mul] at h
  linarith

/-- The backward weight of a locally integrable coefficient is the absolutely continuous
weight started at the total integral. -/
lemma backward_eq_weightAC (b : ℝ → ℝ) (hbint : ∀ t : ℝ, IntervalIntegrable b volume 0 t)
    (T : ℝ) : (fun u => ∫ s in u..T, b s) = weightAC b (∫ s in (0 : ℝ)..T, b s) := by
  funext u
  unfold weightAC
  exact (intervalIntegral.integral_interval_sub_left (hbint T) (hbint u)).symm

lemma backward_continuous (b : ℝ → ℝ) (hbint : ∀ t : ℝ, IntervalIntegrable b volume 0 t)
    (T : ℝ) : Continuous (fun u => ∫ s in u..T, b s) := by
  rw [backward_eq_weightAC b hbint T]
  exact weightAC_continuous b hbint _

lemma centeredAC : centeredACStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b T n hg hgb hbm hbint
    t ht0 htT
  have hT0 : 0 ≤ T n := ht0.trans htT
  have h := centered_core S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b T n
    (fun j u => ∫ s in u..T n, b n j s) hg hgb (fun j => backward_continuous (b n j) (hbint j) _)
    (fun j => ?_) t ht0 htT
  · exact h
  · set R0 := ∫ s in (0 : ℝ)..T n, b n j s with hR0
    have hRw : ∀ u, (∫ s in u..T n, b n j s) = weightAC (b n j) R0 u := fun u =>
      congrFun (backward_eq_weightAC (b n j) (hbint j) (T n)) u
    obtain ⟨-, hae⟩ := productRuleAC d Ω mΩ S k α X x0 hc hx0 hU hsde j (b n j) R0 (hbm j)
      (hbint j)
    filter_upwards [hae] with ω hω
    have h := hω (Real.toNNReal (T n))
    rw [Real.coe_toNNReal _ hT0] at h
    have hT : weightAC (b n j) R0 (T n) = 0 := by
      unfold weightAC
      exact sub_self _
    have h00 : weightAC (b n j) R0 0 = R0 := by
      unfold weightAC
      rw [intervalIntegral.integral_same, sub_zero]
    rw [hT, zero_mul] at h
    simp only [hRw, h00]
    linarith

end Centered

/-! ### Assembling the five `H0154` fields from the fields -/

section Assembly
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma intervalIntegrable_of_bound (f : ℝ → ℝ) (hf : Measurable f) (a b : ℝ) (hab : a ≤ b)
    (C : ℝ) (hC : ∀ u ∈ Set.Icc a b, |f u| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
  rw [min_eq_left hab, max_eq_right hab] at hu
  rw [Real.norm_eq_abs]
  exact hC u ⟨hu.1.le, hu.2⟩

/-- The actual increment with the backward weight written as a product-rule weight. -/
lemma Zactual_eq_R {m d : ℕ} (k kw : Fin d → Fin S.m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (n : Fin m) (j : Fin d) :
    Zactual S k kw α X g b T t n j = twoDriverIncrement S (kw j) (k j)
      (fun s ω => g n j s * Real.sqrt (X s ω j))
      (fun (s : ℝ≥0) ω => (fun u => ∫ s in u..T n, b n j s) (s : ℝ) * (α j * Real.sqrt (X s ω j)))
      (Real.toNNReal (T n)) (Real.toNNReal t) := by
  have : (fun (s : ℝ≥0) ω => α j * (∫ u in (s : ℝ)..T n, b n j u) * Real.sqrt (X s ω j)) =
      fun (s : ℝ≥0) ω => (fun u => ∫ s in u..T n, b n j s) (s : ℝ) * (α j * Real.sqrt (X s ω j)) := by
    funext s ω
    ring
  unfold Zactual
  rw [this]

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- Joint measurability of an almost surely continuous adapted state on a time interval,
through its everywhere-continuous modification on a null set of the initial σ-algebra. -/
lemma joint_measurable_ae {d : ℕ} (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t)) (U : NNReal) (j : Fin d) (a b : ℝ) (ha : 0 ≤ a)
    (hb : b ≤ U) :
    AEStronglyMeasurable (fun p : ℝ × Ω => (stateR X p.1 p.2 j : ℝ))
      ((volume.restrict (Set.Ioc a b)).prod S.μ) := by
  classical
  have hae : ∀ᵐ ω ∂S.μ, ∀ j, Continuous fun t => (X t ω j : ℝ) := ae_all_iff.2 hcont
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hN0 : MeasurableSet[S.ℱ 0] N := S.usual_null N hNmeas hNnull
  have hNt : ∀ t, MeasurableSet[S.ℱ t] N := fun t => S.ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN0
  set X' : ℝ≥0 → Ω → Fin d → NNReal := fun t => N.piecewise (fun _ => (0 : Fin d → NNReal)) (X t)
    with hX'def
  have hX'N : ∀ t ω, ω ∈ N → X' t ω = 0 := fun t ω hω => Set.piecewise_eq_of_mem _ _ _ hω
  have hX'nN : ∀ t ω, ω ∉ N → X' t ω = X t ω := fun t ω hω => Set.piecewise_eq_of_notMem _ _ _ hω
  have hcont' : ∀ ω j, Continuous fun t => (X' t ω j : ℝ) := by
    intro ω j
    by_cases hω : ω ∈ N
    · simp only [hX'N _ ω hω]
      exact continuous_const
    · simp only [hX'nN _ ω hω]
      have : ω ∉ {ω | ¬ ∀ j, Continuous fun t => (X t ω j : ℝ)} := fun h => hω (hNsub h)
      simp only [Set.mem_ofPred_eq, not_not] at this
      exact this j
  have hadapt' : ∀ t, Measurable[S.ℱ t] (X' t) := fun t =>
    Measurable.piecewise (hNt t) measurable_const (hadapt t)
  have hX' : ∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[filtR S.ℱ s] (stateR X' s) :=
    fun s _ => hadapt' _
  have hcontU' : ∀ ω, Continuous (fun s : Set.Icc (0 : ℝ) U => (stateR X' s.val ω j : ℝ)) :=
    fun ω => (hcont' ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  have h := localized_state_jointly_measurable S.μ (filtR S.ℱ) U (stateR X') hX' j hcontU' a b
    ha hb
  refine h.congr ?_
  refine ae_iff.2 (measure_mono_null (t := (Set.univ ×ˢ N : Set (ℝ × Ω))) (fun p hp => ?_) ?_)
  · refine ⟨Set.mem_univ _, ?_⟩
    by_contra hpN
    exact hp (by simp only [stateR, hX'nN _ _ hpN])
  · rw [Measure.prod_prod, hNnull, mul_zero]

open Novel.ZeroMeanReversionVarianceSupportProof in
/-- The assembly from continuous backward weights and a centered representation. -/
lemma assembly_core {m d : ℕ} (k kw : Fin d → Fin S.m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont_ae : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ)
    (hg : ∀ n j, Measurable (g n j))
    (hgb : ∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C)
    (hRc : ∀ n j, Continuous (fun u : ℝ => ∫ s in u..T n, b n j s))
    (hρm : ∀ j, Measurable (ρ j)) (hρ : ∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1)
    (hcww : ∀ j s, S.c (kw j) (kw j) s = 1) (hcwu : ∀ j s, S.c (kw j) (k j) s = ρ j s)
    (hcross1 : ∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0)
    (hcross2 : ∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0)
    (U : NNReal) (t : ℝ) (ht0 : 0 ≤ t) (hT : ∀ n, t ≤ T n ∧ T n ≤ U)
    (hcen : ∀ n : Fin m, Integrable (Yactual S kw X g b T n) S.μ ∧
      Yactual S kw X g b T n - S.μ[Yactual S kw X g b T n | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
        fun ω => ∑ j, Zactual S k kw α X g b T t n j ω) :
    H0154 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n)
      (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X))
      (stateR X t) g b ρ α T t ∧
    (V0150 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n) =ᵐ[S.μ]
      fun ω => (A0154 g b ρ α T t).mulVec (fun j => (stateR X t ω j : ℝ))) := by
  have hcuu : ∀ j s, S.c (k j) (k j) s = 1 := fun j s => by simpa using hc j j s
  -- the backward weights
  have hRm : ∀ n j, Measurable (fun u : ℝ => ∫ s in u..T n, b n j s) :=
    fun n j => (hRc n j).measurable
  have hRb : ∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |∫ s in u..T n, b n j s| ≤ C := by
    intro n j T'
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T')).exists_bound_of_continuousOn
      (hRc n j).continuousOn
    exact ⟨C, fun u hu => by rw [← Real.norm_eq_abs]; exact hC u hu⟩
  -- the four field-level identities at every meeting
  have hker : ∀ n : Fin m,
      (∀ i j : Fin d, Integrable (fun ω => Zactual S k kw α X g b T t n i ω *
        Zactual S k kw α X g b T t n j ω) S.μ) ∧
      (∀ j : Fin d, S.μ[fun ω => Zactual S k kw α X g b T t n j ω ^ 2 | S.ℱ (Real.toNNReal t)]
        =ᵐ[S.μ] S.μ[I0154 g b ρ α T t (stateR X) n j | S.ℱ (Real.toNNReal t)]) ∧
      (∀ i j : Fin d, (∀ s, S.c (kw i) (kw j) s = 0) → (∀ s, S.c (kw i) (k j) s = 0) →
        (∀ s, S.c (k i) (kw j) s = 0) → (∀ s, S.c (k i) (k j) s = 0) →
        S.μ[fun ω => Zactual S k kw α X g b T t n i ω * Zactual S k kw α X g b T t n j ω
          | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] 0) :=
    fun n => kernelIsometry m d Ω mΩ S k kw α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde hsq
      g b ρ T n (hg n) (hgb n) (hRm n) (hRb n) hcww hcuu hcwu t ht0 (hT n).1
  -- the kernel is interval integrable
  have hK : ∀ n j, IntervalIntegrable (K0154 g b ρ α T n j) volume t (T n) := by
    intro n j
    obtain ⟨Cg, hCg⟩ := hgb n j (T n)
    obtain ⟨CR, hCR⟩ := hRb n j (T n)
    have hKm : Measurable (K0154 g b ρ α T n j) := by
      unfold K0154
      exact (((hg n j).pow_const 2).add
        (((((measurable_const.mul (hρm j)).mul (hg n j)).mul_const _).mul (hRm n j)))).add
        ((measurable_const.mul ((hRm n j).pow_const 2)))
    refine intervalIntegrable_of_bound _ hKm t (T n) (hT n).1 ((Cg + |α j| * CR) ^ 2)
      fun u hu => ?_
    have hu' : u ∈ Set.Icc (0 : ℝ) (T n) := ⟨ht0.trans hu.1, hu.2⟩
    have hg' : |g n j u| ≤ Cg := hCg u hu'
    have hR' : |α j * ∫ s in u..T n, b n j s| ≤ |α j| * CR := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCR u hu') (abs_nonneg _)
    have hr : |ρ j u| ≤ 1 := abs_le.mpr (hρ j u)
    have hK : K0154 g b ρ α T n j u = (g n j u) ^ 2 +
        2 * ρ j u * g n j u * (α j * ∫ s in u..T n, b n j s) +
        (α j * ∫ s in u..T n, b n j s) ^ 2 := by
      simp only [K0154]
      ring
    rw [hK]
    set a := g n j u with ha
    set R' := α j * ∫ s in u..T n, b n j s with hR
    have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans hg'
    have hCR0 : 0 ≤ |α j| * CR := (abs_nonneg _).trans hR'
    have h1 : |a ^ 2| ≤ Cg ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hg' 2
    have h3 : |R' ^ 2| ≤ (|α j| * CR) ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hR' 2
    have h2 : |2 * ρ j u * a * R'| ≤ 2 * Cg * (|α j| * CR) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      calc 2 * |ρ j u| * |a| * |R'| ≤ 2 * 1 * Cg * (|α j| * CR) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hg'
              (abs_nonneg _) (by norm_num)) hR' (abs_nonneg _) (by positivity)
        _ = 2 * Cg * (|α j| * CR) := by ring
    calc |a ^ 2 + 2 * ρ j u * a * R' + R' ^ 2|
        ≤ |a ^ 2| + |2 * ρ j u * a * R'| + |R' ^ 2| := abs_add_three _ _ _
      _ ≤ Cg ^ 2 + 2 * Cg * (|α j| * CR) + (|α j| * CR) ^ 2 := by linarith
      _ = (Cg + |α j| * CR) ^ 2 := by ring
  -- the frozen integration assembly
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l U (stateR X) :=
    fun l hl => localizationAe S k α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde U l hl
  have h4 : ∀ (n : Fin m) (i j : Fin d), i ≠ j →
      S.μ[fun ω => Zactual S k kw α X g b T t n i ω * Zactual S k kw α X g b T t n j ω
        | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] 0 := by
    intro n i j hij
    refine (hker n).2.2 i j (hcross1 i j hij) (hcross2 i j hij) ?_ ?_
    · intro s
      rw [S.c_symm]
      exact hcross2 j i (Ne.symm hij) s
    · intro s
      rw [hc]
      exact if_neg hij
  -- the fifth field from the joint measurability of the almost surely continuous state
  have h5 : ∀ (n : Fin m) (j : Fin d),
      S.μ[I0154 g b ρ α T t (stateR X) n j | filtR S.ℱ t] =ᵐ[S.μ]
        fun ω => ∫ u in t..T n, K0154 g b ρ α T n j u * stateR X t ω j := fun n j =>
    (localized_weighted_integral S.μ (filtR S.ℱ) α U (stateR X) hX hH x0 hx0' t (T n) ht0
      (hT n).1 (hT n).2 j (K0154 g b ρ α T n j) (hK n j)
      (joint_measurable_ae S X hcont_ae hadapt U j t (T n) ht0 (hT n).2)).2
  have hb : H0154 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n)
      (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X))
      (stateR X t) g b ρ α T t :=
    ⟨fun n i j => (hker n).1 i j, fun n => (hcen n).2, fun n j => (hker n).2.1 j, h4, h5⟩
  exact ⟨hb, actual_variance0154 (S.ℱ (Real.toNNReal t)) S.μ (S.ℱ.le _) _ _ _ _ g b ρ α T t hb⟩

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma assembly : assemblyStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hb hρm hρ
    hcww hcwu hcross1 hcross2 U t ht0 hT
  have hcont_ae : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ) :=
    fun j => Eventually.of_forall fun ω => hcont ω j
  have hRw : ∀ n j, ContDiff ℝ 2 (fun u => ∫ s in u..T n, b n j s) ∧
      (∀ u, HasDerivAt (fun u => ∫ s in u..T n, b n j s) (-(b n j u)) u) ∧
      (∫ s in T n..T n, b n j s) = 0 := fun n j => backwardWeight (b n j) (T n) (hb n j)
  refine assembly_core S k kw α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb
    (fun n j => (hRw n j).1.continuous) hρm hρ hcww hcwu hcross1 hcross2 U t ht0 hT fun n => ?_
  have h := centered m d Ω mΩ S k kw α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde hsq g b T n
    (fun j u => ∫ s in u..T n, b n j s) (hg n) (hgb n) (fun j => (hRw n j).1)
    (fun j => (hRw n j).2.1) (fun j => (hRw n j).2.2) t ht0 (hT n).1
  refine ⟨h.1, ?_⟩
  refine h.2.trans (Eventually.of_forall fun ω => ?_)
  simp only [Zactual_eq_R]

/-- The actual increment with the backward weight in the form of `centeredACStatement`. -/
lemma Zactual_eq_AC {m d : ℕ} (k kw : Fin d → Fin S.m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (n : Fin m) (j : Fin d) :
    Zactual S k kw α X g b T t n j = twoDriverIncrement S (kw j) (k j)
      (fun s ω => g n j s * Real.sqrt (X s ω j))
      (fun (s : ℝ≥0) ω => (∫ u in (s : ℝ)..T n, b n j u) * (α j * Real.sqrt (X s ω j)))
      (Real.toNNReal (T n)) (Real.toNNReal t) := by
  have : (fun (s : ℝ≥0) ω => α j * (∫ u in (s : ℝ)..T n, b n j u) * Real.sqrt (X s ω j)) =
      fun (s : ℝ≥0) ω => (∫ u in (s : ℝ)..T n, b n j u) * (α j * Real.sqrt (X s ω j)) := by
    funext s ω
    ring
  unfold Zactual
  rw [this]

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma assemblyAC : assemblyACStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hbm hbint
    hρm hρ hcww hcwu hcross1 hcross2 U t ht0 hT
  have hcont_ae : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ) :=
    fun j => Eventually.of_forall fun ω => hcont ω j
  refine assembly_core S k kw α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb
    (fun n j => backward_continuous (b n j) (hbint n j) (T n)) hρm hρ hcww hcwu hcross1 hcross2
    U t ht0 hT fun n => ?_
  have h := centeredAC m d Ω mΩ S k kw α X x0 hc hcont_ae hadapt hx0 hx0le hU hsde hsq g b T n
    (hg n) (hgb n) (hbm n) (hbint n) t ht0 (hT n).1
  refine ⟨h.1, ?_⟩
  refine h.2.trans (Eventually.of_forall fun ω => ?_)
  simp only [Zactual_eq_AC]

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma assemblyAe : assemblyAeStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hbm hbint
    hρm hρ hcww hcwu hcross1 hcross2 U t ht0 hT
  refine assembly_core S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb
    (fun n j => backward_continuous (b n j) (hbint n j) (T n)) hρm hρ hcww hcwu hcross1 hcross2
    U t ht0 hT fun n => ?_
  have h := centeredAC m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b T n
    (hg n) (hgb n) (hbm n) (hbint n) t ht0 (hT n).1
  refine ⟨h.1, ?_⟩
  refine h.2.trans (Eventually.of_forall fun ω => ?_)
  simp only [Zactual_eq_AC]

end Assembly

/-! ### The actual meeting-variance law and support from the fields -/

section Support
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma frozen_meetingVariance : localizedMeetingVarianceStatement :=
  zeroMeanReversionVarianceSupport.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma meetingVarianceFromFields : meetingVarianceFromFieldsStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hb hρm hρ
    hcww hcwu hcross1 hcross2 U t hT
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l t (stateR X) :=
    fun l hl => localization S k α X x0 hc hcont hadapt hx0 hx0le hU hsde t l hl
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  obtain ⟨hbundle, -⟩ := assembly m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq
    g b ρ T hg hgb hb hρm hρ hcww hcwu hcross1 hcross2 U (t : ℝ) t.coe_nonneg hT
  have h := frozen_meetingVariance m d Ω mΩ S.μ inferInstance (filtR S.ℱ) α t (stateR X) hX hH
    (fun n => Yactual S kw X g b T n) (fun n j => Zactual S k kw α X g b T t n j)
    (I0154 g b ρ α T t (stateR X)) g b ρ T (fun n => (hT n).1) hρ hbundle
  exact ⟨h.1 x0 hx0', h.2⟩

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma meetingVarianceFromFieldsAC : meetingVarianceFromFieldsACStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hbm hbint
    hρm hρ hcww hcwu hcross1 hcross2 U t hT
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l t (stateR X) :=
    fun l hl => localization S k α X x0 hc hcont hadapt hx0 hx0le hU hsde t l hl
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  obtain ⟨hbundle, -⟩ := assemblyAC m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde
    hsq g b ρ T hg hgb hbm hbint hρm hρ hcww hcwu hcross1 hcross2 U (t : ℝ) t.coe_nonneg hT
  have h := frozen_meetingVariance m d Ω mΩ S.μ inferInstance (filtR S.ℱ) α t (stateR X) hX hH
    (fun n => Yactual S kw X g b T n) (fun n j => Zactual S k kw α X g b T t n j)
    (I0154 g b ρ α T t (stateR X)) g b ρ T (fun n => (hT n).1) hρ hbundle
  exact ⟨h.1 x0 hx0', h.2⟩

open Novel.ZeroMeanReversionVarianceSupportProof in
lemma meetingVarianceFromFieldsAe : meetingVarianceFromFieldsAeStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hbm hbint
    hρm hρ hcww hcwu hcross1 hcross2 U t hT
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l t (stateR X) :=
    fun l hl => localizationAe S k α X x0 hc hcont hadapt hx0 hx0le hU hsde t l hl
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  obtain ⟨hbundle, -⟩ := assemblyAe m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde
    hsq g b ρ T hg hgb hbm hbint hρm hρ hcww hcwu hcross1 hcross2 U (t : ℝ) t.coe_nonneg hT
  have h := frozen_meetingVariance m d Ω mΩ S.μ inferInstance (filtR S.ℱ) α t (stateR X) hX hH
    (fun n => Yactual S kw X g b T n) (fun n j => Zactual S k kw α X g b T t n j)
    (I0154 g b ρ α T t (stateR X)) g b ρ T (fun n => (hT n).1) hρ hbundle
  exact ⟨h.1 x0 hx0', h.2⟩

end Support


lemma localizationProp : localizationStatement := by
  intro d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl
  exact localization S k α X x0 hc hcont hadapt hx0 hx0le hU hsde T l hl

end Localization

/-! ### The short-rate jump from the forward-rate construction (13.3) -/

section ShortRateJump
open Novel.ZeroMeanReversionVarianceSupportProof
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-! #### The meeting count -/

lemma count_eq_card {N : ℕ} (T : Fin N → ℝ) (s : ℝ) :
    j01530 T s = (Finset.univ.filter fun i : Fin N => T i ≤ s).card := by
  classical
  unfold j01530
  rw [Finset.sum_boole]
  simp

lemma count_le_of_lt {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (n : Fin N) (s : ℝ)
    (hs : s < T n) : j01530 T s ≤ n.val := by
  classical
  rw [count_eq_card, ← Fin.card_Iio]
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_Iio]
  exact hT.lt_iff_lt.mp (hi.2.trans_lt hs)

lemma count_ge_of_le {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (n : Fin N) (s : ℝ)
    (hs : T n ≤ s) : n.val + 1 ≤ j01530 T s := by
  classical
  rw [count_eq_card, ← Fin.card_Iic]
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_Iic] at hi
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (hT.monotone hi).trans hs⟩

lemma count_at_meeting {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (n : Fin N) :
    j01530 T (T n) = n.val + 1 := by
  classical
  rw [count_eq_card, ← Fin.card_Iic]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
  exact hT.le_iff_le

lemma count_eq_of_between {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (n : Fin N) (s : ℝ)
    (hs : s < T n) (hlow : ∀ i, i < n → T i ≤ s) : j01530 T s = n.val := by
  classical
  rw [count_eq_card, ← Fin.card_Iio]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  exact ⟨fun h => hT.lt_iff_lt.mp (h.trans_lt hs), hlow i⟩

lemma count_eventually {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (n : Fin N) :
    ∀ᶠ t in 𝓝[<] T n, j01530 T t = n.val := by
  classical
  have h1 : ∀ᶠ t in 𝓝[<] T n, ∀ i ∈ Finset.univ.filter (fun i : Fin N => i < n), T i ≤ t := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Finset.mem_filter] at hi
    filter_upwards [Ioo_mem_nhdsLT (hT hi.2)] with t ht
    exact ht.1.le
  filter_upwards [h1, self_mem_nhdsWithin] with t ht hlt
  exact count_eq_of_between T hT n t hlt fun i hi => ht i (by simp [hi])

lemma G_succ (γ : ℕ → ℝ) (k : ℕ) : G01530 γ (k+1) - G01530 γ k = γ (k+1) := by
  unfold G01530
  rw [Finset.sum_range_succ]
  ring

/-! #### Regularity of the source coefficients -/

lemma lam_intInt (lam : ℝ → ℝ) (hm : Measurable lam)
    (hb : ∀ l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam u| ≤ B) (a b : ℝ) :
    IntervalIntegrable lam volume a b := by
  rcases le_total a b with hab | hab
  · obtain ⟨B, hB⟩ := hb a b
    exact intervalIntegrable_of_bound lam hm a b hab B hB
  · obtain ⟨B, hB⟩ := hb b a
    exact (intervalIntegrable_of_bound lam hm b a hab B hB).symm

/-- The maturity kernel is measurable and bounded on compacts in its maturity. -/
lemma hSrc_maturity_intInt {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (ha : Measurable a) (hlm : Measurable lam)
    (hlb : ∀ l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam u| ≤ B) (s l r : ℝ) :
    IntervalIntegrable (fun z => h01530 T a lam γ s z) volume l r := by
  have hi := lam_intInt lam hlm hlb
  have hm : Measurable (fun z => h01530 T a lam γ s z) :=
    (source_h_measurable T a lam γ ha hi).comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC, -, hG⟩ := finite_loading_bound N γ
  have hcont : Continuous (fun z => Real.exp (-(∫ q in s..z, lam q))) :=
    Real.continuous_exp.comp (intervalIntegral.continuous_primitive hi s).neg
  rcases le_total l r with hlr | hlr
  · obtain ⟨D, hD⟩ := (isCompact_Icc (a := l) (b := r)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine intervalIntegrable_of_bound _ hm l r hlr (|a s| * D * (N * C)) fun z hz => ?_
    unfold h01530
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) ?_ (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hD z hz)))
    · rw [← Real.norm_eq_abs]; exact hD z hz
    · exact hG _ (by have := meeting_count_le T z; omega)
  · obtain ⟨D, hD⟩ := (isCompact_Icc (a := r) (b := l)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine (intervalIntegrable_of_bound _ hm r l hlr (|a s| * D * (N * C)) fun z hz => ?_).symm
    unfold h01530
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) ?_ (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hD z hz)))
    · rw [← Real.norm_eq_abs]; exact hD z hz
    · exact hG _ (by have := meeting_count_le T z; omega)

/-- The maturity kernel is bounded by `|a(s)| G` at maturities after `s`. -/
lemma hSrc_bound_of_le {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (hl : ∀ u, 0 ≤ lam u) (Gb : ℝ) (hG : ∀ k ≤ N, |G01530 γ k| ≤ Gb) (s z : ℝ)
    (hsz : s ≤ z) : |h01530 T a lam γ s z| ≤ |a s| * Gb := by
  unfold h01530
  rw [abs_mul, abs_mul]
  calc |a s| * |Real.exp (-(∫ q in s..z, lam q))| * |G01530 γ (j01530 T z - j01530 T s)|
      ≤ |a s| * 1 * Gb := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (decay_bound lam hl s z hsz) (abs_nonneg _))
          (hG _ (by have := meeting_count_le T z; omega)) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) zero_le_one)
    _ = |a s| * Gb := by ring

/-- Uniform bounds on the source scale and loadings up to `T n`. -/
lemma src_bounds {N : ℕ} (T : Fin N → ℝ) (a : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) (n : Fin N) :
    ∃ A Gb : ℝ, 0 ≤ A ∧ 0 ≤ Gb ∧ (∀ j, ∀ s ∈ Set.Icc (0 : ℝ) (T n), |a j s| ≤ A) ∧
      (∀ j, ∀ m ≤ N, |G01530 (γ j) m| ≤ Gb) := by
  classical
  choose Aj hAj using fun j => hab j 0 (T n)
  choose Cj hCj using fun j => finite_loading_bound N (γ j)
  refine ⟨∑ j, |Aj j|, ∑ j, |N * Cj j|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun j s hs => ?_, fun j m hm => ?_⟩
  · exact (hAj j s hs).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Aj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))
  · exact ((hCj j).2.2 m hm).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |N * Cj j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)))

/-- A bound on a continuous path over `[0, T]`, uniform over the factors. -/
lemma path_bound (X : ℝ≥0 → Ω → Fin d → NNReal) (ω : Ω)
    (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) (U : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) U, |(X (Real.toNNReal s) ω j : ℝ)| ≤ M := by
  classical
  have : ∀ j, ∃ M, ∀ s ∈ Set.Icc (0 : ℝ) U, |(X (Real.toNNReal s) ω j : ℝ)| ≤ M := fun j => by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := U)).exists_bound_of_continuousOn
      ((hcω j).comp continuous_real_toNNReal).continuousOn
    exact ⟨M, fun s hs => by rw [← Real.norm_eq_abs]; exact hM s hs⟩
  choose Mj hMj using this
  refine ⟨∑ j, |Mj j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun j s hs => ?_⟩
  exact (hMj j s hs).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |Mj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

/-! #### The pre-jump kernel and drift -/

/-- The maturity kernel with the loading of the meeting interval before `T_n`. -/
noncomputable def tilde {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ) (n : Fin N)
    (s t : ℝ) : ℝ :=
  a s * Real.exp (-(∫ q in s..t, lam q)) * G01530 γ (n.val - j01530 T s)

/-- The drift with the pre-jump kernel. -/
noncomputable def tildeDrift {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (s t : ℝ) (ω : Ω) : ℝ :=
  ∑ j, tilde T (a j) (lam j) (γ j) n s t * (∫ z in s..t, hSrc T a lam γ j s z) *
    (X (Real.toNNReal s) ω j : ℝ)

lemma hSrc_eq_tilde {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (n : Fin N) (j : Fin d) (s t : ℝ) (ht : j01530 T t = n.val) :
    hSrc T a lam γ j s t = tilde T (a j) (lam j) (γ j) n s t := by
  unfold hSrc h01530 tilde
  rw [ht]

lemma driftSrc_eq_tilde {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (s t : ℝ) (ω : Ω) (ht : j01530 T t = n.val) :
    driftSrc T a lam γ X s t ω = tildeDrift T a lam γ X n s t ω := by
  unfold driftSrc tildeDrift
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hSrc_eq_tilde T a lam γ n j s t ht]

/-- The maturity jump of the kernel at `T_n` is `g_{n,j}` before `T_n` and zero after. -/
lemma hSrc_sub_tilde {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (n : Fin N) (j : Fin d) (s : ℝ) :
    hSrc T a lam γ j s (T n) - tilde T (a j) (lam j) (γ j) n s (T n) = gJump T a lam γ n j s := by
  unfold hSrc h01530 tilde gJump g01530
  rw [count_at_meeting T hT n]
  by_cases hs : s < T n
  · rw [if_pos hs]
    have hj := count_le_of_lt T hT n s hs
    have h1 : n.val + 1 - j01530 T s = (n.val - j01530 T s) + 1 := by omega
    rw [h1, ← G_succ (γ j) (n.val - j01530 T s)]
    ring
  · rw [if_neg hs]
    have hj := count_ge_of_le T hT n s (not_lt.mp hs)
    rw [Nat.sub_eq_zero_of_le hj, Nat.sub_eq_zero_of_le (by omega)]
    ring

lemma bJump_eq {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (n : Fin N)
    (j : Fin d) (s : ℝ) :
    bJump T a lam γ n j s = gJump T a lam γ n j s * ∫ z in s..T n, hSrc T a lam γ j s z := by
  unfold bJump gJump b01530 hSrc
  split_ifs
  · rfl
  · rw [zero_mul]

lemma driftSrc_eq_tilde_add {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (s : ℝ) (ω : Ω) :
    driftSrc T a lam γ X s (T n) ω = tildeDrift T a lam γ X n s (T n) ω +
      ∑ j, bJump T a lam γ n j s * (X (Real.toNNReal s) ω j : ℝ) := by
  unfold driftSrc tildeDrift
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bJump_eq, ← hSrc_sub_tilde T hT a lam γ n j s]
  ring

/-- The stochastic-integrand jump at `T_n`. -/
lemma loadInt_diff {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (j : Fin d)
    (hi : ∀ l r, IntervalIntegrable (lam j) volume l r) (s : ℝ≥0) (ω : Ω) :
    Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) * loadInt T a lam γ X j (n.val + 1) s ω +
      (-(Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)))) * loadInt T a lam γ X j n.val s ω =
      gJump T a lam γ n j s * Real.sqrt (X s ω j) := by
  have hE : Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) *
      Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q) =
      Real.exp (-(∫ q in (s : ℝ)..T n, lam j q)) := by
    rw [← Real.exp_add, ← intervalIntegral.integral_interval_sub_left (hi 0 (T n)) (hi 0 s)]
    congr 1
    ring
  unfold loadInt gJump g01530
  by_cases hs : (s : ℝ) < T n
  · rw [if_pos hs]
    have hj := count_le_of_lt T hT n s hs
    have h1 : n.val + 1 - j01530 T s = (n.val - j01530 T s) + 1 := by omega
    rw [h1]
    have hG := G_succ (γ j) (n.val - j01530 T s)
    linear_combination (a j s * Real.sqrt (X s ω j) * (Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) *
      Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q))) * hG +
      (a j s * Real.sqrt (X s ω j) * γ j (n.val - j01530 T s + 1)) * hE
  · rw [if_neg hs]
    have hj := count_ge_of_le T hT n s (not_lt.mp hs)
    rw [Nat.sub_eq_zero_of_le hj, Nat.sub_eq_zero_of_le (by omega)]
    ring

/-- The direct integrand of the forward rate as a multiple of the loading integrand. -/
lemma hSrc_integrand_eq {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (j : Fin d)
    (hi : ∀ l r, IntervalIntegrable (lam j) volume l r) (u : ℝ) :
    (fun (s : ℝ≥0) ω => hSrc T a lam γ j s u * Real.sqrt (X s ω j)) =
      Real.exp (-(∫ q in (0 : ℝ)..u, lam j q)) • loadInt T a lam γ X j (j01530 T u) +
        (0 : ℝ) • loadInt T a lam γ X j (j01530 T u) := by
  funext s ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
  unfold hSrc h01530 loadInt
  have hE : Real.exp (-(∫ q in (0 : ℝ)..u, lam j q)) *
      Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q) =
      Real.exp (-(∫ q in (s : ℝ)..u, lam j q)) := by
    rw [← Real.exp_add, ← intervalIntegral.integral_interval_sub_left (hi 0 u) (hi 0 s)]
    congr 1
    ring
  linear_combination (-(a j s * G01530 (γ j) (j01530 T u - j01530 T s) * Real.sqrt (X s ω j))) * hE

/-- Measurability and local bounds of the deterministic coefficient of `loadInt`. -/
lemma loadInt_coefficient {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) (j : Fin d) (m : ℕ) :
    let K : ℝ≥0 → ℝ := fun s => a j s * Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q) *
      G01530 (γ j) (m - j01530 T s)
    Measurable K ∧ ∀ T' : ℝ≥0, ∃ C, ∀ s, s ≤ T' → |K s| ≤ C := by
  have hi := lam_intInt (lam j) (hlm j) (hlb j)
  set K : ℝ≥0 → ℝ := fun s => a j s * Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q) *
    G01530 (γ j) (m - j01530 T s) with hK
  have hKm : Measurable K := by
    have h1 : Measurable (fun s : ℝ≥0 => a j s) := (ha j).comp NNReal.continuous_coe.measurable
    have h2 : Measurable (fun s : ℝ≥0 => Real.exp (∫ q in (0 : ℝ)..(s : ℝ), lam j q)) :=
      (Real.continuous_exp.comp (intervalIntegral.continuous_primitive hi 0)).measurable.comp
        NNReal.continuous_coe.measurable
    have h3 : Measurable (fun s : ℝ≥0 => G01530 (γ j) (m - j01530 T s)) :=
      (measurable_of_countable (fun i : ℕ => G01530 (γ j) (m - i))).comp
        ((meeting_count_measurable T).comp NNReal.continuous_coe.measurable)
    exact (h1.mul h2).mul h3
  have hKb : ∀ T' : ℝ≥0, ∃ C, ∀ s, s ≤ T' → |K s| ≤ C := by
    intro T'
    obtain ⟨A, hA⟩ := hab j 0 T'
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T')).exists_bound_of_continuousOn
      (Real.continuous_exp.comp (intervalIntegral.continuous_primitive hi 0)).continuousOn
    obtain ⟨C, hC, -, hG⟩ := finite_loading_bound m (γ j)
    refine ⟨|A| * |D| * |(m : ℝ) * C|, fun s hs => ?_⟩
    have hs' : (s : ℝ) ∈ Set.Icc (0 : ℝ) T' := ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩
    simp only [hK, abs_mul]
    refine mul_le_mul (mul_le_mul ((hA s hs').trans (le_abs_self _)) ?_ (abs_nonneg _)
      (abs_nonneg _)) ?_ (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · rw [← Real.norm_eq_abs]
      exact (hD s hs').trans (le_abs_self _)
    · exact (hG _ (Nat.sub_le _ _)).trans ((le_abs_self ((m : ℝ) * C)).trans (abs_mul _ _).le)
  exact ⟨hKm,hKb⟩

/-- The loading integrands are (U4). -/
lemma loadInt_U4 (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) (j : Fin d) (m : ℕ) :
    U4 S.ℱ S.μ (loadInt T a lam γ X j m) := by
  obtain ⟨hKm,hKb⟩ := loadInt_coefficient T a lam γ ha hlm hlb hab j m
  exact (coefficient_U5 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq j _ hKm hKb 0).1

/-! #### The left limit of the drift -/

lemma tildeDrift_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) (ω : Ω)
    (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) (t : ℝ) :
    Measurable (fun s => tildeDrift T a lam γ X n s t ω) := by
  have hi : ∀ j l r, IntervalIntegrable (lam j) volume l r :=
    fun j => lam_intInt (lam j) (hlm j) (hlb j)
  unfold tildeDrift
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable (fun s => tilde T (a j) (lam j) (γ j) n s t) := by
    unfold tilde
    exact ((ha j).mul ((decay_joint_measurable (lam j) (hi j)).comp
      (measurable_id.prodMk measurable_const))).mul
      ((measurable_of_countable (fun i : ℕ => G01530 (γ j) (n.val - i))).comp
        (meeting_count_measurable T))
  have h2 : Measurable (fun s => ∫ z in s..t, hSrc T a lam γ j s z) :=
    variable_interval_measurable (fun s z => hSrc T a lam γ j s z)
      (source_h_measurable T (a j) (lam j) (γ j) (ha j) (hi j)) t
  have h3 : Measurable (fun s => (X (Real.toNNReal s) ω j : ℝ)) :=
    ((hcω j).comp continuous_real_toNNReal).measurable
  exact (h1.mul h2).mul h3

lemma tildeDrift_continuous {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) (ω : Ω) (s : ℝ) :
    Continuous (fun t => tildeDrift T a lam γ X n s t ω) := by
  have hi : ∀ j l r, IntervalIntegrable (lam j) volume l r :=
    fun j => lam_intInt (lam j) (hlm j) (hlb j)
  unfold tildeDrift
  refine continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous (fun t => tilde T (a j) (lam j) (γ j) n s t) := by
    unfold tilde
    exact (continuous_const.mul (Real.continuous_exp.comp
      (intervalIntegral.continuous_primitive (hi j) s).neg)).mul continuous_const
  have h2 : Continuous (fun t => ∫ z in s..t, hSrc T a lam γ j s z) :=
    intervalIntegral.continuous_primitive
      (fun l r => hSrc_maturity_intInt T (a j) (lam j) (γ j) (ha j) (hlm j) (hlb j) s l r) s
  exact (h1.mul h2).mul continuous_const

lemma tildeDrift_bound {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (hl : ∀ j u, 0 ≤ lam j u)
    (A Gb M : ℝ) (hA0 : 0 ≤ A) (hGb0 : 0 ≤ Gb) (hM0 : 0 ≤ M)
    (hA : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) (T n), |a j s| ≤ A)
    (hG : ∀ j, ∀ m ≤ N, |G01530 (γ j) m| ≤ Gb) (ω : Ω)
    (hM : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) (T n), |(X (Real.toNNReal s) ω j : ℝ)| ≤ M)
    (s t : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T n) :
    |tildeDrift T a lam γ X n s t ω| ≤ d * ((A * Gb) * (A * Gb * T n) * M) := by
  have hsT : s ∈ Set.Icc (0 : ℝ) (T n) := ⟨hs0, hst.trans htT⟩
  have hTn : 0 ≤ T n := hs0.trans (hst.trans htT)
  unfold tildeDrift
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j, |tilde T (a j) (lam j) (γ j) n s t * (∫ z in s..t, hSrc T a lam γ j s z) *
      (X (Real.toNNReal s) ω j : ℝ)| ≤ (A * Gb) * (A * Gb * T n) * M := by
    intro j
    have h1 : |tilde T (a j) (lam j) (γ j) n s t| ≤ A * Gb := by
      unfold tilde
      rw [abs_mul, abs_mul]
      calc |a j s| * |Real.exp (-(∫ q in s..t, lam j q))| * |G01530 (γ j) (n.val - j01530 T s)|
          ≤ A * 1 * Gb := mul_le_mul (mul_le_mul (hA j s hsT) (decay_bound (lam j) (hl j) s t hst)
            (abs_nonneg _) hA0) (hG j _ (by have := n.2; omega)) (abs_nonneg _)
            (mul_nonneg hA0 zero_le_one)
        _ = A * Gb := by ring
    have h2 : |∫ z in s..t, hSrc T a lam γ j s z| ≤ A * Gb * T n := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := A * Gb)
        (f := fun z => hSrc T a lam γ j s z) fun z hz => by
          rw [Set.uIoc_of_le hst] at hz
          rw [Real.norm_eq_abs]
          exact (hSrc_bound_of_le T (a j) (lam j) (γ j) (hl j) Gb (hG j) s z hz.1.le).trans
            (mul_le_mul_of_nonneg_right (hA j s hsT) hGb0)
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA0 hGb0)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hA0 hGb0)) (hM j s hsT)
      (abs_nonneg _) (mul_nonneg (mul_nonneg hA0 hGb0) (by positivity))
  calc (∑ j, |tilde T (a j) (lam j) (γ j) n s t * (∫ z in s..t, hSrc T a lam γ j s z) *
        (X (Real.toNNReal s) ω j : ℝ)|) ≤ ∑ _j : Fin d, (A * Gb) * (A * Gb * T n) * M :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = d * ((A * Gb) * (A * Gb * T n) * M) := by simp

lemma drift_tendsto {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (hTn : 0 < T n)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (ω : Ω) (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) :
    Tendsto (fun t => ∫ s in (0 : ℝ)..t, tildeDrift T a lam γ X n s t ω) (𝓝[<] T n)
      (𝓝 (∫ s in (0 : ℝ)..T n, tildeDrift T a lam γ X n s (T n) ω)) := by
  obtain ⟨A, Gb, hA0, hGb0, hA, hG⟩ := src_bounds T a γ hab n
  obtain ⟨M, hM0, hM⟩ := path_bound X ω hcω (T n)
  set C : ℝ := d * ((A * Gb) * (A * Gb * T n) * M) with hC
  have hC0 : 0 ≤ C := by positivity
  have hF : ∀ t ∈ Set.Icc (0 : ℝ) (T n), (∫ s in (0 : ℝ)..t, tildeDrift T a lam γ X n s t ω) =
      ∫ s in (0 : ℝ)..T n, Set.indicator {s | s ≤ t} (fun s => tildeDrift T a lam γ X n s t ω) s :=
    fun t ht => (intervalIntegral.integral_indicator ht).symm
  have hmain := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := T n) (l := 𝓝[<] T n)
    (F := fun t s => Set.indicator {s | s ≤ t} (fun s => tildeDrift T a lam γ X n s t ω) s)
    (f := fun s => tildeDrift T a lam γ X n s (T n) ω) (fun _ => C) ?_ ?_ ?_ ?_
  · refine hmain.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hTn] with t ht
    exact (hF t ⟨ht.1.le, ht.2.le⟩).symm
  · exact Eventually.of_forall fun t =>
      ((tildeDrift_measurable T a lam γ X n ha hlm hlb ω hcω t).indicator
        measurableSet_Iic).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hTn] with t ht
    refine Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le hTn.le] at hs
    rw [Real.norm_eq_abs]
    by_cases hst : s ≤ t
    · rw [Set.indicator_of_mem (show s ∈ {s | s ≤ t} from hst)]
      exact tildeDrift_bound T a lam γ X n hl A Gb M hA0 hGb0 hM0 hA hG ω hM s t hs.1.le hst
        ht.2.le
    · rw [Set.indicator_of_notMem (show s ∉ {s | s ≤ t} from hst), abs_zero]
      exact hC0
  · exact intervalIntegrable_const
  · have hne : ∀ᵐ s : ℝ ∂volume, s ≠ T n := by
      rw [ae_iff]
      simpa using Real.volume_singleton (a := T n)
    filter_upwards [hne] with s hs hsI
    rw [Set.uIoc_of_le hTn.le] at hsI
    have hslt : s < T n := lt_of_le_of_ne hsI.2 hs
    refine (((tildeDrift_continuous T a lam γ X n ha hlm hlb ω s).tendsto (T n)).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hslt] with t ht
    rw [Set.indicator_of_mem (show s ∈ {s | s ≤ t} from ht.1.le)]

/-! #### Integrability on `[0, T_n]` -/

lemma bJump_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) (n : Fin N) (j : Fin d) :
    Measurable (bJump T a lam γ n j) := by
  unfold bJump
  exact Measurable.ite measurableSet_Iio
    (source_b_measurable T (a j) (lam j) (γ j) (ha j) (lam_intInt (lam j) (hlm j) (hlb j)) n)
    measurable_const

lemma bJump_intInt {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (hTn : 0 < T n)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (ω : Ω) (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) (j : Fin d) :
    IntervalIntegrable (fun u => bJump T a lam γ n j u * (X (Real.toNNReal u) ω j : ℝ)) volume 0
      (T n) := by
  obtain ⟨A, hA⟩ := hab j 0 (T n)
  obtain ⟨C, hC, hg, hb⟩ := source_coefficients_bound T (a j) (lam j) (γ j) (hl j) n 0 A hTn.le hA
  obtain ⟨M, hM0, hM⟩ := path_bound X ω hcω (T n)
  have hm : Measurable (fun u => bJump T a lam γ n j u * (X (Real.toNNReal u) ω j : ℝ)) :=
    (bJump_measurable T a lam γ ha hlm hlb n j).mul
      ((hcω j).comp continuous_real_toNNReal).measurable
  refine intervalIntegrable_of_bound _ hm 0 (T n) hTn.le
    (((A * C) * (A * (N * C) * (T n - 0))) * M) fun u hu => ?_
  rw [abs_mul]
  refine mul_le_mul ?_ (hM j u hu) (abs_nonneg _) ?_
  · unfold bJump
    split_ifs
    · exact hb u hu
    · rw [abs_zero]
      exact (abs_nonneg _).trans (hb u hu)
  · exact (abs_nonneg _).trans (hb u hu)

lemma tildeDrift_intInt {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (hTn : 0 < T n)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (ω : Ω) (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) :
    IntervalIntegrable (fun s => tildeDrift T a lam γ X n s (T n) ω) volume 0 (T n) := by
  obtain ⟨A, Gb, hA0, hGb0, hA, hG⟩ := src_bounds T a γ hab n
  obtain ⟨M, hM0, hM⟩ := path_bound X ω hcω (T n)
  exact intervalIntegrable_of_bound _ (tildeDrift_measurable T a lam γ X n ha hlm hlb ω hcω (T n))
    0 (T n) hTn.le _ fun s hs =>
      tildeDrift_bound T a lam γ X n hl A Gb M hA0 hGb0 hM0 hA hG ω hM s (T n) hs.1 hs.2 le_rfl

/-- The drift jump at `T_n`. -/
lemma drift_jump {N : ℕ} (T : Fin N → ℝ) (hT : StrictMono T) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (n : Fin N) (hTn : 0 < T n)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (ω : Ω) (hcω : ∀ j, Continuous fun t => (X t ω j : ℝ)) :
    (∫ s in (0 : ℝ)..T n, driftSrc T a lam γ X s (T n) ω) =
      (∫ s in (0 : ℝ)..T n, tildeDrift T a lam γ X n s (T n) ω) +
        ∑ j, ∫ u in (0 : ℝ)..T n, bJump T a lam γ n j u * (X (Real.toNNReal u) ω j : ℝ) := by
  have h1 : (fun s => driftSrc T a lam γ X s (T n) ω) = fun s =>
      tildeDrift T a lam γ X n s (T n) ω +
        ∑ j, bJump T a lam γ n j s * (X (Real.toNNReal s) ω j : ℝ) :=
    funext fun s => driftSrc_eq_tilde_add T hT a lam γ X n s ω
  have hB : IntervalIntegrable
      (fun s => ∑ j, bJump T a lam γ n j s * (X (Real.toNNReal s) ω j : ℝ)) volume 0 (T n) := by
    have := IntervalIntegrable.sum Finset.univ fun j _ =>
      bJump_intInt T a lam γ X n hTn ha hlm hl hlb hab ω hcω j
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  rw [h1, intervalIntegral.integral_add (tildeDrift_intInt T a lam γ X n hTn ha hlm hl hlb hab ω
    hcω) hB, intervalIntegral.integral_finset_sum fun j _ =>
      bJump_intInt T a lam γ X n hTn ha hlm hl hlb hab ω hcω j]

/-! #### The short-rate jump -/

/-- The source curve-jump argument needs continuity and the loading integrands in (U4),
independently of the SDE used to establish their integrability. -/
lemma shortRateJump_core {N : ℕ} (kw : Fin d → Fin S.m)
    (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hcont : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ)
    (hT : StrictMono T) (hTpos : ∀ n, 0 < T n)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (hU4 : ∀ j (m : ℕ), U4 S.ℱ S.μ (loadInt T a lam γ X j m)) :
    (∀ (t : ℝ≥0) (u : ℝ), ∀ᵐ ω ∂S.μ, forwardSrc S kw T a lam γ X c t u ω =
      c + (∫ s in (0 : ℝ)..(t : ℝ), driftSrc T a lam γ X s u ω) +
        ∑ j, S.I (kw j) (fun (s : ℝ≥0) ω => hSrc T a lam γ j s u * Real.sqrt (X s ω j)) t ω) ∧
    ∀ n : Fin N, ∀ᵐ ω ∂S.μ, ∃ L : ℝ,
      Tendsto (fun t : ℝ => shortSrc S kw T a lam γ X c (Real.toNNReal t) ω) (𝓝[<] T n) (𝓝 L) ∧
      shortSrc S kw T a lam γ X c (Real.toNNReal (T n)) ω - L =
        Yactual S kw X (gJump T a lam γ) (bJump T a lam γ) T n ω := by
  have hi : ∀ j l r, IntervalIntegrable (lam j) volume l r :=
    fun j => lam_intInt (lam j) (hlm j) (hlb j)
  refine ⟨fun t u => ?_, fun n => ?_⟩
  · -- the version identity
    have hj : ∀ j, ∀ᵐ ω ∂S.μ, S.I (kw j)
        (fun (s : ℝ≥0) ω => hSrc T a lam γ j s u * Real.sqrt (X s ω j)) t ω =
        Real.exp (-(∫ q in (0 : ℝ)..u, lam j q)) *
          S.I (kw j) (loadInt T a lam γ X j (j01530 T u)) t ω := by
      intro j
      rw [hSrc_integrand_eq T a lam γ X j (hi j) u]
      filter_upwards [S.int_linear (kw j) _ _ _ _ (hU4 j _) (hU4 j _) t] with ω hω
      rw [hω]
      simp
    filter_upwards [ae_all_iff.2 hj] with ω hω
    unfold forwardSrc
    congr 1
    exact Finset.sum_congr rfl fun j _ => (hω j).symm
  · -- the jump at meeting `n`
    have hcnt := count_at_meeting T hT n
    have hev := count_eventually T hT n
    have hIc : ∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => S.I (kw j) (loadInt T a lam γ X j n.val) t ω :=
      fun j => S.int_continuous _ _ (hU4 j n.val)
    have hlin : ∀ j, ∀ᵐ ω ∂S.μ,
        S.I (kw j) (fun (s : ℝ≥0) ω => gJump T a lam γ n j s * Real.sqrt (X s ω j))
          (Real.toNNReal (T n)) ω =
        Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) *
            S.I (kw j) (loadInt T a lam γ X j (n.val + 1)) (Real.toNNReal (T n)) ω +
          (-(Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)))) *
            S.I (kw j) (loadInt T a lam γ X j n.val) (Real.toNNReal (T n)) ω := by
      intro j
      have heq : (fun (s : ℝ≥0) ω => gJump T a lam γ n j s * Real.sqrt (X s ω j)) =
          Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) • loadInt T a lam γ X j (n.val + 1) +
            (-(Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)))) • loadInt T a lam γ X j n.val := by
        funext s ω
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact (loadInt_diff T hT a lam γ X n j (hi j) s ω).symm
      rw [heq]
      filter_upwards [S.int_linear (kw j) _ _ _ _ (hU4 j _) (hU4 j _) (Real.toNNReal (T n))]
        with ω hω
      rw [hω]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    filter_upwards [ae_all_iff.2 hcont, ae_all_iff.2 hIc, ae_all_iff.2 hlin] with ω hcω hIω hlω
    refine ⟨c + (∫ s in (0 : ℝ)..T n, tildeDrift T a lam γ X n s (T n) ω) +
      ∑ j, Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) *
        S.I (kw j) (loadInt T a lam γ X j n.val) (Real.toNNReal (T n)) ω, ?_, ?_⟩
    · have h1 := drift_tendsto T a lam γ X n (hTpos n) ha hlm hl hlb hab ω hcω
      have h2 : Tendsto (fun t : ℝ => ∑ j, Real.exp (-(∫ q in (0 : ℝ)..t, lam j q)) *
          S.I (kw j) (loadInt T a lam γ X j n.val) (Real.toNNReal t) ω) (𝓝[<] T n)
          (𝓝 (∑ j, Real.exp (-(∫ q in (0 : ℝ)..T n, lam j q)) *
            S.I (kw j) (loadInt T a lam γ X j n.val) (Real.toNNReal (T n)) ω)) := by
        refine (Continuous.tendsto ?_ (T n)).mono_left nhdsWithin_le_nhds
        exact continuous_finset_sum _ fun j _ => (Real.continuous_exp.comp
          (intervalIntegral.continuous_primitive (hi j) 0).neg).mul
          ((hIω j).comp continuous_real_toNNReal)
      refine ((tendsto_const_nhds.add h1).add h2).congr' ?_
      filter_upwards [hev, Ioo_mem_nhdsLT (hTpos n)] with t ht ht0
      unfold shortSrc forwardSrc
      rw [Real.coe_toNNReal t ht0.1.le, ht]
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (driftSrc_eq_tilde T a lam γ X n s t ω ht).symm
    · unfold shortSrc forwardSrc Yactual
      rw [Real.coe_toNNReal _ (hTpos n).le, hcnt,
        drift_jump T hT a lam γ X n (hTpos n) ha hlm hl hlb hab ω hcω]
      simp only [hlω, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
      ring

lemma shortRateJump : shortRateJumpStatement := by
  intro N d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq T a lam γ c hT hTpos ha hlm
    hl hlb hab
  have hU4 : ∀ j (m : ℕ), U4 S.ℱ S.μ (loadInt T a lam γ X j m) := fun j m =>
    loadInt_U4 S k α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq T a lam γ ha hlm hlb hab j m
  exact shortRateJump_core S kw X hcont T a lam γ c hT hTpos ha hlm hl hlb hab hU4

end ShortRateJump

/-! ### The complete meeting-variance conclusions and the source capstone -/

section VCongr
variable {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]

/-- The vector of conditional variances respects almost-sure equality of the jumps. -/
lemma V0150_congr_ae {m : ℕ} (μ : @Measure Ω mΩ) (Y Y' : Fin m → Ω → ℝ)
    (h : ∀ n, Y n =ᵐ[μ] Y' n) : V0150 G μ Y =ᵐ[μ] V0150 G μ Y' := by
  have hall : ∀ᵐ ω ∂μ, ∀ n, Var[Y n; μ | G] ω = Var[Y' n; μ | G] ω :=
    ae_all_iff.2 fun n => condVar_congr_ae (m := G) (μ := μ) (h n)
  filter_upwards [hall] with ω hω
  funext n
  exact hω n

end VCongr

section Capstone
open Novel.ZeroMeanReversionVarianceSupportProof
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma gJump_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j))
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) (n : Fin N) (j : Fin d) :
    Measurable (gJump T a lam γ n j) := by
  unfold gJump
  exact Measurable.ite measurableSet_Iio
    (source_g_measurable T (a j) (lam j) (γ j) (ha j) (lam_intInt (lam j) (hlm j) (hlb j)) n)
    measurable_const

lemma gJump_bound {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (hl : ∀ j u, 0 ≤ lam j u) (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (n : Fin N) (j : Fin d) (l r : ℝ) :
    ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |gJump T a lam γ n j u| ≤ B := by
  obtain ⟨A, hA⟩ := hab j l r
  obtain ⟨C, hC, hγ, -⟩ := finite_loading_bound N (γ j)
  refine ⟨|A| * C, fun u hu => ?_⟩
  unfold gJump
  split_ifs with hu'
  · unfold g01530
    rw [abs_mul, abs_mul]
    calc |a j u| * |Real.exp (-(∫ q in u..T n, lam j q))| * |γ j (n.val + 1 - j01530 T u)|
        ≤ |A| * 1 * C := mul_le_mul (mul_le_mul ((hA u hu).trans (le_abs_self A))
          (decay_bound (lam j) (hl j) u (T n) hu'.le) (abs_nonneg _) (abs_nonneg _))
          (hγ _ (by have := n.2; omega)) (abs_nonneg _) (by positivity)
      _ = |A| * C := by ring
  · rw [abs_zero]
    positivity

lemma bJump_bound {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (hl : ∀ j u, 0 ≤ lam j u) (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)
    (n : Fin N) (j : Fin d) (l r : ℝ) :
    ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |bJump T a lam γ n j u| ≤ B := by
  obtain ⟨A, hA⟩ := hab j l r
  obtain ⟨C, hC, hγ, hG⟩ := finite_loading_bound N (γ j)
  refine ⟨(|A| * C) * (|A| * (N * C) * |T n - l|), fun u hu => ?_⟩
  unfold bJump
  split_ifs with hu'
  · unfold b01530
    rw [abs_mul]
    have h1 : |g01530 T (a j) (lam j) (γ j) n u| ≤ |A| * C := by
      unfold g01530
      rw [abs_mul, abs_mul]
      calc |a j u| * |Real.exp (-(∫ q in u..T n, lam j q))| * |γ j (n.val + 1 - j01530 T u)|
          ≤ |A| * 1 * C := mul_le_mul (mul_le_mul ((hA u hu).trans (le_abs_self A))
            (decay_bound (lam j) (hl j) u (T n) hu'.le) (abs_nonneg _) (abs_nonneg _))
            (hγ _ (by have := n.2; omega)) (abs_nonneg _) (by positivity)
        _ = |A| * C := by ring
    have h2 : |∫ z in u..T n, h01530 T (a j) (lam j) (γ j) u z| ≤ |A| * (N * C) * |T n - l| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T n)
        (C := |A| * (N * C)) (f := fun z => h01530 T (a j) (lam j) (γ j) u z) fun z hz => by
          rw [Set.uIoc_of_le hu'.le] at hz
          rw [Real.norm_eq_abs]
          exact (hSrc_bound_of_le T (a j) (lam j) (γ j) (hl j) (N * C) hG u z hz.1.le).trans
            (mul_le_mul_of_nonneg_right ((hA u hu).trans (le_abs_self A)) (by positivity))
      rw [Real.norm_eq_abs] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [abs_of_nonneg (by linarith [hu'.le]), abs_of_nonneg (by linarith [hu.1, hu'.le])]
      linarith [hu.1]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  · rw [abs_zero]
    positivity

lemma bJump_intInt_all {N : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (ha : ∀ j, Measurable (a j)) (hlm : ∀ j, Measurable (lam j)) (hl : ∀ j u, 0 ≤ lam j u)
    (hlb : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B)
    (hab : ∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) (n : Fin N) (j : Fin d) (T' : ℝ) :
    IntervalIntegrable (bJump T a lam γ n j) volume 0 T' := by
  have hm := bJump_measurable T a lam γ ha hlm hlb n j
  rcases le_total 0 T' with h | h
  · obtain ⟨B, hB⟩ := bJump_bound T a lam γ hl hab n j 0 T'
    exact intervalIntegrable_of_bound _ hm 0 T' h B hB
  · obtain ⟨B, hB⟩ := bJump_bound T a lam γ hl hab n j T' 0
    exact (intervalIntegrable_of_bound _ hm T' 0 h B hB).symm

lemma frozen_meetingVarianceFull : meetingVarianceStatement :=
  zeroMeanReversionVarianceSupport.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma fullMeetingVarianceFromFields : fullMeetingVarianceFromFieldsStatement := by
  intro m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq g b ρ T hg hgb hbm hbint
    hρm hρ hcww hcwu hcross1 hcross2 U t hT
  intro A V c B b'
  have hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[filtR S.ℱ s] (stateR X s) :=
    fun s _ => hadapt _
  have hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 S.μ (filtR S.ℱ) α l t (stateR X) :=
    fun l hl => localizationAe S k α X x0 hc hcont hadapt hx0 hx0le hU hsde t l hl
  have hx0' : stateR X 0 =ᵐ[S.μ] fun _ => x0 := by
    show X (Real.toNNReal 0) =ᵐ[S.μ] _
    rw [Real.toNNReal_zero]
    exact hx0
  obtain ⟨hbundle, -⟩ := assemblyAe m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde
    hsq g b ρ T hg hgb hbm hbint hρm hρ hcww hcwu hcross1 hcross2 U (t : ℝ) t.coe_nonneg hT
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    show 0 ≤ (α j)^2*(t : ℝ)/2
    positivity
  have htrans : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * stateR X t ω j)) ∂S.μ) =
        Real.exp (-(∑ j, (x0 j : ℝ) * l j / (1 + c j * l j))) := fun l hl =>
    localized_initial_transform S.μ (filtR S.ℱ) α l t (stateR X) hl hX (hH l hl) x0 hx0'
  have hfr := frozen_meetingVarianceFull m d Ω (filtR S.ℱ t) (filtR S.ℱ t)
    mΩ S.μ inferInstance ((filtR S.ℱ).le _) le_rfl (fun n => Yactual S kw X g b T n)
    (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X)) (stateR X t)
    (hadapt _) g b ρ α T t (fun n => (hT n).1) hρ hbundle
  have hmain := (hfr.2.2 c hc0).1 x0 htrans
  refine ⟨hfr.1, hfr.2.1, hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
    hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2.2.1,
    hmain.2.2.2.2.2.2.2.2.2, fun s hs => ?_⟩
  intro c'
  have hc0' : ∀ j, 0 ≤ c' j := fun j => by
    show 0 ≤ (α j)^2*((t : ℝ)-s)/2
    have := hs.2
    positivity
  have hfrs := frozen_meetingVarianceFull m d Ω (filtR S.ℱ t) (filtR S.ℱ s)
    mΩ S.μ inferInstance ((filtR S.ℱ).le _) ((filtR S.ℱ).mono hs.2)
    (fun n => Yactual S kw X g b T n)
    (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X)) (stateR X t)
    (hadapt _) g b ρ α T t (fun n => (hT n).1) hρ hbundle
  have hcond : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X t ω j)) | filtR S.ℱ s] =ᵐ[S.μ]
        fun ω => Real.exp (-(∑ j, (stateR X s ω j : ℝ) * l j / (1 + c' j * l j))) := fun l hl =>
    localized_conditional_transform S.μ (filtR S.ℱ) α l t (stateR X) hl hX (hH l hl) s hs
  have hks := (hfrs.2.2 c' hc0').2 (stateR X s) (hX s hs) hcond
  refine ⟨hks.1, hks.2.1, hks.2.2, fun i => ?_⟩
  -- the conditional mean (15.15)
  have htr := transform d Ω mΩ S k α X x0 hc hcont hadapt hx0 hx0le hU hsde t
  have hint : ∀ j, Integrable (fun ω => (stateR X t ω j : ℝ)) S.μ := fun j =>
    ((htr.2.2.2 j).1).integrable one_le_two
  have hmean : ∀ j, S.μ[fun ω => (stateR X t ω j : ℝ) | filtR S.ℱ s] =ᵐ[S.μ]
      fun ω => (stateR X s ω j : ℝ) := fun j => ((htr.2.2.2 j).2.2.2.2.2 s hs).2.1
  have hVi : (fun ω => V ω i) =ᵐ[S.μ] fun ω => ∑ j, A i j * (stateR X t ω j : ℝ) := by
    filter_upwards [hfr.2.1] with ω hω
    show V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n) ω i =
      ∑ j, A i j * (stateR X t ω j : ℝ)
    rw [hω]
    simp only [Matrix.mulVec, dotProduct]
    rfl
  refine (condExp_congr_ae hVi).trans ?_
  have hsum := condExp_finsum S (fun j ω => A i j * (stateR X t ω j : ℝ)) (Real.toNNReal s)
    fun j => (hint j).const_mul _
  refine hsum.trans ?_
  have hterm : ∀ j, S.μ[fun ω => A i j * (stateR X t ω j : ℝ) | S.ℱ (Real.toNNReal s)] =ᵐ[S.μ]
      fun ω => A i j * (stateR X s ω j : ℝ) := by
    intro j
    have h1 := condExp_smul (μ := S.μ) (A i j) (fun ω => (stateR X t ω j : ℝ))
      (S.ℱ (Real.toNNReal s))
    have h1' : S.μ[fun ω => A i j * (stateR X t ω j : ℝ) | S.ℱ (Real.toNNReal s)] =ᵐ[S.μ]
        A i j • S.μ[fun ω => (stateR X t ω j : ℝ) | S.ℱ (Real.toNNReal s)] := h1
    filter_upwards [h1', hmean j] with ω h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul]
    have h2' : (S.μ[fun ω => (stateR X t ω j : ℝ) | S.ℱ (Real.toNNReal s)]) ω =
      (stateR X s ω j : ℝ) := h2
    rw [h2']
  filter_upwards [ae_all_iff.2 hterm] with ω hω
  exact Finset.sum_congr rfl fun j _ => hω j

lemma sourceMeetingVariance : sourceMeetingVarianceStatement := by
  intro N m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq T a lam γ c ρ hT hTpos
    ha hlm hl hlb hab hρm hρ hcww hcwu hcross1 hcross2 rows U t hT'
  intro g b Tr A V
  have hg : ∀ n j, Measurable (g n j) := fun n j => gJump_measurable T a lam γ ha hlm hlb _ j
  have hgb : ∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C := fun n j T' =>
    gJump_bound T a lam γ hl hab (rows n) j 0 T'
  have hbm : ∀ n j, Measurable (b n j) := fun n j => bJump_measurable T a lam γ ha hlm hlb _ j
  have hbint : ∀ n j (T' : ℝ), IntervalIntegrable (b n j) volume 0 T' := fun n j T' =>
    bJump_intInt_all T a lam γ ha hlm hl hlb hab (rows n) j T'
  have hmv := meetingVarianceFromFieldsAe m d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU
    hsde hsq g b ρ Tr hg hgb hbm hbint hρm hρ hcww hcwu hcross1 hcross2 U t hT'
  have hsr := (shortRateJump N d Ω mΩ S k kw α X x0 hc hcont hadapt hx0 hx0le hU hsde hsq
    T a lam γ c hT hTpos ha hlm hl hlb hab).2
  have hj : ∀ n, jumpSrc S kw T a lam γ X c (rows n) =ᵐ[S.μ] Yactual S kw X g b Tr n := by
    intro n
    filter_upwards [hsr (rows n)] with ω hω
    obtain ⟨L, hL, hjump⟩ := hω
    unfold jumpSrc
    rw [hL.limUnder_eq]
    exact hjump
  have hV : V =ᵐ[S.μ] V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b Tr n) :=
    V0150_congr_ae (filtR S.ℱ t) S.μ _ _ hj
  refine ⟨hj, hV, ⟨?_, ?_⟩, fun s hs => ?_⟩
  · rw [Measure.map_congr hV]
    exact hmv.1.1
  · rw [Measure.map_congr hV]
    exact hmv.1.2
  · intro c'
    have h := hmv.2 s hs
    refine ⟨h.1, fun D hD E hE => ?_, h.2.2⟩
    rw [Measure.map_congr (ae_restrict_of_ae hV)]
    exact h.2.1 D hD E hE

end Capstone

theorem zeroMeanReversionUpstreamBridge : Standalone.ZeroMeanReversionUpstreamBridge.statement :=
  ⟨extension, zeroIntegral, ito, localizationProp, localizationAeProp, transform, incrementsProp,
    twoDriverIsometryProp, crossFactorProp, coefficientProp, actualIncrement, kernelIsometry,
    productRuleProp, backwardWeight, centered, assembly, meetingVarianceFromFields,
    productRuleAC, centeredAC, assemblyAC, meetingVarianceFromFieldsAC, assemblyAe,
    meetingVarianceFromFieldsAe, shortRateJump, fullMeetingVarianceFromFields,
    sourceMeetingVariance⟩

end Novel.ZeroMeanReversionUpstreamBridgeProof

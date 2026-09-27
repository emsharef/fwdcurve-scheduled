import Standalone.RecurrenceNecessityGaussian
import Novel.RecurrentLoadingDiffusionProof
import Novel.SeparableMeetingRepresentationProof
import Novel.MeetingLoadingLawProof
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrenceNecessityGaussian
namespace Novel.RecurrenceNecessityGaussianProof

section Det
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- A bounded Borel deterministic integrand is in (U4). -/
lemma det_U4 (G : ℝ≥0 → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) :
    U4 S.ℱ S.μ (fun s _ => G s) := by
  have h := Novel.RecurrentLoadingDiffusionProof.U4_scaled S (fun _ _ => (1:ℝ))
    stronglyMeasurable_const 1 (fun _ _ => by simp) G hG (fun _ => ⟨C, fun s _ => hC s⟩)
  simpa using h

/-- A bounded Borel deterministic integrand is in (U5) on every horizon. -/
lemma det_U5 (G : ℝ≥0 → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (T : ℝ≥0) :
    U5 S.ℱ S.μ (fun s _ => G s) T := by
  refine ⟨det_U4 S G hG C hC, ?_⟩
  have hle : (∫⁻ s in Set.Icc (0:ℝ) T, ENNReal.ofReal ((G (Real.toNNReal s)) ^ 2)) ≤
      ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (T:ℝ) := by
    calc _ ≤ ∫⁻ _s in Set.Icc (0:ℝ) T, ENNReal.ofReal (C ^ 2) :=
          lintegral_mono fun s => ENNReal.ofReal_le_ofReal (by
            have := hC (Real.toNNReal s)
            nlinarith [abs_nonneg (G (Real.toNNReal s)), sq_abs (G (Real.toNNReal s))])
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  simp only [lintegral_const, measure_univ, mul_one]
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- The second moment of the integral of a bounded deterministic integrand. -/
lemma second_moment (k : Fin S.m) (G : ℝ≥0 → ℝ) (hG : Measurable G) (C : ℝ)
    (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0) :
    ∫ ω, (S.I k (fun s _ => G s) τ ω) ^ 2 ∂S.μ =
      ∫ s in (0:ℝ)..τ, G (Real.toNNReal s) * G (Real.toNNReal s) * S.c k k (Real.toNNReal s) := by
  haveI := S.isProbabilityMeasure
  set H : ℝ≥0 → Ω → ℝ := fun s _ => G s
  have hU5 := det_U5 S G hG C hC τ
  have hM := S.int_product_martingale k k H H τ hU5 hU5
  set D : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u,
    G (Real.toNNReal s) * G (Real.toNNReal s) * S.c k k (Real.toNNReal s) with hD
  set M : ℝ≥0 → Ω → ℝ := fun u ω => S.I k H (min u τ) ω * S.I k H (min u τ) ω -
    ∫ s in (0 : ℝ)..(min u τ : ℝ≥0), H (Real.toNNReal s) ω * H (Real.toNNReal s) ω *
      S.c k k (Real.toNNReal s) with hMdef
  have hcond : S.μ[M τ | S.ℱ 0] =ᵐ[S.μ] M 0 := hM.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ τ)
  have hM0 : M 0 =ᵐ[S.μ] 0 := by
    filter_upwards [S.int_zero k H hU5.1] with ω hω
    simp [hMdef, min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ), hω]
  have hMt : M τ = fun ω => (S.I k H τ ω) ^ 2 - D τ := by
    funext ω
    simp only [hMdef, min_self, sq, hD, H]
  have hL2 : MemLp (S.I k H τ) 2 S.μ := (S.int_martingale k H τ hU5).2 τ le_rfl
  have hint : ∫ ω, M τ ω ∂S.μ = 0 := by
    calc ∫ ω, M τ ω ∂S.μ = ∫ ω, (S.μ[M τ | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
      _ = ∫ ω, M 0 ω ∂S.μ := integral_congr_ae hcond
      _ = 0 := by rw [integral_congr_ae hM0]; simp
  rw [hMt, integral_sub hL2.integrable_sq (integrable_const _), integral_const] at hint
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at hint
  linarith

/-- For a Brownian driver, `∫_0^t c_kk = t`. -/
lemma c_integral (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) (t : ℝ≥0) :
    ∫ s in (0:ℝ)..t, S.c k k (Real.toNNReal s) = t := by
  haveI := S.isProbabilityMeasure
  have hM := S.B_covariation k k
  set N : ℝ≥0 → Ω → ℝ := fun u ω => S.B k u ω * S.B k u ω -
    ∫ s in (0 : ℝ)..u, S.c k k (Real.toNNReal s) with hN
  have hcond : S.μ[N t | S.ℱ 0] =ᵐ[S.μ] N 0 := hM.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t)
  have hN0 : N 0 =ᵐ[S.μ] 0 := by
    filter_upwards [S.B_zero k] with ω hω
    simp [hN, hω]
  have hint : ∫ ω, N t ω ∂S.μ = 0 := by
    calc ∫ ω, N t ω ∂S.μ = ∫ ω, (S.μ[N t | S.ℱ 0]) ω ∂S.μ := (integral_condExp (S.ℱ.le 0)).symm
      _ = ∫ ω, N 0 ω ∂S.μ := integral_congr_ae hcond
      _ = 0 := by rw [integral_congr_ae hN0]; simp
  have hL2 : MemLp (S.B k t) 2 S.μ := S.B_memLp_two k t
  have hsq : ∫ ω, S.B k t ω * S.B k t ω ∂S.μ = t := by
    have hc := hB.covariance_eval t t
    rw [min_self, covariance, hB.integral_eval] at hc
    simpa using hc
  have e : N t = fun ω => S.B k t ω * S.B k t ω - ∫ s in (0 : ℝ)..t, S.c k k (Real.toNNReal s) :=
    rfl
  rw [e, integral_sub (by simpa [sq] using hL2.integrable_sq) (integrable_const _), integral_const,
    hsq] at hint
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at hint
  linarith

/-- For a Brownian driver, `c_kk = 1` at almost every positive time. -/
lemma c_one (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) :
    ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → S.c k k (Real.toNNReal s) = 1 := by
  set g : ℝ → ℝ := fun s => S.c k k (Real.toNNReal s)
  have hgm : Measurable g := (S.c_measurable k k).comp measurable_real_toNNReal
  have hgl : LocallyIntegrable g volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨T, hT⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨C, hC⟩ := S.c_bounded_on_compacts k k (Real.toNNReal T)
    refine Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne
      hgm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with s hs
    rw [Real.norm_eq_abs]
    apply hC
    have hsT := hT hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hsT
    exact Real.toNNReal_le_toNNReal ((le_abs_self s).trans hsT)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hgl] with x hx hxpos
  have hev : (fun y => y) =ᶠ[𝓝 x] fun y => ∫ t in (0:ℝ)..y, g t := by
    filter_upwards [lt_mem_nhds hxpos] with y hy
    have := c_integral S k hB (Real.toNNReal y)
    rw [Real.coe_toNNReal y hy.le] at this
    exact this.symm
  exact ((hx 0).congr_of_eventuallyEq hev).unique (hasDerivAt_id x)

/-- The isometry for a Brownian driver: `E I(G)_τ² = ∫_0^τ G²`. -/
lemma isometry (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) (G : ℝ≥0 → ℝ)
    (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0) :
    ∫ ω, (S.I k (fun s _ => G s) τ ω) ^ 2 ∂S.μ = ∫ s in (0:ℝ)..τ, G (Real.toNNReal s) ^ 2 := by
  rw [second_moment S k G hG C hC τ]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [c_one S k hB] with s hs hmem
  rw [Set.uIoc_of_le τ.coe_nonneg] at hmem
  rw [hs hmem.1]
  ring

end Det

/-! ### Step approximations on a uniform grid of `(0, τ]` -/

/-- The grid point `τ i / (m+1)`. -/
noncomputable def grid (τ : ℝ≥0) (m i : ℕ) : ℝ≥0 := τ * i / (m + 1)

/-- The left-endpoint step function of `G` on the grid. -/
noncomputable def step (G : ℝ≥0 → ℝ) (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℝ :=
  ∑ i : Fin (m+1), G (grid τ m i) * Set.indicator (Set.Ioc (grid τ m i) (grid τ m (i+1))) 1 s

lemma grid_coe (τ : ℝ≥0) (m i : ℕ) : (grid τ m i : ℝ) = τ * i / (m + 1) := by
  simp [grid]

lemma grid_mono (τ : ℝ≥0) (m i : ℕ) : grid τ m i ≤ grid τ m (i+1) := by
  rw [← NNReal.coe_le_coe, grid_coe, grid_coe]
  gcongr
  push_cast
  linarith

lemma grid_le (τ : ℝ≥0) (m : ℕ) (i : Fin (m+1)) : grid τ m ((i:ℕ)+1) ≤ τ := by
  rw [← NNReal.coe_le_coe, grid_coe, div_le_iff₀ (by positivity)]
  have : ((i:ℕ):ℝ) + 1 ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  push_cast
  nlinarith [τ.coe_nonneg]

/-- The index of the cell containing `s ∈ (0, τ]`. -/
noncomputable def cell (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℕ := ⌈(s:ℝ) * (m + 1) / τ⌉₊ - 1

lemma mem_cell_iff (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) (hs0 : 0 < s) (hsτ : s ≤ τ) (i : ℕ) :
    s ∈ Set.Ioc (grid τ m i) (grid τ m (i+1)) ↔ i = cell τ m s := by
  have hτ : (0:ℝ) < τ := lt_of_lt_of_le (by exact_mod_cast hs0) (by exact_mod_cast hsτ)
  set x : ℝ := (s:ℝ) * (m + 1) / τ with hx
  have hx0 : 0 < x := by positivity
  have hmem : s ∈ Set.Ioc (grid τ m i) (grid τ m (i+1)) ↔ (i:ℝ) < x ∧ x ≤ (i:ℝ) + 1 := by
    rw [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, grid_coe, grid_coe, hx,
      lt_div_iff₀ hτ, div_le_iff₀ hτ, div_lt_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  rw [hmem]
  show _ ↔ i = ⌈x⌉₊ - 1
  constructor
  · rintro ⟨h1, h2⟩
    have : ⌈x⌉₊ = i + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      push_cast
      exact ⟨by linarith, h2⟩
    omega
  · intro hi
    have hc1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; exact hx0)
    have hi' : ⌈x⌉₊ = i + 1 := by omega
    have h1 := Nat.ceil_lt_add_one hx0.le
    have h2 := Nat.le_ceil x
    rw [hi'] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, h2⟩

lemma cell_lt (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) (hs0 : 0 < s) (hsτ : s ≤ τ) : cell τ m s < m + 1 := by
  have hτ : (0:ℝ) < τ := lt_of_lt_of_le (by exact_mod_cast hs0) (by exact_mod_cast hsτ)
  have hx : (s:ℝ) * (m + 1) / τ ≤ m + 1 := by
    rw [div_le_iff₀ hτ]
    have : (s:ℝ) ≤ τ := by exact_mod_cast hsτ
    nlinarith
  have := Nat.ceil_le.2 (by exact_mod_cast hx : (s:ℝ) * (m + 1) / τ ≤ ((m + 1 : ℕ) : ℝ))
  unfold cell
  omega

lemma step_eq (G : ℝ≥0 → ℝ) (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) (hs0 : 0 < s) (hsτ : s ≤ τ) :
    step G τ m s = G (grid τ m (cell τ m s)) := by
  unfold step
  rw [Finset.sum_eq_single ⟨cell τ m s, cell_lt τ m s hs0 hsτ⟩]
  · rw [Set.indicator_of_mem ((mem_cell_iff τ m s hs0 hsτ _).2 rfl)]
    simp
  · intro i _ hi
    rw [Set.indicator_of_notMem, mul_zero]
    rw [mem_cell_iff τ m s hs0 hsτ]
    intro h
    exact hi (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma step_zero (G : ℝ≥0 → ℝ) (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) (hs : ¬ (0 < s ∧ s ≤ τ)) :
    step G τ m s = 0 := by
  unfold step
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Set.indicator_of_notMem, mul_zero]
  rintro ⟨h1, h2⟩
  exact hs ⟨lt_of_le_of_lt zero_le h1, h2.trans (grid_le τ m i)⟩

lemma step_bound (G : ℝ≥0 → ℝ) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0) (m : ℕ) (s : ℝ≥0) :
    |step G τ m s| ≤ C := by
  by_cases hs : 0 < s ∧ s ≤ τ
  · rw [step_eq G τ m s hs.1 hs.2]; exact hC _
  · rw [step_zero G τ m s hs, abs_zero]; exact (abs_nonneg _).trans (hC 0)

lemma step_measurable (G : ℝ≥0 → ℝ) (τ : ℝ≥0) (m : ℕ) : Measurable (step G τ m) := by
  unfold step
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (measurable_const.indicator measurableSet_Ioc)

/-- The grid point of the cell of `s` tends to `s`. -/
lemma grid_cell_tendsto (τ : ℝ≥0) (s : ℝ≥0) (hs0 : 0 < s) (hsτ : s ≤ τ) :
    Tendsto (fun m => grid τ m (cell τ m s)) atTop (𝓝 s) := by
  have hτ : (0:ℝ) < τ := lt_of_lt_of_le (by exact_mod_cast hs0) (by exact_mod_cast hsτ)
  rw [← NNReal.tendsto_coe]
  have hb : ∀ m : ℕ, (s:ℝ) - τ / (m + 1) ≤ grid τ m (cell τ m s) ∧
      (grid τ m (cell τ m s) : ℝ) ≤ s := by
    intro m
    have h := (mem_cell_iff τ m s hs0 hsτ (cell τ m s)).2 rfl
    rw [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, grid_coe, grid_coe] at h
    rw [grid_coe]
    constructor
    · have : (s:ℝ) ≤ τ * ((cell τ m s : ℕ) + 1 : ℕ) / (m + 1) := by exact_mod_cast h.2
      push_cast at this
      rw [mul_add, add_div, mul_one] at this
      linarith
    · exact h.1.le
  have hlim : Tendsto (fun m : ℕ => (s:ℝ) - τ / (m + 1)) atTop (𝓝 s) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (τ:ℝ)).comp (tendsto_add_atTop_nat 1)
    have e : (fun m : ℕ => (s:ℝ) - τ / (m + 1)) =
        fun m => (s:ℝ) - ((fun n : ℕ => (τ:ℝ) / n) ∘ (fun a => a + 1)) m := by
      funext m; simp
    rw [e]
    simpa using tendsto_const_nhds.sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun m => (hb m).1) (fun m => (hb m).2)


section Steps
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma step_U4 (G : ℝ≥0 → ℝ) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0) (m : ℕ) :
    U4 S.ℱ S.μ (fun s _ => step G τ m s) :=
  det_U4 S _ (step_measurable G τ m) C (step_bound G C hC τ m)

/-- The integral of a step function is the sum of its increments. -/
lemma step_integral (k : Fin S.m) (G : ℝ≥0 → ℝ) (τ : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω ∂S.μ, S.I k (fun s _ => step G τ m s) τ ω =
      ∑ i : Fin (m+1), G (grid τ m i) *
        (S.B k (grid τ m ((i:ℕ)+1)) ω - S.B k (grid τ m i) ω) := by
  let H : Fin (m+1) → ℝ≥0 → Ω → ℝ := fun i s _ =>
    Set.indicator (Set.Ioc (grid τ m i) (grid τ m ((i:ℕ)+1))) 1 s
  have hHU : ∀ i, U4 S.ℱ S.μ (H i) := fun i =>
    det_U4 S _ (measurable_const.indicator measurableSet_Ioc) 1 (fun s => by
      by_cases h : s ∈ Set.Ioc (grid τ m i) (grid τ m ((i:ℕ)+1)) <;> simp [h])
  have hsum := Novel.SeparableMeetingRepresentationProof.integral_sum S k H
    (fun i => G (grid τ m i)) hHU Finset.univ τ
  have helem : ∀ i : Fin (m+1), (fun ω => S.I k (H i) τ ω) =ᵐ[S.μ]
      fun ω => S.B k (grid τ m ((i:ℕ)+1)) ω - S.B k (grid τ m i) ω := by
    intro i
    have h := S.int_elementary k (grid τ m i) (grid τ m ((i:ℕ)+1)) (fun _ => (1:ℝ))
      (grid_mono τ m i) measurable_const ⟨1, fun _ => by simp⟩ τ
    have e : (fun s ω => (fun _ : Ω => (1:ℝ)) ω *
        Set.indicator (Set.Ioc (grid τ m i) (grid τ m ((i:ℕ)+1))) 1 s) = H i := by
      funext s ω; simp [H]
    rw [e, min_eq_right (grid_le τ m i),
      min_eq_right ((grid_mono τ m i).trans (grid_le τ m i))] at h
    filter_upwards [h] with ω hω
    rw [hω, one_mul]
  filter_upwards [hsum, ae_all_iff.2 helem] with ω h1 h2
  have e : S.I k (fun s _ => step G τ m s) τ ω =
      S.I k (fun u ω => ∑ i : Fin (m+1), G (grid τ m i) * H i u ω) τ ω := rfl
  rw [e, h1]
  exact Finset.sum_congr rfl fun i _ => by rw [h2 i]

/-- The integral of a step function has a centered Gaussian law with variance `∫ step²`. -/
lemma step_gaussian (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) (G : ℝ≥0 → ℝ)
    (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0) (m : ℕ) :
    S.μ.map (S.I k (fun s _ => step G τ m s) τ) =
      gaussianReal 0 (∫ s in (0:ℝ)..τ, step G τ m (Real.toNNReal s) ^ 2).toNNReal := by
  have := S.isProbabilityMeasure
  let t : Fin (m+2) → ℝ≥0 := fun j => grid τ m j
  let Y : Ω → ℝ := fun ω => ∑ i : Fin (m+1), G (grid τ m i) *
    (S.B k (t i.succ) ω - S.B k (t i.castSucc) ω)
  let L : (Fin (m+1) → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (m+1), G (grid τ m i) • ContinuousLinearMap.proj i
  have hY : HasGaussianLaw Y S.μ := by
    have h := (hB.isGaussianProcess.hasGaussianLaw_increments (t := t)).map_fun L
    convert h using 2 with ω
    simp [L, Y]
  have hXY : S.I k (fun s _ => step G τ m s) τ =ᵐ[S.μ] Y := by
    filter_upwards [step_integral S k G τ m] with ω hω
    rw [hω]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [t, Fin.val_succ]
  have hint : ∫ ω, Y ω ∂S.μ = 0 := by
    simp only [Y]
    refine (integral_finsetSum _ fun i _ => ?_).trans (Finset.sum_eq_zero fun i _ => ?_)
    · exact ((hB.integrable_eval _).sub (hB.integrable_eval _)).const_mul _
    · rw [integral_const_mul, integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
        hB.integral_eval, hB.integral_eval, sub_zero, mul_zero]
  have hvar : Var[Y; S.μ] = ∫ s in (0:ℝ)..τ, step G τ m (Real.toNNReal s) ^ 2 := by
    rw [variance_of_integral_eq_zero hY.aemeasurable hint, ← isometry S k hB _
      (step_measurable G τ m) C (step_bound G C hC τ m) τ]
    exact integral_congr_ae (hXY.mono fun ω hω => by simp [hω])
  rw [Measure.map_congr hXY, hY.map_eq_gaussianReal, hint, hvar]

end Steps


/-! ### Convergence of the step approximations -/

lemma step_tendsto (G : ℝ≥0 → ℝ) (τ : ℝ≥0)
    (hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) → ContinuousAt G (Real.toNNReal s)) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 (τ:ℝ) →
      Tendsto (fun m => step G τ m (Real.toNNReal s)) atTop (𝓝 (G (Real.toNNReal s))) := by
  filter_upwards [hcont] with s hs hmem
  rw [Set.uIoc_of_le τ.coe_nonneg] at hmem
  have h0 : 0 < Real.toNNReal s := Real.toNNReal_pos.2 hmem.1
  have hle : Real.toNNReal s ≤ τ := Real.toNNReal_le_iff_le_coe.2 hmem.2
  have h := (hs hmem.1 hmem.2).tendsto.comp (grid_cell_tendsto τ _ h0 hle)
  refine h.congr fun m => ?_
  simp only [Function.comp, step_eq G τ m _ h0 hle]

lemma diff_tendsto (G : ℝ≥0 → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0)
    (hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) → ContinuousAt G (Real.toNNReal s)) :
    Tendsto (fun m => ∫ s in (0:ℝ)..τ, (G (Real.toNNReal s) - step G τ m (Real.toNNReal s)) ^ 2)
      atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume) (a := 0) (b := τ)
    (F := fun m s => (G (Real.toNNReal s) - step G τ m (Real.toNNReal s)) ^ 2)
    (f := fun _ => (0:ℝ)) (fun _ => (2 * C) ^ 2)
    (Eventually.of_forall fun m => (((hG.comp measurable_real_toNNReal).sub
      ((step_measurable G τ m).comp measurable_real_toNNReal)).pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun m => Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs, abs_pow, sq_abs]
      have h1 := hC (Real.toNNReal s)
      have h2 := step_bound G C hC τ m (Real.toNNReal s)
      have h3 : |G (Real.toNNReal s) - step G τ m (Real.toNNReal s)| ≤ 2 * C := by
        calc _ ≤ |G (Real.toNNReal s)| + |step G τ m (Real.toNNReal s)| := abs_sub _ _
          _ ≤ 2 * C := by linarith
      nlinarith [abs_nonneg (G (Real.toNNReal s) - step G τ m (Real.toNNReal s)),
        sq_abs (G (Real.toNNReal s) - step G τ m (Real.toNNReal s))])
    intervalIntegrable_const
    (by
      filter_upwards [step_tendsto G τ hcont] with s hs hmem
      have := ((hs hmem).const_sub (G (Real.toNNReal s))).pow 2
      simpa using this)
  simpa using h

lemma sq_tendsto (G : ℝ≥0 → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0)
    (hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) → ContinuousAt G (Real.toNNReal s)) :
    Tendsto (fun m => ∫ s in (0:ℝ)..τ, step G τ m (Real.toNNReal s) ^ 2)
      atTop (𝓝 (∫ s in (0:ℝ)..τ, G (Real.toNNReal s) ^ 2)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C ^ 2)
    (Eventually.of_forall fun m =>
      (((step_measurable G τ m).comp measurable_real_toNNReal).pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun m => Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs, abs_pow, sq_abs]
      have h2 := step_bound G C hC τ m (Real.toNNReal s)
      nlinarith [abs_nonneg (step G τ m (Real.toNNReal s)),
        sq_abs (step G τ m (Real.toNNReal s))])
    intervalIntegrable_const
    (by
      filter_upwards [step_tendsto G τ hcont] with s hs hmem
      exact (hs hmem).pow 2)

section Scalar
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma I_measurable (k : Fin S.m) (H : ℝ≥0 → Ω → ℝ) (hH : U4 S.ℱ S.μ H) (t : ℝ≥0) :
    Measurable (S.I k H t) :=
  (S.int_adapted k H hH t).mono (S.ℱ.le t) le_rfl

/-- The characteristic functions of two laws differ by at most `|t| E|X − Y|`. -/
lemma charFun_diff (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => X ω - Y ω) S.μ) (t : ℝ) :
    ‖charFun (S.μ.map X) t - charFun (S.μ.map Y) t‖ ≤ |t| * ∫ ω, |X ω - Y ω| ∂S.μ := by
  have := S.isProbabilityMeasure
  have hint : ∀ Z : Ω → ℝ, Measurable Z →
      Integrable (fun ω => Complex.exp (↑(inner ℝ (Z ω) t) * Complex.I)) S.μ := fun Z hZ =>
    Integrable.of_bound (C := 1) (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (continuous_inner.measurable.comp (hZ.prodMk measurable_const))).mul
        measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, charFun_apply, integral_map hX.aemeasurable (by fun_prop),
    integral_map hY.aemeasurable (by fun_prop), ← integral_sub (hint X hX) (hint Y hY),
    ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ((hXY.abs).const_mul _)
    (Eventually.of_forall fun ω => ?_))
  simp only [RCLike.inner_apply, conj_trivial]
  have e : Complex.exp (↑(t * X ω) * Complex.I) - Complex.exp (↑(t * Y ω) * Complex.I) =
      Complex.exp (↑(t * Y ω) * Complex.I) *
        (Complex.exp (Complex.I * ↑(t * (X ω - Y ω))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

/-- Lemma 032-A for one coordinate: the integral of a bounded Borel deterministic integrand,
continuous at almost every time of `(0, τ]`, is centered Gaussian with variance `∫_0^τ G²`. -/
lemma gaussian_scalar (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) (G : ℝ≥0 → ℝ)
    (hG : Measurable G) (C : ℝ) (hC : ∀ s, |G s| ≤ C) (τ : ℝ≥0)
    (hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) → ContinuousAt G (Real.toNNReal s)) :
    S.μ.map (S.I k (fun s _ => G s) τ) =
      gaussianReal 0 (∫ s in (0:ℝ)..τ, G (Real.toNNReal s) ^ 2).toNNReal := by
  have := S.isProbabilityMeasure
  have hGU := det_U4 S G hG C hC
  set X := S.I k (fun s _ => G s) τ
  let Xm : ℕ → Ω → ℝ := fun m => S.I k (fun s _ => step G τ m s) τ
  have hXm : ∀ m, Measurable (Xm m) := fun m => I_measurable S k _ (step_U4 S G C hC τ m) τ
  have hXmeas : Measurable X := I_measurable S k _ hGU τ
  -- the L² distance
  have hdist : ∀ m, ∫ ω, (X ω - Xm m ω) ^ 2 ∂S.μ =
      ∫ s in (0:ℝ)..τ, (G (Real.toNNReal s) - step G τ m (Real.toNNReal s)) ^ 2 := by
    intro m
    have hD : ∀ s, |G s - step G τ m s| ≤ 2 * C := fun s => by
      calc _ ≤ |G s| + |step G τ m s| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC s, step_bound G C hC τ m s]
    have hlin := S.int_linear k (fun s _ => G s) (fun s _ => step G τ m s) 1 (-1) hGU
      (step_U4 S G C hC τ m) τ
    have e : ((1:ℝ) • (fun (s : ℝ≥0) (_ : Ω) => G s) +
        (-1:ℝ) • fun (s : ℝ≥0) (_ : Ω) => step G τ m s) =
        fun s _ => G s - step G τ m s := by
      funext s ω; simp; ring
    rw [e] at hlin
    rw [← isometry S k hB (fun s => G s - step G τ m s) (hG.sub (step_measurable G τ m))
      (2 * C) hD τ]
    refine integral_congr_ae (hlin.mono fun ω hω => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω
    simp only [hω, X, Xm]
    ring
  have hL2 : ∀ m, MemLp (fun ω => X ω - Xm m ω) 2 S.μ := fun m =>
    ((S.int_martingale k _ τ (det_U5 S G hG C hC τ)).2 τ le_rfl).sub
      ((S.int_martingale k _ τ (det_U5 S _ (step_measurable G τ m) C
        (step_bound G C hC τ m) τ)).2 τ le_rfl)
  -- the first absolute moment of the difference tends to zero
  have habs : Tendsto (fun m => ∫ ω, |X ω - Xm m ω| ∂S.μ) atTop (𝓝 0) := by
    have hle : ∀ m, (∫ ω, |X ω - Xm m ω| ∂S.μ) ^ 2 ≤ ∫ ω, (X ω - Xm m ω) ^ 2 ∂S.μ := by
      intro m
      have hv := variance_nonneg (|fun ω => X ω - Xm m ω|) S.μ
      rw [variance_eq_sub (hL2 m).abs] at hv
      simp only [Pi.pow_apply, Pi.abs_apply, sq_abs] at hv
      linarith
    have hsq : Tendsto (fun m => (∫ ω, |X ω - Xm m ω| ∂S.μ) ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => sq_nonneg _) hle ?_
      simpa only [hdist] using diff_tendsto G hG C hC τ hcont
    have := (hsq.sqrt)
    simp only [Real.sqrt_zero] at this
    refine this.congr fun m => ?_
    rw [Real.sqrt_sq (integral_nonneg fun ω => abs_nonneg _)]
  -- the characteristic functions
  set v := ∫ s in (0:ℝ)..τ, G (Real.toNNReal s) ^ 2
  have hv0 : 0 ≤ v := intervalIntegral.integral_nonneg τ.coe_nonneg fun s _ => sq_nonneg _
  apply Measure.ext_of_charFun
  funext t
  have hlim1 : Tendsto (fun m => charFun (S.μ.map (Xm m)) t) atTop
      (𝓝 (charFun (S.μ.map X) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) (by
      simpa using habs.const_mul |t|)
    rw [norm_sub_rev]
    exact charFun_diff S X (Xm m) hXmeas (hXm m) ((hL2 m).integrable one_le_two) t
  have hlim2 : Tendsto (fun m => charFun (S.μ.map (Xm m)) t) atTop
      (𝓝 (charFun (gaussianReal 0 v.toNNReal) t)) := by
    have e : ∀ m, charFun (S.μ.map (Xm m)) t =
        Complex.exp (-(((∫ s in (0:ℝ)..τ, step G τ m (Real.toNNReal s) ^ 2 : ℝ)) * t ^ 2 / 2 : ℝ)) := by
      intro m
      rw [step_gaussian S k hB G C hC τ m, charFun_gaussianReal,
        Real.coe_toNNReal _ (intervalIntegral.integral_nonneg τ.coe_nonneg fun s _ => sq_nonneg _)]
      push_cast
      ring_nf
    have target : charFun (gaussianReal 0 v.toNNReal) t = Complex.exp (-(v * t ^ 2 / 2 : ℝ)) := by
      rw [charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      ring_nf
    rw [target]
    simp only [e]
    have hc : Continuous fun w : ℝ => Complex.exp (-(w * t ^ 2 / 2 : ℝ)) := by fun_prop
    exact (hc.tendsto v).comp (sq_tendsto G hG C hC τ hcont)
  exact tendsto_nhds_unique hlim1 hlim2

end Scalar


/-! ### The vector form of Lemma 032-A -/

lemma ii_bounded (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ s, |f s| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
    (Eventually.of_forall fun s => by show ‖f s‖ ≤ C; rw [Real.norm_eq_abs]; exact hC s)

lemma quad_gram {N : ℕ} (F : ℝ≥0 → Fin N → ℝ) (hF : ∀ j, Measurable fun s => F s j) (C : ℝ)
    (hC : ∀ s j, |F s j| ≤ C) (τ : ℝ≥0) (u : Fin N → ℝ) :
    u ⬝ᵥ (gram032 F τ *ᵥ u) =
      ∫ s in (0:ℝ)..τ, (∑ j, u j * F (Real.toNNReal s) j) ^ 2 := by
  have hm : ∀ j, Measurable fun s : ℝ => F (Real.toNNReal s) j := fun j =>
    (hF j).comp measurable_real_toNNReal
  have hii : ∀ i j, IntervalIntegrable (fun s : ℝ => u i * u j *
      (F (Real.toNNReal s) i * F (Real.toNNReal s) j)) volume 0 τ := fun i j =>
    ii_bounded _ (measurable_const.mul ((hm i).mul (hm j))) (|u i * u j| * (C * C))
      (fun s => by
        show |u i * u j * (F (Real.toNNReal s) i * F (Real.toNNReal s) j)| ≤ _
        rw [abs_mul, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hC _ i) (hC _ j) (abs_nonneg _)
          ((abs_nonneg _).trans (hC 0 i))) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) 0 τ
  have e : (fun s : ℝ => (∑ j, u j * F (Real.toNNReal s) j) ^ 2) =
      fun s => ∑ i, ∑ j, u i * u j * (F (Real.toNNReal s) i * F (Real.toNNReal s) j) := by
    funext s
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hii2 : ∀ i, IntervalIntegrable (fun s : ℝ => ∑ j, u i * u j *
      (F (Real.toNNReal s) i * F (Real.toNNReal s) j)) volume 0 τ := fun i => by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hii i j) using 1
    funext s
    simp [Finset.sum_apply]
  rw [e, intervalIntegral.integral_finsetSum fun i _ => hii2 i]
  simp only [dotProduct, mulVec, gram032, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hii i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

lemma gram_posSemidef {N : ℕ} (F : ℝ≥0 → Fin N → ℝ) (hF : ∀ j, Measurable fun s => F s j)
    (C : ℝ) (hC : ∀ s j, |F s j| ≤ C) (τ : ℝ≥0) : (gram032 F τ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, gram032, Matrix.of_apply, star_trivial]
    congr 1
    funext s
    ring
  · rw [star_trivial, quad_gram F hF C hC τ x]
    exact intervalIntegral.integral_nonneg τ.coe_nonneg fun s _ => sq_nonneg _

section Vector
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

/-- Lemma 032-A: the vector of integrals of a bounded Borel deterministic integrand, continuous
at almost every time of `(0, τ]`, is centered Gaussian with covariance `∫_0^τ F Fᵀ`. -/
lemma gaussian_vector (k : Fin S.m) (hB : IsPreBrownianReal (S.B k) S.μ) {N : ℕ}
    (F : ℝ≥0 → Fin N → ℝ) (hF : ∀ j, Measurable fun s => F s j) (C : ℝ)
    (hC : ∀ s j, |F s j| ≤ C) (τ : ℝ≥0)
    (hcont : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) →
      ∀ j, ContinuousAt (fun s => F s j) (Real.toNNReal s)) :
    S.μ.map (fun ω => WithLp.toLp 2 fun j => S.I k (fun s _ => F s j) τ ω) =
      multivariateGaussian 0 (gram032 F τ) := by
  have := S.isProbabilityMeasure
  have hU : ∀ j, U4 S.ℱ S.μ (fun s _ => F s j) := fun j => det_U4 S _ (hF j) C (hC · j)
  have hVm : Measurable fun ω => WithLp.toLp 2 fun j => S.I k (fun s _ => F s j) τ ω :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_iff.2 fun j => I_measurable S k _ (hU j) τ)
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_map_eq_charFun_map_inner_one hVm.aemeasurable u,
    charFun_multivariateGaussian (gram_posSemidef F hF C hC τ)]
  set G : ℝ≥0 → ℝ := fun s => ∑ j, u j * F s j
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => measurable_const.mul (hF j)
  have hGC : ∀ s, |G s| ≤ ∑ j, |u j| * C := fun s =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC s j) (abs_nonneg _))
  have hGc : ∀ᵐ (s : ℝ) ∂volume, 0 < s → s ≤ (τ:ℝ) → ContinuousAt G (Real.toNNReal s) := by
    filter_upwards [hcont] with s hs h0 hle
    exact tendsto_finsetSum _ fun j _ => continuousAt_const.mul (hs h0 hle j)
  have hsum := Novel.SeparableMeetingRepresentationProof.integral_sum S k
    (fun j => fun s (_ : Ω) => F s j) (fun j => u j) hU Finset.univ τ
  have hmap : S.μ.map (fun ω => inner ℝ (WithLp.toLp 2 fun j => S.I k (fun s _ => F s j) τ ω) u)
      = S.μ.map (S.I k (fun s _ => G s) τ) := by
    refine Measure.map_congr (hsum.mono fun ω hω => ?_)
    rw [show S.I k (fun s _ => G s) τ ω =
      S.I k (fun s ω => ∑ j ∈ Finset.univ, u j * F s j) τ ω from rfl, hω]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [hmap, gaussian_scalar S k hB G hGm _ hGC τ hGc, charFun_gaussianReal,
    Real.coe_toNNReal _ (intervalIntegral.integral_nonneg τ.coe_nonneg fun s _ => sq_nonneg _)]
  have hq := quad_gram F hF C hC τ (WithLp.ofLp u)
  simp only [G] at hq ⊢
  rw [← hq]
  simp

end Vector


section AC
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- A multivariate Gaussian law with positive definite covariance is absolutely continuous. -/
lemma multivariateGaussian_ac {n : ℕ} (μ : EuclideanSpace ℝ (Fin n)) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) : multivariateGaussian μ S ≪ volume := by
  set R := CFC.sqrt S
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRu : IsUnit R := isUnit_of_mul_isUnit_left (hRR ▸ hS.isUnit)
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) R
  have hLu : IsUnit L := hRu.map _
  have hLs : Function.Surjective L := by
    obtain ⟨u, hu⟩ := hLu
    intro y
    refine ⟨(↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) y, ?_⟩
    rw [← hu, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
  let eq := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    eq.toLinearMap ∘ₗ L.toLinearMap ∘ₗ eq.symm.toLinearMap
  have hA : Function.Surjective A :=
    eq.surjective.comp (hLs.comp eq.symm.surjective)
  have hpi : Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≪ volume :=
    Novel.MeetingLoadingLawProof.pi_ac n _ (fun _ => inferInstance)
      (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
  have h1 := Novel.MeetingLoadingLawProof.affine n n _ A (WithLp.ofLp μ) hpi hA
  have e : (fun x : Fin n → ℝ => μ + L (WithLp.toLp 2 x)) =
      (WithLp.toLp 2) ∘ fun x => WithLp.ofLp μ + A x := by
    funext x
    simp [A, eq]
  unfold multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have e2 : (HAdd.hAdd μ ∘ ⇑L) ∘ WithLp.toLp 2 = WithLp.toLp 2 ∘ fun x => WithLp.ofLp μ + A x := e
  change Measure.map ((HAdd.hAdd μ ∘ ⇑L) ∘ WithLp.toLp 2) _ ≪ _
  rw [e2, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  exact h1.map (by fun_prop)

end AC


theorem recurrenceNecessityGaussian : Standalone.RecurrenceNecessityGaussian.statement := ⟨fun Ω _ S k hB N F hF C hC τ hc => ⟨fun j => det_U4 S _ (hF j) C (hC · j), gaussian_vector S k hB F hF C hC τ hc⟩, fun n μ S hS => multivariateGaussian_ac μ S hS⟩

end Novel.RecurrenceNecessityGaussianProof

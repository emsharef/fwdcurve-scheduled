import Standalone.BoundedVarianceIntegralComparison
import Novel.BoundedVarianceMartingaleProof
import Upstream.IntegralApproximation

open MeasureTheory Filter
open scoped NNReal Topology
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.BoundedVarianceState Standalone.BoundedVarianceMartingale
open Standalone.BoundedVarianceIntegralComparison
open Novel.BoundedVarianceStateProof
namespace Novel.BoundedVarianceIntegralComparisonProof

/-- AX-11 is exactly the standalone restatement over the same data. -/
theorem ofUpstream {Ω : Type*} [MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (A : Upstream.IntegralApproximation S) :
    IntegralApproximation (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) where
  left_endpoint_tendstoInMeasure := A.left_endpoint_tendstoInMeasure

lemma continuous_paths_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ᵐ ω ∂μ, Continuous fun t => X t ω)
    (hY : ∀ᵐ ω ∂μ, Continuous fun t => Y t ω)
    (he : ∀ t, X t =ᵐ[μ] Y t) : ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂μ, ∀ t ∈ D, X t ω = Y t ω :=
    (ae_ball_iff hDc).2 fun t _ => he t
  filter_upwards [hD,hX,hY] with ω hD hx hy t
  have hclosed : IsClosed {s : ℝ≥0 | X s ω = Y s ω} := isClosed_eq hx hy
  have hsub : D ⊆ {s : ℝ≥0 | X s ω = Y s ω} := fun s hs => hD s hs
  have h := closure_minimal hsub hclosed
  rw [hDd.closure_eq] at h
  exact h (Set.mem_univ t)

lemma comparison : comparisonStatement := by
  intro Ω mΩ S R A D k l hμ hB H hS hR hcont hbound hUS hUR
  have hsums : (fun n T => leftEndpoint11 S k H n T) =
      (fun n T => leftEndpoint11 R l H n T) := by
    funext n T ω
    simp only [leftEndpoint11,hB]
  have hRcont := R.int_continuous l H hUR
  rw [hμ] at hRcont
  apply continuous_paths_eq S.μ _ _ (S.int_continuous k H hUS) hRcont
  intro T
  have hs := A.left_endpoint_tendstoInMeasure k H hS hcont hbound hUS T
  have hr := D.left_endpoint_tendstoInMeasure l H hR hcont hbound hUR T
  rw [hμ] at hr
  have he : (fun n => leftEndpoint11 S k H n T) =
      (fun n => leftEndpoint11 R l H n T) := by
    funext n
    exact congrFun (congrFun hsums n) T
  rw [← he] at hr
  exact tendstoInMeasure_ae_unique hs hr

lemma coefficient : Standalone.BoundedVarianceIntegralComparison.coefficientStatement := by
  intro Ω mΩ S R A D P Q k l hμ hB Y hS hR hY
  have hct : Continuous Real.tanh := continuous_iff_continuousAt.2 fun z =>
    (tanh_derivative025 z).continuousAt
  have ha : Continuous a025 := Real.continuous_sqrt.comp (continuous_const.add hct)
  have hcont : ∀ ω, Continuous fun t => a025 (Y t ω) := fun ω => ha.comp (hY ω)
  have hSad : Adapted S.ℱ (fun t ω => a025 (Y t ω)) := fun t => ha.measurable.comp (hS t)
  have hRad : Adapted R.ℱ (fun t ω => a025 (Y t ω)) := fun t => ha.measurable.comp (hR t)
  have hpS := P.continuous_predictable _ hSad hcont
  have hpR := Q.continuous_predictable _ hRad hcont
  have hsq : ∀ s ω, (a025 (Y s ω))^2 ≤ (2:ℝ)^2 := by
    intro s ω
    have hv := bounds025 (Y s ω)
    rw [show (a025 (Y s ω))^2 = v025 (Y s ω) from Real.sq_sqrt (by linarith [hv.1])]
    linarith [hv.2.1]
  have hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ω, |a025 (Y t ω)| ≤ K := by
    refine ⟨2, by norm_num, fun t ω => ?_⟩
    exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1 (by simpa using hsq t ω)
  exact comparison Ω mΩ S R A D k l hμ hB _ hSad hRad hcont hbound
    (Novel.BoundedVarianceMartingaleProof.bounded_U4 S _ hpS 2 hsq)
    (Novel.BoundedVarianceMartingaleProof.bounded_U4 R _ hpR 2 hsq)

lemma sums_one {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    leftEndpoint11 S k (fun _ _ => 1) n T ω = S.B k T ω - S.B k 0 ω := by
  simp only [leftEndpoint11,one_mul]
  rw [Finset.sum_range_sub (fun i : ℕ => S.B k ((i : ℝ≥0) * T / (2 : ℝ≥0)^n) ω)]
  simp [Nat.cast_pow, mul_div_cancel_left₀]

lemma constant : constantStatement := by
  intro Ω mΩ S A k
  have hU : U4 S.ℱ S.μ (fun _ _ => (1:ℝ)) :=
    Novel.BoundedVarianceMartingaleProof.bounded_U4 S _ stronglyMeasurable_const 1 (by intros; simp)
  apply continuous_paths_eq S.μ _ _ (S.int_continuous k _ hU) (S.B_continuous k)
  intro T
  have hp := A.left_endpoint_tendstoInMeasure k (fun _ _ => 1)
    (fun _ => measurable_const) (fun _ => continuous_const)
    ⟨1, by norm_num, by intros; simp⟩ hU T
  have he : (fun n => leftEndpoint11 S k (fun _ _ => 1) n T) =
      fun (_ : ℕ) ω => S.B k T ω - S.B k 0 ω := by
    funext n ω
    exact sums_one S k n T ω
  rw [he] at hp
  have hc : TendstoInMeasure S.μ (fun (_ : ℕ) ω => S.B k T ω - S.B k 0 ω)
      atTop (fun ω => S.B k T ω - S.B k 0 ω) := by
    intro ε hε
    simp [not_le.mpr hε]
  have h := tendstoInMeasure_ae_unique hp hc
  filter_upwards [h,S.B_zero k] with ω he hz
  simpa [hz] using he

/-- For the actual Upstream structures, adaptedness to the smaller filtration
suffices. The common driver, measure, structures and coordinate remain explicit. -/
theorem upstream_coefficient {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S R : Upstream.ItoCalculus Ω)
    (A : Upstream.IntegralApproximation S) (D : Upstream.IntegralApproximation R)
    (P : Upstream.Predictability S.ℱ) (Q : Upstream.Predictability R.ℱ)
    (k : Fin S.m) (l : Fin R.m) (hμ : R.μ = S.μ) (hB : S.B k = R.B l)
    (hRS : ∀ t, R.ℱ t ≤ S.ℱ t) (Y : ℝ≥0 → Ω → ℝ)
    (hR : ∀ t, Measurable[R.ℱ t] (Y t)) (hY : ∀ ω, Continuous fun t => Y t ω) :
    ∀ᵐ ω ∂S.μ, ∀ t,
      S.I k (fun s ω => a025 (Y s ω)) t ω = R.I l (fun s ω => a025 (Y s ω)) t ω :=
  coefficient Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R)
    (ofUpstream S A) (ofUpstream R D) ⟨P.continuous_predictable⟩ ⟨Q.continuous_predictable⟩
    k l hμ hB Y (fun t => (hR t).mono (hRS t) le_rfl) hR hY

/-- The first-coordinate identity with the audited Upstream input. -/
theorem upstream_constant {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : Upstream.ItoCalculus Ω) (A : Upstream.IntegralApproximation S) (k : Fin S.m) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun _ _ => 1) t ω = S.B k t ω :=
  constant Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) (ofUpstream S A) k

theorem boundedVarianceIntegralComparison : Standalone.BoundedVarianceIntegralComparison.statement :=
  ⟨comparison,coefficient,constant⟩

end Novel.BoundedVarianceIntegralComparisonProof

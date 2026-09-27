import Standalone.BoundedVarianceIndependence
import Novel.BoundedVarianceExistenceProof

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceState
open Standalone.BoundedVarianceExistence Standalone.BoundedVarianceIndependence
namespace Novel.BoundedVarianceIndependenceProof

lemma natural_le_path {Ω : Type*} [MeasurableSpace Ω]
    (V : ℝ≥0 → Ω → ℝ) (hV : ∀ t, StronglyMeasurable (V t)) (t : ℝ≥0) :
    Filtration.natural V hV t ≤ MeasurableSpace.comap (fun ω u => V u ω) inferInstance := by
  apply iSup₂_le
  intro u hu s hs
  obtain ⟨v,hv,rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  exact ⟨(fun p : ℝ≥0 → ℝ => p u) ⁻¹' v,(measurable_pi_apply u) hv,rfl⟩

lemma filtration : filtrationStatement := by
  intro Ω mΩ μ V hV t
  apply le_trans (iInf₂_le (t+1) (lt_add_one t))
  apply MeasurableSpace.generateFrom_le
  intro s hs
  apply MeasurableSpace.measurableSet_generateFrom
  rcases hs with hs | hs
  · exact Or.inl (natural_le_path V hV (t+1) _ hs)
  · exact Or.inr hs

/-- Every event in (25)'s augmented path sigma-algebra agrees almost surely
with an event in the unaugmented path sigma-algebra. -/
lemma event025 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : ℝ≥0 → Ω → ℝ) (s : Set Ω) (hs : MeasurableSet[m025 μ V] s) :
    ∃ t : Set Ω, MeasurableSet[MeasurableSpace.comap (fun ω u => V u ω) inferInstance] t ∧
      s =ᵐ[μ] t := by
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC s hs _ =>
    rcases hs with hs | hs
    · exact ⟨s,hs,EventuallyEq.rfl⟩
    · exact ⟨∅,@MeasurableSet.empty Ω (MeasurableSpace.comap (fun ω u => V u ω) inferInstance),ae_eq_empty.2 hs⟩
  | empty => exact ⟨∅,@MeasurableSet.empty Ω (MeasurableSpace.comap (fun ω u => V u ω) inferInstance),EventuallyEq.rfl⟩
  | compl s _ ih =>
    obtain ⟨t,ht,he⟩ := ih
    exact ⟨tᶜ,ht.compl,he.compl⟩
  | iUnion f _ ih =>
    choose t ht he using ih
    exact ⟨⋃ n, t n,MeasurableSet.iUnion ht,EventuallyEqSet.countable_iUnion he⟩

lemma independence : independenceStatement := by
  intro Ω m mΩ μ W V hWV tau hm J hJ
  have hW := hWV.comp (measurable_pi_apply tau) measurable_id
  apply indepFun_iff_measure_inter_preimage_eq_mul.2
  intro s t hs ht
  obtain ⟨u,hu,he⟩ := event025 μ V (J ⁻¹' t) (hm _ (hJ ht))
  obtain ⟨v,hv,rfl⟩ := MeasurableSpace.measurableSet_comap.1 hu
  rw [measure_congr (ae_eq_set_inter EventuallyEq.rfl he),measure_congr he]
  exact hW.measure_inter_preimage_eq_mul s v hs hv

lemma jump : jumpStatement := by
  intro Ω mΩ S R E A D P Q hB i k l hs hμ hdriver hRS hWi hInd hFil lam hl
  obtain ⟨Y,hR,hS,hcont,hzero⟩ := Novel.BoundedVarianceExistenceProof.transfer
    Ω mΩ S R E A D P Q hB k l hs hμ hdriver hRS lam hl
  refine ⟨Y,hR,hS,hcont,hzero,?_⟩
  intro tau htau
  have hIR : IndepFun (S.B i tau) (R.I l (fun s ω => a025 (Y s ω)) tau) S.μ :=
    independence Ω (R.ℱ tau) mΩ S.μ (S.B i) (R.B l) hInd tau (hFil tau)
      _ (R.int_adapted l _ hR.2.2.1 tau)
  have hI := Novel.BoundedVarianceIntegralComparisonProof.coefficient
    Ω mΩ S R A D P Q k l hμ hdriver Y hS.1 hR.1 hcont
  have hIS : IndepFun (S.B i tau) (S.I k (fun s ω => a025 (Y s ω)) tau) S.μ :=
    hIR.congr EventuallyEq.rfl (hI.mono fun ω hω => (hω tau).symm)
  refine ⟨hIS,?_⟩
  have heq : ∀ᵐ ω ∂S.μ, Y tau ω =
      (∫ s in (0:ℝ)..(tau:ℝ), b025 lam (Y (Real.toNNReal s) ω)) +
        S.I k (fun s ω => a025 (Y s ω)) tau ω := by
    filter_upwards [hS.2.2.2.2] with ω hω
    simpa only [add_comm] using hω tau
  have hmeas : AEMeasurable (S.I k (fun s ω => a025 (Y s ω)) tau) S.μ :=
    ((S.int_adapted k _ hS.2.2.1 tau).mono (S.ℱ.le _) le_rfl).aemeasurable
  have hj := Novel.BoundedVarianceStateProof.scheduledJump Ω mΩ S.μ S.isProbabilityMeasure
    (S.B i) hWi lam tau hl htau (fun s ω => Y (Real.toNNReal s) ω)
    (S.I k (fun s ω => a025 (Y s ω)) tau)
    (Eventually.of_forall fun ω => (hcont ω).comp continuous_real_toNNReal) hmeas hIS
    (by simpa only [Real.toNNReal_coe] using heq)
  simpa only [z025,Real.toNNReal_coe] using hj

/-- The constructed noise and nonzero jump with the actual audited Upstream
interfaces. The filtration containment concerns the Brownian basis, not the
noise integral; independence of that integral is the conclusion. -/
theorem upstream_jump {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S R : Upstream.ItoCalculus Ω) (E : Upstream.LipschitzSDE R)
    (A : Upstream.IntegralApproximation S) (D : Upstream.IntegralApproximation R)
    (P : Upstream.Predictability S.ℱ) (Q : Upstream.Predictability R.ℱ)
    (hB : Upstream.BrownianDrivers6 R) (i k : Fin S.m) (l : Fin R.m)
    (hs : ∀ j, j = l) (hμ : R.μ = S.μ) (hdriver : S.B k = R.B l)
    (hRS : ∀ t, R.ℱ t ≤ S.ℱ t) (hWi : IsBrownianReal (S.B i) S.μ)
    (hInd : IndepFun (fun ω t => S.B i t ω) (fun ω t => R.B l t ω) S.μ)
    (hFil : ∀ t, R.ℱ t ≤ m025 S.μ (R.B l)) (lam : ℝ) (hl : 0 < lam) :
    let S' := Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S
    let R' := Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R
    ∃ Y : ℝ≥0 → Ω → ℝ,
      ScalarSolution025 R' l lam Y ∧ ScalarSolution025 S' k lam Y ∧
      (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) ∧
      ∀ tau : ℝ≥0, 0 < tau →
        IndepFun (S.B i tau) (S.I k (fun s ω => a025 (Y s ω)) tau) S.μ ∧
        (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S' i lam Y tau ω) tau =
          S.B i tau ω + S.I k (fun s ω => a025 (Y s ω)) tau ω) ∧
        (∀ᵐ ω ∂S.μ, f025 lam tau (z025 S' i lam Y tau ω) tau ≠ 0) :=
  jump Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream R)
    (Novel.BoundedVarianceExistenceProof.ofUpstream R E)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream S A)
    (Novel.BoundedVarianceIntegralComparisonProof.ofUpstream R D)
    ⟨P.continuous_predictable⟩ ⟨Q.continuous_predictable⟩ hB i k l hs hμ hdriver hRS
    hWi hInd hFil lam hl

theorem boundedVarianceIndependence : Standalone.BoundedVarianceIndependence.statement :=
  ⟨filtration,independence,jump⟩

end Novel.BoundedVarianceIndependenceProof

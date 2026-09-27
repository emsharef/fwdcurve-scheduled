import Standalone.MeetingLoadingLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.MeetingLoadingLaw
namespace Novel.MeetingLoadingLawProof

lemma pi_ac : piStatement := by
  intro m
  induction m with
  | zero =>
    intro ρ _ _
    rw [volume_pi, Measure.pi_of_empty ρ, Measure.pi_of_empty]
  | succ m ih =>
    intro ρ hσ hρ
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
    have h1 := measurePreserving_piFinSuccAbove ρ 0
    have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => (volume : Measure ℝ)) 0
    have hih : Measure.pi (fun j => ρ (Fin.succAbove 0 j)) ≪ volume :=
      ih _ (fun j => hσ _) (fun j => hρ _)
    have hprod := (hρ 0).prod (hih.trans (by rw [volume_pi]))
    have e1 : Measure.pi ρ = ((ρ 0).prod (Measure.pi fun j => ρ (Fin.succAbove 0 j))).map e.symm := by
      rw [← h1.map_eq, Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self,
        Measure.map_id]
    have e2 : (volume : Measure (Fin (m+1) → ℝ)) =
        ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin m => (volume : Measure ℝ))).map e.symm := by
      rw [volume_pi, ← h2.map_eq, Measure.map_map e.symm.measurable e.measurable,
        e.symm_comp_self, Measure.map_id]
    rw [e1, e2]
    exact hprod.map e.symm.measurable

lemma affine : affineStatement := by
  intro m r ν A c hν hA N hN
  have hcont : Continuous fun x : Fin m → ℝ => c + A x :=
    continuous_const.add A.continuous_of_finiteDimensional
  set N' := toMeasurable volume N
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  set s := (fun y : Fin r → ℝ => c + y) ⁻¹' N' with hsdef
  have hsm : MeasurableSet s := (continuous_const.add continuous_id).measurable hN'm
  have hs0 : volume s = 0 := by rw [hsdef, measure_preimage_add]; exact hN'
  have hae : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), A x ∈ sᶜ :=
    (ae_comp_linearMap_mem_iff (μ := volume) (ν := volume) A hA hsm.compl).2
      (measure_eq_zero_iff_ae_notMem.1 hs0)
  have hpre : volume ((fun x => c + A x) ⁻¹' N') = 0 := by
    rw [ae_iff] at hae
    simp only [hsdef, Set.mem_compl_iff, Set.mem_preimage, not_not] at hae
    exact hae
  refine measure_mono_null (subset_toMeasurable volume N) ?_
  rw [Measure.map_apply hcont.measurable hN'm]
  exact hν hpre

lemma law : lawStatement := by
  intro Ω mΩ μ W hB m r τ hτ A c hA
  have := hB.isGaussianProcess.isProbabilityMeasure
  set Δ : Ω → Fin m → ℝ := fun ω l => W (τ l.succ) ω - W (τ l.castSucc) ω with hΔdef
  have hmeas : ∀ l : Fin m, AEMeasurable (fun ω => W (τ l.succ) ω - W (τ l.castSucc) ω) μ :=
    fun l => (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hind := hB.hasIndepIncrements m τ hτ.monotone
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hind
  have hΔ : μ.map Δ ≪ volume := by
    rw [hΔdef, hmap]
    refine pi_ac m _ (fun l => inferInstance) fun l => ?_
    have hl := (hB.hasLaw_sub (τ l.succ) (τ l.castSucc)).map_eq
    have e : (fun ω => W (τ l.succ) ω - W (τ l.castSucc) ω) = W (τ l.succ) - W (τ l.castSucc) := rfl
    rw [e, hl]
    apply gaussianReal_absolutelyContinuous
    have hlt : τ l.castSucc < τ l.succ := hτ (Fin.castSucc_lt_succ (i := l))
    intro h
    rw [nndist_eq_zero] at h
    exact (ne_of_gt hlt) (NNReal.eq h)
  have hΔm : AEMeasurable Δ μ := AEMeasurable.of_eval hmeas
  have hcont : Continuous fun x : Fin m → ℝ => c + A x :=
    continuous_const.add A.continuous_of_finiteDimensional
  have := AEMeasurable.map_map_of_aemeasurable hcont.aemeasurable hΔm
  rw [show (fun ω => c + A (fun l => W (τ l.succ) ω - W (τ l.castSucc) ω)) =
      (fun x => c + A x) ∘ Δ from rfl, ← this]
  exact affine m r _ A c hΔ hA

theorem meetingLoadingLaw : Standalone.MeetingLoadingLaw.statement := ⟨pi_ac, affine, law⟩

end Novel.MeetingLoadingLawProof

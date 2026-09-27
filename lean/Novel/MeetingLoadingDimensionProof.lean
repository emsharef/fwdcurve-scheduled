import Standalone.MeetingLoadingDimension

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace Novel.MeetingLoadingDimensionProof

/-- Coordinatewise locally Lipschitz maps into `Fin r → ℝ` are locally Lipschitz. -/
lemma locallyLipschitzOn_pi {q r : ℕ} (Φ : (Fin q → ℝ) → Fin r → ℝ) (Z : Set (Fin q → ℝ))
    (hΦ : ∀ i, LocallyLipschitzOn Z fun y => Φ y i) :
    ∀ x ∈ Z, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[Z] x, LipschitzOnWith C Φ t := by
  intro x hx
  choose K t ht hL using fun i => hΦ i hx
  refine ⟨Finset.univ.sup K, ⋂ i, t i, iInter_mem.2 ht, fun a ha b hb => ?_⟩
  rw [edist_pi_le_iff]
  intro i
  have ha' : a ∈ t i := mem_iInter.1 ha i
  have hb' : b ∈ t i := mem_iInter.1 hb i
  calc edist (Φ a i) (Φ b i) ≤ K i * edist a b := hL i ha' hb'
    _ ≤ (Finset.univ.sup K : ℝ≥0) * edist a b := by
        gcongr
        exact_mod_cast Finset.le_sup (f := K) (Finset.mem_univ i)

lemma dimension : Standalone.MeetingLoadingDimension.statement := by
  intro Ω mΩ μ hμ q r V Y Φ Z hV hac hΦ hae
  by_contra hqr
  push Not at hqr
  have hloc := locallyLipschitzOn_pi Φ Z hΦ
  have hdim : dimH (Φ '' Z) < ((r : ℝ≥0) : ℝ≥0∞) := by
    calc dimH (Φ '' Z) ≤ dimH Z := dimH_image_le_of_locally_lipschitzOn hloc
      _ ≤ dimH (univ : Set (Fin q → ℝ)) := dimH_mono (subset_univ _)
      _ = q := Real.dimH_univ_pi_fin q
      _ < ((r : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hqr
  have hH := hausdorffMeasure_of_dimH_lt hdim
  have hvol : volume (Φ '' Z) = 0 := by
    have e := hausdorffMeasure_pi_real (ι := Fin r)
    rw [Fintype.card_fin] at e
    rw [← e]
    simpa using hH
  set T := toMeasurable volume (Φ '' Z)
  have hT0 : volume T = 0 := by rw [measure_toMeasurable]; exact hvol
  have hmap : μ (V ⁻¹' T) = 0 := by
    have := hac hT0
    rwa [Measure.map_apply_of_aemeasurable hV (measurableSet_toMeasurable _ _)] at this
  have hin : ∀ᵐ ω ∂μ, V ω ∈ T := by
    filter_upwards [hae] with ω hω
    rw [hω.2]
    exact subset_toMeasurable _ _ ⟨Y ω, hω.1, rfl⟩
  have hnull : μ (V ⁻¹' T)ᶜ = 0 := by
    rw [ae_iff] at hin
    exact hin
  have huniv : μ univ = 0 := by
    rw [← union_compl_self (V ⁻¹' T)]
    exact le_antisymm ((measure_union_le _ _).trans (by rw [hmap, hnull, add_zero])) zero_le
  simp at huniv

theorem meetingLoadingDimension : Standalone.MeetingLoadingDimension.statement := dimension

end Novel.MeetingLoadingDimensionProof

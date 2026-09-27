import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Conditional identities as identities of lower integrals over the sets of a sub-σ-algebra

Supporting lemmas for Claim 008. The claim's conditional expectations are taken in `[0, ∞]`;
their defining property is an identity of lower integrals over every set of the sub-σ-algebra
`G`. The lemma here passes from such an identity to the same identity against any
`G`-measurable nonnegative weight, through the trimmed measures: two measures on `(Ω, m₀)`
that agree on every `G`-set have equal trims to `G`, and the lower integral of a
`G`-measurable function against a measure equals that against its trim
(`MeasureTheory.lintegral_trim`).
-/

open MeasureTheory ENNReal

namespace Novel.CondCalculus

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `∫⁻_A F dP = ∫⁻_A F' dP` for every `A ∈ G`, then `∫⁻ g F dP = ∫⁻ g F' dP` for every
`G`-measurable `g ≥ 0`. -/
lemma lintegral_mul_eq_of_forall_setLIntegral_eq {G : MeasurableSpace Ω} (hG : G ≤ m₀)
    {F F' : Ω → ℝ≥0∞} (hF : Measurable[m₀] F) (hF' : Measurable[m₀] F')
    (h : ∀ A : Set Ω, MeasurableSet[G] A → ∫⁻ ω in A, F ω ∂P = ∫⁻ ω in A, F' ω ∂P)
    {g : Ω → ℝ≥0∞} (hg : Measurable[G] g) :
    ∫⁻ ω, g ω * F ω ∂P = ∫⁻ ω, g ω * F' ω ∂P := by
  have htrim : (P.withDensity F).trim hG = (P.withDensity F').trim hG := by
    refine Measure.ext fun A hA => ?_
    rw [trim_measurableSet_eq hG hA, trim_measurableSet_eq hG hA,
      withDensity_apply _ (hG _ hA), withDensity_apply _ (hG _ hA), h A hA]
  have hg' : Measurable[m₀] g := hg.mono hG le_rfl
  calc ∫⁻ ω, g ω * F ω ∂P
      = ∫⁻ ω, g ω ∂(P.withDensity F) := by
        rw [lintegral_withDensity_eq_lintegral_mul P hF hg']
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ ω, g ω ∂((P.withDensity F).trim hG) := (lintegral_trim hG hg).symm
    _ = ∫⁻ ω, g ω ∂((P.withDensity F').trim hG) := by rw [htrim]
    _ = ∫⁻ ω, g ω ∂(P.withDensity F') := lintegral_trim hG hg
    _ = ∫⁻ ω, g ω * F' ω ∂P := by
        rw [lintegral_withDensity_eq_lintegral_mul P hF' hg']
        simp only [Pi.mul_apply, mul_comm]

end Novel.CondCalculus

import Upstream.ItoCalculus

/-!
# AX-09: predictability of continuous adapted processes

The field is the continuous, real-valued specialization of the adapted
left-continuous predictability fact in [bauerschmidt2020stochastic], p. 14
(`ledger/AXIOMS.md`, AX-09). It contains no SDE, transform, law or support assertion.
It is separate from `ItoCalculus`, so its addition does not strengthen the
hypotheses of claims already formalized using that structure.

The one-point instance verifies the field for every continuous process on that
space: such a process is a deterministic continuous function of time, hence
measurable for the predictable sigma-algebra. This is a degenerate instance
under repository rule 6 and is no evidence of a nontrivial stochastic model.

Re-synced against the ledger amendment at 99e79d64e (2026-09-23): only AX-09's
`Audit:` reference changed. Its sole field `continuous_predictable` and the
`unitInstance` remain unchanged, as do all entries represented by `HJMScheduled`
and `ItoCalculus`; no hypothesis or instance needs modification.
-/

open MeasureTheory
open scoped NNReal

namespace Upstream

/-- The hypothesis interface for the published predictability fact AX-09. -/
structure Predictability {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) : Prop where
  continuous_predictable : ∀ (X : ℝ≥0 → Ω → ℝ),
    (∀ t, Measurable[ℱ t] (X t)) → (∀ ω, Continuous fun t => X t ω) →
    IsStronglyPredictable ℱ X

namespace Predictability

/-- Degenerate non-vacuity instance: all continuous processes on the one-point
space are deterministic, and the predictable time-coordinate lemma applies. -/
theorem unitInstance : Predictability (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Unit) le_rfl) := by
  constructor
  intro X _ hc
  have he : X = fun t (_ : Unit) => X t () := by
    funext t ω
    cases ω
    rfl
  rw [he]
  exact ((hc ()).measurable.comp
    (ItoCalculus.measurable_fst_predictable (Filtration.const ℝ≥0 inferInstance le_rfl))).stronglyMeasurable

end Predictability
end Upstream

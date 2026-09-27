import Upstream.ItoCalculus

/-!
# AX-10: exponential martingale under a deterministic quadratic-variation bound

This is the finite-driver, deterministically stopped specialization of
[bauerschmidt2020stochastic], pp. 58, 60–61, entered as AX-10 in
`ledger/AXIOMS.md`. Both sums in the quadratic variation are retained, including
the cross terms. The bound is on their sum at the stopping horizon. The sole
field concludes the martingale property of the displayed stochastic exponential;
it assumes no bond-price identity, model solution, or independence of integrands.

The one-point instance has zero drivers, covariation densities and integrals.
For every integrand and horizon the exponential is identically one. This is a
degenerate consistency instance under repository rule 6, not evidence of
nontrivial stochastic satisfiability. The field and instance require the
Auditor's check against AX-10 before use.
-/

open MeasureTheory
open scoped NNReal

namespace Upstream

/-- AX-10.2, with the same real-time integration convention as AX-03 to AX-05. -/
noncomputable def quadraticVariation10 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (H : Fin h.m → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
    H k (Real.toNNReal s) ω * H l (Real.toNNReal s) ω * h.c k l (Real.toNNReal s)

/-- AX-10.3, including stopping of the integral and its quadratic variation. -/
noncomputable def exponential10 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (H : Fin h.m → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((∑ k, h.I k (H k) (min t T) ω) -
    (1 / 2 : ℝ) * quadraticVariation10 h H T t ω)

/-- The single published input AX-10, separate from the existing calculus interface. -/
structure ExponentialMartingale {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) : Prop where
  bounded_qv_exponential_martingale :
    ∀ (H : Fin h.m → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (C : ℝ),
      (∀ k, U4 h.ℱ h.μ (H k)) → 0 ≤ C →
      (∀ᵐ ω ∂h.μ, quadraticVariation10 h H T T ω ≤ C) →
      Martingale (exponential10 h H T) h.ℱ h.μ

namespace ExponentialMartingale

/-- Every integral and covariation vanishes in this degenerate model, so the
field reduces to the martingale property of the constant one process. -/
theorem zeroDriverInstance : ExponentialMartingale ItoCalculus.zeroDriverInstance := by
  constructor
  intro H T C _ _ _
  have he : exponential10 ItoCalculus.zeroDriverInstance H T =
      fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ) := by
    funext t ω
    simp [exponential10, quadraticVariation10, ItoCalculus.zeroDriverInstance]
  rw [he]
  exact martingale_const _ _ 1

end ExponentialMartingale
end Upstream

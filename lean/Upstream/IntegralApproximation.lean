import Upstream.ItoCalculus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# AX-11: left-endpoint approximation of the Itô integral

The single field is the specialization in `ledger/AXIOMS.md`, AX-11, of
[bauerschmidt2020stochastic], §3.4, Corollary p. 48. It uses the structure's
existing driver and integral, the grid i T / 2^n, and convergence in measure
at each fixed deterministic T, including T = 0. Adaptedness, everywhere path
continuity, a deterministic global bound, and membership in U4 are explicit.
It asserts neither almost-sure convergence nor equality of integral operators
in different filtrations. Those comparisons remain consumer obligations.

The constructed instance uses `ItoCalculus.zeroDriverInstance`. All driver
increments and all integrals vanish, so every sum and its limit are zero for
every integrand and horizon. It is degenerate under repository rule 6 and is
no evidence of nontrivial stochastic satisfiability. Constructing a genuine
stochastic integral merely to obtain an instance is forbidden by role duty 3b.
The Auditor checked this field and its degenerate instance at a163700b6,
as recorded in ledger/AUDIT_LOG.md on 2026-09-23.

Re-synced with the ledger at c234a390f: the single field retains adaptedness,
everywhere continuity, a deterministic nonnegative global bound and U4 as
premises, and convergence in measure to h.I k H T for each nonnegative T as
its conclusion. The dyadic sum uses the existing h.B k and the nonnegative-real
grid, including n = 0 and T = 0. AX-01 through AX-10 are unchanged by this ledger
addition; no field or instance in the other Upstream structures changes.
The ledger's updated implementation paragraph records the degenerate instance
and its audit; it changes no premise, conclusion or finite-sum convention.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace Upstream

/-- The exact finite sum (AX-11.2), with nonnegative-real grid points (AX-11.1). -/
noncomputable def leftEndpoint11 {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (k : Fin h.m) (H : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n),
    H ((i : ℝ≥0) * T / (2 : ℝ≥0)^n) ω *
      (h.B k (((i + 1 : ℕ) : ℝ≥0) * T / (2 : ℝ≥0)^n) ω -
        h.B k ((i : ℝ≥0) * T / (2 : ℝ≥0)^n) ω)

/-- The sole published input AX-11, over the existing calculus interface. -/
structure IntegralApproximation {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) : Prop where
  left_endpoint_tendstoInMeasure : ∀ (k : Fin h.m) (H : ℝ≥0 → Ω → ℝ),
    Adapted h.ℱ H → (∀ ω, Continuous fun t => H t ω) →
    (∃ K : ℝ, 0 ≤ K ∧ ∀ t ω, |H t ω| ≤ K) → U4 h.ℱ h.μ H →
    ∀ T : ℝ≥0,
      TendstoInMeasure h.μ (fun n => leftEndpoint11 h k H n T) atTop (h.I k H T)

namespace IntegralApproximation

/-- Degenerate consistency instance: every sum and every integral is zero. -/
theorem zeroDriverInstance : IntegralApproximation ItoCalculus.zeroDriverInstance := by
  constructor
  intro k H _ _ _ _ T ε hε
  simp [leftEndpoint11, ItoCalculus.zeroDriverInstance, not_le.mpr hε]

end IntegralApproximation
end Upstream

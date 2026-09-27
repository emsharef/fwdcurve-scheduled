import Standalone.UnifiedSpliceStep0
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Claim 050 (c): the conditional local converse's drifts are locally integrable

The Setting of Step 0 (`UnifiedSpliceStep0`). Claim 049(b)(iv)'s converse chooses, on each maturity
interval `m`, the front end's drift `dL_m + dC_m T` as the value and slope of
`−(R − c_m) + σ^S·∫σ^S`. Here it is written out.
* `kap050`: the front end's primitive on interval `m` is `P(u, T) = T V_m + κ_m`, with
  `κ_m = −u V_{n(u)} − Σ_{τ ∈ S, u < τ, n(τ) ≤ m} τ (V_{n(τ)} − V_{n(τ)−1})`.
* `alpha050`, `beta050`: `R♯(x) = α + β x`, so `α = R♯(0)` and `β = R♯(1) − R♯(0)`.
* `dC050 m = V_m·V_m + H^{0,0}·V_m + V_m·H^{0,0} − β − (2 H^{0,0}·V_{n(u)} + |V_{n(u)}|²)`;
  `dL050 m = V_m·κ_m + H^{0,0}·κ_m − u V_m·H^{0,0} − α + β u + (2 H^{0,0}·V_{n(u)} + |V_{n(u)}|²) u`.

`explicitStatement`: at a time and path where (49.2) holds at every later meeting and `R♯` is
affine, AX-01 holds at every maturity `T ∈ [u, H]` with these drifts. This is Claim 049(b)(iv)
"if" (`UnifiedSpliceConverseAX01`) with the drifts named.

`integrabilityStatement`, (c): on one path, over `[0, H]`, suppose:
* every noise row (`H^{0,μ}`, `H^ζ`, `V_m`) is square integrable (class (L1));
* the block drifts `b_{0,μ}`, `b_ζ` are integrable (L2);
* the block state `z_{0,μ}`, `ζ` is integrable (a continuous `Z` is bounded).

Then every chosen drift `u ↦ dL_m(u)`, `u ↦ dC_m(u)` is integrable on `[0, H]`, i.e. satisfies
(L2). They are linear in `b` and `Z`, and bilinear in the rows with coefficients bounded on
`[0, H]`, so Cauchy–Schwarz applies.
-/

open Matrix NormedSpace MeasureTheory Set

namespace Standalone.SpliceLocalizationConverse
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0

variable {k r : ℕ}

/-- `κ_m = −u V_{n(u)} − Σ_{τ ∈ S, u < τ, n(τ) ≤ m} τ (V_{n(τ)} − V_{n(τ)−1})`. -/
noncomputable def kap050 (S : Finset ℝ) (p : Pt049 k r) (u : ℝ) (m : ℕ) : Fin k → ℝ :=
  -u • p.V (nS S u) - ∑ τ ∈ S, if u < τ ∧ nS S τ ≤ m then
    τ • (p.V (nS S τ) - p.V (nS S τ - 1)) else 0

/-- `R♯(x)`, with the effective level `H^{0,0} + V_{n(u)}`. -/
noncomputable def Rsharp (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u x : ℝ) : ℝ :=
  resid (sharp p.Hp (p.V (nS S u))) p.Hz c A d p.bP p.zP p.bZ p.z x

noncomputable def alpha050 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) : ℝ := Rsharp c A d S p u 0

noncomputable def beta050 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) : ℝ := Rsharp c A d S p u 1 - Rsharp c A d S p u 0

noncomputable def dC050 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) (m : ℕ) : ℝ :=
  p.V m ⬝ᵥ p.V m + p.Hp 0 ⬝ᵥ p.V m + p.V m ⬝ᵥ p.Hp 0 - beta050 c A d S p u -
    (2 * (p.Hp 0 ⬝ᵥ p.V (nS S u)) + p.V (nS S u) ⬝ᵥ p.V (nS S u))

noncomputable def dL050 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) (m : ℕ) : ℝ :=
  p.V m ⬝ᵥ kap050 S p u m + p.Hp 0 ⬝ᵥ kap050 S p u m - u * (p.V m ⬝ᵥ p.Hp 0) -
    alpha050 c A d S p u + beta050 c A d S p u * u +
    (2 * (p.Hp 0 ⬝ᵥ p.V (nS S u)) + p.V (nS S u) ⬝ᵥ p.V (nS S u)) * u

def explicitStatement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
  IsUnit A.det → ∀ (S : Finset ℝ) (H u : ℝ) (p : Pt049 k r), 0 ≤ u → u < H → u ∉ S →
  (∀ τ ∈ S, u < τ → τ < H →
    (∀ μ, 1 ≤ μ → μ ≤ d → p.Hp μ ⬝ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
    p.Hz *ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) →
  (∃ α β : ℝ, ∀ x, Rsharp c A d S p u x = α + β * x) →
  ∀ T ∈ Icc u H, ax01At c A d S
    { p with dL := dL050 c A d S p u, dC := dC050 c A d S p u } u T

def integrabilityStatement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (D : ℝ → Pt049 k r),
  (∀ m ≤ S.card, ∀ l, MemLp (fun u => (D u).V m l) 2 (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, ∀ l, MemLp (fun u => (D u).Hp μ l) 2 (volume.restrict (Icc 0 H))) →
  (∀ i l, MemLp (fun u => (D u).Hz i l) 2 (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, Integrable (fun u => (D u).bP μ) (volume.restrict (Icc 0 H))) →
  (∀ i, Integrable (fun u => (D u).bZ i) (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, Integrable (fun u => (D u).zP μ) (volume.restrict (Icc 0 H))) →
  (∀ i, Integrable (fun u => (D u).z i) (volume.restrict (Icc 0 H))) →
  ∀ m ≤ S.card, Integrable (fun u => dL050 c A d S (D u) u m) (volume.restrict (Icc 0 H)) ∧
    Integrable (fun u => dC050 c A d S (D u) u m) (volume.restrict (Icc 0 H))

def statement : Prop := explicitStatement ∧ integrabilityStatement

end Standalone.SpliceLocalizationConverse

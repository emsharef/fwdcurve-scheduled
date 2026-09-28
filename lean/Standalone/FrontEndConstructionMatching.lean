import Standalone.SpliceLocalizationConverse
import Standalone.UnifiedSpliceQuantifiers

/-! # Claim 055 (d)–(f) at the coefficient level: the matching drifts

Claims 049–050's pointwise data `D : ℝ → Ω → Pt049 k r` (time `u`, path `ω`), with the block
(49.1), `A` invertible, and meeting dates `S`. The cited calculus enters only through AX-01 in the
ledger's form (`AX01`): for every `T ∈ (0, H]`, `(Q ⊗ dt)`-a.e. on `Ω × [0, T]`, `ax01At` at `T`.

* `matched`: the data with Claim 050's explicit drifts `dL_m = ℓ_m(u) = dL050`,
  `dC_m = c_m(u) = dC050`, the matching formula (`eq:frontmatch`).
* `orth`: (`eq:steporth`), `H^{0,μ} G_m = 0` (`1 ≤ μ ≤ d`) and `H^ζ G_m = 0` at every meeting
  `τ ∈ (u, H)`, with `G = V_{n(τ)} − V_{n(τ)−1}`.
* `FieldsMeas`: every coordinate of the given (non-drift) fields is jointly measurable in `(ω, u)`.
  Red's review of the proof of (e) notes that the passage from Claim 049's iterated "almost surely,
  for almost every `u`" to the product form needs it.

Statements:
* `driftConditionStatement`, (d): if `(Q ⊗ dt)`-a.e. on `Ω × [0, H]` (`eq:steporth`) holds and
  `R♯(u, ·)` is affine on `[0, H − u]` (`eq:resaffine`), then off one null set AX-01 holds at every
  maturity `T ∈ [u, H]` with the matching drifts, and hence in the ledger's form.
* `matchingStatement`, (e): with `(A, c)` observable (Red's note 3), if any front-end drifts satisfy
  AX-01 in the ledger's form, then `(Q ⊗ dt)`-a.e. they equal the matching drifts on every interval
  that meets `(u, H)`: `dL_{n(T)}(u) = ℓ_{n(T)}(u)` and `dC_{n(T)}(u) = c_{n(T)}(u)` for every
  `T ∈ (u, H)` off the meetings.
* `theoremStatement`, (f): with `(A, c)` observable, some front-end drifts give AX-01 in the ledger's
  form if and only if (`eq:steporth`) and (`eq:resaffine`) hold `(Q ⊗ dt)`-a.e. on `Ω × [0, H]`.

The processes `L_m`, `C_m` and the progressive measurability of the drifts (parts (a)–(b)) are in
`FrontEndConstructionProcess`, and the derivation of (2.2) from AX-05 (part (c)) is in
`FrontEndConstructionRepresentation`.
-/

open Matrix NormedSpace MeasureTheory Set

namespace Standalone.FrontEndConstructionMatching
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse

variable {k r : ℕ}

/-- The data with the matching drifts `ℓ_m(u)`, `c_m(u)`. -/
noncomputable def matched (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u : ℝ) : Pt049 k r :=
  { p with dL := dL050 c A d S p u, dC := dC050 c A d S p u }

/-- (`eq:steporth`) at every meeting `τ ∈ (u, H)`. -/
def orth (d : ℕ) (S : Finset ℝ) (H : ℝ) (p : Pt049 k r) (u : ℝ) : Prop :=
  ∀ τ ∈ S, u < τ → τ < H →
    (∀ μ, 1 ≤ μ → μ ≤ d → p.Hp μ ⬝ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
    p.Hz *ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0

/-- The conditions of (d) at `(u, ω)`: (`eq:steporth`), and `R♯` affine on `[0, H − u]`. -/
def Cond (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (H : ℝ)
    (p : Pt049 k r) (u : ℝ) : Prop :=
  orth d S H p u ∧ ∃ α β : ℝ, ∀ x ∈ Icc 0 (H - u), Rsharp c A d S p u x = α + β * x

/-- AX-01 in the ledger's form. -/
def AX01 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r) :
    Prop :=
  ∀ T, 0 < T → T ≤ H →
    ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 T))), ax01At c A d S (D q.2 q.1) q.2 T

/-- Joint measurability of the given (non-drift) fields. -/
def FieldsMeas {Ω : Type*} [MeasurableSpace Ω] (D : ℝ → Ω → Pt049 k r) : Prop :=
  (∀ μ l, Measurable fun q : Ω × ℝ => (D q.2 q.1).Hp μ l) ∧
  (∀ i l, Measurable fun q : Ω × ℝ => (D q.2 q.1).Hz i l) ∧
  (∀ μ, Measurable fun q : Ω × ℝ => (D q.2 q.1).bP μ) ∧
  (∀ μ, Measurable fun q : Ω × ℝ => (D q.2 q.1).zP μ) ∧
  (∀ i, Measurable fun q : Ω × ℝ => (D q.2 q.1).bZ i) ∧
  (∀ i, Measurable fun q : Ω × ℝ => (D q.2 q.1).z i) ∧
  (∀ m l, Measurable fun q : Ω × ℝ => (D q.2 q.1).V m l)

/-- `(A, c)` observable. -/
def Observable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0

def driftConditionStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r),
  (∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), Cond c A d S H (D q.2 q.1) q.2) →
  (∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))),
    ∀ T ∈ Icc q.2 H, ax01At c A d S (matched c A d S (D q.2 q.1) q.2) q.2 T) ∧
  AX01 μ c A d S H (fun u ω => matched c A d S (D u ω) u)

def matchingStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det → Observable c A →
  ∀ (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r), FieldsMeas D → AX01 μ c A d S H D →
  ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), ∀ T ∈ Ioo q.2 H, T ∉ S →
    (D q.2 q.1).dL (nS S T) = dL050 c A d S (D q.2 q.1) q.2 (nS S T) ∧
    (D q.2 q.1).dC (nS S T) = dC050 c A d S (D q.2 q.1) q.2 (nS S T)

def theoremStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det → Observable c A →
  ∀ (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r), FieldsMeas D →
    ((∃ dL dC : ℝ → Ω → ℕ → ℝ,
        AX01 μ c A d S H (fun u ω => { D u ω with dL := dL u ω, dC := dC u ω })) ↔
      ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), Cond c A d S H (D q.2 q.1) q.2)

def statement : Prop := driftConditionStatement ∧ matchingStatement ∧ theoremStatement

end Standalone.FrontEndConstructionMatching

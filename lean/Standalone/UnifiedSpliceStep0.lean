import Standalone.UnifiedSpliceAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Claim 049, Step 0: from AX-01 to the pointwise identity

The Setting, with `(u, ω)` fixed data `Pt049` at each time and path. `D u ω` holds:
* the block's rows `H^{0,μ}`, `H^ζ`, drifts `b_{0,μ}`, `b_ζ` and state `z_{0,μ}`, `ζ`;
* the front end's noise `V_m` and drifts `dL_m`, `dC_m` on each maturity interval.

The meeting dates form a finite set `S`. The interval of a maturity `T` is `n(T)`, the number of
meetings at or before `T` (`nS`). The block (49.1) is linear in its state, so Itô's formula (AX-05)
for the representation is the product rule. It gives:
* volatility `σ(u, T) = V_{n(T)}(u) + σ^B(u, T − u)` (`sig049`);
* drift `α(u, T) = dL_{n(T)}(u) + dC_{n(T)}(u) T + D^B(u, T − u)` (`alpha049`), with
  `D^B(x) = Σ_k b_k φ_k(x) − ∂_x F(x, Z_u)` (`driftB049`).

This is the drift and volatility for which the claim's Setting assumes Assumption 2.1. `P(u, T)` is
the front end's primitive `∫_u^T V_{n(v)}(u) dv` (`prim049`).

`step0Statement`: AX-01 in the ledger's form, for every `T ∈ (0, H]`,
`(Q ⊗ dt)`-a.e. on `Ω × [0, T]`: `∫_u^T α(u, v) dv = ½|∫_u^T σ(u, v) dv|²`, with the Euclidean norm.
It implies that `(Q ⊗ dt)`-a.e. on `Ω × [0, H]`, for every maturity `T ∈ (u, H)` that is not a
meeting date, with `m = n(T)`:
`R(u, T − u) − c(u, T) = V_m · P(u, T) − dL_m(u) − dC_m(u) T`.

Here `R` is the block residual (`resid`) and `c(u, T) = σ^B · P + V_m · Σ^B` is the cross part.
This is Step 0's identity: the right side is `(σ^S·∫σ^S − D^S)(u, T)`. The proof:
* AX-01 at the rational `T` holds simultaneously off one null set;
* both sides are continuous in `T`, so it holds at every `T ∈ [u, H]`;
* off the meetings both integrands are continuous in `T`, so the identity differentiates to
  `α = σ · ∫σ`, which rearranges to the display.
-/

open Matrix NormedSpace MeasureTheory Set

namespace Standalone.UnifiedSpliceStep0
open Standalone.UnifiedSpliceAlgebra

/-- The data at one time and path. -/
structure Pt049 (k r : ℕ) where
  Hp : ℕ → Fin k → ℝ
  Hz : Matrix (Fin r) (Fin k) ℝ
  bP : ℕ → ℝ
  zP : ℕ → ℝ
  bZ : Fin r → ℝ
  z : Fin r → ℝ
  V : ℕ → Fin k → ℝ
  dL : ℕ → ℝ
  dC : ℕ → ℝ

variable {k r : ℕ}

/-- `n(T)`: the number of meetings at or before `T`, the interval of the maturity `T`. -/
noncomputable def nS (S : Finset ℝ) (T : ℝ) : ℕ := (S.filter fun τ => τ ≤ T).card

/-- The volatility `σ(u, T) = V_{n(T)} + σ^B(T − u)`. -/
noncomputable def sig049 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u T : ℝ) : Fin k → ℝ :=
  p.V (nS S T) + sigB p.Hp p.Hz c A d (T - u)

/-- The block's drift `D^B(x) = Σ_k b_k φ_k(x) − ∂_x F(x, Z)`. -/
noncomputable def driftB049 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)
    (p : Pt049 k r) (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range (d + 1), p.bP μ * x ^ μ) + ephi c A x ⬝ᵥ p.bZ -
    ((∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * p.zP μ * x ^ (μ - 1)) + ephi c A x ⬝ᵥ (A *ᵥ p.z))

/-- The drift `α(u, T) = dL_{n(T)} + dC_{n(T)} T + D^B(T − u)`. -/
noncomputable def alpha049 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ)
    (p : Pt049 k r) (u T : ℝ) : ℝ :=
  p.dL (nS S T) + p.dC (nS S T) * T + driftB049 c A d p (T - u)

/-- The front end's primitive `P(u, T) = ∫_u^T V_{n(v)} dv`. -/
noncomputable def prim049 (S : Finset ℝ) (p : Pt049 k r) (u T : ℝ) : Fin k → ℝ :=
  fun l => ∫ v in u..T, p.V (nS S v) l

/-- AX-01 at `(ω, u)` and `T`: `∫_u^T α = ½ |∫_u^T σ|²`. -/
def ax01At (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (S : Finset ℝ) (p : Pt049 k r)
    (u T : ℝ) : Prop :=
  ∫ v in u..T, alpha049 c A d S p u v =
    (1 / 2 : ℝ) * ((fun l => ∫ v in u..T, sig049 c A d S p u v l) ⬝ᵥ
      fun l => ∫ v in u..T, sig049 c A d S p u v l)

def step0Statement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (S : Finset ℝ) (H : ℝ) (D : ℝ → Ω → Pt049 k r),
  (∀ T, 0 < T → T ≤ H →
    ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 T))), ax01At c A d S (D q.2 q.1) q.2 T) →
  ∀ᵐ q ∂(μ.prod (volume.restrict (Icc 0 H))), ∀ T ∈ Ioo q.2 H, T ∉ S →
    resid (D q.2 q.1).Hp (D q.2 q.1).Hz c A d (D q.2 q.1).bP (D q.2 q.1).zP (D q.2 q.1).bZ
        (D q.2 q.1).z (T - q.2) -
      (sigB (D q.2 q.1).Hp (D q.2 q.1).Hz c A d (T - q.2) ⬝ᵥ prim049 S (D q.2 q.1) q.2 T +
        (D q.2 q.1).V (nS S T) ⬝ᵥ SigB (D q.2 q.1).Hp (D q.2 q.1).Hz c A d (T - q.2)) =
      (D q.2 q.1).V (nS S T) ⬝ᵥ prim049 S (D q.2 q.1) q.2 T - (D q.2 q.1).dL (nS S T) -
        (D q.2 q.1).dC (nS S T) * T

def statement : Prop := step0Statement

end Standalone.UnifiedSpliceStep0

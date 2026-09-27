import Standalone.SpliceSeveralFactorsAX01

/-! # Claim 041 (a), converse: under (41.3) the cross term has no jumps

The setting is `SpliceSeveralFactorsAX01`'s. `blockPart041` is the block's part
`∫_0^t (D^B − σ^B·∫σ^B − ∑_l cross_l)(u, T) du`, and `stepPart041` is `∑_l S_l S^S_l`, the front
end's `σ^S ∫σ^S`.

* `jumpFreeStatement`: if (41.3) holds almost everywhere before every meeting, the integrated cross
  term is one function `c₀ + C e^{𝒜T}(y + T z)` on `[t, ∞)`. The individual drivers' cross terms may
  jump. Regrouped by block component, their sum is a sum of Claim 035 cross terms whose jumps are
  the components of `H^Z G_m^T`.
* `affineStatement`: under AX-01 and (41.3), the block's part is one affine function of `T` on
  `(t, H)`, the part the front-end drifts absorb, as in Claim 040(b).
* `converseStatement`: if the integrated front-end drift equals the integrated `σ^S ∫σ^S` minus the
  block's part, AX-01 holds in integrated form.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceSeveralFactorsSufficiency
open Standalone.SpliceCrossTermDrift Standalone.SpliceStateBlockCross
open Standalone.SpliceStateBlockAX01 Standalone.SpliceSeveralFactorsAX01

variable {r k L : ℕ}

/-- `∑_l S_l S^S_l`, the front end's `σ^S ∫σ^S`. -/
noncomputable def stepPart041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T

/-- The block's part `∫_0^t (D^B − σ^B·∫σ^B − ∑_l cross_l)(u, T) du`. -/
noncomputable def blockPart041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t T : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, (driftB c A bZ z u T -
    (∑ l, c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l)) *
      c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l))) -
    ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T)

def jumpFreeStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (H : ℝ), PathData041 s HS HZ dL dC bZ z H →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → W041 s HS HZ Tm τ u = 0) →
  ∀ t : ℝ, 0 ≤ t → ∃ (c₀ : ℝ) (y z' : Fin r → ℝ), ∀ T : ℝ, t ≤ T →
    ∫ u in (0:ℝ)..t, ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T =
      c₀ + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z'))

def affineStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (H : ℝ), PathData041 s HS HZ dL dC bZ z H → AX01Path041 s HS HZ dL dC bZ z Tm c A H →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → W041 s HS HZ Tm τ u = 0) →
  ∀ t : ℝ, 0 ≤ t → t < H → ∃ a₀ a₁ : ℝ, ∀ T ∈ Ioo t H,
    blockPart041 s HS HZ bZ z Tm c A t T = a₀ + a₁ * T

def converseStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (H : ℝ), PathData041 s HS HZ dL dC bZ z H → ∀ t T : ℝ, 0 ≤ t → t ≤ T → T ≤ H →
  ∫ u in (0:ℝ)..t, driftS dL dC Tm u T =
    (∫ u in (0:ℝ)..t, stepPart041 s HS Tm u T) - blockPart041 s HS HZ bZ z Tm c A t T →
  ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB c A bZ z u T) =
    ∫ u in (0:ℝ)..t, sigma041 s HS HZ Tm c A u T ⬝ᵥ
      fun l => ∫ v in u..T, sigma041 s HS HZ Tm c A u v l

def statement : Prop := jumpFreeStatement ∧ affineStatement ∧ converseStatement

end Standalone.SpliceSeveralFactorsSufficiency

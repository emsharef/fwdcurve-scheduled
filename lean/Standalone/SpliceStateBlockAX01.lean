import Standalone.SpliceStateBlockCross

/-! # Claim 040 (a)–(c) from AX-01, on one path

The Setting in driver form, on one path `ω`, over the independent base drivers `B^1, …, B^k`:
* the front end's step scales `s_j(u)` and its row `H^S(u) ∈ ℝ^{1×k}`, so `σ^S(u, T) = s_j(u) H^S(u)`
  on `I_j`. Its drift `D^S(u, T) = dL_j(u) + dC_j(u) T` is affine on each `I_j`; the drifts are
  free;
* the block (40.1) `F(x, z) = c e^{Ax} z` and the state `Z` with `dZ = b_Z du + H^Z dB`,
  `H^Z(u) ∈ ℝ^{r×k}`, and `Z_u = z(u)` on the path. By Itô's formula (AX-05) for (40.2) the block
  part has volatility `σ^B(u, T) = c e^{A(T−u)} H^Z(u)` and drift
  `D^B(u, T) = c e^{A(T−u)} (b_Z(u) − A z(u))`.

`sigma040` is `σ = σ^S + σ^B ∈ ℝ^k`. `AX01Path` is AX-01 differentiated in `T`, for almost every
`u ∈ [0, H]` and every `T ∈ [u, H]`: `D^S + D^B = σ(u, T) · ∫_u^T σ(u, v) dv`. `w040` is (40.3),
`w(u) = H^Z(u) H^S(u)^T`.

The statements are pathwise. A consistent process satisfies `AX01Path` on almost every path, so
each holds almost surely. `PathData040` asks that the scales, the loadings and `z` be measurable
and bounded, and that the drifts be interval integrable.

* `necessityStatement` is (a): `AX01Path` forces `Δ_m(u) w(u) = 0` for almost every `u ∈ [0, τ)`,
  at every meeting `τ < H`.
* `jumpFreeStatement` is (b)'s first point. If `Δ_m w = 0` almost everywhere before every meeting,
  the integrated cross term is one function `c₀ + c e^{AT}(y + T z)` on `[t, ∞)`.
* `affineStatement` is (b)'s "only if". Under `AX01Path` and that condition, the block's part, the
  integrated `D^B − σ^B·∫σ^B − cross`, is one affine function of `T` on `(t, H)`, the part the
  front-end drifts absorb.
* `converseStatement` is (b)'s "if". If the integrated front-end drift equals the integrated
  `σ^S ∫σ^S` minus the block's part, AX-01 holds in integrated form.
* `noThirdWayStatement` is (c): if `Δ_m w` is not almost everywhere zero before some meeting, no
  drifts make (40.2) satisfy AX-01 on the path. The jump the family would have to absorb is
  `SpliceStateBlockCross.explicitStatement`'s `c e^{AT}((A^{−1} − τ I) v + T v)` plus a constant.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceStateBlockAX01
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceStateBlockCross

variable {r k : ℕ}

/-- `σ(u, T) = s_j(u) H^S(u) + c e^{A(T−u)} H^Z(u) ∈ ℝ^k`. -/
noncomputable def sigma040 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (u T : ℝ) : Fin k → ℝ :=
  fun l => sigS033 s Tm u T * HS u l + c ⬝ᵥ (exp ((T - u) • A) *ᵥ fun i => HZ u i l)

/-- `w(u) = H^Z(u) H^S(u)^T`. -/
def w040 (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (u : ℝ) : Fin r → ℝ :=
  fun i => ∑ l, HZ u i l * HS u l

/-- The front end's drift `dL_j(u) + dC_j(u) T` on `I_j`. -/
noncomputable def driftS (dL dC : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  dL (idx033 Tm T) u + dC (idx033 Tm T) u * T

/-- The block's drift `c e^{A(T−u)} (b_Z(u) − A z(u))`. -/
noncomputable def driftB (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (bZ z : ℝ → Fin r → ℝ)
    (u T : ℝ) : ℝ :=
  c ⬝ᵥ (exp ((T - u) • A) *ᵥ (bZ u - A *ᵥ z u))

/-- AX-01, differentiated in `T`, on the path. -/
def AX01Path (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (H : ℝ) : Prop :=
  ∀ᵐ u ∂volume, u ∈ Icc 0 H → ∀ T ∈ Icc u H,
    driftS dL dC Tm u T + driftB c A bZ z u T =
      sigma040 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma040 s HS HZ Tm c A u v l

/-- The path data: measurable bounded scales, loadings and state, integrable drifts. -/
def PathData040 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (H : ℝ) : Prop :=
  (∀ j, Measurable (s j)) ∧ (∀ l, Measurable fun u => HS u l) ∧
  (∀ i l, Measurable fun u => HZ u i l) ∧ (∀ i, Measurable fun u => z u i) ∧
  (∃ C : ℝ, (∀ j u, |s j u| ≤ C) ∧ (∀ u l, |HS u l| ≤ C) ∧ (∀ u i l, |HZ u i l| ≤ C) ∧
    ∀ u i, |z u i| ≤ C) ∧
  (∀ j, IntervalIntegrable (dL j) volume 0 H) ∧ (∀ j, IntervalIntegrable (dC j) volume 0 H) ∧
  ∀ i, IntervalIntegrable (fun u => bZ u i) volume 0 H

/-- The block's part `∫_0^t (D^B − σ^B·∫σ^B − cross)(u, T) du`. -/
noncomputable def blockPart (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t T : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, (driftB c A bZ z u T -
    (∑ l, c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l)) *
      c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l))) -
    cross040 s Tm c A (w040 HS HZ) u T)

/-- `σ^S ∫σ^S = |H^S(u)|² s_j(u) S^S(u, T)`. -/
noncomputable def stepPart (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  (∑ l, HS u l ^ 2) * (sigS033 s Tm u T * SS033 s Tm u T)

def necessityStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ)
    (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H : ℝ), PathData040 s HS HZ dL dC bZ z H →
  AX01Path s HS HZ dL dC bZ z Tm c A H →
  ∀ τ ∈ Tm, τ < H → ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w040 HS HZ u = 0

def jumpFreeStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H : ℝ),
  PathData040 s HS HZ dL dC bZ z H →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w040 HS HZ u = 0) →
  ∀ t : ℝ, 0 ≤ t → ∃ (c₀ : ℝ) (y z' : Fin r → ℝ), ∀ T : ℝ, t ≤ T →
    ∫ u in (0:ℝ)..t, cross040 s Tm c A (w040 HS HZ) u T = c₀ + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z'))

def affineStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H : ℝ),
  PathData040 s HS HZ dL dC bZ z H → AX01Path s HS HZ dL dC bZ z Tm c A H →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w040 HS HZ u = 0) →
  ∀ t : ℝ, 0 ≤ t → t < H → ∃ a₀ a₁ : ℝ, ∀ T ∈ Ioo t H,
    blockPart s HS HZ bZ z Tm c A t T = a₀ + a₁ * T

def converseStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H : ℝ),
  PathData040 s HS HZ dL dC bZ z H → ∀ t T : ℝ, 0 ≤ t → t ≤ T → T ≤ H →
  ∫ u in (0:ℝ)..t, driftS dL dC Tm u T =
    (∫ u in (0:ℝ)..t, stepPart s HS Tm u T) - blockPart s HS HZ bZ z Tm c A t T →
  ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB c A bZ z u T) =
    ∫ u in (0:ℝ)..t, sigma040 s HS HZ Tm c A u T ⬝ᵥ
      fun l => ∫ v in u..T, sigma040 s HS HZ Tm c A u v l

def noThirdWayStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (H : ℝ) (τ : ℝ), τ ∈ Tm → τ < H →
  ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w040 HS HZ u = 0) →
  ∀ dL dC : ℕ → ℝ → ℝ, PathData040 s HS HZ dL dC bZ z H →
    ¬ AX01Path s HS HZ dL dC bZ z Tm c A H

def statement : Prop := necessityStatement ∧ jumpFreeStatement ∧ affineStatement ∧
  converseStatement ∧ noThirdWayStatement

end Standalone.SpliceStateBlockAX01

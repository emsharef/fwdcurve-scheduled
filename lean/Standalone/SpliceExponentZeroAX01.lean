import Standalone.SpliceExponentZeroCross
import Standalone.SpliceStateBlockAX01

/-! # Claim 044 (a)–(c) from AX-01, on one path

Claim 040's driver-form Setting (`SpliceStateBlockAX01`), with the block (44.1)
`F(x, z) = ∑_{μ ≤ d} z_{0,μ} x^μ + c e^{Ax} ζ`, on one path `ω`:
* the coefficient `z_{0,μ}` has `dz_{0,μ} = b_{0,μ} du + H^{0,μ} dB`, `H^{0,μ}(u) ∈ ℝ^{1×k}`, and
  `z_{0,μ}(u) = zP μ u` on the path;
* `ζ` is Claim 040's state `Z`, with `H^ζ(u) ∈ ℝ^{r×k}`, drift `b_ζ` and path `z`.

By Itô's formula (AX-05) for `x = T − u` the block has volatility
`σ^B(u, T) = ∑_μ (T − u)^μ H^{0,μ}(u) + c e^{A(T−u)} H^ζ(u)` (`sigmaB044`) and drift
`D^B(u, T) = ∑_μ [(T − u)^μ b_{0,μ}(u) − μ (T − u)^{μ−1} z_{0,μ}(u)] + c e^{A(T−u)}(b_ζ − A ζ)`
(`driftB044`). `sigma044` is `σ = σ^S + σ^B`. `AX01Path044` is AX-01 differentiated in `T`, for
almost every `u ∈ [0, H]` and every `T ∈ [u, H]`: `D^S + D^B = σ(u, T) · ∫_u^T σ(u, v) dv`.
`wP044 μ` is `w_μ = H^{0,μ} H^{S,T}`, and Claim 040's `w040` is `w_ζ` (44.2).

The statements are pathwise, like Claim 040's. `DriverData044` asks that the scales, loadings and
states be measurable and bounded, and that the drifts be interval integrable. `Cond044` is (a)'s
conclusion at every meeting: `Δ_m w_ζ = 0` and `Δ_m w_μ = 0` for `1 ≤ μ ≤ d`, almost everywhere
before the meeting.

* `necessityStatement` is (a): `AX01Path044` forces `Δ_m w_ζ = 0` and `Δ_m w_μ = 0` for
  `1 ≤ μ ≤ d`, for almost every `u ∈ [0, τ)`, at every meeting `τ < H`. Nothing is imposed on `w_0`.
* `levelStatement` is (b)'s first point for the level: for every `w_0`, the level's integrated cross
  term is affine on each maturity interval, so the front end absorbs it.
* `jumpFreeStatement` is (b)'s second point. Under `Cond044` the other cross terms (`restCross044`)
  integrate to one function `c₀ + c e^{AT}(y + T z) + P(T)` on `[t, ∞)`, with `P` a polynomial.
* `affineStatement` is (b)'s "only if". Under `AX01Path044` and `Cond044`, the block's part, the
  integrated `D^B − σ^B·∫σ^B − restCross044`, is one affine function of `T` on `(t, H)`.
* `converseStatement` is (b)'s "if". If the integrated front-end drift equals the integrated
  `σ^S ∫σ^S` plus the level's cross term minus the block's part, AX-01 holds in integrated form.
* `noThirdWayStatement` is (c)'s last point: if `Cond044` fails at some meeting, no drifts make the
  curve satisfy AX-01 on the path.
-/

open Matrix NormedSpace MeasureTheory Set Polynomial
namespace Standalone.SpliceExponentZeroAX01
open Standalone.SpliceCrossTermDrift Standalone.SpliceStateBlockCross
open Standalone.SpliceStateBlockAX01 Standalone.SpliceExponentZeroCross

variable {r k : ℕ}

/-- `σ^B(u, T) = ∑_{μ ≤ d} (T − u)^μ H^{0,μ}(u) + c e^{A(T−u)} H^ζ(u) ∈ ℝ^k`. -/
noncomputable def sigmaB044 (HP : ℕ → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (u T : ℝ) : Fin k → ℝ :=
  fun l => ∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * HP μ u l +
    c ⬝ᵥ (exp ((T - u) • A) *ᵥ fun i => HZ u i l)

/-- `σ(u, T) = s_j(u) H^S(u) + σ^B(u, T) ∈ ℝ^k`. -/
noncomputable def sigma044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (d : ℕ) (u T : ℝ) : Fin k → ℝ :=
  fun l => sigS033 s Tm u T * HS u l + sigmaB044 HP HZ c A d u T l

/-- `w_μ(u) = H^{0,μ}(u) H^S(u)^T`. -/
def wP044 (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ) (μ : ℕ) (u : ℝ) : ℝ :=
  ∑ l, HP μ u l * HS u l

/-- `D^B(u, T) = ∑_μ [(T − u)^μ b_{0,μ}(u) − μ (T − u)^{μ−1} z_{0,μ}(u)] + c e^{A(T−u)}(b_ζ − A ζ)`. -/
noncomputable def driftB044 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)
    (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (u T : ℝ) : ℝ :=
  ∑ μ ∈ Finset.range (d + 1), ((T - u) ^ μ * bP μ u - μ * (T - u) ^ (μ - 1) * zP μ u) +
    driftB c A bZ z u T

/-- AX-01, differentiated in `T`, on the path. -/
def AX01Path044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (H : ℝ) : Prop :=
  ∀ᵐ u ∂volume, u ∈ Icc 0 H → ∀ T ∈ Icc u H,
    driftS dL dC Tm u T + driftB044 c A d bP zP bZ z u T =
      sigma044 s HS HP HZ Tm c A d u T ⬝ᵥ fun l => ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l

/-- The path data: Claim 040's, and measurable bounded coefficient loadings and paths, with
integrable drifts. -/
def DriverData044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (H : ℝ) : Prop :=
  PathData040 s HS HZ dL dC bZ z H ∧ (∀ μ l, Measurable fun u => HP μ u l) ∧
    (∀ μ, Measurable (zP μ)) ∧ (∃ C : ℝ, (∀ μ u l, |HP μ u l| ≤ C) ∧ ∀ μ u, |zP μ u| ≤ C) ∧
    ∀ μ, IntervalIntegrable (bP μ) volume 0 H

/-- (a)'s conclusion at every meeting. -/
def Cond044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (d : ℕ) (τ : ℝ) : Prop :=
  (∀ᵐ u ∂volume, u ∈ Ico 0 τ → (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w040 HS HZ u = 0) ∧
  ∀ μ, 1 ≤ μ → μ ≤ d → ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) * wP044 HS HP μ u = 0

/-- `σ^B·∫σ^B`. -/
noncomputable def bb044 (HP : ℕ → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (u T : ℝ) : ℝ :=
  ∑ l, sigmaB044 HP HZ c A d u T l * ∫ v in u..T, sigmaB044 HP HZ c A d u v l

/-- The cross terms other than the level's: `ζ`'s and those of `z_{0,μ}`, `1 ≤ μ ≤ d`. -/
noncomputable def restCross044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (d : ℕ) (u T : ℝ) : ℝ :=
  cross040 s Tm c A (w040 HS HZ) u T +
    ∑ μ ∈ Finset.range d, crossPoly044 s Tm (μ + 1) (wP044 HS HP (μ + 1)) u T

/-- The block's part `∫_0^t (D^B − σ^B·∫σ^B − restCross044)(u, T) du`. -/
noncomputable def blockPart044 (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (t T : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T -
    restCross044 s HS HP HZ Tm c A d u T)

def necessityStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (d : ℕ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (H : ℝ), DriverData044 s HS HP HZ dL dC bP zP bZ z H →
  AX01Path044 s HS HP HZ dL dC bP zP bZ z Tm c A d H →
  ∀ τ ∈ Tm, τ < H → Cond044 s HS HP HZ Tm d τ

def levelStatement : Prop := ∀ (s : ℕ → ℝ → ℝ) (w : ℝ → ℝ), (∀ j, Measurable (s j)) →
  Measurable w → (∃ C : ℝ, (∀ j u, |s j u| ≤ C) ∧ ∀ u, |w u| ≤ C) →
  ∀ (Tm : Finset ℝ) (t : ℝ), 0 ≤ t → ∀ j : ℕ, ∃ k₀ k₁ : ℝ, ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, crossPoly044 s Tm 0 w u T = k₀ + k₁ * T

def jumpFreeStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (d : ℕ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (H : ℝ), DriverData044 s HS HP HZ dL dC bP zP bZ z H →
  (∀ τ ∈ Tm, Cond044 s HS HP HZ Tm d τ) →
  ∀ t : ℝ, 0 ≤ t → ∃ (c₀ : ℝ) (y z' : Fin r → ℝ) (P : ℝ[X]), ∀ T : ℝ, t ≤ T →
    ∫ u in (0:ℝ)..t, restCross044 s HS HP HZ Tm c A d u T =
      c₀ + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z')) + P.eval T

def affineStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (d : ℕ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (H : ℝ), DriverData044 s HS HP HZ dL dC bP zP bZ z H →
  AX01Path044 s HS HP HZ dL dC bP zP bZ z Tm c A d H → (∀ τ ∈ Tm, Cond044 s HS HP HZ Tm d τ) →
  ∀ t : ℝ, 0 ≤ t → t < H → ∃ a₀ a₁ : ℝ, ∀ T ∈ Ioo t H,
    blockPart044 s HS HP HZ bP zP bZ z Tm c A d t T = a₀ + a₁ * T

def converseStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (d : ℕ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ)
    (Tm : Finset ℝ) (H : ℝ), DriverData044 s HS HP HZ dL dC bP zP bZ z H →
  ∀ t T : ℝ, 0 ≤ t → t ≤ T → T ≤ H →
  ∫ u in (0:ℝ)..t, driftS dL dC Tm u T =
    (∫ u in (0:ℝ)..t, stepPart s HS Tm u T) +
      (∫ u in (0:ℝ)..t, crossPoly044 s Tm 0 (wP044 HS HP 0) u T) -
      blockPart044 s HS HP HZ bP zP bZ z Tm c A d t T →
  ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB044 c A d bP zP bZ z u T) =
    ∫ u in (0:ℝ)..t, sigma044 s HS HP HZ Tm c A d u T ⬝ᵥ
      fun l => ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l

def noThirdWayStatement : Prop := ∀ (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (d : ℕ) (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (bP zP : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (H τ : ℝ), τ ∈ Tm → τ < H → ¬ Cond044 s HS HP HZ Tm d τ →
  ∀ dL dC : ℕ → ℝ → ℝ, DriverData044 s HS HP HZ dL dC bP zP bZ z H →
    ¬ AX01Path044 s HS HP HZ dL dC bP zP bZ z Tm c A d H

def statement : Prop := necessityStatement ∧ levelStatement ∧ jumpFreeStatement ∧
  affineStatement ∧ converseStatement ∧ noThirdWayStatement

end Standalone.SpliceExponentZeroAX01

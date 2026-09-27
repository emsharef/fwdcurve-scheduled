import Standalone.SpliceQuasiExponentialCurve
import Standalone.SpliceQuasiExponentialBlock
import Standalone.SpliceCrossTermConsistency

/-! # Claim 035 (b)–(d): consistency with a quasi-exponential block

The setting is `SpliceQuasiExponentialCurve`'s, with `A` invertible, `(A, b)` controllable (the
Statement's reduction: no nonzero row vector `w` has `w A^k b = 0` for every `k`) and `c ≠ 0`.
Meetings lie in `(0, H)`. `S⁺` and `𝓕_t(E)` are Claim 033's (`SpliceCrossTermConsistency.SPlus033`,
`Fam033`); blocks are `SpliceQuasiExponentialBlock.Block035`. Consistency is in the version form
of Claim 033's revised definition (`HasVersion035`, `Consistent035`): `f(0, ·) ∈ 𝓕(E)`, and for
every `t ≤ H` some random element of `𝓕_t(E)`, with measurable evaluations, agrees with `f(t, T)`
almost surely for every `T ∈ [t, H]`.

`FamPlus035` is `𝓕⁺_t`: `p + g(· − t) + c e^{AT}(Y_m + T Z_m)` on `I_m ∩ [t, H]`, `p ∈ S⁺`,
`g ∈ E`, the indicator-times-quasi-exponential terms of (c)(ii).

* `necessityStatement` is (b): consistency with a block forces `ρ Δ = 0` almost everywhere on
  `[0, τ)` at every meeting `τ` (`SpliceCrossTermConsistency.jump033`).
* `noThirdWayStatement` is (d): if `ρ Δ` is not almost everywhere zero before some meeting, no
  block is consistent with the curve.
* `uncorrelatedSpliceStatement` is (c)(i): with `f(0, ·) ∈ 𝓕(E_1)` and `ρ Δ = 0` almost everywhere
  before every meeting, the curve is consistent with `𝓕(E_1)`.
* `enlargedStatement` is (c)(ii): for every `ρ`, with `f(0, ·) ∈ 𝓕(E_1)`, the curve is consistent
  with `𝓕⁺`.
-/

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceQuasiExponentialConsistency
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceQuasiExponentialCurve Standalone.SpliceQuasiExponentialBlock

variable {r : ℕ}

/-- `f(t, ·)` has a version in `𝓕_t(E)`. -/
def HasVersion035 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ))
    (t : ℝ≥0) : Prop :=
  ∃ g : Ω → ℝ → ℝ, (∀ ω, Fam033 Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
    ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve035 S k₁ k₂ f0 ρ s Tm c A b t T ω

/-- The pair (curve, `𝓕(E)`) is consistent, in the version form. -/
def Consistent035 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  Fam033 Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H → HasVersion035 S k₁ k₂ f0 ρ s Tm c A b H E t

/-- `h ∈ 𝓕⁺_t`: `p + g(· − t) + c e^{AT}(Y_m + T Z_m)` on `I_m ∩ [t, H]`. -/
def FamPlus035 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (H : ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) (t : ℝ) (h : ℝ → ℝ) : Prop :=
  ∃ p : ℝ → ℝ, SPlus033 Tm H p ∧ ∃ g ∈ E, ∃ Y Z : ℕ → Fin r → ℝ, ∀ T ∈ Icc t H,
    h T = p T + g (T - t) + c ⬝ᵥ (exp (T • A) *ᵥ (Y (idx033 Tm T) + T • Z (idx033 Tm T)))

/-- The pair (curve, `𝓕⁺`) is consistent, in the version form. -/
def ConsistentPlus035 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  FamPlus035 c A Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H →
    ∃ g : Ω → ℝ → ℝ, (∀ ω, FamPlus035 c A Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
      ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve035 S k₁ k₂ f0 ρ s Tm c A b t T ω

/-- The standing hypotheses on the block factor. -/
def Standing035 (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ) : Prop :=
  IsUnit A.det ∧ c ≠ 0 ∧ ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0

def necessityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ (ρ H : ℝ), (∀ τ ∈ Tm, 0 < τ ∧ τ < H) →
  ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block035 c A b E →
  Consistent035 S k₁ k₂ f0 ρ s Tm c A b H E →
  ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0

def noThirdWayStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ (ρ H : ℝ), (∀ τ ∈ Tm, 0 < τ ∧ τ < H) →
  ∀ τ ∈ Tm, ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0) →
  ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block035 c A b E →
  ¬ Consistent035 S k₁ k₂ f0 ρ s Tm c A b H E

def uncorrelatedSpliceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ),
  (∀ i, Measurable (s i)) → ∀ C : ℝ, (∀ i u, |s i u| ≤ C) →
  ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ), Standing035 A b c →
  ∀ (ρ H : ℝ) (f0 : ℝ → ℝ), Fam033 Tm H (E1 c A b) 0 f0 →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0) →
  Consistent035 S k₁ k₂ f0 ρ s Tm c A b H (E1 c A b)

def enlargedStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ),
  (∀ i, Measurable (s i)) → ∀ C : ℝ, (∀ i u, |s i u| ≤ C) →
  ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ), Standing035 A b c →
  ∀ (ρ H : ℝ) (f0 : ℝ → ℝ), Fam033 Tm H (E1 c A b) 0 f0 →
  ConsistentPlus035 S k₁ k₂ f0 ρ s Tm c A b H (E1 c A b)

def statement : Prop := necessityStatement ∧ noThirdWayStatement ∧ uncorrelatedSpliceStatement ∧
  enlargedStatement

end Standalone.SpliceQuasiExponentialConsistency

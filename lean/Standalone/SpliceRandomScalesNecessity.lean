import Standalone.SpliceRandomScalesCurve
import Standalone.SpliceQuasiExponentialConsistency

/-! # Claim 039 (b) and (d): a correlated step factor still forces indicator terms

The setting is `SpliceRandomScalesCurve`'s, with Claim 035's standing hypotheses on the block
factor (`SpliceQuasiExponentialConsistency.Standing035`), meetings in `(0, H)`, and blocks
`SpliceQuasiExponentialBlock.Block035`. Consistency is in the version form of Claim 033's revised
definition (`HasVersion039`, `Consistent039`): `f(0, ·) ∈ 𝓕(E)`, and for every `t ≤ H` some random
element of `𝓕_t(E)`, with measurable evaluations, agrees with `f(t, T)` almost surely for every
`T ∈ [t, H]`.

`jumpW` is `ρ_u ψ_u Δ_m(u)` at a meeting `τ`, on the path `ω`.

* `necessityStatement` is (b): consistency with a block forces, almost surely, `ρ_u ψ_u Δ_m(u) = 0`
  for almost every `u ∈ [0, τ)`, at every meeting `τ`.
* `noThirdWayStatement` is (d): if that fails with positive probability, no block is consistent
  with the curve.
-/

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceRandomScalesNecessity
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency Standalone.SpliceQuasiExponentialBlock
open Standalone.SpliceQuasiExponentialConsistency Standalone.SpliceRandomScalesCurve

variable {r : ℕ}

/-- `f(t, ·)` has a version in `𝓕_t(E)`. -/
def HasVersion039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ))
    (t : ℝ≥0) : Prop :=
  ∃ g : Ω → ℝ → ℝ, (∀ ω, Fam033 Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
    ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve039 S k₁ k₂ f0 ρ ψ s Tm c A b t T ω

/-- The pair (curve, `𝓕(E)`) is consistent, in the version form. -/
def Consistent039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  Fam033 Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H → HasVersion039 S k₁ k₂ f0 ρ ψ s Tm c A b H E t

/-- `ρ_u ψ_u Δ_m(u)` at the meeting `τ`, on the path `ω`. -/
noncomputable def jumpW {Ω : Type*} (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ)
    (τ u : ℝ) (ω : Ω) : ℝ :=
  ρ u ω * ψ u ω * jump033 (fun j v => s j v ω) Tm τ u

def necessityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ), Scales039 S s ρ ψ C →
  ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ H : ℝ, (∀ τ ∈ Tm, 0 < τ ∧ τ < H) →
  ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block035 c A b E →
  Consistent039 S k₁ k₂ f0 ρ ψ s Tm c A b H E →
  ∀ᵐ ω ∂S.μ, ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0

def noThirdWayStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ), Scales039 S s ρ ψ C →
  ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ H : ℝ, (∀ τ ∈ Tm, 0 < τ ∧ τ < H) →
  ¬ (∀ᵐ ω ∂S.μ, ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0) →
  ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block035 c A b E →
  ¬ Consistent039 S k₁ k₂ f0 ρ ψ s Tm c A b H E

def statement : Prop := necessityStatement ∧ noThirdWayStatement

end Standalone.SpliceRandomScalesNecessity

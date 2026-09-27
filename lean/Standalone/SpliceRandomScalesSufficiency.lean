import Standalone.SpliceRandomScalesNecessity

/-! # Claim 039 (c): sufficiency of the two constructions

The setting is `SpliceRandomScalesNecessity`'s. `E_1` is the smallest block containing `λ`,
`x λ(x)` and `λΛ` (`SpliceQuasiExponentialBlock.E1`). `𝓕⁺_t` is Claim 035's indicator-enlarged
family (`SpliceQuasiExponentialConsistency.FamPlus035`).

* `uncorrelatedSpliceStatement` is (c)(i). Suppose `f(0, ·) ∈ 𝓕(E_1)` and, almost surely,
  `ρ_u ψ_u Δ_m(u) = 0` for almost every `u < τ` at every meeting `τ`. Then the curve is
  consistent with `𝓕(E_1)`, in the version form.
* `enlargedStatement` is (c)(ii): for all predictable bounded `ρ`, `ψ` and `s`, with
  `f(0, ·) ∈ 𝓕(E_1)`, the curve is consistent with `𝓕⁺`.

A version must have measurable evaluations. So both proofs use the fact that predictable scales
are jointly measurable in `(u, ω)`, which makes the pathwise drift integral measurable in `ω`.
-/

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceRandomScalesSufficiency
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermConsistency
open Standalone.SpliceQuasiExponentialBlock Standalone.SpliceQuasiExponentialConsistency
open Standalone.SpliceRandomScalesCurve Standalone.SpliceRandomScalesNecessity

variable {r : ℕ}

/-- The pair (curve, `𝓕⁺`) is consistent, in the version form. -/
def ConsistentPlus039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  FamPlus035 c A Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H →
    ∃ g : Ω → ℝ → ℝ, (∀ ω, FamPlus035 c A Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
      ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve039 S k₁ k₂ f0 ρ ψ s Tm c A b t T ω

def uncorrelatedSpliceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ),
  Scales039 S s ρ ψ C → ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ (H : ℝ) (f0 : ℝ → ℝ), Fam033 Tm H (E1 c A b) 0 f0 →
  (∀ᵐ ω ∂S.μ, ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0) →
  Consistent039 S k₁ k₂ f0 ρ ψ s Tm c A b H (E1 c A b)

def enlargedStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ),
  Scales039 S s ρ ψ C → ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ),
  Standing035 A b c → ∀ (H : ℝ) (f0 : ℝ → ℝ), Fam033 Tm H (E1 c A b) 0 f0 →
  ConsistentPlus039 S k₁ k₂ f0 ρ ψ s Tm c A b H (E1 c A b)

def statement : Prop := uncorrelatedSpliceStatement ∧ enlargedStatement

end Standalone.SpliceRandomScalesSufficiency

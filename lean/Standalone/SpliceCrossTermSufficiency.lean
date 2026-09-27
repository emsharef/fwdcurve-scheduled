import Standalone.SpliceCrossTermConsistency

/-! # Claim 033 (c): the two sufficient constructions

The setting and the version-form consistency are `SpliceCrossTermConsistency`'s.
`E0 a = span{e^{−ax}, x e^{−ax}, e^{−2ax}}`.

* `e0BlockStatement`: `E0 a` is a block.
* `uncorrelatedSpliceStatement` is (c)(i). Let `f(0, ·) ∈ 𝓕(E_0)` and let `ρ Δ = 0` almost
  everywhere on `[0, τ)` at every meeting `τ`. Then (curve, `𝓕(E_0)`) is consistent. With `ρ = 0`
  this is the uncorrelated splice of [gellert2021short] §3.
* `enlargedStatement` is (c)(ii). For every `ρ` and `f(0, ·) ∈ 𝓕(E_0)`, the curve is consistent
  with the enlarged family `𝓕⁺ = 𝓕(E_0) + span{1_{I_m}(T) e^{−aT}, 1_{I_m}(T) T e^{−aT}}`, in
  the same version form. `FamPlus033 a Tm H E t h` says that `h` is in `𝓕⁺_t` on `[t, H]`: it is
  `p + g(· − t) + e^{−aT}(c_m + d_m T)` on `I_m ∩ [t, H]`, with `p ∈ S⁺` and `g ∈ E`.

In both, the version of `f(t, ·)` is the curve's finite formula: `f(0, ·)`, the drift integral, and
the version of the random part from (a) (`SpliceCrossTermCurve.randomStatement`), built from
finitely many random variables.
-/

open MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceCrossTermSufficiency
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency

/-- `E_0 = span{e^{−ax}, x e^{−ax}, e^{−2ax}}`. -/
noncomputable def E0 (a : ℝ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {fun x => Real.exp (-a * x), fun x => x * Real.exp (-a * x),
    fun x => Real.exp (-(2 * a) * x)}

/-- `h ∈ 𝓕⁺_t`: `p + g(· − t) + e^{−aT}(c_m + d_m T)` on `I_m ∩ [t, H]`. -/
def FamPlus033 (a : ℝ) (Tm : Finset ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) (t : ℝ)
    (h : ℝ → ℝ) : Prop :=
  ∃ p : ℝ → ℝ, SPlus033 Tm H p ∧ ∃ g ∈ E, ∃ c d : ℕ → ℝ, ∀ T ∈ Icc t H,
    h T = p T + g (T - t) + Real.exp (-a * T) * (c (idx033 Tm T) + d (idx033 Tm T) * T)

/-- The pair (curve, `𝓕⁺`) is consistent, in the version form. -/
def ConsistentPlus033 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (H : ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  FamPlus033 a Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H →
    ∃ g : Ω → ℝ → ℝ, (∀ ω, FamPlus033 a Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
      ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve033 S k₁ k₂ f0 a b ρ s Tm t T ω

def e0BlockStatement : Prop := ∀ a : ℝ, Block033 a (E0 a)

def uncorrelatedSpliceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ),
  (∀ i, Measurable (s i)) → ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ H : ℝ), a ≠ 0 →
  ∀ f0 : ℝ → ℝ, Fam033 Tm H (E0 a) 0 f0 →
  (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0) →
  Consistent033 S k₁ k₂ f0 a b ρ s Tm H (E0 a)

def enlargedStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ),
  (∀ i, Measurable (s i)) → ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ H : ℝ), a ≠ 0 →
  ∀ f0 : ℝ → ℝ, Fam033 Tm H (E0 a) 0 f0 →
  ConsistentPlus033 S k₁ k₂ f0 a b ρ s Tm H (E0 a)

def statement : Prop := e0BlockStatement ∧ uncorrelatedSpliceStatement ∧ enlargedStatement

end Standalone.SpliceCrossTermSufficiency

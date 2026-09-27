import Standalone.SpliceCrossTermDrift
import Standalone.ZeroMeanReversionUpstreamBridge
import Mathlib.Analysis.Analytic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Claim 033 (b) and (d): consistency in the version form

The setting is `SpliceCrossTermDrift`'s and `SpliceCrossTermCurve`'s: meeting dates `Tm` in
`(0, H)`, `I_j` the maturities with exactly `j` meetings at or before them, the step volatility
`s_j` on `I_j` (bounded Borel), the block volatility `b e^{−a(T−u)}`, drivers `k₁`, `k₂` of the
cited calculus (AX-03) with `W^S = B^{k₁}` and `W^B = ρ B^{k₁} + √(1 − ρ²) B^{k₂}`.
`curve033` is the HJM curve `f(t, T)`: `f(0, T)`, plus the time integral of the AX-01 drift
(33.1) `alpha033 = σ^S S^S + σ^B S^B + ρ (σ^S S^B + σ^B S^S)`, plus the two driver integrals of
`σ_1 = σ^S + ρ σ^B` and `σ_2 = √(1 − ρ²) σ^B`, each taken maturity by maturity.

The families. `SPlus033` is `S⁺`: functions affine on each `I_j ∩ [0, H]`. `Block033 a E` says
that `E` is a block: a finite-dimensional space of real-analytic functions on `ℝ`, invariant
under the forward shifts `g ↦ g(· + h)`, `h ≥ 0`, and containing `e^{−ax}` and `e^{−2ax}`.
`Fam033 Tm H E t h` says that `h` is in `𝓕_t(E)`: `h = p + g(· − t)` on `[t, H]` with `p ∈ S⁺`
and `g ∈ E`.

Consistency is read in the version form of Red's re-check of Claim 033 (item 3), which PM has
asked Math to adopt: `HasVersion033 … t` says there is a random element `g_t` of `𝓕_t(E)` (every
evaluation `ω ↦ g_t(ω)(T)` measurable) with `g_t(T) = f(t, T)` almost surely for every
`T ∈ [t, H]`; `Consistent033` says `f(0, ·) ∈ 𝓕(E)` and this holds at every `t ≤ H`. The literal
reading ("`f(t, ·)|_{[t,H]} ∈ 𝓕_t(E)` for every `t`, almost surely") is not used: the curve's
values at different maturities are separate integrals, each fixed only up to its own null set.

`jump033 s Tm τ` is the jump `Δ = s_{j} − s_{j−1}` of the step volatility at the meeting `τ`,
where `τ` begins `I_j`.

* `necessityStatement` is (b): if the pair is consistent for some block `E`, then
  `ρ Δ = 0` almost everywhere on `[0, τ)`, for every meeting `τ`.
* `noThirdWayStatement` is (d): let `f(0, ·) ∈ 𝓕(E)` for a block `E`, and let `ρ Δ` not vanish
  almost everywhere on `[0, τ)` for a meeting `τ`. Then the pair is not consistent. More
  precisely, there is a nonempty open set of times `t < τ` at which, almost surely, no element of
  `𝓕_t(E)` agrees with `f(t, ·)` at every rational maturity in `[t, H]`, and `f(t, ·)` has no
  version in `𝓕_t(E)`.

Both need only countably many maturities, as Red's remarks on (b) and (d) say: the members of
`𝓕_t(E)` and the version of the random part (`SpliceCrossTermCurve.randomStatement`) are
continuous on each maturity interval, so agreement at rational maturities suffices.
-/

open MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceCrossTermConsistency
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift

/-- The AX-01 drift (33.1) with the independent drivers written out. -/
noncomputable def alpha033 (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (u T : ℝ) : ℝ :=
  sigS033 s Tm u T * SS033 s Tm u T +
    b * Real.exp (-a * (T - u)) * (b * (1 - Real.exp (-a * (T - u))) / a) +
    cross033 a b ρ s Tm u T

/-- The HJM curve `f(t, T)`, maturity by maturity. -/
noncomputable def curve033 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  f0 T + (∫ u in (0:ℝ)..t, alpha033 a b ρ s Tm u T) +
    S.I k₁ (fun u _ => sigS033 s Tm u T + ρ * (b * Real.exp (-a * (T - u)))) t ω +
    S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * (b * Real.exp (-a * (T - u)))) t ω

/-- The step-plus-ramp family `S⁺`: affine on each `I_j ∩ [0, H]`. -/
def SPlus033 (Tm : Finset ℝ) (H : ℝ) (p : ℝ → ℝ) : Prop :=
  ∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Icc 0 H, idx033 Tm T = j → p T = k₀ + k₁ * T

/-- A block: finite-dimensional, real-analytic, forward-shift invariant, with `e^{−ax}`,
`e^{−2ax}`. -/
structure Block033 (a : ℝ) (E : Submodule ℝ (ℝ → ℝ)) : Prop where
  finiteDimensional : FiniteDimensional ℝ E
  analytic : ∀ g ∈ E, AnalyticOnNhd ℝ g univ
  shift : ∀ g ∈ E, ∀ h : ℝ, 0 ≤ h → (fun x => g (x + h)) ∈ E
  exp_one : (fun x => Real.exp (-a * x)) ∈ E
  exp_two : (fun x => Real.exp (-(2 * a) * x)) ∈ E

/-- `h ∈ 𝓕_t(E)`: `h = p + g(· − t)` on `[t, H]`, `p ∈ S⁺`, `g ∈ E`. -/
def Fam033 (Tm : Finset ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ)) (t : ℝ) (h : ℝ → ℝ) : Prop :=
  ∃ p : ℝ → ℝ, SPlus033 Tm H p ∧ ∃ g ∈ E, ∀ T ∈ Icc t H, h T = p T + g (T - t)

/-- `f(t, ·)` has a version in `𝓕_t(E)` (Red's item 3). -/
def HasVersion033 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (H : ℝ) (E : Submodule ℝ (ℝ → ℝ))
    (t : ℝ≥0) : Prop :=
  ∃ g : Ω → ℝ → ℝ, (∀ ω, Fam033 Tm H E t (g ω)) ∧ (∀ T, Measurable fun ω => g ω T) ∧
    ∀ T ∈ Icc (t : ℝ) H, ∀ᵐ ω ∂S.μ, g ω T = curve033 S k₁ k₂ f0 a b ρ s Tm t T ω

/-- The pair (curve, `𝓕(E)`) is consistent, in the version form. -/
def Consistent033 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (H : ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) : Prop :=
  Fam033 Tm H E 0 f0 ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H → HasVersion033 S k₁ k₂ f0 a b ρ s Tm H E t

/-- The jump `s_j − s_{j−1}` of the step volatility at the meeting `τ` beginning `I_j`. -/
noncomputable def jump033 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (τ u : ℝ) : ℝ :=
  s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u

def necessityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ H : ℝ), a ≠ 0 → b ≠ 0 →
  (∀ τ ∈ Tm, 0 < τ ∧ τ < H) → ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block033 a E →
  Consistent033 S k₁ k₂ f0 a b ρ s Tm H E →
  ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0

def noThirdWayStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (a b ρ H : ℝ), a ≠ 0 → b ≠ 0 →
  (∀ τ ∈ Tm, 0 < τ ∧ τ < H) → ∀ (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)), Block033 a E →
  Fam033 Tm H E 0 f0 →
  ∀ τ ∈ Tm, ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ → ρ * jump033 s Tm τ u = 0) →
  ¬ Consistent033 S k₁ k₂ f0 a b ρ s Tm H E ∧
  ∃ O : Set ℝ, IsOpen O ∧ O.Nonempty ∧ O ⊆ Ioo 0 τ ∧ ∀ t : ℝ≥0, (t : ℝ) ∈ O →
    (∀ᵐ ω ∂S.μ, ¬ ∃ h : ℝ → ℝ, Fam033 Tm H E t h ∧
      ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H → h q = curve033 S k₁ k₂ f0 a b ρ s Tm t q ω) ∧
    ¬ HasVersion033 S k₁ k₂ f0 a b ρ s Tm H E t

def statement : Prop := necessityStatement ∧ noThirdWayStatement

end Standalone.SpliceCrossTermConsistency

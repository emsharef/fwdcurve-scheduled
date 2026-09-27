import Standalone.RecurrentLoadingXi

/-! # Claims 030 and 031 (b): the equation of `Ξ` between meetings

With a bounded predictable scale `h` (Claim 030: `h ≡ 1`) and `t₀ ≥ 0`, `xiCont x` is
`e^{Â(x−t₀)} I(gh)(x)`, with `gh` the fixed integrand `ghInt` of `RecurrentLoadingXi`. By that
target, on a meeting-free `(t₀, t₁)` it is, at each `x ∈ [t₀, t₁)` almost surely, the state
`Ξ_x`, and it is the version of `Ξ` continuous between meetings.

`continuityStatement`: almost surely every coordinate of `xiCont` has continuous paths.
`equationStatement`: almost surely, simultaneously for all `t₀ ≤ y ≤ x`,
`Ξ_x = Ξ_y + ∫_y^x Â Ξ_s ds + β (I(h)(x) − I(h)(y))` coordinate by coordinate, which is
`dΞ = Â Ξ dt + β h dW` of (30.3) (Claim 031: (31.2)) in integral form. No meeting condition is
needed for `xiCont`; it enters only through the identification with `Ξ`. The proof applies
Itô's formula, AX-05, to `e^{Â(x−t₀)}` times the integrals, one coordinate at a time.
-/

open MeasureTheory Matrix
open scoped NNReal
namespace Standalone.RecurrentLoadingXiEquation
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingStateP
open Standalone.RecurrentLoadingXi

/-- The continuous version `e^{Â(x−t₀)} I(gh)(x)` of `Ξ` after `t₀`. -/
noncomputable def xiCont {Ω : Type*} {p r : ℕ} (I : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ≥0 → Ω → ℝ) (t₀ : ℝ) (x : ℝ≥0) (ω : Ω) :
    Fin p × Fin r → ℝ :=
  Ehat030 A ((x : ℝ) - t₀) *ᵥ fun e => I (ghInt Tm v M b A h t₀ e) x ω

def continuityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ), IsStronglyPredictable S.ℱ h →
  ∀ C : ℝ, (∀ s ω, |h s ω| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ),
  ∀ᵐ ω ∂S.μ, ∀ a, Continuous fun x => xiCont (S.I k) Tm v M b A h t₀ x ω a

def equationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ), IsStronglyPredictable S.ℱ h →
  ∀ C : ℝ, (∀ s ω, |h s ω| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ), 0 ≤ t₀ →
  ∀ᵐ ω ∂S.μ, ∀ y x : ℝ≥0, t₀ ≤ y → y ≤ x → ∀ a,
    xiCont (S.I k) Tm v M b A h t₀ x ω a = xiCont (S.I k) Tm v M b A h t₀ y ω a +
      (∫ s in (y : ℝ)..x, (Ahat030 A *ᵥ xiCont (S.I k) Tm v M b A h t₀ (Real.toNNReal s) ω) a) +
      beta030 v b a * (S.I k h x ω - S.I k h y ω)

def statement : Prop := continuityStatement ∧ equationStatement

end Standalone.RecurrentLoadingXiEquation

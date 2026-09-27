import Standalone.RecurrentLoadingDiffusion
import Standalone.RecurrentLoadingRestartP

/-! # Claims 030 and 031 (b): the stochastic state `Ξ`

With a bounded predictable scale `h` (Claim 030: `h ≡ 1`), `Ξ_x` is the vector of
driver integrals up to `x` of `h_s w(s,x)` stopped at `x` (`xiInt`). Fix `t₀ ≥ 0`.
`gt030 s` is `w(s,t₀)` for `s ≤ t₀` and `e^{Â(t₀−s)} β` after it; it does not
depend on `x`, and `ghInt e = h_s gt030(s)_e` is a fixed integrand.

`representationStatement`: if no meeting lies in `(t₀, t₁)`, then for every
`x ∈ [t₀, t₁)`, almost surely, `Ξ_x = e^{Â(x−t₀)} I(gh)(x)`. The right side has
continuous paths (AX-03), so it is the version of `Ξ` continuous between
meetings. `restartStatement`: at a meeting `T` with no meeting in `(t₀, T)`,
almost surely, `Ξ_T = M̂ e^{Â(T−t₀)} I(gh)(T)`, and `e^{Â(x−t₀)} I(gh)(x)` tends
to `e^{Â(T−t₀)} I(gh)(T)` as `x ↑ T`; this is `Ξ_T = M̂ Ξ_{T−}`, the `Ξ` component
of the restart map. The equation of `Ξ` between meetings is not in this target.
-/

open MeasureTheory Matrix Filter Topology
open scoped NNReal
namespace Standalone.RecurrentLoadingXi
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.RecurrentLoadingAlgebra
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingRestartP
open Standalone.RecurrentLoadingDiffusion

/-- `w(s,t₀)` before `t₀`, `e^{Â(t₀−s)} β` after it. -/
noncomputable def gt030 {p r : ℕ} (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (s : ℝ) : Fin p × Fin r → ℝ :=
  if s ≤ t₀ then w030 Tm v M b A s t₀ else Ehat030 (p := p) A (t₀ - s) *ᵥ beta030 v b

/-- The fixed integrand `h_s gt030(s)_e`. -/
noncomputable def ghInt {Ω : Type*} {p r : ℕ} (Tm : Finset ℝ) (v : Fin p → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (h : ℝ≥0 → Ω → ℝ) (t₀ : ℝ) (e : Fin p × Fin r) : ℝ≥0 → Ω → ℝ :=
  fun s ω => h s ω * gt030 Tm v M b A t₀ s e

def representationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ), IsStronglyPredictable S.ℱ h →
  ∀ C : ℝ, (∀ s ω, |h s ω| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ t₁ : ℝ), 0 ≤ t₀ →
  (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < t₁)) →
  (∀ e, U4 S.ℱ S.μ (ghInt Tm v M b A h t₀ e)) ∧
  ∀ x : ℝ≥0, t₀ ≤ x → (x : ℝ) < t₁ → ∀ a, ∀ᵐ ω ∂S.μ,
    S.I k (xiInt Tm v M b A h x a) x ω =
      (Ehat030 A ((x : ℝ) - t₀) *ᵥ fun e => S.I k (ghInt Tm v M b A h t₀ e) x ω) a

def restartStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m) (h : ℝ≥0 → Ω → ℝ), IsStronglyPredictable S.ℱ h →
  ∀ C : ℝ, (∀ s ω, |h s ω| ≤ C) →
  ∀ (p r : ℕ) (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ : ℝ) (T : ℝ≥0), 0 ≤ t₀ → t₀ < T →
  (T : ℝ) ∈ Tm → (∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ < T)) →
  (∀ a, ∀ᵐ ω ∂S.μ, S.I k (xiInt Tm v M b A h T a) T ω =
      (Mhat030 M *ᵥ (Ehat030 A ((T : ℝ) - t₀) *ᵥ
        fun e => S.I k (ghInt Tm v M b A h t₀ e) T ω)) a) ∧
  ∀ᵐ ω ∂S.μ, ∀ a, Tendsto (fun x : ℝ≥0 => (Ehat030 A ((x : ℝ) - t₀) *ᵥ
      fun e => S.I k (ghInt Tm v M b A h t₀ e) x ω) a) (𝓝[<] T)
    (𝓝 ((Ehat030 A ((T : ℝ) - t₀) *ᵥ fun e => S.I k (ghInt Tm v M b A h t₀ e) T ω) a))

def statement : Prop := representationStatement ∧ restartStatement

end Standalone.RecurrentLoadingXi

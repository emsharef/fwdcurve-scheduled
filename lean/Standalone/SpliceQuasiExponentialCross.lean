import Standalone.SpliceCrossTermAlpha
import Standalone.SpliceQuasiExponentialKey

/-! # Claim 035 (a): the cross term and its jump

The setting is Claim 033's (`SpliceCrossTermDrift`, `SpliceCrossTermAlpha`) with the block factor
`σ^B(u, T) = λ(T − u)`, `λ(x) = c e^{Ax} b` (`lam035`), and `Λ(y) = c A^{−1}(e^{Ay} − I) b`
(`Lam035`), with `A` invertible. By (33.1) the cross part of the drift is
`ρ [σ^S(u, T) Λ(T − u) + λ(T − u) S^S(u, T)]` (`cross035`).

On `I_j`, with `κ_j` read off at an anchor `T₀ ∈ I_j` (`SpliceCrossTermAlpha.kappa033`) and
`g(u) = e^{−Au} b`:
* `yCoef035` is `y_j(t) = ρ ∫_0^t (s_j(u) A^{−1} + κ_j(u)) g(u) du`,
* `zCoef035` is `z_j(t) = ρ ∫_0^t s_j(u) g(u) du`.

* `explicitStatement`: for `T ∈ I_j`, `T ≥ t`,
  `X_{t,j}(T) = ∫_0^t ρ[σ^S Λ + λ S^S](u, T) du = −ρ c A^{−1} b ∫_0^t s_j + c e^{AT}(y_j(t) + T z_j(t))`.
  The right side is an entire function of `T`: this is the extension of `X_{t,j}`.
* `jumpStatement` is (35.2): at a meeting `τ` ending `I_m` and beginning `I_{m+1}`, with
  `Δ = s_{m+1} − s_m` and `v_m(t) = ∫_0^t Δ(u) g(u) du` (`SpliceQuasiExponentialKey.vvec`),
  `y_{m+1}(t) − y_m(t) = ρ (A^{−1} − τ I) v_m(t)` and `z_{m+1}(t) − z_m(t) = ρ v_m(t)`, so the
  jump of the extensions is `ρ c e^{AT}(A^{−1} + (T − τ) I) v_m(t) − ρ c A^{−1} b ∫_0^t Δ`.
* `uncorrelatedStatement` is the deterministic core of (c)(i): if `ρ = 0`, or if for almost
  every `u ≤ t` the step volatility at `u` is the same on every maturity interval after `t`, the
  cross term is one function `c₀ + c e^{AT}(y + T z)` for all `T ≥ t`.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceQuasiExponentialKey

variable {r : ℕ}

/-- `λ(x) = c e^{Ax} b`. -/
noncomputable def lam035 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (x : ℝ) : ℝ :=
  c ⬝ᵥ (exp (x • A) *ᵥ b)

/-- `Λ(y) = c A^{−1}(e^{Ay} − I) b`. -/
noncomputable def Lam035 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (y : ℝ) : ℝ :=
  c ⬝ᵥ ((A⁻¹ * (exp (y • A) - 1)) *ᵥ b)

/-- The cross part `ρ [σ^S(u, T) Λ(T − u) + λ(T − u) S^S(u, T)]` of the drift. -/
noncomputable def cross035 (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u T : ℝ) : ℝ :=
  ρ * (sigS033 s Tm u T * Lam035 c A b (T - u) + lam035 c A b (T - u) * SS033 s Tm u T)

/-- `y_j(t) = ρ ∫_0^t (s_j(u) A^{−1} + κ_j(u)) e^{−Au} b du`, anchor `T₀`. -/
noncomputable def yCoef035 (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (j : ℕ) (T0 t : ℝ) : Fin r → ℝ :=
  fun i => ∫ u in (0:ℝ)..t, ρ * (s j u * (A⁻¹ *ᵥ (exp (u • (-A)) *ᵥ b)) i +
    kappa033 s Tm j T0 u * (exp (u • (-A)) *ᵥ b) i)

/-- `z_j(t) = ρ ∫_0^t s_j(u) e^{−Au} b du`. -/
noncomputable def zCoef035 (ρ : ℝ) (s : ℕ → ℝ → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (b : Fin r → ℝ) (j : ℕ) (t : ℝ) : Fin r → ℝ :=
  fun i => ∫ u in (0:ℝ)..t, ρ * (s j u * (exp (u • (-A)) *ᵥ b) i)

def explicitStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ) (ρ : ℝ) (j : ℕ) (t T0 : ℝ), 0 ≤ t → idx033 Tm T0 = j → t ≤ T0 →
  ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T =
      -(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * (∫ u in (0:ℝ)..t, s j u) +
        c ⬝ᵥ (exp (T • A) *ᵥ (yCoef035 ρ s Tm A b j T0 t + T • zCoef035 ρ s A b j t))

def jumpStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ)
  (b : Fin r → ℝ) (ρ : ℝ) (m : ℕ) (τ τl τr T0 T1 t : ℝ),
  τl < τ → τ < τr → (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) →
  T0 ∈ Ioo τl τ → T1 ∈ Ico τ τr → 0 ≤ t → t ≤ T0 →
  yCoef035 ρ s Tm A b (m + 1) T1 t - yCoef035 ρ s Tm A b m T0 t =
      ρ • ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        vvec A b (fun u => s (m + 1) u - s m u) t) ∧
    zCoef035 ρ s A b (m + 1) t - zCoef035 ρ s A b m t =
      ρ • vvec A b (fun u => s (m + 1) u - s m u) t

def uncorrelatedStatement : Prop := ∀ (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ) (ρ t : ℝ), 0 ≤ t →
  (ρ = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 t → ∀ v, t ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u) →
  ∃ (c₀ : ℝ) (y z : Fin r → ℝ), ∀ T : ℝ, t ≤ T →
    ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T = c₀ + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z))

def statement : Prop := explicitStatement ∧ jumpStatement ∧ uncorrelatedStatement

end Standalone.SpliceQuasiExponentialCross

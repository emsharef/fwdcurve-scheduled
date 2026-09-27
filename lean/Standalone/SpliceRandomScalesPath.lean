import Standalone.SpliceQuasiExponentialCross

/-! # Claim 039 (a) and (b), path by path

Claim 039 keeps Claim 035's setting but makes the scales predictable bounded processes:
`σ^S(u, T) = s_m(u)` on `I_m`, `σ^B(u, T) = ψ_u λ(T − u)` and `dW^B = ρ_u dB^1 + √(1 − ρ_u²) dB^2`
(39.1). This file fixes one path `ω`: `s j u`, `ρ u` and `ψ u` are the values `s_j(u, ω)`, `ρ_u(ω)`,
`ψ_u(ω)`, measurable and bounded in `u`, and `wS ρ ψ s` is the weighted step scale
`ρ_u ψ_u s_j(u)`.

* `crossStatement`: the cross part of the drift, `ρ_u [σ^S S^B + σ^B S^S](u, T)` with
  `S^B = ψ_u Λ(T − u)` (`cross039`), is Claim 035's cross part with `ρ = 1` and the step scales
  replaced by `ρ_u ψ_u s_j(u)`.
* `explicitStatement`: so, as in Claim 035(a), for `T ∈ I_j`, `T ≥ t`, the cross term is
  `−c A^{−1} b ∫_0^t ρ ψ s_j + c e^{AT}(y_j(t) + T z_j(t))`, entire in `T`, with Claim 035's `y_j`,
  `z_j` for the weighted scales.
* `jumpStatement` is (39.2): across a meeting `τ`, `y_{m+1} − y_m = (A^{−1} − τ I) v_m(t)` and
  `z_{m+1} − z_m = v_m(t)`, with `v_m(t) = ∫_0^t ρ_u ψ_u Δ_m(u) e^{−Au} b du`.
* `keyStatement` is (b)'s last step on the path: if `v_m(t)` lies in Claim 035's subspace `K` for
  every `t ∈ [0, L)`, then `ρ_u ψ_u Δ_m(u) = 0` for almost every `u ∈ [0, L)`. Here `A` is
  invertible, `(A, b)` controllable and `c ≠ 0`.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceRandomScalesPath
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceQuasiExponentialKey Standalone.SpliceQuasiExponentialCross

variable {r : ℕ}

/-- The weighted step scales `ρ_u ψ_u s_j(u)`. -/
def wS (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun j u => ρ u * ψ u * s j u

/-- The cross part `ρ_u [σ^S(u, T) ψ_u Λ(T − u) + ψ_u λ(T − u) S^S(u, T)]` of the drift. -/
noncomputable def cross039 (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u T : ℝ) : ℝ :=
  ρ u * (sigS033 s Tm u T * (ψ u * Lam035 c A b (T - u)) +
    ψ u * lam035 c A b (T - u) * SS033 s Tm u T)

/-- The scales on the path: measurable and bounded. -/
def PathScales (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) : Prop :=
  (∀ i, Measurable (s i)) ∧ Measurable ρ ∧ Measurable ψ ∧
    ∃ C : ℝ, (∀ i u, |s i u| ≤ C) ∧ (∀ u, |ρ u| ≤ C) ∧ ∀ u, |ψ u| ≤ C

def crossStatement : Prop := ∀ (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (r : ℕ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u T : ℝ),
  cross039 ρ ψ s Tm c A b u T = cross035 1 (wS ρ ψ s) Tm c A b u T

def explicitStatement : Prop := ∀ (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ), PathScales ρ ψ s →
  ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ) (j : ℕ) (t T0 : ℝ), 0 ≤ t → idx033 Tm T0 = j → t ≤ T0 →
  ∀ T : ℝ, idx033 Tm T = j → t ≤ T →
    ∫ u in (0:ℝ)..t, cross039 ρ ψ s Tm c A b u T =
      -(c ⬝ᵥ (A⁻¹ *ᵥ b)) * (∫ u in (0:ℝ)..t, ρ u * ψ u * s j u) +
        c ⬝ᵥ (exp (T • A) *ᵥ (yCoef035 1 (wS ρ ψ s) Tm A b j T0 t +
          T • zCoef035 1 (wS ρ ψ s) A b j t))

def jumpStatement : Prop := ∀ (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ), PathScales ρ ψ s →
  ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
  (m : ℕ) (τ τl τr T0 T1 t : ℝ),
  τl < τ → τ < τr → (∀ v ∈ Ioo τl τ, idx033 Tm v = m) → (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) →
  T0 ∈ Ioo τl τ → T1 ∈ Ico τ τr → 0 ≤ t → t ≤ T0 →
  yCoef035 1 (wS ρ ψ s) Tm A b (m + 1) T1 t - yCoef035 1 (wS ρ ψ s) Tm A b m T0 t =
      (A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        vvec A b (fun u => ρ u * ψ u * (s (m + 1) u - s m u)) t ∧
    zCoef035 1 (wS ρ ψ s) A b (m + 1) t - zCoef035 1 (wS ρ ψ s) A b m t =
      vvec A b (fun u => ρ u * ψ u * (s (m + 1) u - s m u)) t

def keyStatement : Prop := ∀ (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ), PathScales ρ ψ s →
  ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ), c ≠ 0 → (∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0) →
  ∀ (m : ℕ) (L Tm d₁ d₂ : ℝ), d₁ < d₂ →
  (∀ t ∈ Ico 0 L, ∀ T ∈ Ioo d₁ d₂, c ⬝ᵥ (exp (T • A) *ᵥ
    ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ
      vvec A b (fun u => ρ u * ψ u * (s (m + 1) u - s m u)) t)) = 0) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 L → ρ u * ψ u * (s (m + 1) u - s m u) = 0

def statement : Prop := crossStatement ∧ explicitStatement ∧ jumpStatement ∧ keyStatement

end Standalone.SpliceRandomScalesPath

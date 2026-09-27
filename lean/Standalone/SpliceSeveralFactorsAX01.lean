import Standalone.SpliceSeveralFactorsCore
import Standalone.SpliceStateBlockAX01

/-! # Claim 041 (a) and (d) from AX-01, on one path

Claim 040's setting on one path, with `L` step factors. Factor `ℓ` has scales `s_{ℓ,j}(u)` on `I_j`
and row `H^S_ℓ(u) ∈ ℝ^{1×k}`, so `σ^S(u, T) = ∑_ℓ s_{ℓ,j}(u) H^S_ℓ(u)` on `I_j`. Driver by driver,
`σ^S_l(u, T) = S_{l,j}(u)` with the combined scales `S_{l,j} = ∑_ℓ s_{ℓ,j} H^S_{ℓ,l}` (`Scomb`). The
block is `F(x, z) = C e^{𝒜x} z` (41.2), here any `c`, `A` with `A` invertible. `sigma041` is
`σ = σ^S + σ^B`, with `σ^B = C e^{𝒜(T−u)} H^Z`. The drifts are Claim 040's (`driftS`, `driftB`).
`AX01Path041` is AX-01 differentiated in `T`, for almost every `u ∈ [0, H]` and every `T ∈ [u, H]`.

`W041` is `H^Z(u) G_m(u)^T` (41.3), with `G_m = ∑_ℓ Δ_{ℓ,m} H^S_ℓ` (41.1) at the meeting `τ`.

* `necessityStatement` is (a): if `(𝒜, C)` is observable, `AX01Path041` forces `H^Z G_m^T = 0` for
  almost every `u ∈ [0, τ)`, at every meeting `τ < H`.
* `noThirdWayStatement` is (d): if (41.3) fails on a set of positive measure before some meeting,
  no drifts satisfy AX-01 on the path.

The statements are pathwise. A consistent process satisfies `AX01Path041` on almost every path,
so each holds almost surely.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceSeveralFactorsAX01
open Standalone.SpliceCrossTermDrift Standalone.SpliceStateBlockAX01

variable {r k L : ℕ}

/-- The combined step scales `S_{l,j}(u) = ∑_ℓ s_{ℓ,j}(u) H^S_{ℓ,l}(u)` of driver `l`. -/
def Scomb (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ) (l : Fin k) : ℕ → ℝ → ℝ :=
  fun j u => ∑ ℓ, s ℓ j u * HS ℓ u l

/-- `σ(u, T) = ∑_ℓ s_{ℓ,j}(u) H^S_ℓ(u) + C e^{𝒜(T−u)} H^Z(u) ∈ ℝ^k`. -/
noncomputable def sigma041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (u T : ℝ) : Fin k → ℝ :=
  fun l => sigS033 (Scomb s HS l) Tm u T + c ⬝ᵥ (exp ((T - u) • A) *ᵥ fun i => HZ u i l)

/-- AX-01, differentiated in `T`, on the path. -/
def AX01Path041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (H : ℝ) : Prop :=
  ∀ᵐ u ∂volume, u ∈ Icc 0 H → ∀ T ∈ Icc u H,
    driftS dL dC Tm u T + driftB c A bZ z u T =
      sigma041 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma041 s HS HZ Tm c A u v l

/-- `H^Z(u) G_m(u)^T`, with `G_m = ∑_ℓ Δ_{ℓ,m} H^S_ℓ` at the meeting `τ`. -/
noncomputable def W041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (τ u : ℝ) : Fin r → ℝ :=
  fun i => ∑ l, HZ u i l *
    ∑ ℓ, (s ℓ (idx033 Tm τ) u - s ℓ (idx033 Tm τ - 1) u) * HS ℓ u l

/-- The path data: measurable bounded scales, loadings and state, integrable drifts. -/
def PathData041 (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (H : ℝ) : Prop :=
  (∀ ℓ j, Measurable (s ℓ j)) ∧ (∀ ℓ l, Measurable fun u => HS ℓ u l) ∧
  (∀ i l, Measurable fun u => HZ u i l) ∧ (∀ i, Measurable fun u => z u i) ∧
  (∃ C : ℝ, (∀ ℓ j u, |s ℓ j u| ≤ C) ∧ (∀ ℓ u l, |HS ℓ u l| ≤ C) ∧
    (∀ u i l, |HZ u i l| ≤ C) ∧ ∀ u i, |z u i| ≤ C) ∧
  (∀ j, IntervalIntegrable (dL j) volume 0 H) ∧ (∀ j, IntervalIntegrable (dC j) volume 0 H) ∧
  ∀ i, IntervalIntegrable (fun u => bZ u i) volume 0 H

def necessityStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H : ℝ),
  PathData041 s HS HZ dL dC bZ z H → AX01Path041 s HS HZ dL dC bZ z Tm c A H →
  ∀ τ ∈ Tm, τ < H → ∀ᵐ u ∂volume, u ∈ Ico 0 τ → W041 s HS HZ Tm τ u = 0

def noThirdWayStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ) (H τ : ℝ), τ ∈ Tm → τ < H →
  ¬ (∀ᵐ u ∂volume, u ∈ Ico 0 τ → W041 s HS HZ Tm τ u = 0) →
  ∀ dL dC : ℕ → ℝ → ℝ, PathData041 s HS HZ dL dC bZ z H →
    ¬ AX01Path041 s HS HZ dL dC bZ z Tm c A H

def statement : Prop := necessityStatement ∧ noThirdWayStatement

end Standalone.SpliceSeveralFactorsAX01

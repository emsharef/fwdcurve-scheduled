import Standalone.SpliceQuasiExponentialCross

/-! # Claim 040 (a): the cross term and its jump, on one path

On one path the front end's step scales are `s_j(u)` (`σ^S(u, T) = s_j(u) H^S(u)` on `I_j`) and the
covariation density (40.3) is `w(u) = H^Z(u) H^S(u)^T ∈ ℝ^r`. Both are measurable and bounded in `u`.
The cross term of AX-01's right side is
`s_j(u) c A^{−1}(e^{A(T−u)} − I) w(u) + c e^{A(T−u)} w(u) S^S(u, T)` (`cross040`). This is Claim 035's
cross integrand with the fixed vector `ρ b` replaced by `w(u)`.

* `explicitStatement`: on each maturity interval the integrated cross term is a constant plus
  `c e^{AT}(y_j + T z_j)`, entire in `T`. Across a meeting `τ` between `I_m` and `I_{m+1}`,
  `y_{m+1} − y_m = (A^{−1} − τ I) v_m(t)` and `z_{m+1} − z_m = v_m(t)`, with
  `v_m(t) = ∫_0^t Δ_m(u) e^{−Au} w(u) du` (`vvec040`).
* `coreStatement` is (a)'s argument on the path. Suppose that for every `t ∈ [0, τ)` the
  integrated cross term on `(t, H)` equals a function affine on each maturity interval plus a
  real-analytic function. By the Proof, AX-01 gives exactly this, since `D^S` and `σ^S ∫σ^S` are
  affine and `D^B` and `σ^B·∫σ^B` are analytic. Then `Δ_m(u) w(u) = 0` for almost every
  `u ∈ [0, τ)`. Here `A` is invertible and `(A, c)` observable, and Lemma 040-A
  (`SpliceStateBlockObservability`) replaces Claim 035's controllability.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceStateBlockCross
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross

variable {r : ℕ}

/-- The cross term `s_j(u) c A^{−1}(e^{A(T−u)} − I) w(u) + c e^{A(T−u)} w(u) S^S(u, T)`. -/
noncomputable def cross040 (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (w : ℝ → Fin r → ℝ) (u T : ℝ) : ℝ :=
  sigS033 s Tm u T * c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ w u) +
    c ⬝ᵥ (exp ((T - u) • A) *ᵥ w u) * SS033 s Tm u T

/-- `v(t) = ∫_0^t Δ(u) e^{−Au} w(u) du`, componentwise. -/
noncomputable def vvec040 (A : Matrix (Fin r) (Fin r) ℝ) (Δ : ℝ → ℝ) (w : ℝ → Fin r → ℝ)
    (t : ℝ) : Fin r → ℝ :=
  fun i => ∫ u in (0:ℝ)..t, Δ u * (exp (u • (-A)) *ᵥ w u) i

/-- Measurable, bounded step scales and covariation density on the path. -/
def PathData (s : ℕ → ℝ → ℝ) (w : ℝ → Fin r → ℝ) : Prop :=
  (∀ j, Measurable (s j)) ∧ (∀ i, Measurable fun u => w u i) ∧
    ∃ C : ℝ, (∀ j u, |s j u| ≤ C) ∧ ∀ u i, |w u i| ≤ C

def explicitStatement : Prop := ∀ (r : ℕ) (s : ℕ → ℝ → ℝ) (w : ℝ → Fin r → ℝ), PathData s w →
  ∀ (Tm : Finset ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det → ∀ (c : Fin r → ℝ) (t : ℝ),
  0 ≤ t → ∀ (m : ℕ) (τ τl τr : ℝ), τl < τ → τ < τr → (∀ v ∈ Ioo τl τ, idx033 Tm v = m) →
  (∀ v ∈ Ico τ τr, idx033 Tm v = m + 1) → t < τ →
  ∃ (k₀ k₁ : ℝ) (y₀ z₀ y₁ z₁ : Fin r → ℝ),
    (∀ T ∈ Ioo τl τ, t ≤ T →
      ∫ u in (0:ℝ)..t, cross040 s Tm c A w u T = k₀ + c ⬝ᵥ (exp (T • A) *ᵥ (y₀ + T • z₀))) ∧
    (∀ T ∈ Ico τ τr,
      ∫ u in (0:ℝ)..t, cross040 s Tm c A w u T = k₁ + c ⬝ᵥ (exp (T • A) *ᵥ (y₁ + T • z₁))) ∧
    y₁ - y₀ = (A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
      vvec040 A (fun u => s (m + 1) u - s m u) w t ∧
    z₁ - z₀ = vvec040 A (fun u => s (m + 1) u - s m u) w t

def coreStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : ℕ → ℝ → ℝ) (w : ℝ → Fin r → ℝ), PathData s w →
  ∀ (Tm : Finset ℝ) (τ H : ℝ), τ ∈ Tm → τ < H →
  (∀ t ∈ Ico 0 τ, ∃ (p G : ℝ → ℝ), AnalyticOnNhd ℝ G univ ∧
    (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross040 s Tm c A w u T = p T + G T) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    (s (idx033 Tm τ) u - s (idx033 Tm τ - 1) u) • w u = 0

def statement : Prop := explicitStatement ∧ coreStatement

end Standalone.SpliceStateBlockCross

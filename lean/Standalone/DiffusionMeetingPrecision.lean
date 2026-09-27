import Standalone.BondOptionPriceIntervals
import Standalone.BondOptionMeetingVariances

/-! # Claim 046 (e): precision with a diffusion, `P = 1`

`atm P0 m δ Q = P(0, S) m (2Φ(δ√Q/2) − 1)` is the at-the-money price (46.5) at `K = m`, as a function
of the accumulated variance `Q = q/δ² = σ_Σ²`. `eta` is (46.9).

* `sensitivityStatement` is (46.9): `atm` has a positive derivative `d` in `Q`, and a perturbation
  `ε` of the premium `C/δ`, which is `δε` on `C`, moves `Q` to first order by
  `δε/d = 2ε σ_Σ / (P(0, S) m φ(δσ_Σ/2))`.
* `estimatorStatement` is (46.10). The gaps are `ℓ = 1, …, L`, of lengths `λ_ℓ > 0`, and
  `Q(S_0) = Q(0) = 0` is exact. The estimator is `û = Q(S_1)/λ_1` and
  `v̂_ℓ = Q(S_ℓ) − Q(S_{ℓ−1}) − λ_ℓ û` for the meeting in gap `ℓ ≥ 2`. It is exact in the model
  (`Q(S_ℓ) − Q(S_{ℓ−1}) = w_ℓ + λ_ℓ u` with `w_1 = 0`). With each `Q(S_k)` known to within
  `η_k` (`η_0 = 0`), `|Δv̂_ℓ| ≤ η_ℓ + η_{ℓ−1} + (λ_ℓ/λ_1) η_1`, with equality for suitable signs.
-/

namespace Standalone.DiffusionMeetingPrecision
open Standalone.BondOptionMeetingVariances Standalone.BondOptionPriceIntervals

/-- The at-the-money price as a function of `Q = σ_Σ²`. -/
noncomputable def atm (P0 m δ Q : ℝ) : ℝ := P0 * m * (2 * Φ (δ * Real.sqrt Q / 2) - 1)

/-- (46.9): `η = 2ε σ_Σ / (P(0, S) m φ(δσ_Σ/2))`, `σ_Σ = √Q`. -/
noncomputable def eta (P0 m δ ε Q : ℝ) : ℝ :=
  2 * ε * Real.sqrt Q / (P0 * m * φ0167 (δ * Real.sqrt Q / 2))

/-- The estimator of (e): `v̂_ℓ = Q(S_ℓ) − Q(S_{ℓ−1}) − λ_ℓ Q(S_1)/λ_1`. -/
noncomputable def vhat (lam Q : ℕ → ℝ) (ℓ : ℕ) : ℝ := Q ℓ - Q (ℓ - 1) - lam ℓ * (Q 1 / lam 1)

def sensitivityStatement : Prop := ∀ P0 m δ ε Q : ℝ, 0 < P0 → 0 < m → 0 < δ → 0 < Q →
  ∃ d : ℝ, HasDerivAt (atm P0 m δ) d Q ∧ 0 < d ∧ δ * ε / d = eta P0 m δ ε Q

def estimatorStatement : Prop := ∀ (lam : ℕ → ℝ), (∀ k, 0 < lam k) →
  (∀ (Q w : ℕ → ℝ) (u : ℝ), Q 0 = 0 → w 1 = 0 →
    (∀ ℓ, 1 ≤ ℓ → Q ℓ - Q (ℓ - 1) = w ℓ + lam ℓ * u) → ∀ ℓ, 2 ≤ ℓ → vhat lam Q ℓ = w ℓ) ∧
  ∀ (η : ℕ → ℝ), η 0 = 0 → (∀ k, 0 ≤ η k) → ∀ ℓ, 2 ≤ ℓ →
    (∀ (Q e : ℕ → ℝ), e 0 = 0 → (∀ k, |e k| ≤ η k) →
      |vhat lam (Q + e) ℓ - vhat lam Q ℓ| ≤ η ℓ + η (ℓ - 1) + lam ℓ / lam 1 * η 1) ∧
    ∃ e : ℕ → ℝ, e 0 = 0 ∧ (∀ k, |e k| ≤ η k) ∧ ∀ Q : ℕ → ℝ,
      |vhat lam (Q + e) ℓ - vhat lam Q ℓ| = η ℓ + η (ℓ - 1) + lam ℓ / lam 1 * η 1

def statement : Prop := sensitivityStatement ∧ estimatorStatement

end Standalone.DiffusionMeetingPrecision

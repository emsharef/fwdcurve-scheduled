import Standalone.UnifiedSpliceAlgebra
import Standalone.UnifiedSpliceNecessity
import Standalone.UnifiedSpliceDiag

/-! # Claim 049 (c) and (d): representation, cancellations and specializations

At one time `u` on one path, in the notation of `UnifiedSpliceAlgebra`.

(c):
* `aggregationStatement`: with `n_S` step factors, `V_m = Σ_ℓ s_{ℓ,m} H^S_ℓ`, the aggregate step is
  `G_m = V_m − V_{m−1} = Σ_ℓ Δ_{ℓ,m} H^S_ℓ`. It is the only way the step factors enter (49.2). In
  the claim's example, two step factors on the same noise with `Δ_{1,m} = −Δ_{2,m}`, `G_m = 0`, so
  (49.2) holds whatever the block's rows are.
* `reductionStatement`, shared exponents: let `(A', c', P)` realize `(A, c)`, so `P A = A' P` and
  `c = c' P`, with `A` and `A'` invertible. Then the residual and the cross part are unchanged when
  `(A, c, H^ζ, b_ζ, ζ)` is replaced by `(A', c', P H^ζ, P b_ζ, P ζ)`. So (a), (b) and (b2) hold for
  the reduced block, with `P H^ζ` in place of `H^ζ`; `reducedNecessityStatement` is (a) in that
  form. Claim 041(c) supplies the minimal realization and is not restated here.

(b), *Orthogonality alone is not sufficient*:
* `orthogonalityStatement`: with `d = 1`, no exponential part, a block uncorrelated with the
  front end (`V = 0`, so (49.2) holds) and `a_{(0,1),(0,1)} = 1 > 0`, `R♯(x) = −x³/2` is not
  affine, so no drift makes the splice consistent.

(d):
* `prop44Statement`, the sharpening of Proposition 44: with no level noise (`H^{0,0} = 0`), a
  diagonalizable `A` and `R♯` affine, `H^ζ V_{j(u)}^⊤ = 0`. The block noise is orthogonal to the
  current front-end noise, not only to the aggregate step.
* `uncorrelatedStatement`: for a block orthogonal to the current front-end noise, `K = 0`, and
  `R♯ = R` up to an affine function (Claim 037(a)'s setting).
* `sharpEntriesStatement`, the carry-over of Proposition 45 to `a♯`: the entries with
  `μ, ν ≥ 1` are unchanged, and the level's row and column shift by `ω̄ = H V` (plus
  `2ω̄_0 + |V|²` at `(0, 0)`). The same holds for the block's covariances `H^ζ H^{0,μ⊤}`.
-/

open Matrix NormedSpace

namespace Standalone.UnifiedSpliceSpecial
open Standalone.UnifiedSpliceAlgebra

def aggregationStatement : Prop := ∀ (k nS : ℕ) (s : Fin nS → ℕ → ℝ) (HS : Fin nS → Fin k → ℝ)
  (m : ℕ),
    (∑ ℓ, s ℓ m • HS ℓ) - ∑ ℓ, s ℓ (m - 1) • HS ℓ = ∑ ℓ, (s ℓ m - s ℓ (m - 1)) • HS ℓ ∧
    ((∑ ℓ, (s ℓ m - s ℓ (m - 1)) • HS ℓ) = 0 → ∀ (r d : ℕ) (Hp : ℕ → Fin k → ℝ)
      (Hz : Matrix (Fin r) (Fin k) ℝ),
      (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ ∑ ℓ, (s ℓ m - s ℓ (m - 1)) • HS ℓ = 0) ∧
      Hz *ᵥ ∑ ℓ, (s ℓ m - s ℓ (m - 1)) • HS ℓ = 0)

def cancellationStatement : Prop := ∀ (k : ℕ) (s : Fin 2 → ℕ → ℝ) (HS : Fin 2 → Fin k → ℝ)
  (m : ℕ), HS 0 = HS 1 → s 0 m - s 0 (m - 1) = -(s 1 m - s 1 (m - 1)) →
    ∑ ℓ, (s ℓ m - s ℓ (m - 1)) • HS ℓ = 0

def reductionStatement : Prop := ∀ (k r r' d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (c' : Fin r' → ℝ) (A' : Matrix (Fin r') (Fin r') ℝ) (P : Matrix (Fin r') (Fin r) ℝ),
  IsUnit A.det → IsUnit A'.det → P * A = A' * P → c = c' ᵥ* P →
  (∀ (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (x : ℝ),
    resid Hp Hz c A d bP zP bZ z x = resid Hp (P * Hz) c' A' d bP zP (P *ᵥ bZ) (P *ᵥ z) x) ∧
  ∀ (V κ : Fin k → ℝ) (u T : ℝ), cross Hp Hz c A d V κ u T = cross Hp (P * Hz) c' A' d V κ u T

def reducedNecessityStatement : Prop := ∀ (k r r' d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (c' : Fin r' → ℝ) (A' : Matrix (Fin r') (Fin r') ℝ) (P : Matrix (Fin r') (Fin r) ℝ),
  IsUnit A.det → IsUnit A'.det → P * A = A' * P → c = c' ᵥ* P →
  (∀ y : Fin r' → ℝ, (∀ x : ℝ, c' ⬝ᵥ (exp (x • A') *ᵥ y) = 0) → y = 0) →
  ∀ (V₀ V₁ κ₀ κ₁ : Fin k → ℝ) (Tm u d₁ d₂ α β : ℝ), d₁ < d₂ → κ₁ - κ₀ = -Tm • (V₁ - V₀) →
  (∀ T ∈ Set.Ioo d₁ d₂, cross Hp Hz c A d V₁ κ₁ u T - cross Hp Hz c A d V₀ κ₀ u T = α + β * T) →
  (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V₁ - V₀) = 0) ∧ (P * Hz) *ᵥ (V₁ - V₀) = 0

def prop44Statement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  (∃ (P : Matrix (Fin r) (Fin r) ℂ) (lam : Fin r → ℂ), IsUnit P.det ∧
    A.map Complex.ofReal * P = P * diagonal lam) →
  Hp 0 = 0 → ∀ (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (V : Fin k → ℝ),
    (∃ α β : ℝ, ∀ x, resid (sharp Hp V) Hz c A d bP zP bZ z x = α + β * x) → Hz *ᵥ V = 0

def uncorrelatedStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (V : Fin k → ℝ),
  (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ V = 0) → Hz *ᵥ V = 0 →
  ∀ x, Kfun Hp Hz c A d V x = 0 ∧
    resid (sharp Hp V) Hz c A d bP zP bZ z x =
      resid Hp Hz c A d bP zP bZ z x - (2 * (Hp 0 ⬝ᵥ V) + V ⬝ᵥ V) * x

def sharpEntriesStatement : Prop := ∀ (k r : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (V : Fin k → ℝ),
  (∀ μ ν, 1 ≤ μ → 1 ≤ ν → sharp Hp V μ ⬝ᵥ sharp Hp V ν = Hp μ ⬝ᵥ Hp ν) ∧
  (∀ ν, 1 ≤ ν → sharp Hp V 0 ⬝ᵥ sharp Hp V ν = Hp 0 ⬝ᵥ Hp ν + Hp ν ⬝ᵥ V) ∧
  sharp Hp V 0 ⬝ᵥ sharp Hp V 0 = Hp 0 ⬝ᵥ Hp 0 + (2 * (Hp 0 ⬝ᵥ V) + V ⬝ᵥ V) ∧
  (∀ μ, 1 ≤ μ → Hz *ᵥ sharp Hp V μ = Hz *ᵥ Hp μ) ∧ Hz *ᵥ sharp Hp V 0 = Hz *ᵥ Hp 0 + Hz *ᵥ V

def orthogonalityStatement : Prop :=
  let Hp : ℕ → Fin 1 → ℝ := fun μ _ => if μ = 1 then 1 else 0
  let Hz : Matrix (Fin 0) (Fin 1) ℝ := 0
  (∀ μ, 1 ≤ μ → μ ≤ 1 → Hp μ ⬝ᵥ (0 : Fin 1 → ℝ) = 0) ∧ Hz *ᵥ (0 : Fin 1 → ℝ) = 0 ∧
  (∀ x, resid (sharp Hp 0) Hz 0 0 1 0 0 0 0 x = -(x ^ 3 / 2)) ∧
  ¬ ∃ α β : ℝ, ∀ x, resid (sharp Hp 0) Hz 0 0 1 0 0 0 0 x = α + β * x

def statement : Prop := aggregationStatement ∧ cancellationStatement ∧ reductionStatement ∧
  reducedNecessityStatement ∧ orthogonalityStatement ∧ prop44Statement ∧ uncorrelatedStatement ∧ sharpEntriesStatement

end Standalone.UnifiedSpliceSpecial

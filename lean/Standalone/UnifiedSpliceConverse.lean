import Standalone.UnifiedSpliceAlgebra

/-! # Claim 049 (b)(iv), pointwise: consistency is (49.2) and `R♯` affine

At one time `u` on one path, after Step 0. The current interval is `j = j(u)`, and the later ones
are `j + 1, …, M`. On interval `m` the front end has noise `V_m` and primitive `T V_m + κ_m`, with
`κ_j = −u V_j` and `κ_m − κ_{m−1} = −T_m (V_m − V_{m−1})` (continuity at the meetings). The pointwise
form of Assumption 2.1 on `I_m ∩ [u, H]` is `R(T − u) − c_m(u, T) = −(D^S − σ^S·∫σ^S)(u, T)`. The
right side is affine in `T` on `I_m`, with free front-end drifts (Claim 037(a)'s converse), so
consistency at `(u, ω)` means that `T ↦ R(T − u) − c_m(u, T)` is affine on `I_m ∩ [u, H]`. The
intervals are taken open and nonempty here (`lo m < hi m`).

`converseStatement`, (b)(iv): with `A` invertible and `(A, c)` observable, consistency on every
interval `j, …, M` holds iff (49.2) holds at every later meeting and `x ↦ R♯(x)` is affine on `ℝ`.
`R♯` is the residual with the effective level `H^{0,0} + V_j`. The proof is the claim's:
* the two sides differ by `K` and affine terms (`UnifiedSpliceAlgebra`);
* `T ↦ R(T − u) − c_m(u, T)` is real-analytic, so affine on an interval means affine on `ℝ`;
* then each jump is affine, which is (a) (`UnifiedSpliceNecessity`).
-/

open Matrix NormedSpace Set

namespace Standalone.UnifiedSpliceConverse
open Standalone.UnifiedSpliceAlgebra

def converseStatement : Prop := ∀ (k r d : ℕ) (Hp : ℕ → Fin k → ℝ)
  (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (V κ : ℕ → Fin k → ℝ) (Tm lo hi : ℕ → ℝ) (j M : ℕ)
    (u : ℝ), j ≤ M → κ j = -u • V j →
    (∀ m, j < m → m ≤ M → κ m - κ (m - 1) = -Tm m • (V m - V (m - 1))) →
    (∀ m, j ≤ m → m ≤ M → lo m < hi m) →
    ((∀ m, j ≤ m → m ≤ M → ∃ α β : ℝ, ∀ T ∈ Ioo (lo m) (hi m),
        resid Hp Hz c A d bP zP bZ z (T - u) - cross Hp Hz c A d (V m) (κ m) u T = α + β * T) ↔
      ((∀ m, j < m → m ≤ M → (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V m - V (m - 1)) = 0) ∧
          Hz *ᵥ (V m - V (m - 1)) = 0) ∧
        ∃ α β : ℝ, ∀ x, resid (sharp Hp (V j)) Hz c A d bP zP bZ z x = α + β * x))

def statement : Prop := converseStatement

end Standalone.UnifiedSpliceConverse

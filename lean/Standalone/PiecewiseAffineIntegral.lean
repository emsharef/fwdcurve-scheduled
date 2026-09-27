import Standalone.LemmaA

/-!
# Claim 006 (Lemma C): statement only

Scheduled dates `τ 0 = 0 < τ 1 < … < τ N` with the intervals `I_k` of Claim 002
(`Standalone.LemmaA.I`), coefficients `a k, b k ∈ ℝ^d`, and a piecewise-affine function `g`
equal to `a k + (u - T_k) • b k` on `I_k` (6.2). For `t ∈ I_j` and `k ≥ j`, `m_k = max (T_k, t)`.

The statement bundles the parts of `math/claims/006-piecewise-affine-integral.md`:

* **Part (a)**, (6.3): for `t ≤ T`, `t ∈ I_j`, `T ∈ I_k`: `j ≤ k` and
  `∫_t^T g = e_{jk}(t) + (T - m_k) • a k + ½ [(T - T_k)² - (m_k - T_k)²] • b k`, with `e` as in
  (6.4); and (6.5): the same integral is `e_{jk}(t) + τ • g(m_k) + ½ τ² • b k` with
  `τ = T - m_k`;
* **Part (b)**: a quadratic `c₀ + x • c₁ + x² • c₂` vanishing at three distinct `x` has
  `c₀ = c₁ = c₂ = 0`, and an affine `c₀ + x • c₁` vanishing at two distinct `x` has
  `c₀ = c₁ = 0`; (6.6): two quadratics agreeing at three distinct points have the same
  coefficients; (6.7): two functions of the form (6.2) agreeing at two distinct points of every
  `I_k` have the same coefficients.

Encoding choices. As in Claim 002, `g` is any function equal to the affine pieces on each `I_k`;
its values off `[0, ∞)` are irrelevant. The claim's `d ≥ 1` is not assumed (for `d = 0` every
statement is trivial). The "in particular" of (6.6), that the three coefficients of (6.5) are
determined by three values of the integral, is the instance of (6.6) with `p, q, r` the
coefficients of (6.5); it is not stated separately. The Remark (6.8) is not part of the claim.
-/

open MeasureTheory

namespace Standalone.PiecewiseAffineIntegral

/-- (6.4): `e_{jk}(t) = a_j (T_{j+1} - t) + ½ b_j [(T_{j+1} - T_j)² - (t - T_j)²]
+ ∑_{m=j+1}^{k-1} [a_m (T_{m+1} - T_m) + ½ b_m (T_{m+1} - T_m)²]` for `k > j`, and
`e_{jj}(t) = 0`. It does not mention `T`. -/
noncomputable def e {E : Type*} [AddCommGroup E] [Module ℝ E] (τ : ℕ → ℝ) (a b : ℕ → E)
    (j k : ℕ)
    (t : ℝ) : E :=
  if j < k then
    (τ (j + 1) - t) • a j + (((τ (j + 1) - τ j) ^ 2 - (t - τ j) ^ 2) / 2) • b j +
      ∑ m ∈ Finset.Ico (j + 1) k,
        ((τ (m + 1) - τ m) • a m + ((τ (m + 1) - τ m) ^ 2 / 2) • b m)
  else 0

def statement : Prop :=
  ∀ (N d : ℕ) (τ : ℕ → ℝ) (a b : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℝ → EuclideanSpace ℝ (Fin d)),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    -- (6.2)
    (∀ k ≤ N, ∀ u ∈ LemmaA.I τ N k, g u = a k + (u - τ k) • b k) →
    -- Part (a): (6.3) and (6.5)
    (∀ t T : ℝ, t ≤ T → ∀ j ≤ N, ∀ k ≤ N, t ∈ LemmaA.I τ N j → T ∈ LemmaA.I τ N k →
        j ≤ k ∧
        ∫ u in t..T, g u = e τ a b j k t + (T - max (τ k) t) • a k +
          (((T - τ k) ^ 2 - (max (τ k) t - τ k) ^ 2) / 2) • b k ∧
        ∫ u in t..T, g u = e τ a b j k t + (T - max (τ k) t) • g (max (τ k) t) +
          ((T - max (τ k) t) ^ 2 / 2) • b k) ∧
    -- Part (b): quadratic identification
    (∀ (c₀ c₁ c₂ : EuclideanSpace ℝ (Fin d)) (x₁ x₂ x₃ : ℝ), x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
        c₀ + x₁ • c₁ + x₁ ^ 2 • c₂ = 0 → c₀ + x₂ • c₁ + x₂ ^ 2 • c₂ = 0 →
        c₀ + x₃ • c₁ + x₃ ^ 2 • c₂ = 0 → c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) ∧
    -- Part (b): affine identification
    (∀ (c₀ c₁ : EuclideanSpace ℝ (Fin d)) (x₁ x₂ : ℝ), x₁ ≠ x₂ →
        c₀ + x₁ • c₁ = 0 → c₀ + x₂ • c₁ = 0 → c₀ = 0 ∧ c₁ = 0) ∧
    -- (6.6)
    (∀ (p q r p' q' r' : EuclideanSpace ℝ (Fin d)) (x₁ x₂ x₃ : ℝ), x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
        (∀ x ∈ ({x₁, x₂, x₃} : Set ℝ), p + x • q + x ^ 2 • r = p' + x • q' + x ^ 2 • r') →
        p = p' ∧ q = q' ∧ r = r') ∧
    -- (6.7)
    (∀ (a' b' : ℕ → EuclideanSpace ℝ (Fin d)) (g' : ℝ → EuclideanSpace ℝ (Fin d)),
        (∀ k ≤ N, ∀ u ∈ LemmaA.I τ N k, g' u = a' k + (u - τ k) • b' k) →
        (∀ k ≤ N, ∃ u₁ ∈ LemmaA.I τ N k, ∃ u₂ ∈ LemmaA.I τ N k,
          u₁ ≠ u₂ ∧ g u₁ = g' u₁ ∧ g u₂ = g' u₂) →
        ∀ k ≤ N, a k = a' k ∧ b k = b' k)

end Standalone.PiecewiseAffineIntegral

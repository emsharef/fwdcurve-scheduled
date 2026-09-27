import Standalone.BoundedVarianceExistence
import Standalone.SeparableMeetingShapes

/-! # Claim 028: the switching coefficients (28.4)

The state (28.3) lives in `Fin (dim028 p d N)`, indexed through `equiv028` by
the scale block `Fin p`, the `M` block and the `A` block, each of the latter
indexed by a factor `j` and a time interval `k`; `dim028 p d N` is
`p + 2 d (N+1)`. The curve factor `j` is driven by the driver `drv j`.

The coefficients are stated for generic time functions: `ind k` is the
meeting-interval indicator `1_{I_k}`, `eH` the horizon indicator `e_H`, and
`G j k t` stands for `G_{j,k}(t min H)`; only measurability and the bounds
`|ind k| ≤ 1`, `|eH| ≤ 1`, `|G j k| ≤ Gbar` are used. The scale functions
`psi j` are Borel, bounded by `Kψ` and Lipschitz in the state with constant
`Lψ` uniform in time; (beta, Sigma) are in `Coefficients6`.

`lipschitzStatement` gives the Lipschitz constant
`LZ + (1 + 2 Kψ (1 + Gbar)) Lψ` for the sup norms; it is at most the claim's
`LZ + d(N+1)[(1 + 2 Kψ (1 + Gbar)) Lψ]` whenever `d ≥ 1`.
`coefficientsStatement` is the `Coefficients6` assertion of (28.4).
`frozenStatement`, `constantPrimitiveStatement` and `movingPrimitiveStatement`
are part (e) and its converse.
-/

open MeasureTheory
open scoped NNReal
open Standalone.BoundedVarianceExistence Standalone.SeparableMeetingShapes
namespace Standalone.SeparableMeetingMarkovCoefficients

/-- Scale block, then the `M` and `A` blocks. -/
abbrev Index028 (p d N : ℕ) : Type := Fin p ⊕ (Fin d × Fin (N+1)) ⊕ (Fin d × Fin (N+1))

def dim028 (p d N : ℕ) : ℕ := p + (d * (N+1) + d * (N+1))

def equiv028 (p d N : ℕ) : Index028 p d N ≃ Fin (dim028 p d N) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

/-- The scale coordinates `z` of a state `x = (z, mu, a)`. -/
def zpart {p d N : ℕ} (x : Fin (dim028 p d N) → ℝ) : Fin p → ℝ :=
  fun i => x (equiv028 p d N (Sum.inl i))

/-- The drift `b` of (28.4). -/
def drift028 {p d N : ℕ} (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ)
    (eH : ℝ≥0 → ℝ) (G : Fin d → Fin (N+1) → ℝ≥0 → ℝ) :
    ℝ≥0 × (Fin (dim028 p d N) → ℝ) → Fin (dim028 p d N) → ℝ := fun q i =>
  Sum.elim (fun i' => eH q.1 * beta (q.1, zpart q.2) i')
    (Sum.elim
      (fun jk : Fin d × Fin (N+1) =>
        -(ind jk.2 q.1 * eH q.1 * psi jk.1 (q.1, zpart q.2) ^ 2 * G jk.1 jk.2 q.1))
      (fun jk : Fin d × Fin (N+1) => ind jk.2 q.1 * eH q.1 * psi jk.1 (q.1, zpart q.2) ^ 2))
    ((equiv028 p d N).symm i)

/-- The diffusion `sigma` of (28.4). -/
def diffusion028 {p d N m : ℕ} (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
    (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ)
    (eH : ℝ≥0 → ℝ) (drv : Fin d → Fin m) :
    ℝ≥0 × (Fin (dim028 p d N) → ℝ) → Fin (dim028 p d N) → Fin m → ℝ := fun q i l =>
  Sum.elim (fun i' => eH q.1 * Sigma (q.1, zpart q.2) i' l)
    (Sum.elim
      (fun jk : Fin d × Fin (N+1) =>
        if l = drv jk.1 then ind jk.2 q.1 * eH q.1 * psi jk.1 (q.1, zpart q.2) else 0)
      (fun _ => 0))
    ((equiv028 p d N).symm i)

/-- The explicit Lipschitz constant of (a), for the sup norms. -/
def lipschitzStatement : Prop := ∀ (p d N m : ℕ)
  (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ) (eH : ℝ≥0 → ℝ)
  (G : Fin d → Fin (N+1) → ℝ≥0 → ℝ) (drv : Fin d → Fin m) (LZ Kψ Lψ Gbar : ℝ),
  0 ≤ LZ → 0 ≤ Kψ → 0 ≤ Lψ → 0 ≤ Gbar →
  (∀ t z z', ‖beta (t,z) - beta (t,z')‖ ≤ LZ * ‖z - z'‖ ∧
    ‖Sigma (t,z) - Sigma (t,z')‖ ≤ LZ * ‖z - z'‖) →
  (∀ j q, |psi j q| ≤ Kψ) → (∀ j t z z', |psi j (t,z) - psi j (t,z')| ≤ Lψ * ‖z - z'‖) →
  (∀ k t, |ind k t| ≤ 1) → (∀ t, |eH t| ≤ 1) → (∀ j k t, |G j k t| ≤ Gbar) →
  ∀ t (x y : Fin (dim028 p d N) → ℝ),
    ‖drift028 beta psi ind eH G (t,x) - drift028 beta psi ind eH G (t,y)‖ ≤
      (LZ + (1 + 2 * Kψ * (1 + Gbar)) * Lψ) * ‖x - y‖ ∧
    ‖diffusion028 Sigma psi ind eH drv (t,x) - diffusion028 Sigma psi ind eH drv (t,y)‖ ≤
      (LZ + (1 + 2 * Kψ * (1 + Gbar)) * Lψ) * ‖x - y‖

/-- (a): the coefficients (28.4) are in `Coefficients6`. -/
def coefficientsStatement : Prop := ∀ (p d N m : ℕ)
  (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ) (eH : ℝ≥0 → ℝ)
  (G : Fin d → Fin (N+1) → ℝ≥0 → ℝ) (drv : Fin d → Fin m) (Kψ Lψ Gbar : ℝ),
  Coefficients6 beta Sigma →
  (∀ j, Measurable (psi j)) → (∀ j q, |psi j q| ≤ Kψ) →
  (∀ j t z z', |psi j (t,z) - psi j (t,z')| ≤ Lψ * ‖z - z'‖) →
  (∀ k, Measurable (ind k)) → (∀ k t, |ind k t| ≤ 1) →
  Measurable eH → (∀ t, |eH t| ≤ 1) →
  (∀ j k, Measurable (G j k)) → (∀ j k t, |G j k t| ≤ Gbar) →
  Coefficients6 (drift028 beta psi ind eH G) (diffusion028 Sigma psi ind eH drv)

/-- (e): on a time set `J` inside one meeting interval and the horizon, with
time-free scale data and a constant primitive, the coefficients do not depend
on time. -/
def frozenStatement : Prop := ∀ (p d N m : ℕ)
  (beta : ℝ≥0 × (Fin p → ℝ) → Fin p → ℝ) (Sigma : ℝ≥0 × (Fin p → ℝ) → Fin p → Fin m → ℝ)
  (psi : Fin d → ℝ≥0 × (Fin p → ℝ) → ℝ) (ind : Fin (N+1) → ℝ≥0 → ℝ) (eH : ℝ≥0 → ℝ)
  (G : Fin d → Fin (N+1) → ℝ≥0 → ℝ) (drv : Fin d → Fin m) (k : Fin (N+1))
  (J : Set ℝ≥0) (c : Fin d → ℝ),
  (∀ t t' z, beta (t,z) = beta (t',z)) → (∀ t t' z, Sigma (t,z) = Sigma (t',z)) →
  (∀ j t t' z, psi j (t,z) = psi j (t',z)) →
  (∀ t ∈ J, ind k t = 1) → (∀ l, l ≠ k → ∀ t ∈ J, ind l t = 0) → (∀ t ∈ J, eH t = 1) →
  (∀ j, ∀ t ∈ J, G j k t = c j) →
  ∃ (bk : (Fin (dim028 p d N) → ℝ) → Fin (dim028 p d N) → ℝ)
    (σk : (Fin (dim028 p d N) → ℝ) → Fin (dim028 p d N) → Fin m → ℝ),
    ∀ t ∈ J, ∀ x, drift028 beta psi ind eH G (t,x) = bk x ∧
      diffusion028 Sigma psi ind eH drv (t,x) = σk x

/-- (e): zero current-interval loading makes the primitive constant there. -/
def constantPrimitiveStatement : Prop := ∀ (g : ℝ → ℝ) (b t : ℝ),
  IntervalIntegrable g volume 0 b → IntervalIntegrable g volume b t →
  (∀ u ∈ Set.uIcc b t, g u = 0) → G026 g t = G026 g b

/-- Converse in (e): if the loading is `a * phi` on `[b, c]` with `phi`
continuous and the primitive is constant there, then `a * phi` vanishes on
`[b, c]`. The interval must be nondegenerate, as `I_k ∩ [0,H]` is. -/
def movingPrimitiveStatement : Prop := ∀ (g phi : ℝ → ℝ) (a b c : ℝ), b < c →
  (∀ x y, IntervalIntegrable g volume x y) → Continuous phi →
  (∀ u ∈ Set.Icc b c, g u = a * phi u) →
  (∀ t ∈ Set.Icc b c, G026 g t = G026 g b) →
  ∀ u ∈ Set.Icc b c, a * phi u = 0

def statement : Prop := lipschitzStatement ∧ coefficientsStatement ∧ frozenStatement ∧
  constantPrimitiveStatement ∧ movingPrimitiveStatement

end Standalone.SeparableMeetingMarkovCoefficients

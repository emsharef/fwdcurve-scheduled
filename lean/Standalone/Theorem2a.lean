import Standalone.RampDriftIdentified
import Standalone.JumpLawTiltedGaussian
import Mathlib.MeasureTheory.Measure.Prod

/-!
Claim 010, Theorem 2a: statement only. The two equivalences below assemble Claims 007 and
008 with the quantifiers of AX-01 and AX-02. The third equivalence records the differentiated
drift form. Only the standing hypotheses actually used are repeated: measurable sections
of the curve jumps and their vanishing before the meeting. The proof for `HJMScheduled`
derives these sections from its joint measurability field; no measurability of the drift
coefficients is added. Family identities are required only for `t ≥ 0`.

The jump conditions use exactly Claim 008's lower-integral encoding of the conditional
expectation and tilted conditional Gaussian law. The jointly Gaussian corollary and the
parametrization Remark are paper statements, as specified in the claim's Lean shape.
-/

open MeasureTheory

namespace Standalone.Theorem2a

open LemmaA RampDriftIdentified JumpLawTiltedGaussian

/-- (10.4) at a fixed `(ω, t)`. -/
def cond104 {Ω : Type} {d : ℕ} (N : ℕ) (τ : ℕ → ℝ)
    (s : ℕ → ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℕ → ℝ → Ω → ℝ)
    (ω : Ω) (t : ℝ) : Prop :=
  ∀ j ≤ N, t ∈ I τ N j → ∀ k, j ≤ k → k ≤ N →
    a k t ω = aStar τ (fun m => s m t) j k t ∧ b k t ω = bStar (fun m => s m t) k

/-- Part (ii), at every scheduled date. -/
def condii {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → MeasurableSpace Ω)
    (N : ℕ) (τ : ℕ → ℝ) (X y : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ n, 1 ≤ n → n ≤ N → cond83 P (G n) τ n N (X n) (y n) ∧
    cond84 P n N (y n) ∧ cond85 P (G n) τ n N (X n) (y n)

def statement : Prop :=
  ∀ {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (τ : ℕ → ℝ)
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (ξ : ℕ → ℝ → Ω → ℝ) (G : ℕ → MeasurableSpace Ω)
    (s : ℕ → ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℕ → ℝ → Ω → ℝ)
    (X y : ℕ → ℕ → Ω → ℝ),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → (∀ n, G n ≤ m₀) →
    (∀ n, 1 ≤ n → n ≤ N → ∀ u, Measurable (ξ n u)) →
    (∀ n, 1 ≤ n → n ≤ N → ∀ u ω, u < τ n → ξ n u ω = 0) →
    (∀ n k, 1 ≤ n → n ≤ k → k ≤ N → Measurable[G n] (y n k)) →
    -- (10.1), (10.2), (10.3)
    (∀ ω t, 0 ≤ t → ∀ T, t ≤ T → ∀ k ≤ N, T ∈ I τ N k → σ t T ω = s k t) →
    (∀ ω t, 0 ≤ t → ∀ T, t ≤ T → ∀ k ≤ N, T ∈ I τ N k →
      α t T ω = a k t ω + (T - τ k) * b k t ω) →
    (∀ ω n k, 1 ≤ n → n ≤ k → k ≤ N → ∀ u ∈ I τ N k,
      ξ n u ω = X n k ω + y n k ω * (u - τ k)) →
    let A1 : Prop := ∀ T : ℝ, 0 < T → ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc 0 T))),
      ∫ u in p.2..T, α p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..T, σ p.2 u p.1‖ ^ 2
    let A2 : Prop := ∀ n, 1 ≤ n → n ≤ N → H P (G n) τ n (ξ n)
    let B : Prop := ∀ᵐ p ∂(P.prod (volume.restrict (Set.Ici 0))), cond104 N τ s a b p.1 p.2
    let B' : Prop := ∀ᵐ p ∂(P.prod (volume.restrict (Set.Ici 0))), ∀ T, p.2 ≤ T →
      α p.2 T p.1 = inner ℝ (σ p.2 T p.1) (∫ u in p.2..T, σ p.2 u p.1)
    (A1 ↔ B) ∧ (A2 ↔ condii P G N τ X y) ∧ (B ↔ B')

end Standalone.Theorem2a

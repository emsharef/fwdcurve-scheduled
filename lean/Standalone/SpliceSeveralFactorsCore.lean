import Standalone.SpliceStateBlockCross

/-! # Claim 041 (a): the argument on one path, for a sum of cross terms

With several step factors and several drivers, the cross term of AX-01 is a finite sum of
Claim 040 cross terms `cross040 s_q c A w_q`, one per pair `q` of a step scale family `s_q` and a
covariation vector `w_q`. In Claim 041's setting `q` runs over the drivers `l`, with
`s_l = ∑_ℓ s_ℓ H^S_{ℓ,l}` and `w_l = H^Z_{·l}`. The weighted jumps then sum to
`W_m = ∑_q Δ_{q,m} w_q = H^Z G_m^T` (41.3).

`coreStatement` is (a)'s argument for such a sum. Suppose that for every `t ∈ [0, τ)` the
integrated sum on `(t, H)` is affine on each maturity interval plus a real-analytic function.
Then `∑_q Δ_{q,m}(u) w_q(u) = 0` for almost every `u ∈ [0, τ)`. Here `A` is invertible and `(A, c)`
observable.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceSeveralFactorsCore
open Standalone.SpliceCrossTermDrift Standalone.SpliceStateBlockCross

def coreStatement : Prop := ∀ (r n : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, (∀ y : Fin r → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0) →
  ∀ (s : Fin n → ℕ → ℝ → ℝ) (w : Fin n → ℝ → Fin r → ℝ), (∀ q, PathData (s q) (w q)) →
  ∀ (Tm : Finset ℝ) (τ H : ℝ), τ ∈ Tm → τ < H →
  (∀ t ∈ Ico 0 τ, ∃ (p G : ℝ → ℝ), AnalyticOnNhd ℝ G univ ∧
    (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, ∑ q, cross040 (s q) Tm c A (w q) u T = p T + G T) →
  ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    ∑ q, (s q (idx033 Tm τ) u - s q (idx033 Tm τ - 1) u) • w q u = 0

def statement : Prop := coreStatement

end Standalone.SpliceSeveralFactorsCore

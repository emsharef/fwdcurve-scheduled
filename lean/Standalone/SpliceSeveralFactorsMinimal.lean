import Standalone.SpliceSeveralFactorsBlocks

/-! # Claim 041 (c): shared exponents, and the minimal realization

* `minimalStatement`: every block `F(x, z) = C e^{𝒜x} z` with `𝒜` invertible has a minimal
  realization. There are `r'`, an invertible `𝒜'`, an observable pair `(𝒜', C')` and a linear map
  `P` with `P 𝒜 = 𝒜' P`, such that `C e^{𝒜x} z = C' e^{𝒜'x} P z` for all `x` and `z`. The
  construction is the Proof's: the quotient by the unobservable subspace `N`. `𝒜` maps `N` onto
  `N`, so the induced map on the quotient is invertible.
* `reducedStatement` is (c). Under AX-01 for the curve with an arbitrary block `(𝒜, C)`, (41.3)
  holds for the reduced noise `H^{Z'} = P H^Z`. The curve is unchanged with `(𝒜', C', Z' = P Z)`.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceSeveralFactorsMinimal
open Standalone.SpliceSeveralFactorsAX01 Standalone.SpliceSeveralFactorsBlocks

def minimalStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ c : Fin r → ℝ, ∃ (r' : ℕ) (A' : Matrix (Fin r') (Fin r') ℝ) (c' : Fin r' → ℝ)
    (P : Matrix (Fin r') (Fin r) ℝ), IsUnit A'.det ∧ Observable A' c' ∧ P * A = A' * P ∧
    ∀ (x : ℝ) (z : Fin r → ℝ), c ⬝ᵥ (exp (x • A) *ᵥ z) = c' ⬝ᵥ (exp (x • A') *ᵥ (P *ᵥ z))

def reducedStatement : Prop := ∀ (r k L : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (c : Fin r → ℝ) (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin r → ℝ) (Tm : Finset ℝ)
    (H : ℝ), PathData041 s HS HZ dL dC bZ z H → AX01Path041 s HS HZ dL dC bZ z Tm c A H →
  ∃ (r' : ℕ) (A' : Matrix (Fin r') (Fin r') ℝ) (c' : Fin r' → ℝ) (P : Matrix (Fin r') (Fin r) ℝ),
    IsUnit A'.det ∧ Observable A' c' ∧
    (∀ (x : ℝ) (y : Fin r → ℝ), c ⬝ᵥ (exp (x • A) *ᵥ y) = c' ⬝ᵥ (exp (x • A') *ᵥ (P *ᵥ y))) ∧
    ∀ τ ∈ Tm, τ < H → ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
      W041 s HS (fun u i l => (P *ᵥ fun i' => HZ u i' l) i) Tm τ u = 0

def statement : Prop := minimalStatement ∧ reducedStatement

end Standalone.SpliceSeveralFactorsMinimal

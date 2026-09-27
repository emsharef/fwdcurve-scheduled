import Standalone.RecurrenceNecessityCurve
import Standalone.RecurrenceNecessityReduction
import Standalone.RecurrenceNecessityAlgebra

/-! # Claim 032 (a): the rank bound

The HJM curve of (32.1) with constant scale and zero curve jumps, at Claim 029's time
`t = n + 1/2` and maturities `n + i + 3/4`, is `curve032`: the initial curve, plus the drift
integral of `α(s,T) = σ(s,T) ∫_s^T σ(s,u) du`, plus the driver integral of `σ(·,T)`.
A realization at that time with state dimension `q` (`Realized032`) is, as in Claim 029, a
state `Y` in a set `Z ⊆ ℝ^q` and a map `Ψ`, each coordinate locally Lipschitz on `Z`, with the
curve equal to `Ψ(Y)` almost surely.

`generalRankStatement` is Claim 029's rank step for any matrix: if the curve values are almost
surely `c + M δ` for a random vector `δ` with an absolutely continuous law and almost surely
`Ψ(Y)` as above, then `rank M ≤ q`.

`rankStatement` is (a). Let the driver be a pre-Brownian motion, and let `(C, b', c')` be data
of the reduction (`RecurrenceNecessityReduction`): the same shape, `λ(x) = c' e^{xC} b'`, with
every `Γ_δ` positive definite. Then a realization with state dimension `q` forces
`rank ℋ_{R,n} ≤ q` for the block Hankel section (32.2) built from `c'` and `E = e^{C}`.
-/

open MeasureTheory ProbabilityTheory Matrix NormedSpace
open scoped NNReal
namespace Standalone.RecurrenceNecessityRank
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingCurve
open Standalone.RecurrenceNecessityCurve Standalone.RecurrenceNecessityReduction
open Standalone.RecurrenceNecessityAlgebra

variable {r : ℕ}

/-- The HJM drift `α(s,T) = σ(s,T) ∫_s^T σ(s,u) du`. -/
noncomputable def alpha032 (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (b : Fin r → ℝ) (n R : ℕ) (s T : ℝ) : ℝ :=
  a (count029 n R s T) * lam032 c A b (T - s) *
    ∫ u in s..T, a (count029 n R s u) * lam032 c A b (u - s)

/-- The HJM curve at the time `n + 1/2` and the maturity `n + i + 3/4`. -/
noncomputable def curve032 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (f0 : ℝ → ℝ)
    (n R : ℕ) (i : ℕ) (ω : Ω) : ℝ :=
  f0 (mat029 n i) + (∫ s in (0:ℝ)..(time029 n : ℝ), alpha032 a c A b n R s (mat029 n i)) +
    S.I k (sigma032 a c A b n R (mat029 n i)) (time029 n) ω

/-- A realization at the time `n + 1/2`, with state dimension `q`. -/
def Realized032 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (f0 : ℝ → ℝ)
    (n R q : ℕ) : Prop :=
  ∃ (Y : Ω → Fin q → ℝ) (Z : Set (Fin q → ℝ)) (Ψ : (Fin q → ℝ) → Fin (R+1) → ℝ),
    (∀ i, LocallyLipschitzOn Z fun y => Ψ y i) ∧
    ∀ᵐ ω ∂S.μ, Y ω ∈ Z ∧ ∀ i : Fin (R+1), curve032 S k a c A b f0 n R i ω = Ψ (Y ω) i

def generalRankStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (R N : ℕ) (M : Matrix (Fin (R+1)) (Fin N) ℝ)
  (δ : Ω → Fin N → ℝ), AEMeasurable δ μ → μ.map δ ≪ volume →
  ∀ (f : Ω → Fin (R+1) → ℝ) (c : Fin (R+1) → ℝ),
  (∀ᵐ ω ∂μ, f ω = c + M *ᵥ δ ω) →
  ∀ (q : ℕ) (Y : Ω → Fin q → ℝ) (Z : Set (Fin q → ℝ)) (Ψ : (Fin q → ℝ) → Fin (R+1) → ℝ),
  (∀ i, LocallyLipschitzOn Z fun y => Ψ y i) →
  (∀ᵐ ω ∂μ, Y ω ∈ Z ∧ f ω = Ψ (Y ω)) → M.rank ≤ q

def rankStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (f0 : ℝ → ℝ)
    (n R q : ℕ), Realized032 S k a c A b f0 n R q →
  ∀ (C : Matrix (Fin r) (Fin r) ℝ) (b' c' : Fin r → ℝ),
    (∀ x, lam032 c A b x = lam032 c' C b' x) → (∀ δ : ℝ, 0 < δ → (gamma032 C b' δ).PosDef) →
    (Standalone.RecurrenceNecessityAlgebra.blockHankel032 a c' (exp C) R n).rank ≤ q

def statement : Prop := generalRankStatement ∧ rankStatement

end Standalone.RecurrenceNecessityRank

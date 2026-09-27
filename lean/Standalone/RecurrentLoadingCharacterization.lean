import Standalone.MeetingLoadingObstruction
import Standalone.RecurrentLoadingAlgebra

/-! # Claim 030 (c): recurrent loadings characterize the realizable ones for `λ ≡ 1`

With `λ ≡ 1`, a constant scale and zero curve jumps, Claim 029 formalizes a realization at the
time `n + 1/2` of the schedule `T_m = m`, `1 ≤ m ≤ n + R`, as `Realized029`: a random state in
`ℝ^q` and a map, locally Lipschitz in the state, giving the curve at the maturities
`n + i + 3/4`, `i ≤ R`, almost surely. One realization serving every schedule, as (R4)
requires, gives such realizations with the same `q` for every `R` and `n`.

`sufficiencyStatement`: loadings satisfying a linear recurrence of order `L` are realized in
this sense with `q = L`, for every `R`, `n` and initial curve. The state is Claim 030's `Ξ_t`
(with `p = L`, `r = 1`, `A = 0`, `b = c = 1` and the companion data of (H2)); the deterministic
drift and initial curve enter the map as constants, and the map is affine in the state.

`characterizationStatement` is (c): with a Brownian driver, realizations with a common `q` for
every `R` and `n` exist if and only if the loadings satisfy a linear recurrence. Necessity is
Claim 029(b).
-/

open MeasureTheory ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingObstruction
open Standalone.RecurrentLoadingAlgebra
namespace Standalone.RecurrentLoadingCharacterization

def sufficiencyStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (a : ℕ → ℝ) (f0 : ℝ → ℝ) (L : ℕ) (c : Fin L → ℝ), Recurrence030 a L c →
  ∀ R n : ℕ, Realized029 S k a f0 n R L

def characterizationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m), IsBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (f0 : ℝ → ℝ),
    (∃ q : ℕ, ∀ R n : ℕ, Realized029 S k a f0 n R q) ↔
      ∃ (L : ℕ) (c : Fin L → ℝ), Recurrence030 a L c

def statement : Prop := sufficiencyStatement ∧ characterizationStatement

end Standalone.RecurrentLoadingCharacterization

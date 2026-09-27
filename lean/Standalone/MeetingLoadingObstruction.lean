import Standalone.MeetingLoadingCurve
import Standalone.MeetingLoadingRank

/-! # Claim 029 (a)–(c): the obstruction

The HJM curve of (29.1) with `λ ≡ 1`, constant scale and zero curve jumps, on the
schedule `T_m = m`, at the time `t = n + 1/2` and the maturities `n + i + 3/4`,
is `curve029`: the initial curve plus the drift integral of
`α(s,T) = σ(s,T) ∫_s^T σ(s,u) du` plus the driver integral of `σ(·,T)`; the
driver is a standard Brownian motion (`IsBrownianReal`) of the supplied
calculus. A realization at that time with state dimension `q` is a state `Y` in
a set `Z ⊆ ℝ^q` and a map `Ψ`, standing for `y ↦ (G(y, D(t))(n+i+3/4 − t))_i`,
each coordinate locally Lipschitz on `Z` (the regularity added to (R3)), with
the curve equal to `Ψ(Y)` almost surely.

`rankStatement` is (a): such a realization forces `rank H_{R,n} ≤ q`.
`recurrenceStatement` is (b): if realizations with the same `q` exist for every
`R` and `n` (one realization serving every schedule, as (R4) requires), the
loadings satisfy a recurrence (29.4) of order at most `q`.
`harmonicStatement` is (c): for the harmonic ordinal loadings no `q` works.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.MeetingLoadingCurve
namespace Standalone.MeetingLoadingObstruction

/-- The HJM drift of (29.1). -/
noncomputable def alpha029 (a : ℕ → ℝ) (n R : ℕ) (s T : ℝ) : ℝ :=
  a (count029 n R s T) * ∫ u in s..T, a (count029 n R s u)

/-- The HJM curve at the time `n + 1/2` and the maturity `n + i + 3/4`. -/
noncomputable def curve029 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (a : ℕ → ℝ) (f0 : ℝ → ℝ) (n R : ℕ) (i : ℕ) (ω : Ω) : ℝ :=
  f0 (mat029 n i) + (∫ s in (0:ℝ)..(time029 n : ℝ), alpha029 a n R s (mat029 n i)) +
    S.I k (sigma029 a n R (mat029 n i)) (time029 n) ω

/-- A realization at the time `n + 1/2`, with state dimension `q`. -/
def Realized029 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (a : ℕ → ℝ) (f0 : ℝ → ℝ) (n R q : ℕ) : Prop :=
  ∃ (Y : Ω → Fin q → ℝ) (Z : Set (Fin q → ℝ)) (Ψ : (Fin q → ℝ) → Fin (R+1) → ℝ),
    (∀ i, LocallyLipschitzOn Z fun y => Ψ y i) ∧
    ∀ᵐ ω ∂S.μ, Y ω ∈ Z ∧ ∀ i : Fin (R+1), curve029 S k a f0 n R i ω = Ψ (Y ω) i

def rankStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (f0 : ℝ → ℝ) (R n q : ℕ), Realized029 S k a f0 n R q →
    (hankel029 a R n).rank ≤ q

def recurrenceStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (f0 : ℝ → ℝ) (q : ℕ), (∀ R n, Realized029 S k a f0 n R q) →
    ∃ L ≤ q, ∃ c : Fin L → ℝ, Recurrence029 a L c

def harmonicStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsBrownianReal (S.B k) S.μ →
  ∀ (f0 : ℝ → ℝ) (q : ℕ), ¬ ∀ R n, Realized029 S k harmonic029 f0 n R q

def statement : Prop := rankStatement ∧ recurrenceStatement ∧ harmonicStatement

end Standalone.MeetingLoadingObstruction

import Standalone.MeetingLoadingHankel
import Standalone.ZeroMeanReversionUpstreamBridge
import Standalone.SeparableMeetingShapes

/-! # Claim 029 (a): the curve formula (29.3)

The schedule is `T_m = m` for `m = 1, ..., n+R`; `count029 n R s T` is the
number of meetings in `(s, T]`. With `λ ≡ 1` and constant scale the volatility
(29.1) is `sigma029 a n R T s = a_{i(s,T)}`, deterministic. The time is
`t = n + 1/2` and the maturities are `n + i + 3/4`, `i = 0, ..., R`. The
increments are counted backwards from `t`: `ΔW_0 = W_t − W_n` and
`ΔW_l = W_{n−l+1} − W_{n−l}` for `1 ≤ l ≤ n`.

`curveStatement`: every volatility integrand is in (U4), and almost surely,
simultaneously for all `i`, the driver integral of `σ(·, n+i+3/4)` up to `t`
is `(H_{R,n} ΔW)_i`. The HJM curve at these points is the initial curve plus a
deterministic drift integral plus this integral, so (29.3) holds with the
deterministic `c` collecting the first two; the initial curve enters only
through `c`, as Red's review asks. `driftStatement` is AX-01 for (29.1).
-/

open MeasureTheory
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
namespace Standalone.MeetingLoadingCurve

/-- The number of meetings `T_m = m`, `1 ≤ m ≤ n+R`, in `(s, T]`. -/
noncomputable def count029 (n R : ℕ) (s T : ℝ) : ℕ :=
  ((Finset.range (n+R)).filter fun j : ℕ => s < (j:ℝ) + 1 ∧ (j:ℝ) + 1 ≤ T).card

/-- The volatility (29.1) with `λ ≡ 1` and constant scale, as an integrand. -/
noncomputable def sigma029 {Ω : Type*} (a : ℕ → ℝ) (n R : ℕ) (T : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s _ => a (count029 n R s T)

noncomputable def time029 (n : ℕ) : ℝ≥0 := (n : ℝ≥0) + 1/2

noncomputable def mat029 (n : ℕ) (i : ℕ) : ℝ := (n:ℝ) + i + 3/4

/-- The right end of the `l`-th past piece, counted backwards from `t`. -/
noncomputable def upper029 (n : ℕ) (l : Fin (n+1)) : ℝ≥0 :=
  if (l:ℕ) = 0 then time029 n else ((n - l + 1 : ℕ) : ℝ≥0)

/-- The left end of the `l`-th past piece. -/
noncomputable def lower029 (n : ℕ) (l : Fin (n+1)) : ℝ≥0 := ((n - l : ℕ) : ℝ≥0)

def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (a : ℕ → ℝ) (n R : ℕ),
  (∀ T : ℝ, U4 S.ℱ S.μ (sigma029 (Ω := Ω) a n R T)) ∧
  ∀ᵐ ω ∂S.μ, ∀ i : Fin (R+1),
    S.I k (sigma029 a n R (mat029 n i)) (time029 n) ω =
      ∑ l : Fin (n+1), hankel029 a R n i l *
        (S.B k (upper029 n l) ω - S.B k (lower029 n l) ω)

/-- AX-01 for (29.1) at every time and maturity. -/
def driftStatement : Prop := ∀ (a : ℕ → ℝ) (n R : ℕ) (s T : ℝ),
  (∫ u in s..T, a (count029 n R s u) * (∫ v in s..u, a (count029 n R s v))) =
    (∫ u in s..T, a (count029 n R s u)) ^ 2 / 2

def statement : Prop := curveStatement ∧ driftStatement

end Standalone.MeetingLoadingCurve

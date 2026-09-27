import Standalone.MeetingLoadingCurve
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! # Claim 032 (a): the curve formula (32.4)

Claim 029's schedule `T_m = m`, `1 ≤ m ≤ n + R`, time `t = n + 1/2` and maturities
`T^{(i)} = n + i + 3/4`, now with a quasi-exponential shape `λ(x) = c e^{xA} b` (`lam032`) and
constant scale: `σ(s,T) = a_{i(s,T)} λ(T − s)` (`sigma032`). The past is split into Claim 029's
pieces, piece `l` being `(lower029 n l, upper029 n l]` with right end `τ_l`: piece 0 is `(n, t]`
and piece `l ≥ 1` is `(n − l, n − l + 1]`. The coordinates of `ξ_l = ∫_{piece l} e^{A(τ_l − s)} b dW`
are the integrals of `xiInt032`.

`curveStatement`: the volatility integrands and the `ξ` integrands are in (U4), and almost
surely, simultaneously for all `i`, the driver integral of `σ(·, T^{(i)})` up to `t` is
`∑_{l, j} a_{i+l} (c e^{A(T^{(i)} − τ_l)})_j ξ_{l,j}` (`coef032`). The HJM curve at these points is
the initial curve plus a deterministic drift integral plus this integral, which is (32.4) with
the deterministic `c_i` collecting the first two. The pieces meet at finitely many times, where
the integrands differ; AX-03c's zero-energy argument removes them.
-/

open MeasureTheory Matrix NormedSpace
open scoped NNReal
namespace Standalone.RecurrenceNecessityCurve
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingCurve

variable {r : ℕ}

/-- The quasi-exponential shape `λ(x) = c e^{xA} b`. -/
noncomputable def lam032 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (x : ℝ) :
    ℝ :=
  c ⬝ᵥ (exp (x • A) *ᵥ b)

/-- The volatility (32.1) with constant scale, as an integrand. -/
noncomputable def sigma032 {Ω : Type*} (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (b : Fin r → ℝ) (n R : ℕ) (T : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s _ => a (count029 n R s T) * lam032 c A b (T - s)

/-- The integrand of the coordinate `j` of `ξ_l`. -/
noncomputable def xiInt032 {Ω : Type*} (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (n : ℕ)
    (lj : Fin (n+1) × Fin r) : ℝ≥0 → Ω → ℝ :=
  fun s _ => Set.indicator (Set.Ioc (lower029 n lj.1) (upper029 n lj.1)) 1 s *
    (exp (((upper029 n lj.1 : ℝ) - s) • A) *ᵥ b) lj.2

/-- The coefficient `a_{i+l} (c e^{A(T^{(i)} − τ_l)})_j` of `ξ_{l,j}` in (32.4). -/
noncomputable def coef032 (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (n : ℕ)
    (i : ℕ) (lj : Fin (n+1) × Fin r) : ℝ :=
  a (i + lj.1) * (c ᵥ* exp ((mat029 n i - upper029 n lj.1) • A)) lj.2

def curveStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (a : ℕ → ℝ) (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (n R : ℕ),
  (∀ T : ℝ, U4 S.ℱ S.μ (sigma032 (Ω := Ω) a c A b n R T)) ∧
  (∀ lj, U4 S.ℱ S.μ (xiInt032 (Ω := Ω) A b n lj)) ∧
  ∀ᵐ ω ∂S.μ, ∀ i : Fin (R+1),
    S.I k (sigma032 a c A b n R (mat029 n i)) (time029 n) ω =
      ∑ lj : Fin (n+1) × Fin r, coef032 a c A n i lj * S.I k (xiInt032 A b n lj) (time029 n) ω

def statement : Prop := curveStatement

end Standalone.RecurrenceNecessityCurve

import Standalone.CompoundedFuturesIdentification
import Standalone.BondOptionPriceIntervals
import Mathlib.Data.List.Sort

/-! # Claim 022: the listed SR3 option calendar identifies every meeting variance before its
last expiry

Partial target (formalized early, while the claim is under review). It states: the calendar
facts of (22.1)–(22.3) as exact day-number arithmetic (`calendarStatement`: expiries in date
order, every expiry before its future's Reference Quarter, every meeting after the observation
date and at or before the last expiry, and at most one meeting in each expiry gap); the
surface identity (22.4) from Claim 017's coefficient (`surfaceStatement`); and the abstract
identification (b): with at most one meeting per gap, (22.5) recovers every meeting variance
before the last expiry, two variance vectors with equal accumulated variances agree there, and a
gap holding two meetings leaves their split unidentified (`identificationStatement`); and the
exact arithmetic of the precision bound (c) (`precisionStatement`): the at-the-money price as a
function of the accumulated variance and its inverse `q0178`, the derivative (22.7) of the
inverse as the amplification `2√q/(m φ(√q/2))`, its monotonicity in `q` (the amplification grows
with the accumulated variance), the mean-value bound `Δq ≤ amp(q_max) Δc` that makes the
linearization (22.8)–(22.9) an inequality, and the propagated bound (22.8) on a meeting variance
from the two accumulated variances of its gap; the instantiation of (b) on the calendar
(`calendarIdentificationStatement`): in Claim 011's model with the meeting days as dates, equal
accumulated variances at every listed expiry force equal variance vectors, while with only the
four nearest serials listed the gaps (12 Jun, 11 Sep 2026] and (11 Sep, 11 Dec 2026] hold two
and three meetings and two distinct vectors share every accumulated variance, the title's
second clause; and the futures rows (d) (`futuresRowStatement`): Claim 017's quote coefficient
is `δ(b − T_i)` before the accrual start, `(b − T_i)²` inside the window and zero after, and on
the Dec27 Reference Quarter the coefficient of the 8 December 2027 meeting is `(7/360)²`, that
of the 28 January 2026 meeting `δ · 686/360`, their ratio exactly `1274`, and a half-basis-point
quote perturbation moves the exponent by `1.26·10⁻⁵` and the late variance by `0.033`, a standard
deviation between `18` and `19` percentage points; and the thresholds of the rule (22.10)
(`thresholdStatement`): the coefficient `2/φ(0)` of (22.9) is `2√(2π)`, between `5.01` and
`5.02`, the ratio `Δv_n/s_0² ≈ (2/φ(0)) (ε/s_0)(√n + √(n−1))` is nondecreasing in the meeting
index, and it first reaches one at the fifth meeting for `ε/s_0 = 1/20`, at the tenth for
`ε/s_0 = 1/30`, and stays below one through the sixteenth for `ε/s_0 = 1/50` and for every size at
`ε = 0.25` basis points, the sixteenth meeting at `ε/s_0 = 1/40` lying between `0.98` and `0.99`.
and the `ℓ²` form of the propagated bound (`ellTwoStatement`): the recovery (22.5) with a common
accrual length is the map `q ↦ v = L⁻¹ q/δ²` with `L` the lower triangular matrix of ones, and it
is `2/δ²`-Lipschitz in `ℓ²`, a constant slightly larger than the claim's `1/σ_min(K) =
2cos(π/33)/δ²`; and the displayed values of (22.6) (`singularValueStatement`): under the claim's
formula `σ_k(K) = δ²/(2 sin((2k−1)π/66))`, the smallest value is `δ²/(2cos(π/33))` and lies
between `0.0320` and `0.0322`, the largest lies between `0.671` and `0.672`, and their ratio, the
condition number, between `20.9` and `21`; and the singular-value formula itself
(`eigenStatement`): the lower triangular matrix of ones `L` has the bidiagonal inverse `D`,
`(L Lᵀ)⁻¹ = Dᵀ D`, and for `k = 0, …, n−1` the vectors `x^{(k)}_j = sin((j+1)θ_k)` with
`θ_k = (2k+1)π/(2n+1)` are nonzero eigenvectors of `Dᵀ D` with the strictly increasing
eigenvalues `λ_k = 2 − 2cos θ_k = 4 sin²(θ_k/2)`, hence eigenvectors of `L Lᵀ` with eigenvalues
`1/λ_k`, so the `n` singular values of `L` are `1/(2 sin((2k+1)π/(2(2n+1))))`, which for `n = 16`
are the values `1/(2 sin((2k−1)π/66))` of (22.6); and the exact expression (22.8) at the stated
sizes (`exactPrecisionStatement`), as the claim's check evaluates it with forward `m = 1` and the
common accrual length `δ = 91/360`: the exact ratio `Δv_n/s_0²`, the sum over the two expiries
of the amplification (22.7) at `q = δ² k s_0²` times `δ ε / δ²` over `s_0²`, dominates the ratio
of the rule (22.10) and, for `s_0 ≤ 25` bp and at most sixteen meetings, exceeds it by at most
a factor `1 + 2·10⁻⁶`, is nondecreasing in the meeting index, and satisfies the claim's
thresholds exactly, with the sixteenth meeting at `ε = 0.25` bp, `s_0 = 10` bp between `0.98`
and `0.99`. The day numbers are read from the claim's calendar and the accrual lengths are
ACT/360.
-/

open Finset

namespace Standalone.ListedSr3Identification

/-! ### The calendar of (22.1)–(22.3), as day numbers with 1 January 2026 = 1 -/

/-- FOMC decision days of (22.1). -/
def meetings : List ℕ :=
  [28, 77, 119, 168, 210, 259, 301, 343, 392, 441, 483, 525, 574, 623, 665, 707]
/-- Option expiries of (22.3), merged in date order; expiry `ℓ` belongs to future `ℓ / 3`. -/
def expiries : List ℕ :=
  [16, 44, 72, 100, 135, 163, 191, 226, 254, 289, 317, 345,
   380, 408, 436, 471, 499, 527, 562, 590, 618, 653, 681, 709]
/-- Reference-Quarter start days of (22.2), Jun26 to Mar28. -/
def quarterStarts : List ℕ := [77, 168, 259, 350, 441, 532, 623, 714]
/-- The observation date `t_0 = 2 January 2026`. -/
def t0 : ℕ := 2
/-- The gap endpoints `S_0 = t_0 < S_1 < … < S_24`. -/
def gaps : List ℕ := t0 :: expiries

def calendarStatement : Prop :=
  meetings.length = 16 ∧ expiries.length = 24 ∧
  meetings.Pairwise (· < ·) ∧ expiries.Pairwise (· < ·) ∧
  (∀ ℓ, ℓ < 24 → expiries.getD ℓ 0 < quarterStarts.getD (ℓ / 3) 0) ∧
  (∀ i, i < 16 → t0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ expiries.getD 23 0) ∧
  (∀ ℓ, ℓ < 24 → ((List.range 16).filter (fun i =>
    gaps.getD ℓ 0 < meetings.getD i 0 ∧ meetings.getD i 0 ≤ gaps.getD (ℓ+1) 0)).length ≤ 1)

/-! ### The accumulated variance revealed by an expiry -/

/-- `q(S) = δ² ∑_{T_i ≤ S} v_i` of (22.4). -/
noncomputable def qAcc {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (δ S : ℝ) : ℝ :=
  δ^2 * ∑ i ∈ Finset.univ.filter (fun i => τ (i.val+1) ≤ S), (v i : ℝ)

/-- (a): for an expiry before the accrual start, Claim 017's coefficient is (22.4). -/
def surfaceStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b : ℝ), S < a → a ≤ b →
    (Standalone.CompoundedFuturesIdentification.q τ v S a b : ℝ) = qAcc τ v (b - a) S

/-- (b): with at most one meeting per gap, (22.5) recovers every meeting variance before the
last expiry and equal accumulated variances force equal variances there; a gap holding two
meetings leaves their split unidentified. -/
def identificationStatement : Prop :=
  ∀ (N L : ℕ) (τ : ℕ → ℝ) (S : Fin (L+1) → ℝ) (δ : Fin (L+1) → ℝ),
    StrictMono S → (∀ ℓ, 0 < δ ℓ) →
    ((∀ ℓ : Fin L, ∀ i j : Fin N,
        S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
        S ℓ.castSucc < τ (j.val+1) → τ (j.val+1) ≤ S ℓ.succ → i = j) →
      (∀ (v : Fin N → NNReal) (ℓ : Fin L) (i : Fin N),
        S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
        (v i : ℝ) = qAcc τ v (δ ℓ.succ) (S ℓ.succ)/(δ ℓ.succ)^2 -
          qAcc τ v (δ ℓ.castSucc) (S ℓ.castSucc)/(δ ℓ.castSucc)^2) ∧
      (∀ v v' : Fin N → NNReal, (∀ ℓ, qAcc τ v (δ ℓ) (S ℓ) = qAcc τ v' (δ ℓ) (S ℓ)) →
        ∀ i : Fin N, S 0 < τ (i.val+1) → τ (i.val+1) ≤ S (Fin.last L) → v i = v' i)) ∧
    (∀ (ℓ : Fin L) (i j : Fin N), i ≠ j →
      S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
      S ℓ.castSucc < τ (j.val+1) → τ (j.val+1) ≤ S ℓ.succ →
      ∃ v v' : Fin N → NNReal, v ≠ v' ∧ ∀ ℓ', qAcc τ v (δ ℓ') (S ℓ') = qAcc τ v' (δ ℓ') (S ℓ'))

/-! ### (c) the precision arithmetic -/

/-- The at-the-money amplification (22.7) as a function of the accumulated variance `q`:
`dq/dc = 2√q/(m φ(√q/2))`, with `φ` the standard normal density. -/
noncomputable def amp (m q : ℝ) : ℝ :=
  2 * Real.sqrt q / (m * Standalone.BondOptionPriceIntervals.φ0167 (Real.sqrt q / 2))

/-- (c), the exact arithmetic: for a forward `m > 0`, the at-the-money price of Claim 017's
Gaussian call is `m(2Φ(√q/2) − 1)` and `q0178` recovers `q` from it; `q0178 m` has derivative
(22.7) at every price in `[0, m)`; the amplification is nondecreasing in `q`; the mean-value
bound `q(c') − q(c) ≤ amp(q(c')) (c' − c)`; and, with at most one meeting per gap, the meeting
variance recovered by (22.5) from two variance vectors differs by at most the two accumulated
variance differences scaled by the squared accrual lengths, the exact form of (22.8). -/
def precisionStatement : Prop :=
  ∀ m : ℝ, 0 < m →
    (∀ R : NNReal, Standalone.CompoundedFuturesIdentification.C0177 m R m =
        m * (2 * Standalone.CompoundedFuturesIdentification.Φ (Real.sqrt R / 2) - 1) ∧
      Standalone.CompoundedFuturesIdentification.q0178 m
        (Standalone.CompoundedFuturesIdentification.C0177 m R m) = R) ∧
    (∀ c : ℝ, c ∈ Set.Ico 0 m →
      HasDerivAt (Standalone.CompoundedFuturesIdentification.q0178 m)
        (amp m (Standalone.CompoundedFuturesIdentification.q0178 m c)) c) ∧
    (∀ q q' : ℝ, 0 ≤ q → q ≤ q' → amp m q ≤ amp m q') ∧
    (∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' < m →
      |Standalone.CompoundedFuturesIdentification.q0178 m c' -
          Standalone.CompoundedFuturesIdentification.q0178 m c| ≤
        amp m (Standalone.CompoundedFuturesIdentification.q0178 m c') * (c' - c)) ∧
    ∀ (N L : ℕ) (τ : ℕ → ℝ) (S : Fin (L+1) → ℝ) (δ : Fin (L+1) → ℝ),
      StrictMono S → (∀ ℓ, 0 < δ ℓ) →
      (∀ ℓ : Fin L, ∀ i j : Fin N,
        S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
        S ℓ.castSucc < τ (j.val+1) → τ (j.val+1) ≤ S ℓ.succ → i = j) →
      ∀ (v v' : Fin N → NNReal) (ℓ : Fin L) (i : Fin N),
        S ℓ.castSucc < τ (i.val+1) → τ (i.val+1) ≤ S ℓ.succ →
        |(v i : ℝ) - v' i| ≤
          |qAcc τ v (δ ℓ.succ) (S ℓ.succ) - qAcc τ v' (δ ℓ.succ) (S ℓ.succ)| / (δ ℓ.succ)^2 +
          |qAcc τ v (δ ℓ.castSucc) (S ℓ.castSucc) - qAcc τ v' (δ ℓ.castSucc) (S ℓ.castSucc)| /
            (δ ℓ.castSucc)^2

/-! ### The calendar instantiation of (b) and the reduced listing -/

/-- The meeting dates as Claim 011's scheduled dates, in days from 1 January 2026. -/
noncomputable def τCal (n : ℕ) : ℝ := if n = 0 then 0 else ((meetings.getD (n-1) 0 : ℕ) : ℝ)
/-- The gap endpoints of the full calendar, `S_0 = t_0` and the twenty-four expiries. -/
noncomputable def SFull (ℓ : Fin 25) : ℝ := ((gaps.getD ℓ.val 0 : ℕ) : ℝ)
/-- The expiries available when only the four nearest serials are listed: the serials of
January, February, April and May 2026 and every quarterly expiry. -/
def reducedExpiries : List ℕ := [16, 44, 72, 100, 135, 163, 254, 345, 436, 527, 618, 709]
def reducedGaps : List ℕ := t0 :: reducedExpiries
noncomputable def SRed (ℓ : Fin 13) : ℝ := ((reducedGaps.getD ℓ.val 0 : ℕ) : ℝ)
/-- The meetings in a gap `(lo, hi]`. -/
def meetingsIn (lo hi : ℕ) : List ℕ := meetings.filter (fun T => lo < T ∧ T ≤ hi)

/-- (b) on the calendar and the reduced listing: on the full calendar equal accumulated
variances at every expiry force equal variance vectors; the reduced calendar is a sub-list of
the full one in date order, its gaps up to 12 June 2026 hold at most one meeting each, the gap
(12 Jun, 11 Sep 2026] holds the meetings of 17 June and 29 July and the gap (11 Sep, 11 Dec 2026]
those of 16 September, 28 October and 9 December, and two distinct variance vectors share every
accumulated variance of the reduced calendar. -/
def calendarIdentificationStatement : Prop :=
  (∀ v v' : Fin 16 → NNReal,
    (∀ ℓ : Fin 25, qAcc τCal v (91/360) (SFull ℓ) = qAcc τCal v' (91/360) (SFull ℓ)) → v = v') ∧
  reducedExpiries.Pairwise (· < ·) ∧ (∀ x ∈ reducedExpiries, x ∈ expiries) ∧
  (∀ ℓ, ℓ < 6 → (meetingsIn (reducedGaps.getD ℓ 0) (reducedGaps.getD (ℓ+1) 0)).length ≤ 1) ∧
  meetingsIn 163 254 = [168, 210] ∧ meetingsIn 254 345 = [259, 301, 343] ∧
  ∃ v v' : Fin 16 → NNReal, v ≠ v' ∧
    ∀ ℓ : Fin 13, qAcc τCal v (91/360) (SRed ℓ) = qAcc τCal v' (91/360) (SRed ℓ)

/-! ### (d) the futures rows -/

/-- (d): Claim 017's quote coefficient `h` is `δ(b − T)` for a meeting at or before the accrual
start, `(b − T)²` for a meeting inside the window and zero after it; on the Dec27 Reference
Quarter `[15 Sep 2027, 15 Dec 2027)` the 8 December 2027 meeting has coefficient `(7/360)²`,
the 28 January 2026 meeting `δ · 686/360`, their ratio is exactly `1274`, and a perturbation of
the quote by half a basis point moves the exponent by `δ · 0.5 bp`, between `1.26·10⁻⁵` and
`1.27·10⁻⁵`, hence the late variance by between `0.033` and `0.034`, a standard deviation
between `0.18` and `0.19`. -/
def futuresRowStatement : Prop :=
  (∀ a b T : ℝ, T ≤ a → a ≤ b →
    Standalone.CompoundedFuturesIdentification.h a b T = (b - a) * (b - T)) ∧
  (∀ a b T : ℝ, a < T → T ≤ b → Standalone.CompoundedFuturesIdentification.h a b T = (b - T)^2) ∧
  (∀ a b T : ℝ, a ≤ b → b < T → Standalone.CompoundedFuturesIdentification.h a b T = 0) ∧
  let hLate := Standalone.CompoundedFuturesIdentification.h (623/360) (714/360) (707/360)
  let hFirst := Standalone.CompoundedFuturesIdentification.h (623/360) (714/360) (28/360)
  let Δp : ℝ := (91/360) * (1/2) * (1/10000)
  hLate = (7/360)^2 ∧ hFirst = (91/360) * (686/360) ∧ hFirst / hLate = 1274 ∧
  1.26e-5 < Δp ∧ Δp < 1.27e-5 ∧ 0.033 < Δp / hLate ∧ Δp / hLate < 0.034 ∧
  0.18 < Real.sqrt (Δp / hLate) ∧ Real.sqrt (Δp / hLate) < 0.19

/-! ### The thresholds of the rule (22.10) -/

/-- The ratio `Δv_n/s_0²` of (22.10): `(2/φ(0)) (ε/s_0)(√n + √(n−1))`. -/
noncomputable def ratio (ε s0 : ℝ) (n : ℕ) : ℝ :=
  (2 / Standalone.BondOptionPriceIntervals.φ0167 0) * (ε / s0) *
    (Real.sqrt n + Real.sqrt ((n : ℝ) - 1))

/-- The thresholds of (22.10): the coefficient `2/φ(0) = 2√(2π)` lies between `5.01` and `5.02`;
the ratio is nondecreasing in the meeting index; at `ε = 0.5` bp it first reaches one at the
fifth meeting for `s_0 = 10` bp and at the tenth for `s_0 = 15` bp, and stays below one through
the sixteenth for `s_0 = 25` bp; at `ε = 0.25` bp it stays below one through the sixteenth for
all three sizes, the closest case `s_0 = 10` bp lying between `0.98` and `0.99`. -/
def thresholdStatement : Prop :=
  2 / Standalone.BondOptionPriceIntervals.φ0167 0 = 2 * Real.sqrt (2 * Real.pi) ∧
  (5.01 < 2 / Standalone.BondOptionPriceIntervals.φ0167 0 ∧
    2 / Standalone.BondOptionPriceIntervals.φ0167 0 < 5.02) ∧
  (∀ ε s0 : ℝ, 0 ≤ ε → 0 < s0 → Monotone (fun n : ℕ => ratio ε s0 n)) ∧
  (ratio (1/2) 10 4 < 1 ∧ 1 ≤ ratio (1/2) 10 5) ∧
  (ratio (1/2) 15 9 < 1 ∧ 1 ≤ ratio (1/2) 15 10) ∧
  ratio (1/2) 25 16 < 1 ∧
  (0.98 < ratio (1/4) 10 16 ∧ ratio (1/4) 10 16 < 0.99) ∧
  ratio (1/4) 15 16 < 1 ∧ ratio (1/4) 25 16 < 1

/-! ### The ℓ² form of the propagated bound -/

/-- The recovery (22.5) with a common accrual length, `v_i = (q_i − q_{i−1})/δ²` with `q_0 = 0`. -/
noncomputable def recover (n : ℕ) (δ : ℝ) (q : Fin (n+1) → ℝ) (i : Fin n) : ℝ :=
  (q i.succ - q i.castSucc) / δ^2

/-- The `ℓ²` form of (22.8): the recovery `q ↦ v` is the inverse of the lower triangular matrix of
ones scaled by `δ²`, `q_ℓ = δ² Σ_{i<ℓ} v_i`, and it is `2/δ²`-Lipschitz in `ℓ²`:
`‖Δv‖₂² ≤ (2/δ²)² ‖Δq‖₂²`. -/
def ellTwoStatement : Prop :=
  ∀ (n : ℕ) (δ : ℝ), 0 < δ →
    ∀ q q' : Fin (n+1) → ℝ, q 0 = 0 → q' 0 = 0 →
      (∀ ℓ : Fin (n+1), q ℓ = δ^2 * ∑ i : Fin n, if i.val < ℓ.val then recover n δ q i else 0) ∧
      ∑ i, (recover n δ q i - recover n δ q' i)^2 ≤ (2 / δ^2)^2 * ∑ ℓ, (q ℓ - q' ℓ)^2

/-! ### The displayed values of (22.6) -/

/-- The claim's singular values `σ_k(K) = δ²/(2 sin((2k−1)π/(2(2n+1))))` of the `n × n` matrix
`K = δ² L`, with `δ = 91/360`. -/
noncomputable def sigmaK (n k : ℕ) : ℝ :=
  (91/360 : ℝ)^2 / (2 * Real.sin ((2 * (k : ℝ) - 1) * Real.pi / (2 * (2 * (n : ℝ) + 1))))

/-- The displayed values of (22.6) under the claim's formula: for `n = 16` the smallest value is
`δ²/(2cos(π/33))` and lies between `0.0320` and `0.0322`, the largest lies between `0.671` and
`0.672`, and the condition number between `20.9` and `21`. -/
def singularValueStatement : Prop :=
  sigmaK 16 16 = (91/360 : ℝ)^2 / (2 * Real.cos (Real.pi / 33)) ∧
  (0.0320 < sigmaK 16 16 ∧ sigmaK 16 16 < 0.0322) ∧
  (0.671 < sigmaK 16 1 ∧ sigmaK 16 1 < 0.672) ∧
  (20.9 < sigmaK 16 1 / sigmaK 16 16 ∧ sigmaK 16 1 / sigmaK 16 16 < 21)

/-! ### The singular values of the lower triangular matrix of ones -/

/-- The lower triangular matrix of ones, `L_{ij} = 1` for `j ≤ i`. -/
def Lmat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if j ≤ i then 1 else 0
/-- Its inverse, the bidiagonal difference matrix. -/
def Dmat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then 1 else if j.val + 1 = i.val then -1 else 0
/-- The angles `θ_k = (2k+1)π/(2n+1)`. -/
noncomputable def θ22 (n k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)
/-- The eigenvectors `x^{(k)}_j = sin((j+1)θ_k)`. -/
noncomputable def xvec (n k : ℕ) : Fin n → ℝ := fun j => Real.sin (((j.val : ℝ) + 1) * θ22 n k)
/-- The eigenvalues `λ_k = 2 − 2cos θ_k`. -/
noncomputable def lam22 (n k : ℕ) : ℝ := 2 - 2 * Real.cos (θ22 n k)

/-- The singular values of `L`: `D` inverts `L` on both sides, and for every `k` the vector
`x^{(k)}` is a nonzero eigenvector of `Dᵀ D = (L Lᵀ)⁻¹` with eigenvalue `λ_k = 4 sin²(θ_k/2) > 0`,
hence of `L Lᵀ` with eigenvalue `1/λ_k`; the `λ_k` are strictly increasing in `k`, so these are
the `n` eigenvalues of the symmetric matrix `L Lᵀ`, and for `n = 16` the `1/λ_k` are the squares
of the values `1/(2 sin((2k−1)π/66))` of (22.6). -/
def eigenStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    Lmat n * Dmat n = 1 ∧ Dmat n * Lmat n = 1 ∧
    (∀ k : Fin n, 0 < lam22 n k ∧ lam22 n k = 4 * Real.sin (θ22 n k / 2)^2 ∧ xvec n k ≠ 0 ∧
      ((Dmat n).transpose * Dmat n).mulVec (xvec n k) = lam22 n k • xvec n k ∧
      (Lmat n * (Lmat n).transpose).mulVec (xvec n k) = (1 / lam22 n k) • xvec n k) ∧
    StrictMono (fun k : Fin n => lam22 n k) ∧
    ∀ k : Fin 16, 1 / lam22 16 k = (1 / (2 * Real.sin ((2 * (k : ℝ) + 1) * Real.pi / 66)))^2

/-! ### The exact expression (22.8) at the stated sizes -/

/-- The accrual length of the Jun26 Reference Quarter, `91/360`. -/
noncomputable def δ26 : ℝ := 91 / 360

/-- One term of (22.8) at the forward `m = 1`, with `ε` and `s_0` in basis points: the
amplification (22.7) at the accumulated variance `q_k = δ² k s_0²` of `k` meetings of size `s_0`,
times the price perturbation `δ ε`, over `δ²` and over `s_0²`. -/
noncomputable def exactTerm (ε s0 : ℝ) (k : ℕ) : ℝ :=
  amp 1 (δ26^2 * k * (s0 * 1e-4)^2) * (δ26 * (ε * 1e-4)) / δ26^2 / (s0 * 1e-4)^2

/-- The exact ratio `Δv_n/s_0²` of (22.8) for the `n`-th meeting, obtained from the expiries seeing
`n` and `n − 1` meetings. -/
noncomputable def exactRatio (ε s0 : ℝ) (n : ℕ) : ℝ :=
  exactTerm ε s0 n + exactTerm ε s0 (n - 1)

/-- The exact expression (22.8) at the stated sizes, as the claim's check evaluates it (forward
`m = 1`, common accrual length `δ = 91/360`): the exact ratio dominates the ratio of the rule
(22.10) and, for `s_0 ≤ 25` bp and at most sixteen meetings, exceeds it by at most a factor
`1 + 2·10⁻⁶`; it is nondecreasing in the meeting index; and the thresholds of the claim hold for
it exactly: at `ε = 0.5` bp it first reaches one at the fifth meeting for `s_0 = 10` bp and at
the tenth for `s_0 = 15` bp, and stays below one through the sixteenth for `s_0 = 25` bp; at
`ε = 0.25` bp it stays below one through the sixteenth for all three sizes, the closest case
`s_0 = 10` bp lying between `0.98` and `0.99`. -/
def exactPrecisionStatement : Prop :=
  (∀ (ε s0 : ℝ) (n : ℕ), 0 ≤ ε → 0 < s0 → ratio ε s0 n ≤ exactRatio ε s0 n) ∧
  (∀ (ε s0 : ℝ) (n : ℕ), 0 ≤ ε → 0 < s0 → s0 ≤ 25 → n ≤ 16 →
    exactRatio ε s0 n ≤ (1 + 2e-6) * ratio ε s0 n) ∧
  (∀ ε s0 : ℝ, 0 ≤ ε → 0 < s0 → Monotone (fun n : ℕ => exactRatio ε s0 n)) ∧
  (exactRatio (1/2) 10 4 < 1 ∧ 1 ≤ exactRatio (1/2) 10 5) ∧
  (exactRatio (1/2) 15 9 < 1 ∧ 1 ≤ exactRatio (1/2) 15 10) ∧
  exactRatio (1/2) 25 16 < 1 ∧
  (0.98 < exactRatio (1/4) 10 16 ∧ exactRatio (1/4) 10 16 < 0.99) ∧
  exactRatio (1/4) 15 16 < 1 ∧ exactRatio (1/4) 25 16 < 1

def statement : Prop := calendarStatement ∧ surfaceStatement ∧ identificationStatement ∧
  precisionStatement ∧ calendarIdentificationStatement ∧ futuresRowStatement ∧
  thresholdStatement ∧ ellTwoStatement ∧ singularValueStatement ∧ eigenStatement ∧
  exactPrecisionStatement

end Standalone.ListedSr3Identification

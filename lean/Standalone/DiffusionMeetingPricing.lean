import Standalone.DiffusionMeetingGauss

/-! # Claim 046 (b): the futures martingale and the call price, conditional on `GaussLaw`

In the model of `Standalone.DiffusionMeetingGauss`, **under the hypothesis `GaussLaw` (not derived
in Lean)**:
* `G t a b = E_Q[exp ∫_a^b r | F_t]` is an integrable martingale in `t`, with
  `G_0 = exp(A + p)` almost surely;
* `E_Q[B_S⁻¹] = P(0, S) = exp(−∫_0^S f(0, ·))`, so `Q^S`, with density `B_S⁻¹/P(0, S)`, is a
  probability measure;
* under `Q^S`, `log G_S` has law `N(log m − q/2, q)`, with `z`, `q` and `m` of (46.4);
* the call `C(S, a, b, K) = E_Q[B_S⁻¹ (G_S − K)⁺]` is `P(0, S)` times Claim 017's Black integral
  `C0177 m q K`, which is (46.5).

`surfaceStatement` (deterministic) is the Black form of (46.5) and the recovery of
`(P(0, S), m, q)` from a complete surface; `accumulationStatement` (deterministic) is (46.6).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.DiffusionMeetingPricing
open Standalone.CompoundedFuturesIdentification Standalone.DiffusionMeetingGauss

variable {Ω : Type*} {N : ℕ}

/-- `G_t(a, b) = E_Q[exp ∫_a^b r | F_t]`. -/
noncomputable def G [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (t a b : ℝ) : Ω → ℝ :=
  Q[fun ω => Real.exp (∫ u in a..b, rate M u ω) | M.F t]

/-- The discount factor `B_S⁻¹ = exp(−∫_0^S r)`. -/
noncomputable def disc (M : DiffModel Ω N) (S : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-∫ u in (0:ℝ)..S, rate M u ω)

/-- `P(0, S) = exp(−∫_0^S f(0, u) du)`. -/
noncomputable def P0 (M : DiffModel Ω N) (S : ℝ) : ℝ := Real.exp (-Aint M 0 S)

/-- `z = Σ_i j_i v_i + ∫_0^S σ² w (S − s) ds` (46.4). -/
noncomputable def zdiff (M : DiffModel Ω N) (S a b : ℝ) : ℝ :=
  ∑ i, j S a b (M.T i) * M.v i + ∫ s in (0:ℝ)..S, M.g s * (w a b s * (S - s))

/-- `q = Σ_i k_i v_i + ∫_0^S σ² w² ds` (46.4). -/
noncomputable def qdiff (M : DiffModel Ω N) (S a b : ℝ) : ℝ :=
  ∑ i, k S a b (M.T i) * M.v i + ∫ s in (0:ℝ)..S, M.g s * w a b s ^ 2

/-- `m = exp(A + p − z)` (46.4). -/
noncomputable def mdiff (M : DiffModel Ω N) (S a b : ℝ) : ℝ :=
  Real.exp (Aint M a b + pdiff M a b - zdiff M S a b)

/-- The call `C(S, a, b, K) = E_Q[B_S⁻¹ (G_S − K)⁺]`. -/
noncomputable def call [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (S a b K : ℝ) : ℝ :=
  ∫ ω, disc M S ω * max (G M Q S a b ω - K) 0 ∂Q

/-- `Q^S`, with density `B_S⁻¹/P(0, S)`. -/
noncomputable def QS [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (S : ℝ) : Measure Ω :=
  Q.withDensity fun ω => ENNReal.ofReal (disc M S ω / P0 M S)

def pricingStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
    Integrable (fun ω => Real.exp (∫ u in a..b, rate M u ω)) Q ∧
    (∀ t, Integrable (G M Q t a b) Q) ∧
    (∀ s t, s ≤ t → Q[G M Q t a b | M.F s] =ᵐ[Q] G M Q s a b) ∧
    (G M Q 0 a b =ᵐ[Q] fun _ => Real.exp (Aint M a b + pdiff M a b)) ∧
    ∀ S, 0 ≤ S → S ≤ H →
      ∫ ω, disc M S ω ∂Q = P0 M S ∧ IsProbabilityMeasure (QS M Q S) ∧
      HasLaw (fun ω => Real.log (G M Q S a b ω))
        (gaussianReal (Real.log (mdiff M S a b) - qdiff M S a b / 2) (qdiff M S a b).toNNReal)
        (QS M Q S) ∧
      ∀ K, call M Q S a b K = P0 M S * C0177 (mdiff M S a b) (qdiff M S a b).toNNReal K

/-- (46.5) in Black form, and the recovery of `(P(0, S), m, q)` from a complete surface
`K ↦ P(0, S) · C0177 m q K`, `K > 0`: `P(0, S) = lim_{K↓0} (−∂_K C)`, `P(0, S) m = lim_{K↓0} C`,
and `q = 4 [Φ⁻¹((1 + C(m)/(P(0, S) m))/2)]²`; together they determine `(P(0, S), m, q)`. -/
def surfaceStatement : Prop := ∀ (P m : ℝ) (q : NNReal), 0 < P → 0 < m →
  (∀ K, 0 < K → 0 < q → P * C0177 m q K = P * (m * Φ ((Real.log (m / K) + q / 2) / Real.sqrt q) -
    K * Φ ((Real.log (m / K) + q / 2) / Real.sqrt q - Real.sqrt q))) ∧
  (∀ K, q = 0 → P * C0177 m q K = P * max (m - K) 0) ∧
  Filter.Tendsto (fun K => -deriv (fun K => P * C0177 m q K) K) (nhdsWithin 0 (Set.Ioi 0))
    (nhds P) ∧
  Filter.Tendsto (fun K => P * C0177 m q K) (nhdsWithin 0 (Set.Ioi 0)) (nhds (P * m)) ∧
  4 * Function.invFun Φ ((1 + P * C0177 m q m / (P * m)) / 2) ^ 2 = q ∧
  ∀ (P' m' : ℝ) (q' : NNReal), 0 < P' → 0 < m' →
    ((∀ K, 0 < K → P * C0177 m q K = P' * C0177 m' q' K) ↔ P = P' ∧ m = m' ∧ q = q')

/-- `Q(S) = Σ_{T_i ≤ S} v_i + ∫_0^S σ²`. -/
noncomputable def Qacc (M : DiffModel Ω N) (S : ℝ) : ℝ :=
  ∑ i, (if M.T i ≤ S then M.v i else 0) + ∫ s in (0:ℝ)..S, M.g s

/-- (46.6), for an expiry before accrual, `0 ≤ S < a`: `q = δ² Q(S)` and `z = δ ∫_0^S Q`; and
`z = log G_0 − log m`, free of the initial curve. -/
def accumulationStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N) (S a b : ℝ),
  (∀ i, 0 < M.T i) → Measurable M.g → (∃ C, ∀ s, |M.g s| ≤ C) → 0 ≤ S → S < a → a ≤ b →
    qdiff M S a b = (b - a) ^ 2 * Qacc M S ∧
    zdiff M S a b = (b - a) * (∑ i, (if M.T i ≤ S then (S - M.T i) * M.v i else 0) +
      ∫ s in (0:ℝ)..S, M.g s * (S - s)) ∧
    zdiff M S a b = (b - a) * ∫ x in (0:ℝ)..S, Qacc M x ∧
    zdiff M S a b = (Aint M a b + pdiff M a b) - Real.log (mdiff M S a b)

def statement : Prop := pricingStatement ∧ surfaceStatement ∧ accumulationStatement

end Standalone.DiffusionMeetingPricing

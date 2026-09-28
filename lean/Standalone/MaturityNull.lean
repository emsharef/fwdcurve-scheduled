import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.EReal.Basic

/-! # Claim 051: one exceptional set for all maturities

`(Ω, 𝓕, Q)` is a probability space and `d ≥ 1`. `Q ⊗ dt` on `Ω × [0, ∞)` is
`μ.prod (volume.restrict (Ici 0))`, with points `p = (ω, t)`. The drift `α t u ω` and the
volatility `σ t u ω ∈ ℝ^d` (`EuclideanSpace ℝ (Fin d)`, Euclidean norm and inner product) are
arbitrary functions; no measurability is assumed. The horizon is `H ∈ (0, ∞]`, an `EReal` with
`0 < H`; `H = ⊤` is the published lemma. A maturity `T ≤ H` is a real `T` with `(T : EReal) ≤ H`.

Hypotheses (`Hyp`), in the publication's order:
* (H1) `hypIntegrable`: `(Q ⊗ dt)`-a.e., if `t ≤ H` then `u ↦ α t u ω` and `u ↦ σ t u ω` are
  Lebesgue integrable on `[t, T]` for every maturity `T` with `t ≤ T ≤ H`;
* (H2) `hypDrift`: for every maturity `T ∈ (0, H]`, `(Q ⊗ dt)`-a.e. on `Ω × [0, T]`, (51.1)
  `∫_t^T α(t, u) du = ½ |∫_t^T σ(t, u) du|²`. This is the form of the `drift_integrated` field
  of `Upstream.HJMScheduled` (AX-01), with the same measure `μ.prod (volume.restrict (Icc 0 T))`,
  here taken as a hypothesis; the claim uses no hypothesis structure.

Conclusions, each an almost-everywhere statement for `Q ⊗ dt`, which is the same as one null set
`N` off which the statement holds:
* (a) `integratedStatement`: off one null set, if `t ≤ H` then (51.1) holds for every maturity
  `T` with `t ≤ T ≤ H`;
* (b) `differentiatedStatement`: off one null set, (a) holds and, for every maturity `T` with
  `t < T < H` at which both maturity sections are continuous, (51.2)
  `α(t, T) = ⟨σ(t, T), ∫_t^T σ(t, u) du⟩`;
* (b′) `intervalStatement`: for scheduled dates `0 = T_0 < T_1 < … < T_n`, off one null set, (a)
  holds and, if both maturity sections are continuous on each open interval `(T_k, T_{k+1})`,
  `k < n`, and on `(T_n, ∞)`, then (51.2) holds at every `T ∈ (t, H)` other than `T_1, …, T_n`.
-/

open MeasureTheory Set

namespace Standalone.MaturityNull

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- (51.1) at `(ω, t)` and the maturity `T`. -/
def driftAt (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (ω : Ω) (t T : ℝ) : Prop :=
  ∫ u in t..T, α t u ω = (1 / 2 : ℝ) * ‖∫ u in t..T, σ t u ω‖ ^ 2

/-- (51.2) at `(ω, t)` and the maturity `T`. -/
def diffDriftAt (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (ω : Ω) (t T : ℝ) : Prop :=
  α t T ω = inner ℝ (σ t T ω) (∫ u in t..T, σ t u ω)

/-- (H1): the maturity sections are integrable on `[t, T]` for every maturity `t ≤ T ≤ H`. -/
def hypIntegrable (μ : Measure Ω) (α : ℝ → ℝ → Ω → ℝ)
    (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal) : Prop :=
  ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), (p.2 : EReal) ≤ H →
    ∀ T : ℝ, p.2 ≤ T → (T : EReal) ≤ H →
      IntegrableOn (fun u => α p.2 u p.1) (Icc p.2 T) ∧
      IntegrableOn (fun u => σ p.2 u p.1) (Icc p.2 T)

/-- (H2): (51.1) for every fixed maturity `T ∈ (0, H]`, `(Q ⊗ dt)`-a.e. on `Ω × [0, T]`. -/
def hypDrift (μ : Measure Ω) (α : ℝ → ℝ → Ω → ℝ)
    (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal) : Prop :=
  ∀ T : ℝ, 0 < T → (T : EReal) ≤ H →
    ∀ᵐ p ∂(μ.prod (volume.restrict (Icc 0 T))), driftAt α σ p.1 p.2 T

/-- (a) off one null set. -/
def integratedAt (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal)
    (p : Ω × ℝ) : Prop :=
  (p.2 : EReal) ≤ H → ∀ T : ℝ, p.2 ≤ T → (T : EReal) ≤ H → driftAt α σ p.1 p.2 T

/-- (a): one null set serves every maturity. -/
def integratedStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal),
    0 < H → hypIntegrable μ α σ H → hypDrift μ α σ H →
    ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), integratedAt α σ H p

/-- (b): off the same null set as (a), (51.2) at every interior maturity where both maturity
sections are continuous. -/
def differentiatedStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal),
    0 < H → hypIntegrable μ α σ H → hypDrift μ α σ H →
    ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), integratedAt α σ H p ∧
      ∀ T : ℝ, p.2 < T → (T : EReal) < H →
        ContinuousAt (fun u => α p.2 u p.1) T → ContinuousAt (fun u => σ p.2 u p.1) T →
        diffDriftAt α σ p.1 p.2 T

/-- (b′), the published form: with scheduled dates `0 = T_0 < T_1 < … < T_n` and continuity of
both maturity sections inside each maturity interval, (51.2) at every interior maturity other
than the dates, off the same null set as (a). -/
def intervalStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (α : ℝ → ℝ → Ω → ℝ) (σ : ℝ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (H : EReal)
    (n : ℕ) (τ : ℕ → ℝ), τ 0 = 0 → StrictMonoOn τ (Iic n) →
    0 < H → hypIntegrable μ α σ H → hypDrift μ α σ H →
    ∀ᵐ p ∂(μ.prod (volume.restrict (Ici (0 : ℝ)))), integratedAt α σ H p ∧
      ((∀ k < n, ContinuousOn (fun u => α p.2 u p.1) (Ioo (τ k) (τ (k + 1))) ∧
          ContinuousOn (fun u => σ p.2 u p.1) (Ioo (τ k) (τ (k + 1)))) →
        ContinuousOn (fun u => α p.2 u p.1) (Ioi (τ n)) →
        ContinuousOn (fun u => σ p.2 u p.1) (Ioi (τ n)) →
        ∀ T : ℝ, p.2 < T → (T : EReal) < H → (∀ i, 1 ≤ i → i ≤ n → T ≠ τ i) →
          diffDriftAt α σ p.1 p.2 T)

def statement : Prop := integratedStatement ∧ differentiatedStatement ∧ intervalStatement

end Standalone.MaturityNull

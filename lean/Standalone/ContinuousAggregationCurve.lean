import Standalone.DiffusionMeetingConsistency
import Standalone.DiffusionMeetingPricing

/-! # Claim 054 (b), (d): the post-cutoff curve and the later futures quotes

Claim 046's model `DiffModel`, with its forward curve `fwd` (46.1), short rate `rate`, `Aint`,
`pdiff`, and `Qacc M A = Σ_{T_i ≤ A} v_i + ∫_0^A g`, which is `V_A` of (54.1). For a cutoff `A`:
* `M1 M A = Σ_{T_i ≤ A} T_i v_i + ∫_0^A s g(s) ds`, the `M_{1,A}` of (54.1);
* `yA M A = r_A − f₀(A)`;
* `post M A a b = Σ_{T_i > A} h_i v_i + ∫_A^b g h`, the fixed post-`A` contribution of (54.4).

* `curveStatement`, (54.2), pathwise and deterministic (for `g` measurable and bounded): for
  `0 ≤ A ≤ t` and every `U`,
  `f(t, U) = f₀(U) + y_A + V_A (U − A) + Σ_{A<T_i≤t}[Z_i + v_i(U − T_i)] + (Y_t − Y_A) + ∫_A^t g(s)(U − s) ds`.
* `pdiffSplitStatement`, deterministic: for `0 ≤ A ≤ a ≤ b`,
  `p = δ(b V_A − M_{1,A}) + post`, `δ = b − a`.
* `futuresStatement`, (54.4), **conditional on `GaussLaw`**: for `0 ≤ A ≤ a ≤ b ≤ H`, `G_0(a, b)`
  is almost surely `exp(∫_a^b f₀ + δ(b V_A − M_{1,A}) + post)`.
* `futuresPairStatement`, conditional on `GaussLaw`: two models on the same meeting dates, with
  the same initial curve, the same post-`A` variances, the same `g` on `(A, H]`, and equal
  `(V_A, M_{1,A})`, have equal almost-sure futures quotes `G_0(a, b)` for `A ≤ a ≤ b ≤ H`.
-/

open MeasureTheory

namespace Standalone.ContinuousAggregationCurve
open Standalone.CompoundedFuturesIdentification (h)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw rate Aint pdiff)
open Standalone.DiffusionMeetingPricing (G Qacc)
open Standalone.DiffusionMeetingConsistency (fwd)

variable {Ω : Type*} {N : ℕ}

/-- `M_{1,A} = Σ_{T_i ≤ A} T_i v_i + ∫_0^A s g(s) ds`. -/
noncomputable def M1 (M : DiffModel Ω N) (A : ℝ) : ℝ :=
  ∑ i, (if M.T i ≤ A then M.T i * M.v i else 0) + ∫ s in (0:ℝ)..A, s * M.g s

/-- `y_A = r_A − f₀(A)`. -/
noncomputable def yA (M : DiffModel Ω N) (A : ℝ) (ω : Ω) : ℝ := rate M A ω - M.f0 A

/-- The fixed post-`A` contribution `Σ_{T_i > A} h_i v_i + ∫_A^b g h`. -/
noncomputable def post (M : DiffModel Ω N) (A a b : ℝ) : ℝ :=
  ∑ i, (if A < M.T i then h a b (M.T i) * M.v i else 0) + ∫ s in A..b, M.g s * h a b s

def curveStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N), Measurable M.g →
  (∃ C, ∀ s, |M.g s| ≤ C) → ∀ A t U : ℝ, 0 ≤ A → A ≤ t → ∀ ω,
    fwd M t U ω = M.f0 U + yA M A ω + Qacc M A * (U - A) +
      ∑ i, (if A < M.T i ∧ M.T i ≤ t then M.Z i ω + M.v i * (U - M.T i) else 0) +
      (M.Y t ω - M.Y A ω) + ∫ s in A..t, M.g s * (U - s)

def pdiffSplitStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N), Measurable M.g →
  (∃ C, ∀ s, |M.g s| ≤ C) → ∀ A a b : ℝ, 0 ≤ A → A ≤ a → a ≤ b →
    pdiff M a b = (b - a) * (b * Qacc M A - M1 M A) + post M A a b

def futuresStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ A a b : ℝ, 0 ≤ A → A ≤ a → a ≤ b → b ≤ H →
    G M Q 0 a b =ᵐ[Q]
      fun _ => Real.exp (Aint M a b + (b - a) * (b * Qacc M A - M1 M A) + post M A a b)

def futuresPairStatement : Prop := ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
  (N : ℕ) (Q : Measure Ω) (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
  (M : DiffModel Ω N) (M' : DiffModel Ω' N) (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
  ∀ A a b : ℝ, 0 ≤ A → A ≤ a → a ≤ b → b ≤ H →
    M.f0 = M'.f0 → M.T = M'.T → (∀ i, A < M.T i → M.v i = M'.v i) →
    (∀ s, A < s → s ≤ H → M.g s = M'.g s) → Qacc M A = Qacc M' A → M1 M A = M1 M' A →
    ∀ x x' : ℝ, (G M Q 0 a b =ᵐ[Q] fun _ => x) → (G M' Q' 0 a b =ᵐ[Q'] fun _ => x') → x = x'

def statement : Prop :=
  curveStatement ∧ pdiffSplitStatement ∧ futuresStatement ∧ futuresPairStatement

end Standalone.ContinuousAggregationCurve

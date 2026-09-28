import Standalone.DiffusionMeetingPricing

/-! # Claim 052: two fixed strikes with a known initial curve and a deterministic background

Claim 046's model `Standalone.DiffusionMeetingGauss.DiffModel`, with its definitions `Aint`
(`A₀ = ∫_a^b f(0, u) du`), `P0`, `pdiff`, `zdiff`, `qdiff`, `mdiff` and `call`, and Claim 017's
coefficients `w`, `h`, `j`, `k` and Black integral `C0177`. `K₀ = exp A₀`.

* (a) `meanStatement`, deterministic: for `a ≤ b` and `0 ≤ S ≤ b`, the pointwise identities
  (52.2), `h − w (S − s) = w (b − S) ≥ 0` for `s ≤ S ≤ b` and `h ≥ 0`; then `z ≤ p` and (52.1)
  `m ≥ K₀`. It assumes only `v ≥ 0` and `g` measurable, bounded and nonnegative.
* (b) `scaleStatement`, deterministic: (52.3) `c_{cK}(cM, q) = c · c_K(M, q)` for `c, M > 0`;
  hence `P c_K(m, q)/(P K₀) = c_{K/K₀}(m/K₀, q)`, and `m/K₀ = exp(p − z)`.
* (c) `twoStrikeStatement`, **conditional on `GaussLaw`** for each of two models `M`, `M'` (on
  possibly different probability spaces, with possibly different meetings and backgrounds) whose
  initial curves give the same `A₀ = ∫_a^b f(0, u) du` and the same `P(0, S)` ("the initial bond
  curve is known"; only these two numbers enter, Red's note 3): for `0 ≤ a ≤ b ≤ H`, `0 ≤ S ≤ H`, `S ≤ b` and any `K₁ > K₀`, (52.4)
  equal calls at `K₀` and at `K₁` iff `m = m'` and `q = q'`, including `q = 0`. With `q = 0` the
  call is `P(0, S) (m − K)⁺` and `m = K₀ + C(K₀)/P(0, S)`.
* (d) `futuresStatement`, conditional on `GaussLaw`: the futures quote `G_0(a, b)` is almost surely
  `exp(A₀ + p)`; for any almost-sure value `x` of it, (52.5) `p = log x − A₀` and
  `z = log x − log m`; and equal quotes with equal calls at `K₀`, `K₁` iff `(p, z, q)` agree.
* (e) `surfaceStatement`, conditional on `GaussLaw`: under (c)'s hypotheses, equal calls at `K₀`
  and `K₁` iff equal complete surfaces `K ↦ C(S, a, b, K)`, `K > 0`.
-/

open MeasureTheory ProbabilityTheory

namespace Standalone.TwoStrikeInitialCurve
open Standalone.CompoundedFuturesIdentification (w h j k C0177)
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw Aint pdiff)
open Standalone.DiffusionMeetingPricing (G P0 zdiff qdiff mdiff call)

/-- (a): (52.2), `z ≤ p` and (52.1) `m ≥ K₀`, deterministic. -/
def meanStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N) (S a b : ℝ),
  (∀ i, 0 ≤ M.v i) → Measurable M.g → (∃ C, ∀ s, |M.g s| ≤ C) → (∀ s, 0 ≤ M.g s) →
  a ≤ b → 0 ≤ S → S ≤ b →
    (∀ s, s ≤ S → h a b s - w a b s * (S - s) = w a b s * (b - S)) ∧
    (∀ s, 0 ≤ h a b s) ∧
    zdiff M S a b ≤ pdiff M a b ∧
    Real.exp (Aint M a b) ≤ mdiff M S a b

/-- (b): (52.3), and the price normalized by `P K₀`, deterministic. -/
def scaleStatement : Prop :=
  (∀ (c m : ℝ) (q : NNReal) (K : ℝ), 0 < c → 0 < m → C0177 (c * m) q (c * K) = c * C0177 m q K) ∧
  (∀ (P K₀ m : ℝ) (q : NNReal) (K : ℝ), 0 < P → 0 < K₀ → 0 < m →
    P * C0177 m q K / (P * K₀) = C0177 (m / K₀) q (K / K₀)) ∧
  ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N) (S a b : ℝ),
    mdiff M S a b / Real.exp (Aint M a b) = Real.exp (pdiff M a b - zdiff M S a b)

/-- (c): two strikes `K₀ = exp A₀` and `K₁ > K₀` determine `(m, q)`, conditional on `GaussLaw`;
and the case `q = 0`. -/
def twoStrikeStatement : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (N N' : ℕ) (Q : Measure Ω)
    (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (M : DiffModel Ω N) (M' : DiffModel Ω' N') (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
    ∀ S a b K₁ : ℝ, 0 ≤ a → a ≤ b → b ≤ H → 0 ≤ S → S ≤ H → S ≤ b →
      Aint M a b = Aint M' a b → P0 M S = P0 M' S →
      Real.exp (Aint M a b) < K₁ →
      ((call M Q S a b (Real.exp (Aint M a b)) = call M' Q' S a b (Real.exp (Aint M a b)) ∧
          call M Q S a b K₁ = call M' Q' S a b K₁) ↔
        mdiff M S a b = mdiff M' S a b ∧ qdiff M S a b = qdiff M' S a b) ∧
      (qdiff M S a b = 0 →
        (∀ K, call M Q S a b K = P0 M S * max (mdiff M S a b - K) 0) ∧
        mdiff M S a b = Real.exp (Aint M a b) + call M Q S a b (Real.exp (Aint M a b)) / P0 M S)

/-- (d): the futures quote, (52.5), and identification of `(p, z, q)`, conditional on
`GaussLaw`. -/
def futuresStatement : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (N N' : ℕ) (Q : Measure Ω)
    (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (M : DiffModel Ω N) (M' : DiffModel Ω' N') (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
    ∀ S a b K₁ : ℝ, 0 ≤ a → a ≤ b → b ≤ H → 0 ≤ S → S ≤ H → S ≤ b →
      Aint M a b = Aint M' a b → P0 M S = P0 M' S →
      Real.exp (Aint M a b) < K₁ →
      (G M Q 0 a b =ᵐ[Q] fun _ => Real.exp (Aint M a b + pdiff M a b)) ∧
      ∀ x x' : ℝ, (G M Q 0 a b =ᵐ[Q] fun _ => x) → (G M' Q' 0 a b =ᵐ[Q'] fun _ => x') →
        pdiff M a b = Real.log x - Aint M a b ∧
        zdiff M S a b = Real.log x - Real.log (mdiff M S a b) ∧
        ((x = x' ∧
            call M Q S a b (Real.exp (Aint M a b)) = call M' Q' S a b (Real.exp (Aint M a b)) ∧
            call M Q S a b K₁ = call M' Q' S a b K₁) ↔
          pdiff M a b = pdiff M' a b ∧ zdiff M S a b = zdiff M' S a b ∧
            qdiff M S a b = qdiff M' S a b)

/-- (e): two strikes carry the whole surface, conditional on `GaussLaw`. -/
def surfaceStatement : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (N N' : ℕ) (Q : Measure Ω)
    (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (M : DiffModel Ω N) (M' : DiffModel Ω' N') (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
    ∀ S a b K₁ : ℝ, 0 ≤ a → a ≤ b → b ≤ H → 0 ≤ S → S ≤ H → S ≤ b →
      Aint M a b = Aint M' a b → P0 M S = P0 M' S →
      Real.exp (Aint M a b) < K₁ →
      ((call M Q S a b (Real.exp (Aint M a b)) = call M' Q' S a b (Real.exp (Aint M a b)) ∧
          call M Q S a b K₁ = call M' Q' S a b K₁) ↔
        ∀ K, 0 < K → call M Q S a b K = call M' Q' S a b K)

def statement : Prop :=
  meanStatement ∧ scaleStatement ∧ twoStrikeStatement ∧ futuresStatement ∧ surfaceStatement

end Standalone.TwoStrikeInitialCurve

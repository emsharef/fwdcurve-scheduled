import Standalone.D3EventVariances
import Mathlib.Probability.CDF

/-! # Claim 014: ideal European bond calls in the finite Gaussian model -/

open MeasureTheory ProbabilityTheory
open Standalone.D3EventVariances

namespace Standalone.BondOptionMeetingVariances

noncomputable def C {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S U K : ℝ) : ℝ :=
  ∫ ω, Real.exp (-logB τ v S ω) * max (bond τ v S U ω - K) 0 ∂Q v

noncomputable def QS {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S : ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (Real.exp (-logB τ v S ω)))

noncomputable def z {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S : ℝ) : NNReal :=
  ∑ i ∈ past τ S, v i

noncomputable def q {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S U : ℝ) : NNReal :=
  ((U - S)^2).toNNReal * z τ v S

noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

noncomputable def D0148 {N : ℕ} (v : Fin N → NNReal) (a : Fin N → ℝ) (ω : Ω N) : ℝ :=
  Real.exp (∑ i, (a i * ω i - (v i : ℝ) * a i ^ 2 / 2))

noncomputable def Q0148 {N : ℕ} (v : Fin N → NNReal) (a : Fin N → ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (D0148 v a ω))

noncomputable def L0149 {N : ℕ} (b : ℝ) (c : Fin N → ℝ) (ω : Ω N) : ℝ :=
  b + ∑ i, c i * ω i

def v0146 (ε : NNReal) : Fin 3 → NNReal := ![ε, 2*ε, 3*ε]

def w0146 (ε : NNReal) : Fin 3 → NNReal := ![2*ε, ε, 3*ε]

noncomputable def q0147 (price : ℝ) : ℝ :=
  4 * (Function.invFun Φ ((1+price)/2))^2

noncomputable def z0147 {N : ℕ} (S U price : Fin N → ℝ) (i : Fin N) : ℝ :=
  q0147 (price i)/(U i-S i)^2

noncomputable def v0147 {N : ℕ} (S U price : Fin N → ℝ) (i : Fin N) : ℝ :=
  z0147 S U price i - if h : i.val = 0 then 0 else
    z0147 S U price ⟨i.val-1, by omega⟩

/- The finite-product probability space and bond are exactly Claim 011's definitions.
The last expiry has no finite upper bound. `invFun Φ` is used only at exact model prices,
where strict monotonicity proves the inverse identity. No pricing or Gaussian-law
formula is a hypothesis of this statement. -/
def statement : Prop :=
  (∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
    (∀ S, IsProbabilityMeasure (QS τ v S)) ∧
    (∀ S U, HasLaw (fun ω => Real.log (bond τ v S U ω))
      (gaussianReal (-(q τ v S U : ℝ)/2) (q τ v S U)) (QS τ v S)) ∧
    (∀ S U K, 0 < K → Integrable
      (fun ω => Real.exp (-logB τ v S ω) * max (bond τ v S U ω-K) 0) (Q v)) ∧
    (∀ S U K, 0 < K → 0 < q τ v S U →
      C τ v S U K =
        Φ ((-Real.log K+(q τ v S U : ℝ)/2)/Real.sqrt (q τ v S U)) -
        K*Φ (((-Real.log K+(q τ v S U : ℝ)/2)/Real.sqrt (q τ v S U)) -
          Real.sqrt (q τ v S U))) ∧
    (∀ S U K, q τ v S U = 0 → C τ v S U K = max (1-K) 0) ∧
    (∀ S U, C τ v S U 1 = 2*Φ (Real.sqrt (q τ v S U)/2)-1) ∧
    (∀ S U, C τ v S U 1 ∈ Set.Ico (0 : ℝ) 1) ∧
    (∀ (w : Fin N → NNReal) S U, S < U →
      (C τ v S U 1 = C τ w S U 1 ↔ z τ v S = z τ w S)) ∧
    (∀ (w : Fin N → NNReal) S,
      (∀ U K, S < U → 0 < K → C τ v S U K = C τ w S U K) ↔ z τ v S = z τ w S) ∧
    (∀ S U, q0147 (C τ v S U 1) = (q τ v S U : ℝ)) ∧
    (∀ S U, S < U → q0147 (C τ v S U 1)/(U-S)^2 = (z τ v S : ℝ)) ∧
    (∀ (S U : Fin N → ℝ), StrictMonoOn τ (Set.Iic N) →
      (∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2))) →
      (∀ i, S i < U i) →
      (∀ i, v0147 S U (fun j => C τ v (S j) (U j) 1) i = (v i : ℝ)) ∧
      (∀ w : Fin N → NNReal,
        (∀ i, C τ v (S i) (U i) 1 = C τ w (S i) (U i) 1) → v = w)) ∧
    (τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → ∀ U ω, bond τ v 0 U ω = 1)) ∧
  (∀ ε : NNReal, 0 < ε → v0146 ε ≠ w0146 ε ∧
    (∀ U K, (3 : ℝ) < U → 0 < K → C (fun n => n) (v0146 ε) 3 U K =
      C (fun n => n) (w0146 ε) 3 U K))

end Standalone.BondOptionMeetingVariances

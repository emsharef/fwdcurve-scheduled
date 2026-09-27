import Mathlib.Probability.CondVar
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Claim 013: conditional variance assembly with the complete drift contribution

The stochastic representation, conditional isometry, cross-factor orthogonality and
conditional first-moment integration are hypotheses of `momentStatement`. No Brownian
integral, CIR solution, stochastic product rule, or existence theorem is asserted here.
The deterministic kernels and the affine assembly are given explicitly.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Standalone.StochasticMeetingVariance

noncomputable def E (θ : ℝ → ℝ) (t u : ℝ) : ℝ := Real.exp (-(∫ s in t..u, θ s))

noncomputable def R (θ b : ℝ → ℝ) (T t : ℝ) : ℝ :=
  ∫ s in t..T, b s * E θ t s

def F (g ρ α R : ℝ) : ℝ := g ^ 2 + 2 * ρ * g * α * R + α ^ 2 * R ^ 2

noncomputable def kernel0136 {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ α θ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m) (j : Fin d) (u : ℝ) : ℝ :=
  F (g n j u) (ρ j u) (α j u) (R (θ j) (b n j) (T n) u)

noncomputable def A {m d : ℕ} (K : Fin m → Fin d → ℝ → ℝ)
    (θ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  fun n j => ∫ u in t..T n, K n j u * E (θ j) t u

noncomputable def C {m d : ℕ} (K : Fin m → Fin d → ℝ → ℝ)
    (θ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun n => ∑ j, ∫ u in t..T n, K n j u * (1 - E (θ j) t u)

/-- The conditional centered-square argument for one meeting, with distinct premises
for (13.14), conditional isometry, orthogonality, and conditional moment integration. -/
def momentStatement : Prop :=
  ∀ (Ω : Type) (m₀ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (G : MeasurableSpace Ω), G ≤ m₀ → ∀ (d : ℕ) (Y : Ω → ℝ)
    (Z I01314 : Fin d → Ω → ℝ) (K θ : Fin d → ℝ → ℝ) (v : Fin d → Ω → ℝ) (t T : ℝ),
    (∀ i j, Integrable (fun ω => Z i ω * Z j ω) μ) →
    (Y - μ[Y | G] =ᵐ[μ] fun ω => ∑ j, Z j ω) →
    (∀ j, μ[fun ω => Z j ω ^ 2 | G] =ᵐ[μ] μ[I01314 j | G]) →
    (∀ i j, i ≠ j → μ[fun ω => Z i ω * Z j ω | G] =ᵐ[μ] 0) →
    (∀ j, μ[I01314 j | G] =ᵐ[μ] fun ω =>
      ∫ u in t..T, K j u * (1 + (v j ω - 1) * E (θ j) t u)) →
    Var[Y; μ | G] =ᵐ[μ] fun ω =>
      ∑ j, ∫ u in t..T, K j u * (1 + (v j ω - 1) * E (θ j) t u)

def affineStatement : Prop :=
  ∀ (m d : ℕ) (K : Fin m → Fin d → ℝ → ℝ) (θ : Fin d → ℝ → ℝ)
    (T : Fin m → ℝ) (t : ℝ) (v : Fin d → ℝ) (V : Fin m → ℝ),
    (∀ n, t ≤ T n) → (∀ n j u, 0 ≤ K n j u) → (∀ j u, 0 ≤ θ j u) →
    (∀ j, 0 ≤ v j) →
    (∀ n j, IntervalIntegrable (K n j) volume t (T n)) →
    (∀ n j, IntervalIntegrable (fun u => K n j u * E (θ j) t u) volume t (T n)) →
    (∀ n, V n = ∑ j, ∫ u in t..T n, K n j u * (1 + (v j - 1) * E (θ j) t u)) →
    V = C K θ T t + (A K θ T t).mulVec v ∧
    (∀ n j, 0 ≤ A K θ T t n j) ∧ (∀ n, 0 ≤ C K θ T t n) ∧
    V ∈ {x | ∃ z : Fin d → ℝ, (∀ j, 0 ≤ z j) ∧ x = C K θ T t + (A K θ T t).mulVec z} ∧
    (∀ w, (A K θ T t).transpose.mulVec w = 0 → dotProduct w (V - C K θ T t) = 0) ∧
    (A K θ T t).rank ≤ d ∧
    m - d ≤ Module.finrank ℝ (LinearMap.ker (A K θ T t).transpose.mulVecLin)

/-- The backward equation at any point of continuity of the deterministic coefficients.
Local integrability is explicit; this is not a stochastic product formula. -/
def backwardStatement : Prop :=
  ∀ (θ b : ℝ → ℝ) (T t : ℝ), Measurable θ → Measurable b →
    (∀ a c, IntervalIntegrable θ volume a c) →
    (∀ a c, IntervalIntegrable (fun s => b s * Real.exp (-(∫ u in (0 : ℝ)..s, θ u))) volume a c) →
    ContinuousAt θ t → ContinuousAt b t →
    HasDerivAt (R θ b T) (θ t * R θ b T t - b t) t

def statement : Prop :=
  momentStatement ∧ affineStatement ∧ backwardStatement ∧
  (∀ g ρ α r : ℝ, F g ρ α r = (g + ρ * α * r) ^ 2 + (1 - ρ ^ 2) * (α * r) ^ 2) ∧
  (∀ g ρ α r : ℝ, -1 ≤ ρ → ρ ≤ 1 → 0 ≤ F g ρ α r) ∧
  (∀ (m d : ℕ) (g b : Fin m → Fin d → ℝ → ℝ) (ρ α θ : Fin d → ℝ → ℝ)
    (T : Fin m → ℝ), (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      ∀ n j u, 0 ≤ kernel0136 g b ρ α θ T n j u) ∧
  (∀ θ b T, R θ b T T = 0) ∧
  (∀ θ r b v : ℝ, (θ * r - b) * v + r * (θ * (1 - v)) = θ * r - b * v)

end Standalone.StochasticMeetingVariance

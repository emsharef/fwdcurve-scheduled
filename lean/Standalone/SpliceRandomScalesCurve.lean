import Standalone.SpliceRandomScalesPath
import Standalone.SpliceQuasiExponentialCurve

/-! # Claim 039 (a): the curve with predictable bounded scales, and its random part

The setting is (39.1) with drivers `k₁`, `k₂` of the cited calculus (AX-03): `W^S = B^{k₁}` and
`W^B = ρ_u B^{k₁} + √(1 − ρ_u²) B^{k₂}`. The scales `s_j(u, ω)`, `ρ_u(ω)` and `ψ_u(ω)` are processes
indexed by `u ∈ ℝ`. `Scales039` asks that on `u ≥ 0` they be predictable, that they be bounded,
with `|ρ| ≤ 1`, and that every path be Borel in `u`. The last property follows from
predictability on `u ≥ 0`; it is stated for the pathwise integrals.

`alpha039` is the AX-01 drift on one path,
`σ^S S^S + ψ_u² λΛ(T − u) + ρ_u [σ^S ψ_u Λ(T − u) + ψ_u λ(T − u) S^S]`. `curve039` is the HJM
curve `f(t, T)`: `f(0, T)`, the pathwise drift integral, and the driver integrals of
`σ_1 = σ^S + ρ_u ψ_u λ(T − u)` and `σ_2 = √(1 − ρ_u²) ψ_u λ(T − u)`, maturity by maturity.

`randomStatement` is (a)'s random part. For every `T` and `t`, almost surely, the random part
equals `I_1(s_j)(t) + c e^{AT} (X_1 + X_2)`, with `j` the maturity interval of `T`,
`X_1 = I_1(ρ ψ e^{−A·} b)(t)` and `X_2 = I_2(√(1 − ρ²) ψ e^{−A·} b)(t)` componentwise. The right side
is built from finitely many random variables, the same for every `T`. So it is one version of the
random part, simultaneously in `T`, and it lies in `S⁺ + span{c e^{AT} y}`.
-/

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceRandomScalesCurve
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceRandomScalesPath

variable {r : ℕ}

/-- Predictable bounded scales with Borel paths, `|ρ| ≤ 1`. -/
def Scales039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (s : ℕ → ℝ → Ω → ℝ)
    (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) : Prop :=
  (∀ j, IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => s j u ω)) ∧
  IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => ρ u ω) ∧
  IsStronglyPredictable S.ℱ (fun (u : ℝ≥0) ω => ψ u ω) ∧
  (∀ j ω, Measurable fun u => s j u ω) ∧ (∀ ω, Measurable fun u => ρ u ω) ∧
  (∀ ω, Measurable fun u => ψ u ω) ∧
  (∀ j u ω, |s j u ω| ≤ C) ∧ (∀ u ω, |ρ u ω| ≤ 1) ∧ ∀ u ω, |ψ u ω| ≤ C

/-- The AX-01 drift on one path. -/
noncomputable def alpha039 (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u T : ℝ) : ℝ :=
  sigS033 s Tm u T * SS033 s Tm u T + ψ u ^ 2 * (lam035 c A b (T - u) * Lam035 c A b (T - u)) +
    cross039 ρ ψ s Tm c A b u T

/-- The HJM curve `f(t, T)`, maturity by maturity. -/
noncomputable def curve039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  f0 T + (∫ u in (0:ℝ)..t, alpha039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm
      c A b u T) +
    S.I k₁ (fun u ω => s (idx033 Tm T) u ω + ρ u ω * ψ u ω * lam035 c A b (T - u)) t ω +
    S.I k₂ (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * lam035 c A b (T - u)) t ω

/-- `X_1 + X_2`, the random vector of the version of the random part. -/
noncomputable def Yv039 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (ρ ψ : ℝ → Ω → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (ω : Ω) :
    Fin r → ℝ :=
  (fun i => S.I k₁ (fun u ω => ρ u ω * ψ u ω * (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω) +
    fun i => S.I k₂ (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω *
      (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω

def randomStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ), Scales039 S s ρ ψ C →
  ∀ (Tm : Finset ℝ) (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ) (T : ℝ) (t : ℝ≥0),
  ∀ᵐ ω ∂S.μ,
    S.I k₁ (fun u ω => s (idx033 Tm T) u ω + ρ u ω * ψ u ω * lam035 c A b (T - u)) t ω +
      S.I k₂ (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * lam035 c A b (T - u)) t ω =
    S.I k₁ (fun u ω => s (idx033 Tm T) u ω) t ω + c ⬝ᵥ (exp (T • A) *ᵥ Yv039 S k₁ k₂ ρ ψ A b t ω)

def statement : Prop := randomStatement

end Standalone.SpliceRandomScalesCurve

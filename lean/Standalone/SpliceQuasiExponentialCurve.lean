import Standalone.SpliceQuasiExponentialCross
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 035 (a): the curve and the version of its random part

The setting is `SpliceQuasiExponentialCross`'s, with drivers `k₁`, `k₂` of the cited calculus
(AX-03), `W^S = B^{k₁}` and `W^B = ρ B^{k₁} + √(1 − ρ²) B^{k₂}`. The block volatility is
`σ^B(u, T) = λ(T − u)`, so `S^B(u, T) = Λ(T − u)`. `alpha035` is the AX-01 drift (33.1),
`σ^S S^S + λΛ(T − u) + ρ[σ^S Λ(T − u) + λ(T − u) S^S]`, and `curve035` is the HJM curve `f(t, T)`:
`f(0, T)`, the drift integral, and the driver integrals of `σ_1 = σ^S + ρ σ^B` and
`σ_2 = √(1 − ρ²) σ^B`, maturity by maturity.

`randomStatement`: for every `T` and `t`, almost surely, the random part equals
`I_1(s_j)(t) + c e^{AT} (ρ X_1 + √(1 − ρ²) X_2)`, with `j` the maturity interval of `T` and
`X_k = I_k(e^{−A·} b)(t)` componentwise. The right side is built from finitely many random
variables, the same for every `T`: it is one version of the random part, simultaneously in `T`,
and it lies in `S⁺ + span{c e^{AT} y}`. The identity itself holds for each `T` almost surely.
-/

open Matrix NormedSpace MeasureTheory Set
open scoped NNReal
namespace Standalone.SpliceQuasiExponentialCurve
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceQuasiExponentialCross

variable {r : ℕ}

/-- The AX-01 drift (33.1) with the block factor `λ(T − u)`. -/
noncomputable def alpha035 (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (u T : ℝ) : ℝ :=
  sigS033 s Tm u T * SS033 s Tm u T + lam035 c A b (T - u) * Lam035 c A b (T - u) +
    cross035 ρ s Tm c A b u T

/-- The HJM curve `f(t, T)`, maturity by maturity. -/
noncomputable def curve035 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  f0 T + (∫ u in (0:ℝ)..t, alpha035 ρ s Tm c A b u T) +
    S.I k₁ (fun u _ => sigS033 s Tm u T + ρ * lam035 c A b (T - u)) t ω +
    S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * lam035 c A b (T - u)) t ω

def randomStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k₁ k₂ : Fin S.m) (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ), (∀ i, Measurable (s i)) →
  ∀ C : ℝ, (∀ i u, |s i u| ≤ C) → ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ)
  (ρ T : ℝ) (t : ℝ≥0), ∀ᵐ ω ∂S.μ,
    S.I k₁ (fun u _ => sigS033 s Tm u T + ρ * lam035 c A b (T - u)) t ω +
      S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * lam035 c A b (T - u)) t ω =
    S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω + c ⬝ᵥ (exp (T • A) *ᵥ
      (ρ • (fun i => S.I k₁ (fun u _ => (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω) +
        Real.sqrt (1 - ρ ^ 2) • (fun i => S.I k₂ (fun u _ => (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω)))

def statement : Prop := randomStatement

end Standalone.SpliceQuasiExponentialCurve

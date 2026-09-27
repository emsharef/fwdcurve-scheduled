import Standalone.RecurrentApproxMeanSquare
import Standalone.RecurrentLoadingAlgebra
import Mathlib.Probability.BrownianMotion.Basic

/-! # Claim 048 (b): the bond-price error

The driver `k` of the restated calculus `ItoCalculus` (AX-03) is a Brownian motion
(`IsPreBrownianReal`, the hypothesis of Lemma 032-A). The shape is quasi-exponential, (H1):
`λ(x) = c e^{xA} b` (`shape030 c b A`). Fix `t ≥ 0`.

**The version.** For `s ≤ t ≤ u`, `i(s, u) = i(s, t) + i(t, u)` and `e^{(u−s)A} = e^{(u−t)A} e^{(t−s)A}`,
so `σ(s, u) = Σ_{n ≤ N, j} g_{n,j}(u) h_{n,j}(s)`, with
* `hq048 … t n j s = h_{n,j}(s) = 1{s ≤ t, i(s, t) = n} (e^{(t−s)A} b)_j`;
* `gq048 … t n j u = g_{n,j}(u) = a_{n + i(t,u)} (c e^{(u−t)A})_j`.

With `ζ_{n,j} = ∫_0^t h_{n,j} dW` (`zeta048`), the version is
`V(t, u) = f_0(u) + ∫_0^t α(s, u) ds + Σ_{n,j} g_{n,j}(u) ζ_{n,j}` (`V048`). The same `ζ` serve the
approximating model. The bond price is `P(t, T) = exp(−∫_t^T V(t, u) du)` (`P048`).

`bondStatement`, (b): under the hypotheses of (a), with `f_0` Borel and `|f_0| ≤ F_0` on `[0, H]`,
for `0 ≤ t ≤ T ≤ H`, for each of the two models:
* `V(t, ·)` is measurable in `(ω, u)`, bounded in `u` on `[t, H]`, and, for each `u ∈ [t, H]`,
  `V(t, u) = f(t, u)` almost surely, for the curve `f` of (48.2) (`fwd048`);
* (48.6) `E|log P(t, T) − log P̃(t, T)|² ≤ ε²(Λ²H³ + ¼Ā²Λ⁴H⁶)`;
* (48.7) `E|P(t, T) − P̃(t, T)|² ≤ 2√3 e^{2HF_0 + 5Ā²Λ²H³} ε²(Λ²H³ + ¼Ā²Λ⁴H⁶)`.
-/

open MeasureTheory ProbabilityTheory Matrix NormedSpace
open scoped NNReal

namespace Standalone.RecurrentApproxBond
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxMeanSquare Standalone.ZeroMeanReversionUpstreamBridge

variable {r : ℕ}

/-- `h_{n,j}(s) = 1{s ≤ t, i(s, t) = n} (e^{(t−s)A} b)_j`. -/
noncomputable def hq048 (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ)
    (n : ℕ) (j : Fin r) (s : ℝ) : ℝ :=
  if s ≤ t ∧ count030 Tm s t = n then (exp ((t - s) • A) *ᵥ b) j else 0

/-- `g_{n,j}(u) = a_{n + i(t,u)} (c e^{(u−t)A})_j`. -/
noncomputable def gq048 (Tm : Finset ℝ) (a : ℕ → ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t : ℝ) (n : ℕ) (j : Fin r) (u : ℝ) : ℝ :=
  a (n + count030 Tm t u) * (c ᵥ* exp ((u - t) • A)) j

/-- `ζ_{n,j} = ∫_0^t h_{n,j} dW`. -/
noncomputable def zeta048 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (Tm : Finset ℝ) (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ≥0) (n : ℕ) (j : Fin r) :
    Ω → ℝ :=
  S.I k (fun s _ => hq048 Tm b A t n j s) t

/-- The version `V(t, u) = f_0(u) + ∫_0^t α(s, u) ds + Σ g_{n,j}(u) ζ_{n,j}`. -/
noncomputable def V048 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (f0 : ℝ → ℝ) (Tm : Finset ℝ) (a : ℕ → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t : ℝ≥0) (u : ℝ) (ω : Ω) : ℝ :=
  f0 u + (∫ s in (0:ℝ)..t, alpha048 Tm a (shape030 c b A) s u) +
    ∑ n ∈ Finset.range (Tm.card + 1), ∑ j, gq048 Tm a c A t n j u * zeta048 S k Tm b A t n j ω

/-- The bond price `P(t, T) = exp(−∫_t^T V(t, u) du)`. -/
noncomputable def P048 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (f0 : ℝ → ℝ) (Tm : Finset ℝ) (a : ℕ → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-∫ u in (t:ℝ)..T, V048 S k f0 Tm a c b A t u ω)

def bondStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m),
  IsPreBrownianReal (S.B k) S.μ →
  ∀ (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (a a' : ℕ → ℝ)
    (H Λ ε Abar : ℝ), Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar →
  ∀ (f0 : ℝ → ℝ) (F0 : ℝ), Measurable f0 → (∀ x ∈ Set.Icc 0 H, |f0 x| ≤ F0) →
  ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
    (∀ a₀ : ℕ → ℝ, (a₀ = a ∨ a₀ = a') →
      Measurable (fun p : Ω × ℝ => V048 S k f0 Tm a₀ c b A t p.2 p.1) ∧
      (∀ ω, ∃ C, ∀ u ∈ Set.Icc (t:ℝ) H, |V048 S k f0 Tm a₀ c b A t u ω| ≤ C) ∧
      ∀ u ∈ Set.Icc (t:ℝ) H, (fun ω => V048 S k f0 Tm a₀ c b A t u ω) =ᵐ[S.μ]
        fwd048 S k f0 Tm a₀ (shape030 c b A) t u) ∧
    ∫ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) - Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2
        ∂S.μ ≤ ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4) ∧
    ∫ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 ∂S.μ ≤
      2 * Real.sqrt 3 * Real.exp (2 * H * F0 + 5 * Abar ^ 2 * Λ ^ 2 * H ^ 3) *
        (ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4))

def statement : Prop := bondStatement

end Standalone.RecurrentApproxBond

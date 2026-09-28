import Standalone.RecurrentApproxBond
import Standalone.RecurrentApproxPriceBounds

/-! # Claim 053: the published constants of the approximation theorem

Claim 048's setting (`Standalone.RecurrentApproxEstimates.Hyp048`, the curves `fwd048`, the versions
`V048`, the bond prices `P048`). The paper's `ā` is `Ā` (`Abar`); `ε` is the loading error, `Λ`
bounds `|λ|` on `[0, H]`, and `F₀` bounds `|f₀|` on `[0, H]`. For `0 ≤ t ≤ T ≤ H`, (53.1):
* `B_{t,T} = Λ² t (T − t)² + Ā²Λ⁴ t² T² (T − t)²` (`B053`);
* `E_{t,T} = Ā²Λ² (t T (T − t) + 4 t (T − t)²)` (`E053`);
* `C_H = (4/27) Λ² H³ + (1/16) Ā²Λ⁴ H⁶` (`C053`).

* (a) `forwardStatement`: the forward bounds (`eq:pointbound`), (`eq:uniformbound`) are Claim 048's
  (48.4)–(48.5); this is `Standalone.RecurrentApproxMeanSquare.meanSquareStatement` itself, cited,
  with no new proof.
* (e) `gaussStatement`: if `X ~ N(μ, v)`, `X' ~ N(μ', v')`, `X − X' ~ N(m, w)` and
  `−2μ + 4v ≤ E`, `−2μ' + 4v' ≤ E`, then (53.5) `E|e^{−X} − e^{−X'}|² ≤ √6 e^E (m² + w)`.
* The price statements assume, as Claim 048(b) (`bondStatement`) does, a quasi-exponential shape
  `λ = shape030 c b A` ((H1) of Claim 030), a Brownian driver (`IsPreBrownianReal`) in the cited
  calculus AX-03, and the bond prices `P048` defined from the versions `V048`. For
  `0 ≤ t ≤ T ≤ H`:
  * (b) `pointLogStatement`, (53.2): `E|log P(t, T) − log P̃(t, T)|² ≤ ε² B_{t,T}`;
  * (c) `pointPriceStatement`, (53.3): `E|P(t, T) − P̃(t, T)|² ≤ √6 e^{2F₀(T − t) + E_{t,T}} ε² B_{t,T}`;
  * (d) `uniformStatement`: `B_{t,T} ≤ C_H` and `E_{t,T} ≤ Ā²Λ²H³` (for `0 ≤ t ≤ T ≤ H`), and
    (53.4) `E|log P − log P̃|² ≤ ε² C_H`, `E|P − P̃|² ≤ √6 e^{2HF₀ + Ā²Λ²H³} ε² C_H`.
    These bound each expectation at each fixed `(t, T)`, that is, the supremum of expectations;
    nothing is stated about the expected pathwise supremum.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Standalone.ApproximationConstants
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxBond Standalone.ZeroMeanReversionUpstreamBridge

/-- `B_{t,T}` (53.1). -/
noncomputable def B053 (Λ Abar t T : ℝ) : ℝ :=
  Λ ^ 2 * t * (T - t) ^ 2 + Abar ^ 2 * Λ ^ 4 * t ^ 2 * T ^ 2 * (T - t) ^ 2

/-- `E_{t,T}` (53.1). -/
noncomputable def E053 (Λ Abar t T : ℝ) : ℝ :=
  Abar ^ 2 * Λ ^ 2 * (t * T * (T - t) + 4 * t * (T - t) ^ 2)

/-- `C_H` (53.1). -/
noncomputable def C053 (Λ Abar H : ℝ) : ℝ :=
  4 / 27 * Λ ^ 2 * H ^ 3 + 1 / 16 * Abar ^ 2 * Λ ^ 4 * H ^ 6

/-- (a): Claim 048's (48.4)–(48.5), cited. -/
def forwardStatement : Prop := Standalone.RecurrentApproxMeanSquare.meanSquareStatement

/-- (e): the Gaussian price lemma (53.5). -/
def gaussStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (X X' : Ω → ℝ), Measurable X → Measurable X' →
  ∀ (μ μ' m E : ℝ) (v v' w : ℝ≥0), HasLaw X (gaussianReal μ v) P →
    HasLaw X' (gaussianReal μ' v') P → HasLaw (fun ω => X ω - X' ω) (gaussianReal m w) P →
    -2 * μ + 4 * v ≤ E → -2 * μ' + 4 * v' ≤ E →
    ∫ ω, (Real.exp (-X ω) - Real.exp (-X' ω)) ^ 2 ∂P ≤
      Real.sqrt 6 * Real.exp E * (m ^ 2 + w)

/-- (b): the pointwise log-price bound (53.2). -/
def pointLogStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m),
  IsPreBrownianReal (S.B k) S.μ →
  ∀ (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (a a' : ℕ → ℝ)
    (H Λ ε Abar : ℝ), Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar →
  ∀ (f0 : ℝ → ℝ) (F0 : ℝ), Measurable f0 → (∀ x ∈ Set.Icc 0 H, |f0 x| ≤ F0) →
  ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
    ∫ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) - Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2
        ∂S.μ ≤ ε ^ 2 * B053 Λ Abar t T

/-- (c): the pointwise price bound (53.3). -/
def pointPriceStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω)
  (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (a a' : ℕ → ℝ)
    (H Λ ε Abar : ℝ), Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar →
  ∀ (f0 : ℝ → ℝ) (F0 : ℝ), Measurable f0 → (∀ x ∈ Set.Icc 0 H, |f0 x| ≤ F0) →
  ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
    ∫ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 ∂S.μ ≤
      Real.sqrt 6 * Real.exp (2 * F0 * (T - t) + E053 Λ Abar t T) * (ε ^ 2 * B053 Λ Abar t T)

/-- (d): the uniform bounds (53.4), and `B_{t,T} ≤ C_H`, `E_{t,T} ≤ Ā²Λ²H³`. -/
def uniformStatement : Prop :=
  (∀ Λ Abar H t T : ℝ, 0 ≤ t → t ≤ T → T ≤ H →
    B053 Λ Abar t T ≤ C053 Λ Abar H ∧ E053 Λ Abar t T ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3) ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m),
  IsPreBrownianReal (S.B k) S.μ →
  ∀ (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (Tm : Finset ℝ) (a a' : ℕ → ℝ)
    (H Λ ε Abar : ℝ), Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar →
  ∀ (f0 : ℝ → ℝ) (F0 : ℝ), Measurable f0 → (∀ x ∈ Set.Icc 0 H, |f0 x| ≤ F0) →
  ∀ (t : ℝ≥0) (T : ℝ), (t:ℝ) ≤ T → T ≤ H →
    ∫ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) - Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2
        ∂S.μ ≤ ε ^ 2 * C053 Λ Abar H ∧
    ∫ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 ∂S.μ ≤
      Real.sqrt 6 * Real.exp (2 * H * F0 + Abar ^ 2 * Λ ^ 2 * H ^ 3) * (ε ^ 2 * C053 Λ Abar H)

def statement : Prop := forwardStatement ∧ gaussStatement ∧ pointLogStatement ∧
  pointPriceStatement ∧ uniformStatement

end Standalone.ApproximationConstants

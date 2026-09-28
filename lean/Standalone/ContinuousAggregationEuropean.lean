import Standalone.ContinuousAggregationLevel
import Mathlib.Order.LiminfLimsup

/-! # Claim 054 (b), (c): the post-cutoff state and European post-cutoff cash claims

Claim 046's model. For a cutoff `A` and horizon `H`:
* the post-`A` state space is `State N A H = ℝ^N × ℝ^{ℚ ∩ (A, H]}` (`Rat' A H` is `ℚ ∩ (A, H]`);
* the post-`A` state (`Xi`) is `Ξ = ((1{T_i > A} Z_i)_i, (Y_q − Y_A)_{q ∈ ℚ ∩ (A, H]})`. The claim's
  `E = ℝ^{post} × ℝ^{ℚ ∩ (A, H]}` is the same space with the pre-`A` meeting coordinates removed;
  here they are kept and are identically `0`, so that the state space does not depend on the
  model;
* `J A H t ξ = limsup_n 2^{−n} Σ_{q ∈ 2^{−n}ℤ ∩ (A, t]} ξ_q` (`riem`, `J`), which depends on `ξ`
  only through its coordinates `q ≤ t`. Where the limsup is not finite, Lean's `limsup` on `ℝ` is
  `0` (`J_unbounded`, `J_atBot`), which is the Borel convention of Red's note 2;
* `Lam M A H V t y ξ = ∫_A^t f₀ + y(t − A) + V(t − A)²/2 + Σ_{A<T_i≤t}[ξ_i(t − T_i) + v_i(t − T_i)²/2]
  + J_t(ξ) + ∫_A^t ∫_A^s g(u)(s − u) du ds`, the Borel function `Λ_V` of (b).

`lambdaStatement` (deterministic, for `g`, `f₀` measurable and bounded and `Y` with continuous
paths): for `0 ≤ A ≤ t ≤ H`, on every path, `∫_A^t r = Λ_{V_A}(t, y_A, Ξ)`; `(y, ξ) ↦ Λ_V(t, y, ξ)`
is measurable; and `J_t` depends on `ξ` only through its coordinates `q ≤ t`.

**Conditional on `GaussLaw`:**
* `lawStatement`: `Ξ` is almost everywhere measurable, and under `Q^A` the pair `(y_A, Ξ)` has law
  `N(0, V_A) ⊗ λ_post`, `λ_post = law_Q(Ξ)`;
* `europeanStatement`, (54.3), for Borel `Ψ : ℝ × State → [0, ∞]` and `A ≤ S ≤ H`:
  `E_Q[B_S⁻¹ Ψ(y_A, Ξ)] = P(0, A) ∫ e^{−Λ_{V_A}(S, y, ξ)} Ψ(y, ξ) d(N(0, V_A) ⊗ λ_post)`;
* `postLawPairStatement`: two models on the same meeting dates, with the same post-`A` variances
  and the same `g` on `(A, H]`, have the same `λ_post`;
* `europeanPairStatement`: if moreover they share `f₀` and `V_A`, every European post-`A` cash
  claim `Ψ(y_A, Ξ)` paid at `S ∈ [A, H]` has the same price.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.ContinuousAggregationEuropean
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw rate)
open Standalone.DiffusionMeetingPricing (QS Qacc disc P0)
open Standalone.ContinuousAggregationCurve (yA)

variable {Ω : Type*} {N : ℕ}

/-- The rational times in `(A, H]`. -/
abbrev Rat' (A H : ℝ) := {q : ℚ // A < q ∧ (q : ℝ) ≤ H}

/-- The post-`A` state space. -/
abbrev State (N : ℕ) (A H : ℝ) := (Fin N → ℝ) × (Rat' A H → ℝ)

/-- The post-`A` state `Ξ = ((1{T_i > A} Z_i)_i, (Y_q − Y_A)_q)`. -/
noncomputable def Xi (M : DiffModel Ω N) (A H : ℝ) (ω : Ω) : State N A H :=
  (fun i => if A < M.T i then M.Z i ω else 0, fun q => M.Y q.1 ω - M.Y A ω)

/-- The `j`-th dyadic point `(⌊A 2ⁿ⌋ + j + 1)/2ⁿ` of `(A, t]`. -/
noncomputable def dy (A : ℝ) (n j : ℕ) : ℚ := ((⌊A * 2 ^ n⌋ + j + 1 : ℤ) : ℚ) / 2 ^ n

/-- The dyadic Riemann sum `2^{−n} Σ_{q ∈ 2^{−n}ℤ ∩ (A, t]} ξ_q`; a point above `H` contributes
`0`. -/
noncomputable def riem (A H t : ℝ) (n : ℕ) (ξ : Rat' A H → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (⌊t * 2 ^ n⌋ - ⌊A * 2 ^ n⌋).toNat,
    (if h : A < (dy A n j : ℝ) ∧ (dy A n j : ℝ) ≤ H then ξ ⟨dy A n j, h⟩ else 0) / 2 ^ n

/-- `J_t(ξ) = limsup_n` of the dyadic Riemann sums. -/
noncomputable def J (A H t : ℝ) (ξ : Rat' A H → ℝ) : ℝ :=
  Filter.limsup (fun n => riem A H t n ξ) Filter.atTop

/-- The Borel function `Λ_V(t, y, ξ)` of (b). -/
noncomputable def Lam (M : DiffModel Ω N) (A H V t y : ℝ) (ξ : State N A H) : ℝ :=
  (∫ u in A..t, M.f0 u) + y * (t - A) + V * (t - A) ^ 2 / 2 +
    ∑ i, (if A < M.T i ∧ M.T i ≤ t then
      ξ.1 i * (t - M.T i) + M.v i * (t - M.T i) ^ 2 / 2 else 0) +
    J A H t ξ.2 + ∫ s in A..t, ∫ u in A..s, M.g u * (s - u)

def lambdaStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N), Measurable M.g →
  (∃ C, ∀ s, |M.g s| ≤ C) → Measurable M.f0 → (∃ C, ∀ s, |M.f0 s| ≤ C) →
  (∀ ω, Continuous fun u => M.Y u ω) → ∀ A H t : ℝ, 0 ≤ A → A ≤ t → t ≤ H →
    (∀ ω, ∫ u in A..t, rate M u ω = Lam M A H (Qacc M A) t (yA M A ω) (Xi M A H ω)) ∧
    (∀ V, Measurable fun p : ℝ × State N A H => Lam M A H V t p.1 p.2) ∧
    ∀ ξ ξ' : Rat' A H → ℝ, (∀ q : Rat' A H, (q.1 : ℝ) ≤ t → ξ q = ξ' q) → J A H t ξ = J A H t ξ'

def lawStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ A : ℝ, 0 ≤ A → A ≤ H →
    AEMeasurable (Xi M A H) Q ∧
    (QS M Q A).map (fun ω => (yA M A ω, Xi M A H ω)) =
      (gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))

def europeanStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ A S : ℝ, 0 ≤ A → A ≤ S → S ≤ H → ∀ Ψ : ℝ × State N A H → ℝ≥0∞, Measurable Ψ →
    ∫⁻ ω, ENNReal.ofReal (disc M S ω) * Ψ (yA M A ω, Xi M A H ω) ∂Q =
      ENNReal.ofReal (P0 M A) * ∫⁻ p, ENNReal.ofReal (Real.exp (-Lam M A H (Qacc M A) S p.1 p.2)) *
        Ψ p ∂((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H)))

def postLawPairStatement : Prop := ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
  (N : ℕ) (Q : Measure Ω) (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
  (M : DiffModel Ω N) (M' : DiffModel Ω' N) (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
  ∀ A : ℝ, 0 ≤ A → A ≤ H → M.T = M'.T → (∀ i, A < M.T i → M.v i = M'.v i) →
    (∀ s, A < s → s ≤ H → M.g s = M'.g s) →
    Q.map (Xi M A H) = Q'.map (Xi M' A H)

def europeanPairStatement : Prop := ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
  (N : ℕ) (Q : Measure Ω) (Q' : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
  (M : DiffModel Ω N) (M' : DiffModel Ω' N) (H : ℝ), GaussLaw M Q H → GaussLaw M' Q' H →
  ∀ A S : ℝ, 0 ≤ A → A ≤ S → S ≤ H → M.f0 = M'.f0 → M.T = M'.T →
    (∀ i, A < M.T i → M.v i = M'.v i) → (∀ s, A < s → s ≤ H → M.g s = M'.g s) →
    Qacc M A = Qacc M' A → ∀ Ψ : ℝ × State N A H → ℝ≥0∞, Measurable Ψ →
    ∫⁻ ω, ENNReal.ofReal (disc M S ω) * Ψ (yA M A ω, Xi M A H ω) ∂Q =
      ∫⁻ ω, ENNReal.ofReal (disc M' S ω) * Ψ (yA M' A ω, Xi M' A H ω) ∂Q'

def statement : Prop := lambdaStatement ∧ lawStatement ∧ europeanStatement ∧
  postLawPairStatement ∧ europeanPairStatement

end Standalone.ContinuousAggregationEuropean

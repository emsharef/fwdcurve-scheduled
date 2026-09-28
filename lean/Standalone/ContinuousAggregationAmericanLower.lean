import Standalone.ContinuousAggregationEuropean
import Standalone.ContinuousAggregationSectioning

/-! # Claim 054 (e): the American value, its definitions, and the lower bound

Claim 046's model. `A ≤ S ≤ H` is the exercise window.

* `natural M S t` is the drivers' natural σ-algebra `σ(Z_i : T_i ≤ t) ∨ σ(Y_s : 0 ≤ s ≤ t)`,
  frozen at `S` (exercise times are at most `S`).
* `modelFilt M Q S` is its usual augmentation, `𝔽_t = ⋂_{t' > t} (natural_{t'} ∨ 𝒩_Q)`, on the
  completed space. It is met with the completed σ-algebra only so that it is a filtration of that
  space. Under `GaussLaw` the meet changes nothing (`modelFiltStatement`): every `Y_s` is almost
  surely equal to a measurable Wiener integral.
* `modelTimes` is `𝒯[A, S]`, the `𝔽`-stopping times with values in `[A, S]`.
* `payoff` is `B_τ⁻¹ Φ(τ, y_A, Ξ)` for a Borel `Φ : ℝ × (ℝ × E) → ℝ`, and `Uval` is
  `U = sup_{τ ∈ 𝒯[A, S]} E_Q[B_τ⁻¹ Φ(τ, y_A, Ξ)]`.
* `postFilt` is `σ(Y′, Ξ′_{≤t})` on `ℝ × E`, frozen at `S`. Its usual augmentation under
  `N(0, V_A) ⊗ λ_post` gives the stopping times `𝒯̃[A, S]` of (54.6) (`Sectioning.times`).
* `Pay` is the integrand `e^{−Λ_{V_A}(t, y, ξ)} Φ(t, y, ξ)` of (54.6).

Statements:
* `lamJointStatement`: `Λ_V` is jointly Borel in `(t, y, ξ)` (for `f₀`, `g` measurable and
  bounded). This is (b)'s "Borel function" on `[A, H] × ℝ × E`, which (e) needs.
* `modelFiltStatement`, conditional on `GaussLaw`: a set is in `𝔽_t` if and only if, for every
  `s > t`, it is `Q`-a.e. equal to a set in `natural_s`.
* `lowerStatement`, conditional on `GaussLaw`: under the envelope (54.5),
  `P(0, A) · sup_{ρ ∈ 𝒯̃} ∫ e^{−Λ} Φ d(N(0, V_A) ⊗ λ_post) ≤ U`, and the values defining `U` are
  bounded above. Each `ρ ∈ 𝒯̃` gives the exercise time `ρ(y_A, Ξ) ∈ 𝒯[A, S]` with that value.
  The reverse inequality, which needs (54-R), is stated in `ContinuousAggregationAmerican`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.ContinuousAggregationAmericanLower
open Standalone.DiffusionMeetingGauss (DiffModel GaussLaw)
open Standalone.DiffusionMeetingPricing (Qacc disc P0)
open Standalone.ContinuousAggregationCurve (yA)
open Standalone.ContinuousAggregationEuropean (Rat' State Xi Lam)
open Standalone.ContinuousAggregationSectioning (times value₂)

variable {Ω : Type*} {N : ℕ}

/-- `σ(Z_i : T_i ≤ t ∧ S) ∨ σ(Y_s : 0 ≤ s ≤ t ∧ S)`. -/
def natural (M : DiffModel Ω N) (S t : ℝ) : MeasurableSpace Ω :=
  (⨆ (i : Fin N) (_ : M.T i ≤ min t S), MeasurableSpace.comap (M.Z i) inferInstance) ⊔
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ min t S), MeasurableSpace.comap (M.Y s) inferInstance

/-- The usual augmentation `𝔽_t = ⋂_{t' > t} (natural_{t'} ∨ 𝒩_Q)` on the completed space. -/
noncomputable def modelFilt [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (S : ℝ) :
    Filtration ℝ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω Q)) where
  seq t := (⨅ s ∈ Ioi t, eventuallyMeasurableSpace (natural M S s) (ae Q)) ⊓ inferInstance
  mono' := fun _ _ h => inf_le_inf_right _ (le_iInf₂ fun s hs => iInf₂_le s (lt_of_le_of_lt h hs))
  le' := fun _ => inf_le_right

/-- `𝒯[A, S]`. -/
def modelTimes [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (A S : ℝ) :
    Set (NullMeasurableSpace Ω Q → ℝ) :=
  {τ | (∀ ω, τ ω ∈ Icc A S) ∧ IsStoppingTime (modelFilt M Q S) (fun ω => (τ ω : WithTop ℝ))}

/-- `B_τ⁻¹ Φ(τ, y_A, Ξ)`. -/
noncomputable def payoff (M : DiffModel Ω N) (A H : ℝ) (Φ : ℝ × (ℝ × State N A H) → ℝ)
    (τ : Ω → ℝ) (ω : Ω) : ℝ :=
  disc M (τ ω) ω * Φ (τ ω, (yA M A ω, Xi M A H ω))

/-- `U = sup_{τ ∈ 𝒯[A, S]} E_Q[B_τ⁻¹ Φ(τ, y_A, Ξ)]`. -/
noncomputable def Uval [MeasurableSpace Ω] (M : DiffModel Ω N) (Q : Measure Ω) (A S H : ℝ)
    (Φ : ℝ × (ℝ × State N A H) → ℝ) : ℝ :=
  sSup ((fun τ => ∫ ω, payoff M A H Φ τ ω ∂Q.completion) '' modelTimes M Q A S)

/-- `σ(Y′, Ξ′_{≤t ∧ S})` on `ℝ × E`. -/
def postFilt (M : DiffModel Ω N) (A H S : ℝ) :
    Filtration ℝ (inferInstance : MeasurableSpace (ℝ × State N A H)) where
  seq t := MeasurableSpace.comap Prod.fst inferInstance ⊔
    (⨆ (i : Fin N) (_ : M.T i ≤ min t S),
      MeasurableSpace.comap (fun p : ℝ × State N A H => p.2.1 i) inferInstance) ⊔
    ⨆ (q : Rat' A H) (_ : (q.1 : ℝ) ≤ min t S),
      MeasurableSpace.comap (fun p : ℝ × State N A H => p.2.2 q) inferInstance
  mono' := fun _ _ h => sup_le_sup (sup_le_sup le_rfl (iSup_mono fun _ =>
      iSup_mono' fun hi => ⟨hi.trans (min_le_min_right _ h), le_rfl⟩))
    (iSup_mono fun _ => iSup_mono' fun hq => ⟨hq.trans (min_le_min_right _ h), le_rfl⟩)
  le' := fun _ => sup_le (sup_le measurable_fst.comap_le (iSup₂_le fun i _ =>
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).comap_le))
    (iSup₂_le fun q _ => ((measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)).comap_le)

/-- `e^{−Λ_{V_A}(t, y, ξ)} Φ(t, y, ξ)`. -/
noncomputable def Pay (M : DiffModel Ω N) (A H : ℝ) (Φ : ℝ × (ℝ × State N A H) → ℝ)
    (q : ℝ × (ℝ × State N A H)) : ℝ :=
  Real.exp (-Lam M A H (Qacc M A) q.1 q.2.1 q.2.2) * Φ q

def lamJointStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N), Measurable M.g →
  (∃ C, ∀ s, |M.g s| ≤ C) → Measurable M.f0 → (∃ C, ∀ s, |M.f0 s| ≤ C) → ∀ A H V : ℝ,
    Measurable fun q : ℝ × (ℝ × State N A H) => Lam M A H V q.1 q.2.1 q.2.2

def modelFiltStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ S : ℝ, S ≤ H → ∀ (t : ℝ) (B : Set Ω),
    MeasurableSet[modelFilt M Q S t] B ↔
      ∀ s, t < s → ∃ C, MeasurableSet[natural M S s] C ∧ B =ᵐ[Q] C

def lowerStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (N : ℕ) (Q : Measure Ω)
  [IsProbabilityMeasure Q] (M : DiffModel Ω N) (H : ℝ), GaussLaw M Q H →
  ∀ A S : ℝ, 0 ≤ A → A ≤ S → S ≤ H →
  ∀ (Φ : ℝ × (ℝ × State N A H) → ℝ) (D : ℝ × State N A H → ℝ), Measurable Φ → Measurable D →
    Integrable D ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))) →
    (∀ t ∈ Icc A S, ∀ p, |Pay M A H Φ (t, p)| ≤ D p) →
    BddAbove ((fun τ => ∫ ω, payoff M A H Φ τ ω ∂Q.completion) '' modelTimes M Q A S) ∧
    (∀ ρ ∈ times ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H)))
        (postFilt M A H S) A S,
      (fun ω : NullMeasurableSpace Ω Q => ρ (yA M A ω, Xi M A H ω)) ∈ modelTimes M Q A S ∧
      ∫ ω, payoff M A H Φ (fun ω => ρ (yA M A ω, Xi M A H ω)) ω ∂Q.completion =
        P0 M A * ∫ p, Pay M A H Φ (ρ p, p)
          ∂((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H))).completion) ∧
    P0 M A * value₂ ((gaussianReal 0 (Qacc M A).toNNReal).prod (Q.map (Xi M A H)))
      (postFilt M A H S) A S (Pay M A H Φ) ≤ Uval M Q A S H Φ

def statement : Prop := lamJointStatement ∧ modelFiltStatement ∧ lowerStatement

end Standalone.ContinuousAggregationAmericanLower

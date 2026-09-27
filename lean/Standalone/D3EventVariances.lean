import Standalone.D2Instance
import Mathlib.Probability.CondVar
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.Order.LeftRightLim

/-!
# Claim 011: explicit scalar curve and arbitrary Gaussian meeting variances

Coordinates are indexed by `Fin N`, with date `τ (i.val + 1)`. The measure and filtration
below are the product Borel measure and the uncompleted coordinate filtration. Completion,
the path-space Markov assertion, and the ideal option half-moment are separate targets;
see the claim's Formalization notes for the exact scope of the proved statement.
-/

open MeasureTheory ProbabilityTheory

namespace Standalone.D3EventVariances

abbrev Ω (N : ℕ) := Fin N → ℝ

noncomputable def Q {N : ℕ} (v : Fin N → NNReal) : Measure (Ω N) :=
  Measure.infinitePi fun i => gaussianReal 0 (v i)

def filt {N : ℕ} (τ : ℕ → ℝ) : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N)) where
  seq t := ⨆ (i : Fin N) (_ : τ (i.val + 1) ≤ t),
    MeasurableSpace.comap (fun ω : Ω N => ω i) inferInstance
  mono' := fun _ _ hst => iSup_mono fun _ => iSup_mono' fun h => ⟨h.trans hst, le_rfl⟩
  le' := fun _ => iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

noncomputable def past {N : ℕ} (τ : ℕ → ℝ) (t : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => τ (i.val + 1) ≤ t

noncomputable def X {N : ℕ} (τ : ℕ → ℝ) (t : ℝ) (ω : Ω N) : ℝ :=
  ∑ i ∈ past τ t, ω i

noncomputable def curve {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (t x T : ℝ) : ℝ := x + ∑ i ∈ past τ t, (v i : ℝ) * (T - τ (i.val + 1))

noncomputable def f {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (t T : ℝ) (ω : Ω N) : ℝ := curve τ v t (X τ t ω) T

noncomputable def ξ {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (i : Fin N) (u : ℝ) (ω : Ω N) : ℝ :=
  if τ (i.val + 1) ≤ u then ω i + (v i : ℝ) * (u - τ (i.val + 1)) else 0

noncomputable def ξNat {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (n : ℕ) (u : ℝ) (ω : Ω N) : ℝ :=
  if h : 1 ≤ n ∧ n ≤ N then ξ τ v ⟨n - 1, by omega⟩ u ω else 0

noncomputable def factor {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (T : ℝ) (i : Fin N) (ω : Ω N) : ℝ :=
  Real.exp (-((T - τ (i.val + 1)) * ω i + (v i : ℝ) * (T - τ (i.val + 1)) ^ 2 / 2))

noncomputable def discounted {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (T t : ℝ) (ω : Ω N) : ℝ := ∏ i ∈ past τ t, factor τ v T i ω

noncomputable def logB {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (t : ℝ) (ω : Ω N) : ℝ :=
  ∑ i ∈ past τ t, ((t - τ (i.val + 1)) * ω i + (v i : ℝ) * (t - τ (i.val + 1)) ^ 2 / 2)

noncomputable def bond {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (t T : ℝ) (ω : Ω N) : ℝ := Real.exp (-(∫ u in t..T, f τ v t u ω))

noncomputable def Δr {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (i : Fin N) (ω : Ω N) : ℝ :=
  f τ v (τ (i.val + 1)) (τ (i.val + 1)) ω -
    Function.leftLim (fun t => f τ v t t ω) (τ (i.val + 1))

def statement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    -- The jump condition, with its actual conditional expectation and interval integral.
    (∀ (i : Fin N) (T : ℝ), τ (i.val + 1) ≤ T →
      (Q v)[fun ω => Real.exp (-(∫ u in τ (i.val + 1)..T, ξ τ v i u ω)) |
        D2Instance.leftLimit (filt τ) (τ (i.val + 1))] =ᵐ[Q v] 1) ∧
    -- The normalized products (11.9) are true martingales, not merely local ones.
    (∀ T, Martingale (discounted τ v T) (filt τ) (Q v)) ∧
    (∀ t ω, 0 ≤ t → ∫ s in (0 : ℝ)..t, f τ v s s ω = logB τ v t ω) ∧
    (∀ t T ω, bond τ v t T ω / Real.exp (logB τ v t ω) = discounted τ v T t ω) ∧
    -- The forward equation and scalar parametrization.
    (∀ t T ω, t ≤ T → f τ v t T ω = ∑ i ∈ past τ t, ξ τ v i T ω) ∧
    (∀ t T, Function.Injective (fun x : ℝ => curve τ v t x T)) ∧
    (∀ s t (ω : Ω N), s ≤ t → X τ t ω = X τ s ω +
      ∑ i ∈ past τ t \ past τ s, ω i) ∧
    (∀ i ω, Δr τ v i ω = ω i) ∧
    -- Every prescribed meeting variance is recovered before the meeting.
    (∀ (i : Fin N) (t : ℝ), t < τ (i.val + 1) →
      Var[Δr τ v i; Q v | filt τ t] =ᵐ[Q v] fun _ => (v i : ℝ)) ∧
    -- Varying model parameters yields precisely the nonnegative orthant.
    Set.range (fun w : Fin N → NNReal => fun i => Var[fun ω : Ω N => ω i; Q w]) =
      {w : Fin N → ℝ | ∀ i, 0 ≤ w i}

end Standalone.D3EventVariances

import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 026: integrals on one time interval

The supplied AX-03/AX-04 calculus gives the stochastic integral masked to
(lo, hi], with its (U4) domain, adaptedness, continuous paths, start and freeze
identities. No finite expected energy, SDE existence or Markov closure is assumed.
The calculus is the existing standalone mirror of the audited input.
-/

open MeasureTheory ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge
open scoped NNReal
namespace Standalone.SeparableMeetingIntegrals

noncomputable def H026 {Ω : Type*} (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0) :
    ℝ≥0 → Ω → ℝ := fun s ω =>
  (Set.indicator (Set.Iic hi) (fun _ => (1:ℝ)) s * chi s ω) -
  (Set.indicator (Set.Iic lo) (fun _ => (1:ℝ)) s * chi s ω)

noncomputable def J026 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  S.I k (H026 chi lo hi)

def statement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0), lo ≤ hi → U4 S.ℱ S.μ chi →
  (∀ s ω, H026 chi lo hi s ω = if lo < s ∧ s ≤ hi then chi s ω else 0) ∧
  U4 S.ℱ S.μ (H026 chi lo hi) ∧
  Adapted S.ℱ (J026 S k chi lo hi) ∧
  (∀ᵐ ω ∂S.μ, Continuous fun t => J026 S k chi lo hi t ω) ∧
  (∀ᵐ ω ∂S.μ, ∀ t, J026 S k chi lo hi t ω =
    S.I k chi (min t hi) ω - S.I k chi (min t lo) ω) ∧
  (∀ᵐ ω ∂S.μ, ∀ t,
    (t ≤ lo → J026 S k chi lo hi t ω = 0) ∧
    (hi ≤ t → J026 S k chi lo hi t ω = J026 S k chi lo hi hi ω)) ∧
  (∀ (a : ℝ) t, S.I k (a • H026 chi lo hi) t =ᵐ[S.μ] a • J026 S k chi lo hi t)

end Standalone.SeparableMeetingIntegrals

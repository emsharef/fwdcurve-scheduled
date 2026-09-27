import Standalone.RecurrenceNecessityRank
import Standalone.RecurrenceNecessityGaussian
import Standalone.RecurrenceNecessityAlgebra

/-! # Claim 032: assembly

`necessityStatement` is (b). The driver is a pre-Brownian motion and the shape
`λ(x) = c e^{xA} b` is not identically zero. If realizations (`Realized032`, Claim 029's notion)
with the same state dimension `q` exist for every `R` and `n`, as one realization serving every
schedule gives by (R4), then the loadings satisfy a recurrence (29.4) of order at most `q + 1`.
The initial curve is any deterministic curve.

`characterizationStatement` is (c). For a nonzero quasi-exponential shape, from the zero initial
curve, realizations with a common `q` for every `R` and `n` exist if and only if the loadings
are linearly recurrent. Sufficiency is Claim 030's construction: the state is `Ξ_t`, with the
companion data of (H2).

`statement` gathers Claim 032: the Hankel-to-recurrence step (`RecurrenceNecessityAlgebra`),
Lemma 032-A (`RecurrenceNecessityGaussian`), the reduction and (32.3)
(`RecurrenceNecessityReduction`), the curve formula (32.4) (`RecurrenceNecessityCurve`), the rank
bound (a) (`RecurrenceNecessityRank`), (b) and (c).
-/

open MeasureTheory ProbabilityTheory
namespace Standalone.RecurrenceNecessityAssembly
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.MeetingLoadingHankel
open Standalone.RecurrenceNecessityCurve Standalone.RecurrenceNecessityRank

def necessityStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (f0 : ℝ → ℝ) (q : ℕ),
  (∃ x : ℝ, lam032 c A b x ≠ 0) → (∀ R n : ℕ, Realized032 S k a c A b f0 n R q) →
  ∃ L ≤ q + 1, ∃ coef : Fin L → ℝ, Recurrence029 a L coef

def characterizationStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω)
  (S : ItoCalculus Ω) (k : Fin S.m), IsPreBrownianReal (S.B k) S.μ →
  ∀ (a : ℕ → ℝ) (r : ℕ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
  (∃ x : ℝ, lam032 c A b x ≠ 0) →
  ((∃ q : ℕ, ∀ R n : ℕ, Realized032 S k a c A b (fun _ => 0) n R q) ↔
    ∃ (L : ℕ) (coef : Fin L → ℝ), Recurrence029 a L coef)

def statement : Prop :=
  Standalone.RecurrenceNecessityAlgebra.statement ∧ Standalone.RecurrenceNecessityGaussian.statement ∧
  Standalone.RecurrenceNecessityReduction.statement ∧ Standalone.RecurrenceNecessityCurve.statement ∧
  Standalone.RecurrenceNecessityRank.statement ∧ necessityStatement ∧ characterizationStatement

end Standalone.RecurrenceNecessityAssembly

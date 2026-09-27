import Standalone.SpliceLocalizationConverse

/-! # Claim 050 (c): the Section 2 regularity of the converse's curve

Red's note 1, now in the proof of (c): the curve built by the conditional converse also satisfies
the regularity conditions of Section 2, in particular local integrability in maturity. Here that is
the existence of maturity-uniform envelopes, integrable in time.

* `sigEnvStatement`: there is a constant `C`, depending only on `c`, `A`, `d` and `H`, with
  `|σ_l(u, T)| ≤ Σ_m |V_{m,l}(u)| + C (Σ_μ |H^{0,μ}_l(u)| + Σ_i |H^ζ_{i,l}(u)|)` for `0 ≤ u ≤ T ≤ H`.
  This is `sup_{T ≤ H} |σ(u, T)|² ≤ C′(Σ_m |V_m(u)|² + Σ_k |H^k(u)|²)`.
* `alphaEnvStatement`: likewise
  `|α(u, T)| ≤ Σ_m (|dL_m(u)| + |H| |dC_m(u)|) + C (Σ_μ (|b_{0,μ}| + |z_{0,μ}|) + Σ_i (|b_{ζ,i}| + |ζ_i|))`.
* `envelopeStatement`: under (c)'s hypotheses (`SpliceLocalizationConverse`), the `σ`-envelope is
  square integrable on `[0, H]`. With the converse's drifts, the `α`-envelope is integrable.

Progressive measurability in `(t, T)` concerns the filtration, and is not formalized.
-/

open Matrix NormedSpace MeasureTheory Set

namespace Standalone.SpliceLocalizationRegularity
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse

def sigEnvStatement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (S : Finset ℝ) (H : ℝ), ∃ C : ℝ, ∀ (p : Pt049 k r) (u T : ℝ), 0 ≤ u → u ≤ T → T ≤ H →
    ∀ l, |sig049 c A d S p u T l| ≤ (∑ m ∈ Finset.range (S.card + 1), |p.V m l|) +
      C * ((∑ μ ∈ Finset.range (d + 1), |p.Hp μ l|) + ∑ i, |p.Hz i l|)

def alphaEnvStatement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (S : Finset ℝ) (H : ℝ), ∃ C : ℝ, ∀ (p : Pt049 k r) (u T : ℝ), 0 ≤ u → u ≤ T → T ≤ H →
    |alpha049 c A d S p u T| ≤ (∑ m ∈ Finset.range (S.card + 1), (|p.dL m| + |H| * |p.dC m|)) +
      C * ((∑ μ ∈ Finset.range (d + 1), (|p.bP μ| + |p.zP μ|)) + ∑ i, (|p.bZ i| + |p.z i|))

def envelopeStatement : Prop := ∀ (k r d : ℕ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (D : ℝ → Pt049 k r),
  (∀ m ≤ S.card, ∀ l, MemLp (fun u => (D u).V m l) 2 (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, ∀ l, MemLp (fun u => (D u).Hp μ l) 2 (volume.restrict (Icc 0 H))) →
  (∀ i l, MemLp (fun u => (D u).Hz i l) 2 (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, Integrable (fun u => (D u).bP μ) (volume.restrict (Icc 0 H))) →
  (∀ i, Integrable (fun u => (D u).bZ i) (volume.restrict (Icc 0 H))) →
  (∀ μ ≤ d, Integrable (fun u => (D u).zP μ) (volume.restrict (Icc 0 H))) →
  (∀ i, Integrable (fun u => (D u).z i) (volume.restrict (Icc 0 H))) →
  ∀ C : ℝ,
    (∀ l, MemLp (fun u => (∑ m ∈ Finset.range (S.card + 1), |(D u).V m l|) +
      C * ((∑ μ ∈ Finset.range (d + 1), |(D u).Hp μ l|) + ∑ i, |(D u).Hz i l|)) 2
        (volume.restrict (Icc 0 H))) ∧
    Integrable (fun u => (∑ m ∈ Finset.range (S.card + 1),
      (|dL050 c A d S (D u) u m| + |H| * |dC050 c A d S (D u) u m|)) +
      C * ((∑ μ ∈ Finset.range (d + 1), (|(D u).bP μ| + |(D u).zP μ|)) +
        ∑ i, (|(D u).bZ i| + |(D u).z i|))) (volume.restrict (Icc 0 H))

def statement : Prop := sigEnvStatement ∧ alphaEnvStatement ∧ envelopeStatement

end Standalone.SpliceLocalizationRegularity

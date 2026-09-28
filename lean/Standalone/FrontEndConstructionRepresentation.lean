import Standalone.FrontEndConstructionProcess
import Standalone.SpliceLocalizationRegularity

/-! # Claim 055 (c): the assembled representation satisfies (2.2)

The Setting of `FrontEndConstructionProcess` (conditional on the cited calculus AX-03 to AX-05).
For deterministic initial values `l₀ m`, `c₀ m`, put, for `0 ≤ t ≤ T ≤ H`,
`f(t, T) = L_{n(T)}(t) + C_{n(T)}(t) T + F(T − t, Z_t)` (`fwd`, (`eq:splice`)), with the block (49.1)
`F(x, z) = Σ_μ z_{0,μ} x^μ + c e^{xA} ζ` (`Fblock`). The front-end drifts are the matching ones of (a),
so the pointwise data is `matched D`.

Statements:
* `representationStatement`, (c)(i): for every `T ∈ [0, H]`,
  - every coordinate `σ_l(·, T) = sig049(D(·), ·, T)_l` is a (U4) integrand;
  - almost surely, for all `t ≤ T`,
    `f(t, T) = f(0, T) + ∫_0^t α(u, T) du + Σ_l ∫_0^t σ_l(u, T) dB^l_u`, with
    `α(u, T) = alpha049(matched D(u), u, T)` and `σ` as above. These are the coefficients of
    Claims 049–050.
* `regularityStatement`, (c)(ii), the regularity of Section 2:
  - for each `T`, `α(·, T)` and each `σ_l(·, T)` are progressively measurable;
  - `α` and `σ_l` are jointly measurable in `(u, T, ω)`, hence Borel in `T` for fixed `(u, ω)`;
  - almost surely there are envelopes `E_σ`, square integrable on `[0, H]`, and `E_α`, integrable
    on `[0, H]`, with `|σ_l(u, T)| ≤ E_σ(u)` and `|α(u, T)| ≤ E_α(u)` for `0 ≤ u ≤ T ≤ H`. So
    `sup_{T ≤ H} |σ(u, T)|²` and `sup_{T ≤ H} |α(u, T)|` are integrable on `[0, H]`.
-/

open MeasureTheory Set Matrix
open scoped NNReal

namespace Standalone.FrontEndConstructionRepresentation
open Standalone.ZeroMeanReversionUpstreamBridge (ItoCalculus U4 LocallyIntegrableDrift driverForm)
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.FrontEndConstructionMatching Standalone.FrontEndConstructionProcess

/-- The block (49.1), `F(x, z) = Σ_μ z_{0,μ} x^μ + c e^{xA} ζ`. -/
noncomputable def Fblock {d r : ℕ} (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ)
    (z : Fin (d + 1 + r) → ℝ) : ℝ :=
  (∑ μ : Fin (d + 1), z (pIdx μ) * x ^ (μ : ℕ)) + ephi c A x ⬝ᵥ fun i => z (zIdx i)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `f(t, T) = L_{n(T)}(t) + C_{n(T)}(t) T + F(T − t, Z_t)`. -/
noncomputable def fwd (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (l₀ c₀ : ℕ → ℝ) (t : ℝ≥0) (T : ℝ) (ω : Ω) : ℝ :=
  Lproc IC c A S H x₀ HB KB V (nS S T) (l₀ (nS S T)) t ω +
    Cproc IC c A S H x₀ HB KB V (nS S T) (c₀ (nS S T)) t ω * T +
    Fblock c A (T - t) (driverForm IC.I x₀ HB KB t ω)

def representationStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (IC : ItoCalculus Ω)
  (d r : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ)
  (x₀ : Fin (d + 1 + r) → ℝ) (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ)
  (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ) (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ), Setting IC HB KB V →
  ∀ (l₀ c₀ : ℕ → ℝ) (T : ℝ), 0 ≤ T → T ≤ H →
    (∀ l, U4 IC.ℱ IC.μ fun s ω => sig049 c A d S (pt IC x₀ HB KB V s ω) s T l) ∧
    ∀ᵐ ω ∂IC.μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      fwd IC c A S H x₀ HB KB V l₀ c₀ t T ω = fwd IC c A S H x₀ HB KB V l₀ c₀ 0 T ω +
        (∫ s in (0 : ℝ)..t,
          alpha049 c A d S (matched c A d S (pt IC x₀ HB KB V s ω) s) s T) +
        ∑ l, IC.I l (fun s ω => sig049 c A d S (pt IC x₀ HB KB V s ω) s T l) t ω

def regularityStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (IC : ItoCalculus Ω)
  (d r : ℕ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ)
  (x₀ : Fin (d + 1 + r) → ℝ) (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ)
  (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ) (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ), Setting IC HB KB V →
    (∀ T, IsStronglyProgressive IC.ℱ fun (s : ℝ≥0) ω =>
      alpha049 c A d S (matched c A d S (pt IC x₀ HB KB V s ω) s) s T) ∧
    (∀ T l, IsStronglyProgressive IC.ℱ fun (s : ℝ≥0) ω =>
      sig049 c A d S (pt IC x₀ HB KB V s ω) s T l) ∧
    Measurable (fun q : ℝ × ℝ × Ω =>
      alpha049 c A d S (matched c A d S (pt IC x₀ HB KB V q.1 q.2.2) q.1) q.1 q.2.1) ∧
    (∀ l, Measurable fun q : ℝ × ℝ × Ω => sig049 c A d S (pt IC x₀ HB KB V q.1 q.2.2) q.1 q.2.1 l) ∧
    ∀ᵐ ω ∂IC.μ, ∃ Eσ Eα : ℝ → ℝ, MemLp Eσ 2 (volume.restrict (Icc 0 H)) ∧
      Integrable Eα (volume.restrict (Icc 0 H)) ∧ ∀ u T, 0 ≤ u → u ≤ T → T ≤ H →
        (∀ l, |sig049 c A d S (pt IC x₀ HB KB V u ω) u T l| ≤ Eσ u) ∧
        |alpha049 c A d S (matched c A d S (pt IC x₀ HB KB V u ω) u) u T| ≤ Eα u

def statement : Prop := representationStatement ∧ regularityStatement

end Standalone.FrontEndConstructionRepresentation

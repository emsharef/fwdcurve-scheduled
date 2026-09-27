import Standalone.LemmaA
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 009 (the non-vacuity instance for D2): statement only

An explicit member of the step-plus-ramp family satisfies every field of the hypothesis
structure `Upstream.HJMScheduled` of `ledger/AXIOMS.md`
(`math/claims/009-d2-instance.md`, Part (a)).

The instance. Dates `τ 0 = 0 < … < τ N` with the intervals `I_k` of Claim 002, step
volatilities `s k ∈ ℝ^d`, slope jumps `y n k ≥ 0` (as `NNReal`). The index set is
`P = {(n, k) : 1 ≤ n ≤ k ≤ N}`, the sample space `Ω = ℝ^P`, the measure `Q` the product of the
centered Gaussians `N(0, y n k)` (`Measure.infinitePi` of `gaussianReal`; `N(0, 0) = δ_0`), the
coordinates `X n k`, and the filtration `F_t = σ(X_{m,k} : (m, k) ∈ P, τ m ≤ t)`. The
coefficients are (9.1) `σ(t, T) = s_k` for `T ∈ I_k`, `T ≥ t`, and `0` for `T < t`; (9.2)
`α(t, T) = ⟪σ(t, T), ∫_t^T σ(t, u) du⟫` for `T ≥ t` and `0` for `T < t`; (9.3)
`ξ_n(u) = X_{n,k} + y_{n,k} (u - τ k)` for `u ∈ I_k`, `k ≥ n`, and `0` for `u < τ n`; and
`f(0, ·)` any Borel function bounded on `[0, T]` for every `T > 0`.

A statement-only file may import Mathlib and `Standalone` only, so the fields of
`Upstream.HJMScheduled` are restated here for this instance, spelled exactly as the structure's
fields, with `leftLimit` and `paramFiltration` copied from `lean/Upstream/HJMScheduled.lean`.
The proof file `lean/Novel/D2InstanceProof.lean` also packages the instance as a value of
`Upstream.HJMScheduled`, as the claim's Review asks. AX-01 is stated pointwise, for every `ω`,
`0 ≤ t` and `T ≥ t`, as the claim does, and in the field's `(Q ⊗ dt)`-a.e. form. Part (b)
(membership in `S⁺`, needing a Brownian motion) is not a Lean target of the claim.

Encoding choices. The step `u ↦ s_k` on `I_k` is the finite sum of indicators
`∑_{k ≤ N} 1_{I_k}(u) s_k` (so `0` for `u < 0`), and (9.3) likewise. `N ≥ 1` is not assumed.
-/

open MeasureTheory ProbabilityTheory

namespace Standalone.D2Instance

open Standalone.LemmaA

/-- The index set `P = {(n, k) : 1 ≤ n ≤ k ≤ N}` of the level jumps. -/
def P (N : ℕ) : Type := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ N}

/-- The sample space `Ω = ℝ^P`, with its product (Borel) σ-algebra. -/
abbrev Ω (N : ℕ) : Type := P N → ℝ

/-- `Q = ⊗_{(n, k) ∈ P} N(0, y_{n,k})`. -/
noncomputable def Q (N : ℕ) (y : ℕ → ℕ → NNReal) : Measure (Ω N) :=
  Measure.infinitePi fun p : P N => gaussianReal 0 (y p.1.1 p.1.2)

/-- The coordinate `X_{n,k}` for `(n, k) ∈ P`, and `0` for the unused pairs. -/
noncomputable def X (N n k : ℕ) (ω : Ω N) : ℝ :=
  if h : 1 ≤ n ∧ n ≤ k ∧ k ≤ N then ω ⟨(n, k), h⟩ else 0

/-- `F_t = σ(X_{m,k} : (m, k) ∈ P, τ m ≤ t)`. -/
def filt (N : ℕ) (τ : ℕ → ℝ) : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N)) where
  seq t := ⨆ (p : P N) (_ : τ p.1.1 ≤ t),
    MeasurableSpace.comap (fun ω : Ω N => ω p) inferInstance
  mono' := fun _ _ hst => iSup_mono fun _ => iSup_mono' fun h => ⟨h.trans hst, le_rfl⟩
  le' := fun _ => iSup₂_le fun p _ => (measurable_pi_apply p).comap_le

variable {d : ℕ}

/-- (2.2): the deterministic step `u ↦ s_k` for `u ∈ I_k`, `k ≤ N`, and `0` for `u < 0`. -/
noncomputable def step (τ : ℕ → ℝ) (N : ℕ) (s : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ k ∈ Finset.range (N + 1), (I τ N k).indicator (fun _ => s k) u

/-- (9.1): `σ(t, T) = s_k` for `T ∈ I_k` with `T ≥ t`, and `0` for `T < t`. -/
noncomputable def σ (τ : ℕ → ℝ) (N : ℕ) (s : ℕ → EuclideanSpace ℝ (Fin d)) (t T : ℝ)
    (_ : Ω N) : EuclideanSpace ℝ (Fin d) :=
  if T < t then 0 else step τ N s T

/-- (9.2): the differentiated HJM drift `α(t, T) = ⟪σ(t, T), ∫_t^T σ(t, u) du⟫` for `T ≥ t`,
and `0` for `T < t`. -/
noncomputable def α (τ : ℕ → ℝ) (N : ℕ) (s : ℕ → EuclideanSpace ℝ (Fin d)) (t T : ℝ)
    (ω : Ω N) : ℝ :=
  if T < t then 0 else inner ℝ (σ τ N s t T ω) (∫ u in t..T, σ τ N s t u ω)

/-- (9.3): `ξ_n(u) = X_{n,k} + y_{n,k} (u - τ k)` for `u ∈ I_k`, `k ≥ n`, and `0` for
`u < τ n`. -/
noncomputable def ξ (τ : ℕ → ℝ) (N : ℕ) (y : ℕ → ℕ → NNReal) (n : ℕ) (u : ℝ) (ω : Ω N) :
    ℝ :=
  ∑ k ∈ Finset.Ico n (N + 1), (I τ N k).indicator (fun u => X N n k ω + y n k * (u - τ k)) u

section Copies

/-! The two auxiliary definitions of `lean/Upstream/HJMScheduled.lean`, copied verbatim. -/

variable {Ω' : Type*} {m₀ : MeasurableSpace Ω'}

set_option warn.classDefReducibility false in
/-- `ℱ_(t)⁻ = ⨆ s < t, ℱ s` (as `Upstream.leftLimit`). -/
def leftLimit (ℱ : Filtration ℝ m₀) (t : ℝ) : MeasurableSpace Ω' :=
  ⨆ s < t, ℱ s

/-- The filtration `t ↦ ℬ(ℝ) ⊗ ℱ t` on `ℝ × Ω'` (as `Upstream.paramFiltration`). -/
def paramFiltration (ℱ : Filtration ℝ m₀) :
    Filtration ℝ (Prod.instMeasurableSpace : MeasurableSpace (ℝ × Ω')) where
  seq t := MeasurableSpace.prod inferInstance (ℱ t)
  mono' _ _ hst :=
    sup_le_sup (MeasurableSpace.comap_mono le_rfl) (MeasurableSpace.comap_mono (ℱ.mono hst))
  le' t := sup_le_sup (MeasurableSpace.comap_mono le_rfl) (MeasurableSpace.comap_mono (ℱ.le t))

end Copies

def statement : Prop :=
  ∀ (N d : ℕ) (τ : ℕ → ℝ) (s : ℕ → EuclideanSpace ℝ (Fin d)) (y : ℕ → ℕ → NNReal)
    (f₀ : ℝ → ℝ),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    Measurable f₀ → (∀ T : ℝ, 0 < T → ∃ C : ℝ, ∀ u ∈ Set.Icc 0 T, |f₀ u| ≤ C) →
    let μ := Q N y
    let ℱ := filt N τ
    let α := α τ N s
    let σ := σ τ N s
    let ξ := ξ τ N y
    -- the fields of `Upstream.HJMScheduled`, in the ledger's order
    IsProbabilityMeasure μ ∧
    τ 0 = 0 ∧ StrictMonoOn τ (Set.Iic N) ∧
    -- (S7), Assumption 3.3(i)
    Measurable f₀ ∧ (∀ T : ℝ, 0 < T → IntegrableOn f₀ (Set.Icc 0 T)) ∧
    -- (S7), Assumption 3.3(ii)
    IsStronglyProgressive (paramFiltration ℱ) (fun t (p : ℝ × Ω N) => α t p.1 p.2) ∧
    (∀ t T ω, T < t → α t T ω = 0) ∧
    (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂μ,
      ∫⁻ u in Set.Icc 0 T, ∫⁻ s in Set.Icc 0 u, ENNReal.ofReal |α s u ω| < ⊤) ∧
    -- (S7), Assumption 3.3(iii)
    IsStronglyProgressive (paramFiltration ℱ) (fun t (p : ℝ × Ω N) => σ t p.1 p.2) ∧
    (∀ t T ω, T < t → σ t T ω = 0) ∧
    (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂μ,
      ∑ i, ∫⁻ u in Set.Icc 0 T,
        (∫⁻ s in Set.Icc 0 u, ENNReal.ofReal ((σ s u ω i) ^ 2)) ^ (1 / 2 : ℝ) < ⊤) ∧
    -- (S7), Assumption 3.3(v)
    (∀ n, 1 ≤ n → n ≤ N →
      Measurable[MeasurableSpace.prod inferInstance (ℱ (τ n))] fun p : ℝ × Ω N => ξ n p.1 p.2) ∧
    (∀ n, 1 ≤ n → n ≤ N → ∀ u ω, u < τ n → ξ n u ω = 0) ∧
    (∀ n, 1 ≤ n → n ≤ N → ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂μ,
      ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal |ξ n u ω| < ⊤) ∧
    -- AX-01, pointwise: for every `ω`, `0 ≤ t` and `T ≥ t`
    (∀ (ω : Ω N) (t T : ℝ), 0 ≤ t → t ≤ T →
      ∫ u in t..T, α t u ω = (1 / 2 : ℝ) * ‖∫ u in t..T, σ t u ω‖ ^ 2) ∧
    -- AX-01, the field `drift_integrated`
    (∀ T : ℝ, 0 < T →
      ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Icc 0 T))),
        ∫ u in p.2..T, α p.2 u p.1 = (1 / 2 : ℝ) * ‖∫ u in p.2..T, σ p.2 u p.1‖ ^ 2) ∧
    -- AX-02, the field `jump_martingale`
    (∀ n, 1 ≤ n → n ≤ N → ∀ T : ℝ, τ n ≤ T →
      μ[fun ω => Real.exp (-(∫ u in τ n..T, ξ n u ω)) | leftLimit ℱ (τ n)] =ᵐ[μ] 1)

end Standalone.D2Instance

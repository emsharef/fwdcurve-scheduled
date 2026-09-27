import Standalone.ZeroMeanReversionVarianceSupport
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Claim 015, Upstream bridge: consuming the audited stochastic-calculus fields

Partial target for the route prescribed by the policy of 2026-09-22: the remaining stochastic
inputs of Claim 015 are consumed from the hypothesis structure `Upstream.ItoCalculus`
(ledger entries AX-03 to AX-05, audited field by field at 4197cd057) rather than built in
`lean/Novel/`. The structure is restated here verbatim, as `lean/Standalone/D2Instance.lean`
restates `Upstream.HJMScheduled`, so that this file imports no `Upstream` module.

Proved in this partial target:

* `extensionStatement`: the backward exponential `E0152` of (15.17), which has a pole past the
  horizon, agrees on `(-∞, T]` with a globally `C²` function of `(s, x)`; this is the function
  to which the Itô-formula field AX-05 (which requires global `C²`) is applied.
* `zeroIntegralStatement`: under the fields, the integral of the zero integrand vanishes almost
  surely simultaneously in time; this identifies the driver-form process of AX-05 with the
  variance state written with one driver per coordinate.

* `itoStatement`: the Itô representation (15.20) from the field AX-05: for variance states
  solving the zero-mean-reversion equation written with `I`, with one driver per coordinate
  carrying the identity covariation, the backward exponential up to the horizon equals its
  initial value plus the driver integrals of the (U4) integrands `Gint`; the drift term of
  the field cancels on the horizon by the frozen development's generator identity.

* `localizationStatement`: `H0152` of the frozen development for the actual variance states,
  under the same hypotheses with continuous adapted paths and an initial value at most one: the
  localizers `σ01521` of the frozen development, read as stopping times of the structure's
  filtration, stop the driver integrals by the field AX-04b; the stopped integrands are bounded,
  hence (U5), so the field AX-03c makes the stopped representation a square-integrable
  martingale, which is the stopped backward exponential.

* `localizationAeStatement`: the same with the paths continuous only almost surely, as the
  field AX-03a delivers them: the state is modified on a null set of the initial σ-algebra
  (usual conditions), the integral operator respects integrands that agree almost surely at
  all times (from AX-03b, the diagonal case of AX-03c, and AX-03a's zero and continuity
  clauses), and the stopped exponential of the original state is adapted and equal almost
  surely to that of the modification.

* `transformStatement`: the frozen development's consequences of `H0152`, now for the actual
  states under the fields: the terminal law (15.2) as the product transition law, the
  conditional transform (15.13) in the structure's filtration, the regular conditional
  transition kernel, and the independence, moments, martingale property, zero-scale constancy,
  conditional moments and absorption of the state coordinates.

* `incrementStatement`: the conditional isometry and orthogonality of increments of the driver
  integrals over `[t, T]` given `F_t`, from AX-03c applied to the integrands cut off before
  `t` (AX-04b with the constant stopping time `t`); this is the tool for the conditional
  isometry and cross-factor orthogonality fields of `H0154`.

* `twoDriverIsometryStatement` and `crossFactorStatement`: the conditional isometry (15.28)
  of a two-driver increment `∫_t^T Hw dB^{kw} + ∫_t^T Hu dB^{ku}` and the conditional
  orthogonality of two such increments on drivers with zero cross covariation, in the
  abstract form of the first, third and fourth `H0154` fields, from `incrementStatement`.

* `coefficientStatement` and `actualIncrementStatement`: the coefficient integrands
  `K √v_j` with measurable locally bounded `K` are square integrable on every horizon, by
  Tonelli against the state mean `E v_j(s) = v_j(0)` of `transformStatement` and the
  predictability of the SDE integrand `√v_j`; hence the actual two-driver increments
  satisfy the conditional isometry with the covariation integrands `K₁² c v_j`,
  `2 K₁ K₂ c v_j`, `K₂² c v_j`, and the cross-factor orthogonality.

* `kernelIsometryStatement`: the first, third and fourth `H0154` fields for the actual
  increments `Z_{n,j}` of (15.27) with the source's full kernel `K0154`: the three covariation
  integrals combine into `I_{n,j}` along the almost surely continuous paths, with the drivers'
  covariations `1`, `ρ_j`, `1`.

* `productRuleStatement`: the product rule (15.26) from the field AX-05 applied to
  `f(s, x) = R(s) x_j` for a `C²` weight `R` with `R' = −b`: the drift is `−b v_j`, the
  second derivatives vanish, and only the factor's own driver survives; with `R(T) = 0` this
  is the backward-integral identity `∫_t^T b v_j = R(t) v_j(t) + ∫_t^T R α_j √v_j dU_j`.

* `backwardWeightStatement` and `centeredStatement`: the backward weight of a `C¹`
  coefficient is a `C²` weight of the product rule, and the second `H0154` field: the actual
  meeting jump (15.24) is integrable and its centered residual given `F_t` is the sum of the
  two-driver increments `Z_{n,j}`, by the product rule at the horizon and the martingale
  property of the driver integrals (AX-03c).

* `assemblyStatement`: the five `H0154` fields assembled from the fields for the jumps and
  increments defined from them, through the frozen development's integration assembly, which
  supplies the fifth field and the affine identity of the actual conditional jump variances.

* `meetingVarianceFromFieldsStatement`: the actual meeting-variance law, its exact support
  and the conditional versions of the frozen `localizedMeetingVarianceStatement`, now with
  `H0152` and `H0154` derived from the fields rather than assumed.

* `productRuleACStatement`: the product rule for an absolutely continuous weight
  `R(s) = R₀ − ∫_0^s b` with `b` merely measurable and locally integrable, by applying AX-05
  to the product of the state coordinate with a deterministic drift-only coordinate; this
  removes the smoothness of the drift coefficient assumed by `productRuleStatement`.

* `centeredACStatement`, `assemblyACStatement`, `meetingVarianceFromFieldsACStatement`: the
  centered representation, the five `H0154` fields with the affine identity, and the
  meeting-variance law with its exact support, for measurable locally integrable drift
  coefficients `b_{n,j}` in place of `C¹` ones, through the absolutely continuous product rule.

* `assemblyAeStatement`, `meetingVarianceFromFieldsAeStatement`: the same with the paths of the
  state continuous only almost surely, as the field AX-03a delivers them: the joint
  measurability of the state on a time interval is obtained from an everywhere-continuous
  modification on a null set of the initial σ-algebra, and `H0152` from
  `localizationAeStatement`.

* `shortRateJumpStatement`: the forward rate (13.3) of Claim 013 built from the fields with the
  source coefficients, its short rate `r_t = f(t,t)`, and the identification of the short-rate
  jump at each meeting with the meeting jump (15.24), `Y_n = Δr_{T_n}`, together with the
  existence of the left limit of the short rate at the meeting; the stochastic part of the
  forward rate is taken in the version whose continuous deterministic maturity factor is
  factored out of the driver integral, and that version is shown almost surely equal to the
  direct one at every time and maturity.

* `fullMeetingVarianceFromFieldsStatement`: the complete list of conclusions of the frozen
  `meetingVarianceStatement` for the actual conditional variance vector of the meeting jumps
  defined from the fields, (15.4)–(15.8) and (15.13)–(15.16), with `H0154` derived from the
  fields and the joint transforms from the derived `H0152`; and
  `sourceMeetingVarianceStatement`: the same law, support and conditional law for the actual
  short-rate jumps `Δr_{T_n}` of the forward-rate construction (13.3) at any retained meetings.

Independence, support, affine-hull and meeting-variance conclusions are not assumed anywhere.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
open Standalone.ZeroMeanReversionVarianceSupport

namespace Standalone.ZeroMeanReversionUpstreamBridge

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-! ### The hypothesis structure of `lean/Upstream/ItoCalculus.lean`, restated verbatim -/

def U4 (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (H : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ H ∧ ∀ t : ℝ≥0, ∀ᵐ ω ∂μ,
    ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((H (Real.toNNReal s) ω) ^ 2) < ⊤

def U5 (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop :=
  U4 ℱ μ H ∧
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((H (Real.toNNReal s) ω) ^ 2)) ∂μ < ⊤

def LocallyIntegrableDrift (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (K : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ K ∧ ∀ t : ℝ≥0, ∀ᵐ ω ∂μ,
    ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal |K (Real.toNNReal s) ω| < ⊤

noncomputable def driverForm {m n : ℕ} (I : Fin m → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (x : Fin n → ℝ) (H : Fin n → Fin m → ℝ≥0 → Ω → ℝ) (K : Fin n → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (i : Fin n) : ℝ :=
  x i + ∑ k, I k (H i k) t ω + ∫ s in (0 : ℝ)..t, K i (Real.toNNReal s) ω

noncomputable def dT {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  fderiv ℝ f p (1, 0)
noncomputable def dX {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) (i : Fin n) : ℝ :=
  fderiv ℝ f p (0, Pi.single i 1)
noncomputable def dXX {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) (i j : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ f) p (0, Pi.single i 1) (0, Pi.single j 1)

structure ItoCalculus (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  μ : Measure Ω
  [isProbabilityMeasure : IsProbabilityMeasure μ]
  ℱ : Filtration ℝ≥0 m₀
  m : ℕ
  B : Fin m → ℝ≥0 → Ω → ℝ
  c : Fin m → Fin m → ℝ≥0 → ℝ
  I : Fin m → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ
  usual_null : ∀ s : Set Ω, MeasurableSet s → μ s = 0 → MeasurableSet[ℱ 0] s
  usual_rightContinuous : ∀ t, ℱ t = ⨅ s, ⨅ (_ : t < s), ℱ s
  c_measurable : ∀ k l, Measurable (c k l)
  c_bounded_on_compacts : ∀ k l (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |c k l s| ≤ C
  c_symm : ∀ k l s, c k l s = c l k s
  B_adapted : ∀ k, Adapted ℱ (B k)
  B_zero : ∀ k, B k 0 =ᵐ[μ] 0
  B_continuous : ∀ k, ∀ᵐ ω ∂μ, Continuous fun t => B k t ω
  B_memLp_two : ∀ k t, MemLp (B k t) 2 μ
  B_martingale : ∀ k, Martingale (B k) ℱ μ
  B_covariation : ∀ k l,
    Martingale (fun t ω => B k t ω * B l t ω - ∫ s in (0 : ℝ)..t, c k l (Real.toNNReal s)) ℱ μ
  int_elementary : ∀ k (a b : ℝ≥0) (ξ : Ω → ℝ), a ≤ b → Measurable[ℱ a] ξ →
    (∃ C, ∀ ω, |ξ ω| ≤ C) → ∀ t,
    (fun ω => I k (fun s ω => ξ ω * Set.indicator (Set.Ioc a b) 1 s) t ω) =ᵐ[μ]
      fun ω => ξ ω * (B k (min t b) ω - B k (min t a) ω)
  int_linear : ∀ k H K (a b : ℝ), U4 ℱ μ H → U4 ℱ μ K → ∀ t,
    I k (a • H + b • K) t =ᵐ[μ] a • I k H t + b • I k K t
  int_adapted : ∀ k H, U4 ℱ μ H → Adapted ℱ (I k H)
  int_zero : ∀ k H, U4 ℱ μ H → I k H 0 =ᵐ[μ] 0
  int_continuous : ∀ k H, U4 ℱ μ H → ∀ᵐ ω ∂μ, Continuous fun t => I k H t ω
  int_martingale : ∀ k H T, U5 ℱ μ H T →
    Martingale (fun t ω => I k H (min t T) ω) ℱ μ ∧ ∀ t, t ≤ T → MemLp (I k H t) 2 μ
  int_product_martingale : ∀ k l H K T, U5 ℱ μ H T → U5 ℱ μ K T →
    Martingale (fun t ω => I k H (min t T) ω * I l K (min t T) ω -
      ∫ s in (0 : ℝ)..(min t T : ℝ≥0), H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
        c k l (Real.toNNReal s)) ℱ μ
  stopped_martingale : ∀ (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0),
    Martingale (fun t ω => X (min t T) ω) ℱ μ → (∀ᵐ ω ∂μ, Continuous fun t => X t ω) →
    IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) →
    Martingale (fun t ω => X (min (min t T) (τ ω)) ω) ℱ μ
  int_stopped : ∀ k H (τ : Ω → ℝ≥0), U4 ℱ μ H → IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) →
    ∀ t, (fun ω => I k H (min t (τ ω)) ω) =ᵐ[μ]
      fun ω => I k (fun s ω => Set.indicator {s | s ≤ τ ω} (fun _ => (1 : ℝ)) s * H s ω) t ω
  ito_formula : ∀ (n : ℕ) (x : Fin n → ℝ) (H : Fin n → Fin m → ℝ≥0 → Ω → ℝ)
      (K : Fin n → ℝ≥0 → Ω → ℝ) (f : ℝ × (Fin n → ℝ) → ℝ),
    (∀ i k, U4 ℱ μ (H i k)) → (∀ i, LocallyIntegrableDrift ℱ μ (K i)) → ContDiff ℝ 2 f →
    (∀ i k, U4 ℱ μ (fun s ω => dX f ((s : ℝ), driverForm I x H K s ω) i * H i k s ω)) ∧
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, f ((t : ℝ), driverForm I x H K t ω) = f (0, x) +
      (∫ s in (0 : ℝ)..t, (dT f (s, driverForm I x H K (Real.toNNReal s) ω) +
        ∑ i, dX f (s, driverForm I x H K (Real.toNNReal s) ω) i * K i (Real.toNNReal s) ω +
        (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l, dXX f (s, driverForm I x H K (Real.toNNReal s) ω) i j *
          H i k (Real.toNNReal s) ω * H j l (Real.toNNReal s) ω * c k l (Real.toNNReal s))) +
      ∑ i, ∑ k, I k (fun s ω => dX f ((s : ℝ), driverForm I x H K s ω) i * H i k s ω) t ω

attribute [instance] ItoCalculus.isProbabilityMeasure

/-! ### Conversions between the structure's `ℝ≥0` time index and Claim 015's real time -/

/-- The filtration extended to real times, constant on negative times. -/
def filtR (ℱ : Filtration ℝ≥0 m₀) : Filtration ℝ m₀ where
  seq t := ℱ (Real.toNNReal t)
  mono' := fun _ _ hst => ℱ.mono (Real.toNNReal_le_toNNReal hst)
  le' := fun t => ℱ.le _
/-- A state process extended to real times, constant on negative times. -/
def stateR {d : ℕ} (X : ℝ≥0 → Ω → Fin d → NNReal) (t : ℝ) : Ω → Fin d → NNReal :=
  X (Real.toNNReal t)

/-! ### The extended backward exponential and the driver-form data -/

/-- A smooth saturating replacement for `T - s`: equal to `T - s` for `s ≤ T`, zero for
`s ≥ T + δ`, and never below `-δ`. -/
noncomputable def g0155 (T δ s : ℝ) : ℝ :=
  (T - s) * (1 - Real.smoothTransition ((s - T) / δ))
noncomputable def qExt (α T δ l s : ℝ) : ℝ := l / (1 + (α ^ 2 * g0155 T δ s / 2) * l)
/-- The backward exponential extended past the horizon. -/
noncomputable def EExt {d : ℕ} (α l : Fin d → ℝ) (T δ : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  Real.exp (-(∑ j, qExt (α j) T δ (l j) p.1 * p.2 j))
/-- The saturation width, chosen so that every denominator stays positive. -/
noncomputable def δ0155 {d : ℕ} (α l : Fin d → ℝ) : ℝ := 1 / (1 + ∑ j, (α j) ^ 2 * l j)

/-- One driver per coordinate: the integrand `α_j √X_j` on driver `k j`, zero on the others. -/
noncomputable def Hdrv {d m : ℕ} (k : Fin d → Fin m) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) (k' : Fin m) : ℝ≥0 → Ω → ℝ :=
  if k' = k i then fun s ω => α i * Real.sqrt (X s ω i) else fun _ _ => 0
/-- The Itô-formula integrand of the extended backward exponential along driver `k i`. -/
noncomputable def Gint {d : ℕ} (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (α l : Fin d → ℝ)
    (T : ℝ) (x0 : Fin d → NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => dX (EExt α l T (δ0155 α l))
    ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (fun _ _ _ => 0) s ω) i *
    Hdrv k α X i (k i) s ω

/-! ### Statements -/

/-- The backward exponential agrees on `(-∞, T]` with a globally `C²` function. -/
def extensionStatement : Prop :=
  ∀ (d : ℕ) (α l : Fin d → ℝ) (T : ℝ), (∀ j, 0 ≤ l j) →
    ∃ f : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ 2 f ∧ ∀ s x, s ≤ T → f (s, x) = E0152 α l T s x

/-- The Itô representation (15.20) from the field AX-05: for variance states solving the
zero-mean-reversion equation written with `I`, with one driver per coordinate carrying the
identity covariation, the backward exponential up to the horizon is its initial value plus the
driver integrals of `Gint`, each of which is a (U4) integrand; the drift term cancels by the
generator identity. -/
def itoStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (X 0 =ᵐ[S.μ] fun _ => x0) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ (T : ℝ) (l : Fin d → ℝ), (∀ j, 0 ≤ l j) →
      (∀ i, U4 S.ℱ S.μ (Gint S k α l T x0 X i)) ∧
      ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
        E0152 α l T t (fun i => (X t ω i : ℝ)) =
          E0152 α l T 0 (fun i => (x0 i : ℝ)) + ∑ i, S.I (k i) (Gint S k α l T x0 X i) t ω

/-- The integral of the zero integrand vanishes almost surely, simultaneously in time. -/
def zeroIntegralStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω) (k : Fin S.m),
    ∀ᵐ ω ∂S.μ, ∀ t, S.I k (fun _ _ => (0 : ℝ)) t ω = 0

/-- `H0152` for the actual variance states under the fields, with one driver `k j` per
coordinate carrying the identity covariation, continuous adapted paths, an initial value at
most one, and the zero-mean-reversion integral equation written with `I`. -/
def localizationStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ (T : NNReal) (l : Fin d → ℝ), (∀ j, 0 ≤ l j) →
      H0152 S.μ (filtR S.ℱ) α l T (stateR X)

/-- `H0152` under the fields' almost-sure path continuity: the same as `localizationStatement`
with continuity of each coordinate's paths only almost surely, as the field AX-03a's
continuity clause delivers it. -/
def localizationAeStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ (T : NNReal) (l : Fin d → ℝ), (∀ j, 0 ≤ l j) →
      H0152 S.μ (filtR S.ℱ) α l T (stateR X)

/-- The frozen development's consequences of `H0152` for the actual variance states under the
fields: the terminal law (15.2) as the product transition law `Q01513`, the conditional
transform (15.13) in the structure's filtration, the measurable regular conditional
transition kernel, and the independence, second moments, mean, variance, finite-horizon
martingale property, zero-scale constancy, conditional moments and absorption of the state
coordinates. -/
def transformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ T : NNReal,
      (S.μ.map (fun ω j => (stateR X T ω j : ℝ)) = Q01513 (fun j => (α j)^2*(T : ℝ)/2) x0) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
          S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X T ω j)) | filtR S.ℱ s] =ᵐ[S.μ]
            fun ω => Real.exp (-(∑ j, (stateR X s ω j : ℝ)*l j/(1+((α j)^2*((T : ℝ)-s)/2)*l j)))) ∧
        (∀ B, MeasurableSet B → Measurable[filtR S.ℱ s]
          (fun ω => Q01513 (fun j => (α j)^2*((T : ℝ)-s)/2) (stateR X s ω) B)) ∧
        ∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ B, MeasurableSet B →
          (S.μ.restrict D).map (fun ω j => (stateR X T ω j : ℝ)) B =
            ∫⁻ ω in D, Q01513 (fun j => (α j)^2*((T : ℝ)-s)/2) (stateR X s ω) B ∂S.μ) ∧
      iIndepFun (fun j ω => (stateR X T ω j : ℝ)) S.μ ∧ ∀ j : Fin d,
        MemLp (fun ω => (stateR X T ω j : ℝ)) 2 S.μ ∧
        (∫ ω, (stateR X T ω j : ℝ) ∂S.μ) = x0 j ∧
        Var[fun ω => (stateR X T ω j : ℝ); S.μ] = (α j)^2*(T : ℝ)*x0 j ∧
        Martingale (fun (s : Set.Icc (0 : ℝ) T) ω => (stateR X s.val ω j : ℝ))
          (filt0152 (filtR S.ℱ) T) S.μ ∧
        (α j = 0 → ∀ᵐ ω ∂S.μ, stateR X T ω j = x0 j) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T,
          MemLp (fun ω => (stateR X s ω j : ℝ)) 2 S.μ ∧
          (S.μ[fun ω => (stateR X T ω j : ℝ) | filtR S.ℱ s] =ᵐ[S.μ]
            fun ω => (stateR X s ω j : ℝ)) ∧
          (S.μ[fun ω => (stateR X T ω j : ℝ)^2 | filtR S.ℱ s] =ᵐ[S.μ]
            fun ω => (stateR X s ω j : ℝ)^2+(α j)^2*((T : ℝ)-s)*stateR X s ω j) ∧
          (Var[fun ω => (stateR X T ω j : ℝ); S.μ | filtR S.ℱ s] =ᵐ[S.μ]
            fun ω => (α j)^2*((T : ℝ)-s)*stateR X s ω j) ∧
          (∀ᵐ ω ∂S.μ, stateR X s ω j = 0 → stateR X T ω j = 0)

/-- Conditional isometry and orthogonality of increments of the driver integrals on a horizon,
from AX-03c and AX-04b: for (U5) integrands `H`, `K` and `t ≤ T`, the increment of `∫ H dB^k`
over `[t, T]` is square integrable, and the conditional expectation given `F_t` of the product
of the increments of `∫ H dB^k` and `∫ K dB^l` is that of `∫_t^T H K c_{kl} ds`. -/
def incrementStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω) (k l : Fin S.m)
    (H K : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0), t ≤ T → U5 S.ℱ S.μ H T → U5 S.ℱ S.μ K T →
    MemLp (fun ω => S.I k H T ω - S.I k H t ω) 2 S.μ ∧
    S.μ[fun ω => (S.I k H T ω - S.I k H t ω) * (S.I l K T ω - S.I l K t ω) | S.ℱ t] =ᵐ[S.μ]
      S.μ[fun ω => ∫ s in (t : ℝ)..T, H (Real.toNNReal s) ω * K (Real.toNNReal s) ω *
        S.c k l (Real.toNNReal s) | S.ℱ t]

/-- The increment over `[t, T]` of the two-driver integral `∫ Hw dB^{kw} + ∫ Hu dB^{ku}`. -/
noncomputable def twoDriverIncrement (S : ItoCalculus Ω) (kw ku : Fin S.m)
    (Hw Hu : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  (S.I kw Hw T ω - S.I kw Hw t ω) + (S.I ku Hu T ω - S.I ku Hu t ω)

/-- The conditional isometry (15.28) for a two-driver increment: it is square integrable and
its conditional second moment given `F_t` is the conditional expectation of the integral over
`[t, T]` of `Hw² c_{ww} + 2 Hw Hu c_{wu} + Hu² c_{uu}`, written as three interval
integrals. -/
def twoDriverIsometryStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω) (kw ku : Fin S.m)
    (Hw Hu : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0), t ≤ T → U5 S.ℱ S.μ Hw T → U5 S.ℱ S.μ Hu T →
    MemLp (twoDriverIncrement S kw ku Hw Hu T t) 2 S.μ ∧
    S.μ[fun ω => twoDriverIncrement S kw ku Hw Hu T t ω ^ 2 | S.ℱ t] =ᵐ[S.μ]
      S.μ[fun ω =>
        (∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hw (Real.toNNReal s) ω *
          S.c kw kw (Real.toNNReal s)) +
        2 * (∫ s in (t : ℝ)..T, Hw (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
          S.c kw ku (Real.toNNReal s)) +
        (∫ s in (t : ℝ)..T, Hu (Real.toNNReal s) ω * Hu (Real.toNNReal s) ω *
          S.c ku ku (Real.toNNReal s)) | S.ℱ t]

/-- Cross-factor conditional orthogonality: two two-driver increments whose four driver pairs
have zero covariation have an integrable product with zero conditional expectation given
`F_t`. -/
def crossFactorStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω) (kw ku kw' ku' : Fin S.m)
    (Hw Hu Hw' Hu' : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0), t ≤ T →
    U5 S.ℱ S.μ Hw T → U5 S.ℱ S.μ Hu T → U5 S.ℱ S.μ Hw' T → U5 S.ℱ S.μ Hu' T →
    (∀ s, S.c kw kw' s = 0) → (∀ s, S.c kw ku' s = 0) →
    (∀ s, S.c ku kw' s = 0) → (∀ s, S.c ku ku' s = 0) →
    Integrable (fun ω => twoDriverIncrement S kw ku Hw Hu T t ω *
      twoDriverIncrement S kw' ku' Hw' Hu' T t ω) S.μ ∧
    S.μ[fun ω => twoDriverIncrement S kw ku Hw Hu T t ω *
      twoDriverIncrement S kw' ku' Hw' Hu' T t ω | S.ℱ t] =ᵐ[S.μ] 0

/-- Square integrability on every horizon of the coefficient integrands `K(s) √v_j(s)` for a
measurable locally bounded `K`, from the predictability of `√v_j` (the SDE integrand) and the
state mean `E v_j(s) = v_j(0)` derived in `transformStatement`. -/
def coefficientStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (j : Fin d) (K : ℝ≥0 → ℝ), Measurable K → (∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) →
    ∀ T : ℝ≥0, U5 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) T

/-- The conditional isometry and the cross-factor orthogonality for the actual two-driver
increments `∫_t^T K₁ √v_j dB^{kw} + ∫_t^T K₂ √v_j dB^{k j}` with measurable locally bounded
coefficients: the square roots cancel in the covariation integrands, which are
`K₁² c_{ww} v_j`, `2 K₁ K₂ c_{wu} v_j` and `K₂² c_{uu} v_j`. -/
def actualIncrementStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (kw : Fin d → Fin S.m) (K₁ K₂ : Fin d → ℝ≥0 → ℝ),
    (∀ j, Measurable (K₁ j)) → (∀ j, Measurable (K₂ j)) →
    (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |K₁ j s| ≤ C) →
    (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |K₂ j s| ≤ C) →
    ∀ (T t : ℝ≥0), t ≤ T →
    (∀ j : Fin d,
      MemLp (twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
        (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t) 2 S.μ ∧
      S.μ[fun ω => twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω ^ 2 | S.ℱ t] =ᵐ[S.μ]
        S.μ[fun ω =>
          (∫ s in (t : ℝ)..T, K₁ j (Real.toNNReal s) ^ 2 * S.c (kw j) (kw j) (Real.toNNReal s) *
            (X (Real.toNNReal s) ω j : ℝ)) +
          2 * (∫ s in (t : ℝ)..T, K₁ j (Real.toNNReal s) * K₂ j (Real.toNNReal s) *
            S.c (kw j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) +
          (∫ s in (t : ℝ)..T, K₂ j (Real.toNNReal s) ^ 2 * S.c (k j) (k j) (Real.toNNReal s) *
            (X (Real.toNNReal s) ω j : ℝ)) | S.ℱ t]) ∧
    (∀ i j : Fin d,
      (∀ s, S.c (kw i) (kw j) s = 0) → (∀ s, S.c (kw i) (k j) s = 0) →
      (∀ s, S.c (k i) (kw j) s = 0) → (∀ s, S.c (k i) (k j) s = 0) →
      Integrable (fun ω =>
        twoDriverIncrement S (kw i) (k i) (fun s ω => K₁ i s * Real.sqrt (X s ω i))
          (fun s ω => K₂ i s * Real.sqrt (X s ω i)) T t ω *
        twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω) S.μ ∧
      S.μ[fun ω =>
        twoDriverIncrement S (kw i) (k i) (fun s ω => K₁ i s * Real.sqrt (X s ω i))
          (fun s ω => K₂ i s * Real.sqrt (X s ω i)) T t ω *
        twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω | S.ℱ t] =ᵐ[S.μ] 0)

/-- The actual meeting-`n` factor-`j` increment `Z_{n,j} = ∫_t^{T_n} √v_j (g dW_j + α R dU_j)`
of (15.27), with `R_{n,j}(u) = ∫_u^{T_n} b_{n,j}`, on the drivers `kw j` (the `W`) and `k j`
(the `U`). -/
noncomputable def Zactual {m d : ℕ} (S : ItoCalculus Ω) (k kw : Fin d → Fin S.m)
    (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ)
    (T : Fin m → ℝ) (t : ℝ) (n : Fin m) (j : Fin d) : Ω → ℝ :=
  twoDriverIncrement S (kw j) (k j) (fun s ω => g n j s * Real.sqrt (X s ω j))
    (fun s ω => α j * (∫ u in (s : ℝ)..T n, b n j u) * Real.sqrt (X s ω j))
    (Real.toNNReal (T n)) (Real.toNNReal t)

/-- The first, third and fourth `H0154` fields for the actual increments `Z_{n,j}` with the
source's full kernel: products of increments are integrable; the conditional second moment of
`Z_{n,j}` given `F_t` is the conditional expectation of `I_{n,j} = ∫_t^{T_n} K0154 v_j du`,
the within-factor covariation calculation (15.28) with the drivers' covariations `1`, `ρ_j`,
`1`; and for two factors whose four drivers have zero cross covariation the product of
increments has zero conditional expectation. -/
def kernelIsometryStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m),
    (∀ j, Measurable (g n j)) → (∀ j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ j, Measurable (fun u : ℝ => ∫ s in u..T n, b n j s)) →
    (∀ j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |∫ s in u..T n, b n j s| ≤ C) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (k j) (k j) s = 1) →
    (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    ∀ t : ℝ, 0 ≤ t → t ≤ T n →
    (∀ i j : Fin d, Integrable (fun ω => Zactual S k kw α X g b T t n i ω *
      Zactual S k kw α X g b T t n j ω) S.μ) ∧
    (∀ j : Fin d, S.μ[fun ω => Zactual S k kw α X g b T t n j ω ^ 2 | S.ℱ (Real.toNNReal t)]
      =ᵐ[S.μ] S.μ[I0154 g b ρ α T t (stateR X) n j | S.ℱ (Real.toNNReal t)]) ∧
    (∀ i j : Fin d, (∀ s, S.c (kw i) (kw j) s = 0) → (∀ s, S.c (kw i) (k j) s = 0) →
      (∀ s, S.c (k i) (kw j) s = 0) → (∀ s, S.c (k i) (k j) s = 0) →
      S.μ[fun ω => Zactual S k kw α X g b T t n i ω * Zactual S k kw α X g b T t n j ω
        | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ] 0)

/-- The product rule (15.26) from the field AX-05: for a `C²` weight `R` with `R' = −b`, the
weighted state `R(t) v_j(t)` is `R(0) v_j(0) − ∫_0^t b v_j du + ∫_0^t R α_j √v_j dU_j`,
simultaneously in `t`, with a (U4) integrand; and, when `R(T) = 0` and the paths are
continuous, `∫_t^T b v_j du = R(t) v_j(t) + ∫_t^T R α_j √v_j dU_j`. -/
def productRuleStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (X 0 =ᵐ[S.μ] fun _ => x0) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ (j : Fin d) (R b : ℝ → ℝ), ContDiff ℝ 2 R → (∀ u, HasDerivAt R (-(b u)) u) →
      U4 S.ℱ S.μ (fun s ω => R s * (α j * Real.sqrt (X s ω j))) ∧
      (∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, R t * (X t ω j : ℝ) =
        R 0 * (x0 j : ℝ) - (∫ u in (0 : ℝ)..t, b u * (X (Real.toNNReal u) ω j : ℝ)) +
          S.I (k j) (fun s ω => R s * (α j * Real.sqrt (X s ω j))) t ω) ∧
      ((∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) → ∀ T : ℝ≥0, R T = 0 →
        ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, t ≤ T →
          (∫ u in (t : ℝ)..T, b u * (X (Real.toNNReal u) ω j : ℝ)) =
            R t * (X t ω j : ℝ) +
              (S.I (k j) (fun s ω => R s * (α j * Real.sqrt (X s ω j))) T ω -
                S.I (k j) (fun s ω => R s * (α j * Real.sqrt (X s ω j))) t ω))

/-- The actual meeting jump (15.24) at meeting `n`:
`Y_n = Σ_j [∫_0^{T_n} b_{n,j} v_j du + ∫_0^{T_n} g_{n,j} √v_j dW_j]`. -/
noncomputable def Yactual {m d : ℕ} (S : ItoCalculus Ω) (kw : Fin d → Fin S.m)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m) :
    Ω → ℝ :=
  fun ω => ∑ j, ((∫ u in (0 : ℝ)..T n, b n j u * (X (Real.toNNReal u) ω j : ℝ)) +
    S.I (kw j) (fun s ω => g n j s * Real.sqrt (X s ω j)) (Real.toNNReal (T n)) ω)

/-- The backward weight `R_{n,j}(u) = ∫_u^{T_n} b_{n,j}` of a `C¹` coefficient is `C²`, has
derivative `−b_{n,j}` and vanishes at `T_n`. -/
def backwardWeightStatement : Prop :=
  ∀ (b : ℝ → ℝ) (T : ℝ), ContDiff ℝ 1 b →
    ContDiff ℝ 2 (fun u => ∫ s in u..T, b s) ∧
    (∀ u, HasDerivAt (fun u => ∫ s in u..T, b s) (-(b u)) u) ∧
    (∫ s in T..T, b s) = 0

/-- The centered representation, the second `H0154` field, for the actual meeting jump (15.24)
under the fields: for `C²` weights `R_{n,j}` with `R' = −b_{n,j}` and `R(T_n) = 0`, the jump
`Y_n` is integrable and `Y_n − E[Y_n | F_t] = Σ_j Z_{n,j}` with the two-driver increments
`Z_{n,j} = ∫_t^{T_n} √v_j (g_{n,j} dW_j + α_j R_{n,j} dU_j)`. -/
def centeredStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m) (R : Fin d → ℝ → ℝ),
    (∀ j, Measurable (g n j)) → (∀ j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ j, ContDiff ℝ 2 (R j)) → (∀ j u, HasDerivAt (R j) (-(b n j u)) u) →
    (∀ j, R j (T n) = 0) →
    ∀ t : ℝ, 0 ≤ t → t ≤ T n →
      Integrable (Yactual S kw X g b T n) S.μ ∧
      Yactual S kw X g b T n - S.μ[Yactual S kw X g b T n | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
        fun ω => ∑ j, twoDriverIncrement S (kw j) (k j)
          (fun s ω => g n j s * Real.sqrt (X s ω j))
          (fun s ω => R j s * (α j * Real.sqrt (X s ω j)))
          (Real.toNNReal (T n)) (Real.toNNReal t) ω

/-- The five `H0154` fields assembled from the fields, and the affine identity of the actual
conditional jump variances: for the meeting jumps (15.24) and increments (15.27) defined from
the fields, with `C¹` drift coefficients, measurable locally bounded diffusion coefficients,
within-factor correlations in `[−1, 1]` and cross-factor drivers of zero covariation, the
frozen development's bundle `H0154` holds at every observation time before the meetings, and
the vector of actual conditional jump variances is the full-kernel matrix `A0154` applied to
the state. -/
def assemblyStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, ContDiff ℝ 1 (b n j)) → (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U : NNReal) (t : ℝ), 0 ≤ t → (∀ n, t ≤ T n ∧ T n ≤ U) →
      H0154 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n)
        (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X))
        (stateR X t) g b ρ α T t ∧
      (V0150 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n) =ᵐ[S.μ]
        fun ω => (A0154 g b ρ α T t).mulVec (fun j => (stateR X t ω j : ℝ)))

/-- The actual meeting-variance law and its exact support from the fields: under the
hypotheses of `assemblyStatement`, at an observation time `t` before the meetings, the law of
the vector of actual conditional jump variances is the image of the product transition law
`Q01513` under the full-kernel matrix, its support is the translated cone of (15.14), and the
same holds conditionally on every earlier time `s ≤ t` through a measurable regular
conditional law, exactly as in the frozen development's `localizedMeetingVarianceStatement`
with `H0152` and `H0154` now derived from the fields. -/
def meetingVarianceFromFieldsStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, ContDiff ℝ 1 (b n j)) → (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U t : NNReal), (∀ n, (t : ℝ) ≤ T n ∧ T n ≤ U) →
      let A := A0154 g b ρ α T t
      (let c := fun j => (α j)^2*(t : ℝ)/2;
        S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) =
          (Q01513 c x0).map A.mulVec ∧
        (S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n))).support =
          cone0154 (A01514 A c x0) (b01514 A 0 c x0)) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        let c := fun j => (α j)^2*((t : ℝ)-s)/2
        (∀ B, MeasurableSet B → Measurable[filtR S.ℱ s]
          (fun ω => ((Q01513 c (stateR X s ω)).map A.mulVec) B)) ∧
        (∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ B, MeasurableSet B →
          (S.μ.restrict D).map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) B =
            ∫⁻ ω in D, ((Q01513 c (stateR X s ω)).map A.mulVec) B ∂S.μ) ∧
        ∀ ω, ((Q01513 c (stateR X s ω)).map A.mulVec).support =
          cone0154 (A01514 A c (stateR X s ω)) (b01514 A 0 c (stateR X s ω))

/-- The absolutely continuous weight `R(s) = R₀ − ∫_0^s b` of a locally integrable
coefficient `b`. -/
noncomputable def weightAC (b : ℝ → ℝ) (R0 s : ℝ) : ℝ := R0 - ∫ u in (0 : ℝ)..s, b u

/-- The product rule (15.26) for an absolutely continuous weight: for a measurable locally
integrable coefficient `b` and `R(s) = R₀ − ∫_0^s b`, the weighted state `R(t) v_j(t)` is
`R₀ v_j(0) − ∫_0^t b v_j du + ∫_0^t R α_j √v_j dU_j`, simultaneously in `t`, with a (U4)
integrand. This is the field AX-05 applied to the product of the state coordinate with the
deterministic drift-only coordinate `R`, so no smoothness of `b` is needed; it covers the
source's bounded measurable drift coefficients. -/
def productRuleACStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (X 0 =ᵐ[S.μ] fun _ => x0) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    ∀ (j : Fin d) (b : ℝ → ℝ) (R0 : ℝ), Measurable b →
      (∀ t : ℝ, IntervalIntegrable b MeasureTheory.volume 0 t) →
      U4 S.ℱ S.μ (fun (s : ℝ≥0) ω => weightAC b R0 s * (α j * Real.sqrt (X s ω j))) ∧
      ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, weightAC b R0 t * (X t ω j : ℝ) =
        R0 * (x0 j : ℝ) - (∫ u in (0 : ℝ)..t, b u * (X (Real.toNNReal u) ω j : ℝ)) +
          S.I (k j) (fun (s : ℝ≥0) ω => weightAC b R0 s * (α j * Real.sqrt (X s ω j))) t ω

/-- The centered representation for measurable locally integrable drift coefficients: with the
backward weights `R_{n,j}(u) = ∫_u^{T_n} b_{n,j}`, the jump `Y_n` is integrable and
`Y_n − E[Y_n | F_t] = Σ_j Z_{n,j}`, the `Z_{n,j}` being the two-driver increments of
`centeredStatement`; the product rule at the horizon is the absolutely continuous one. -/
def centeredACStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (n : Fin m),
    (∀ j, Measurable (g n j)) → (∀ j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ j, Measurable (b n j)) →
    (∀ j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    ∀ t : ℝ, 0 ≤ t → t ≤ T n →
      Integrable (Yactual S kw X g b T n) S.μ ∧
      Yactual S kw X g b T n - S.μ[Yactual S kw X g b T n | S.ℱ (Real.toNNReal t)] =ᵐ[S.μ]
        fun ω => ∑ j, twoDriverIncrement S (kw j) (k j)
          (fun s ω => g n j s * Real.sqrt (X s ω j))
          (fun (s : ℝ≥0) ω => (∫ u in (s : ℝ)..T n, b n j u) * (α j * Real.sqrt (X s ω j)))
          (Real.toNNReal (T n)) (Real.toNNReal t) ω

/-- `assemblyStatement` with measurable locally integrable drift coefficients in place of `C¹`
ones. -/
def assemblyACStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, Measurable (b n j)) →
    (∀ n j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U : NNReal) (t : ℝ), 0 ≤ t → (∀ n, t ≤ T n ∧ T n ≤ U) →
      H0154 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n)
        (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X))
        (stateR X t) g b ρ α T t ∧
      (V0150 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n) =ᵐ[S.μ]
        fun ω => (A0154 g b ρ α T t).mulVec (fun j => (stateR X t ω j : ℝ)))

/-- `meetingVarianceFromFieldsStatement` with measurable locally integrable drift coefficients
in place of `C¹` ones. -/
def meetingVarianceFromFieldsACStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, Measurable (b n j)) →
    (∀ n j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U t : NNReal), (∀ n, (t : ℝ) ≤ T n ∧ T n ≤ U) →
      let A := A0154 g b ρ α T t
      (let c := fun j => (α j)^2*(t : ℝ)/2;
        S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) =
          (Q01513 c x0).map A.mulVec ∧
        (S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n))).support =
          cone0154 (A01514 A c x0) (b01514 A 0 c x0)) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        let c := fun j => (α j)^2*((t : ℝ)-s)/2
        (∀ B, MeasurableSet B → Measurable[filtR S.ℱ s]
          (fun ω => ((Q01513 c (stateR X s ω)).map A.mulVec) B)) ∧
        (∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ B, MeasurableSet B →
          (S.μ.restrict D).map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) B =
            ∫⁻ ω in D, ((Q01513 c (stateR X s ω)).map A.mulVec) B ∂S.μ) ∧
        ∀ ω, ((Q01513 c (stateR X s ω)).map A.mulVec).support =
          cone0154 (A01514 A c (stateR X s ω)) (b01514 A 0 c (stateR X s ω))

/-- `assemblyACStatement` with the paths of the state continuous only almost surely. -/
def assemblyAeStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, Measurable (b n j)) →
    (∀ n j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U : NNReal) (t : ℝ), 0 ≤ t → (∀ n, t ≤ T n ∧ T n ≤ U) →
      H0154 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n)
        (fun n j => Zactual S k kw α X g b T t n j) (I0154 g b ρ α T t (stateR X))
        (stateR X t) g b ρ α T t ∧
      (V0150 (S.ℱ (Real.toNNReal t)) S.μ (fun n => Yactual S kw X g b T n) =ᵐ[S.μ]
        fun ω => (A0154 g b ρ α T t).mulVec (fun j => (stateR X t ω j : ℝ)))

/-- `meetingVarianceFromFieldsACStatement` with the paths of the state continuous only almost
surely: the actual meeting-variance law and its exact support from the fields, with `H0152`
and `H0154` derived under the field AX-03a's almost-sure path continuity. -/
def meetingVarianceFromFieldsAeStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, Measurable (b n j)) →
    (∀ n j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U t : NNReal), (∀ n, (t : ℝ) ≤ T n ∧ T n ≤ U) →
      let A := A0154 g b ρ α T t
      (let c := fun j => (α j)^2*(t : ℝ)/2;
        S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) =
          (Q01513 c x0).map A.mulVec ∧
        (S.μ.map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n))).support =
          cone0154 (A01514 A c x0) (b01514 A 0 c x0)) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        let c := fun j => (α j)^2*((t : ℝ)-s)/2
        (∀ B, MeasurableSet B → Measurable[filtR S.ℱ s]
          (fun ω => ((Q01513 c (stateR X s ω)).map A.mulVec) B)) ∧
        (∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ B, MeasurableSet B →
          (S.μ.restrict D).map (V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)) B =
            ∫⁻ ω in D, ((Q01513 c (stateR X s ω)).map A.mulVec) B ∂S.μ) ∧
        ∀ ω, ((Q01513 c (stateR X s ω)).map A.mulVec).support =
          cone0154 (A01514 A c (stateR X s ω)) (b01514 A 0 c (stateR X s ω))

/-! ### The short-rate jump from the forward-rate construction (13.3) -/

/-- The maturity volatility kernel `h_j(s,u)` of (13.3) for factor `j`, from the source
formulas. -/
noncomputable def hSrc {N d : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (j : Fin d) (s u : ℝ) : ℝ :=
  h01530 T (a j) (lam j) (γ j) s u

/-- The differentiated HJM drift `α(s,u) = Σ_j h_j(s,u) (∫_s^u h_j(s,z) dz) v_j(s)` of (13.3)
along the state. -/
noncomputable def driftSrc {N d : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (s u : ℝ) (ω : Ω) : ℝ :=
  ∑ j, hSrc T a lam γ j s u * (∫ z in s..u, hSrc T a lam γ j s z) * (X (Real.toNNReal s) ω j : ℝ)

/-- The stochastic integrand of the forward rate of a maturity with meeting count `k`, with
its continuous deterministic maturity factor `exp(−∫_0^u λ_j)` removed:
`a_j(s) exp(∫_0^s λ_j) G_{k−j(s),j} √v_j(s)`. -/
noncomputable def loadInt {N d : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (j : Fin d) (k : ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => a j s * Real.exp (∫ q in (0 : ℝ)..s, lam j q) * G01530 (γ j) (k - j01530 T s) *
    Real.sqrt (X s ω j)

/-- The forward rate `f(t,u)` of (13.3) from the fields, in the version whose stochastic part is
the continuous maturity factor `exp(−∫_0^u λ_j)` times the driver integral of `loadInt` at the
meeting count of the maturity. -/
noncomputable def forwardSrc {N d : ℕ} (S : ItoCalculus Ω) (kw : Fin d → Fin S.m) (T : Fin N → ℝ)
    (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (c : ℝ)
    (t : ℝ≥0) (u : ℝ) (ω : Ω) : ℝ :=
  c + (∫ s in (0 : ℝ)..(t : ℝ), driftSrc T a lam γ X s u ω) +
    ∑ j, Real.exp (-(∫ q in (0 : ℝ)..u, lam j q)) *
      S.I (kw j) (loadInt T a lam γ X j (j01530 T u)) t ω

/-- The short rate `r_t = f(t,t)`. -/
noncomputable def shortSrc {N d : ℕ} (S : ItoCalculus Ω) (kw : Fin d → Fin S.m) (T : Fin N → ℝ)
    (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (c : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  forwardSrc S kw T a lam γ X c t (t : ℝ) ω

/-- The coefficient `g_{n,j}` of (13.4) for `s < T_n`, zero at and after `T_n`. -/
noncomputable def gJump {N d : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (n : Fin N) (j : Fin d) (s : ℝ) : ℝ :=
  if s < T n then g01530 T (a j) (lam j) (γ j) n s else 0

/-- The coefficient `b_{n,j}` of (13.4) for `s < T_n`, zero at and after `T_n`. -/
noncomputable def bJump {N d : ℕ} (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (n : Fin N) (j : Fin d) (s : ℝ) : ℝ :=
  if s < T n then b01530 T (a j) (lam j) (γ j) n s else 0

/-- The short-rate jump from the forward-rate construction (13.3): for the source coefficients
of Claim 013 with measurable locally bounded `a_j`, `λ_j ≥ 0` and finite loadings, under the
fields' SDE hypotheses, the forward rate built from the fields agrees almost surely at every
time and maturity with the direct construction, and at every meeting `T_n` the short rate
`r_t = f(t,t)` has a left limit almost surely whose jump `r_{T_n} − r_{T_n−}` is the meeting
jump (15.24) with the coefficients (13.4). -/
def shortRateJumpStatement : Prop :=
  ∀ (N d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
    StrictMono T → (∀ n, 0 < T n) →
    (∀ j, Measurable (a j)) → (∀ j, Measurable (lam j)) → (∀ j u, 0 ≤ lam j u) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) →
    (∀ (t : ℝ≥0) (u : ℝ), ∀ᵐ ω ∂S.μ, forwardSrc S kw T a lam γ X c t u ω =
      c + (∫ s in (0 : ℝ)..(t : ℝ), driftSrc T a lam γ X s u ω) +
        ∑ j, S.I (kw j) (fun (s : ℝ≥0) ω => hSrc T a lam γ j s u * Real.sqrt (X s ω j)) t ω) ∧
    ∀ n : Fin N, ∀ᵐ ω ∂S.μ, ∃ L : ℝ,
      Tendsto (fun t : ℝ => shortSrc S kw T a lam γ X c (Real.toNNReal t) ω) (𝓝[<] T n) (𝓝 L) ∧
      shortSrc S kw T a lam γ X c (Real.toNNReal (T n)) ω - L =
        Yactual S kw X (gJump T a lam γ) (bJump T a lam γ) T n ω

/-- The short-rate jump at meeting `n`: `r_{T_n}` minus the left limit of the short rate at `T_n`
along real times. -/
noncomputable def jumpSrc {N d : ℕ} (S : ItoCalculus Ω) (kw : Fin d → Fin S.m) (T : Fin N → ℝ)
    (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (c : ℝ)
    (n : Fin N) (ω : Ω) : ℝ :=
  shortSrc S kw T a lam γ X c (Real.toNNReal (T n)) ω -
    limUnder (𝓝[<] T n) (fun t : ℝ => shortSrc S kw T a lam γ X c (Real.toNNReal t) ω)

/-- The complete meeting-variance conclusions from the fields: under the hypotheses of
`meetingVarianceFromFieldsAeStatement`, the vector `V` of actual conditional variances of the
meeting jumps at an observation time `t` before the meetings is `A0154` applied to the state,
its law is the image of the product transition law, and (15.4)–(15.8) hold: exact support,
closedness, affine hull, the almost-sure affine equalities, second moments and means, the
covariance kernel with its kernel and rank, and the atom at the deterministic contribution;
and for every earlier time `s ≤ t`, (15.14)–(15.15): the measurable regular conditional law with
its exact support, and the conditional mean `A0154 v(s)`. -/
def fullMeetingVarianceFromFieldsStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
    (∀ n j, Measurable (g n j)) →
    (∀ n j (T' : ℝ), ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) T', |g n j u| ≤ C) →
    (∀ n j, Measurable (b n j)) →
    (∀ n j (T' : ℝ), IntervalIntegrable (b n j) MeasureTheory.volume 0 T') →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (U t : NNReal), (∀ n, (t : ℝ) ≤ T n ∧ T n ≤ U) →
      let A := A0154 g b ρ α T t
      let V := V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b T n)
      let c := fun j => (α j)^2*(t : ℝ)/2
      let B := A01514 A c x0
      let b' := b01514 A 0 c x0
      (∀ n j, 0 ≤ A n j) ∧
      (V =ᵐ[S.μ] fun ω => A.mulVec (fun j => (stateR X t ω j : ℝ))) ∧
      S.μ.map V = (Q01513 c x0).map A.mulVec ∧
      (S.μ.map V).support = cone0154 B b' ∧
      IsClosed (cone0154 B b') ∧
      (affineSpan ℝ (cone0154 B b') : Set (Fin m → ℝ)) =
        (fun y => b' + y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
      (∀ w, (∀ᵐ y ∂S.μ.map V, dotProduct w (y - b') = 0) ↔ B.transpose.mulVec w = 0) ∧
      (∀ i, MemLp (fun ω => V ω i) 2 S.μ ∧ (∫ ω, V ω i ∂S.μ) = ∑ j, A i j * x0 j) ∧
      (∀ i k, cov[fun ω => V ω i, fun ω => V ω k; S.μ] = cov0157 A (fun j => 2 * c j * x0 j) i k) ∧
      LinearMap.ker (cov0157 A (fun j => 2 * c j * x0 j)).mulVecLin =
        LinearMap.ker B.transpose.mulVecLin ∧
      (cov0157 A (fun j => 2 * c j * x0 j)).rank = B.rank ∧
      (S.μ.map V) {b'} =
        ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, B i j ≠ 0) then (x0 j : ℝ) / c j else 0))) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        let c' := fun j => (α j)^2*((t : ℝ)-s)/2
        (∀ E, MeasurableSet E → Measurable[filtR S.ℱ s]
          (fun ω => ((Q01513 c' (stateR X s ω)).map A.mulVec) E)) ∧
        (∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ E, MeasurableSet E →
          (S.μ.restrict D).map V E =
            ∫⁻ ω in D, ((Q01513 c' (stateR X s ω)).map A.mulVec) E ∂S.μ) ∧
        (∀ ω, ((Q01513 c' (stateR X s ω)).map A.mulVec).support =
          cone0154 (A01514 A c' (stateR X s ω)) (b01514 A 0 c' (stateR X s ω))) ∧
        ∀ i, S.μ[fun ω => V ω i | filtR S.ℱ s] =ᵐ[S.μ]
          fun ω => ∑ j, A i j * (stateR X s ω j : ℝ)

/-- The meeting-variance law of the actual short-rate jumps of the forward-rate construction
(13.3): for the source coefficients and any retained meetings `rows` after the observation
time `t`, the short-rate jumps `Δr_{T_n}` agree almost surely with the meeting jumps (15.24)
with the coefficients (13.4), the vector of their actual conditional variances agrees almost
surely with that of the meeting jumps, and its law, exact support and regular conditional law
with exact support given every earlier time are those of `fullMeetingVarianceFromFieldsStatement`. -/
def sourceMeetingVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ) (ρ : Fin d → ℝ → ℝ),
    StrictMono T → (∀ n, 0 < T n) →
    (∀ j, Measurable (a j)) → (∀ j, Measurable (lam j)) → (∀ j u, 0 ≤ lam j u) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B) →
    (∀ j, Measurable (ρ j)) →
    (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
    (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
    (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (U t : NNReal), (∀ n, (t : ℝ) ≤ T (rows n) ∧ T (rows n) ≤ U) →
      let g : Fin m → Fin d → ℝ → ℝ := fun n => gJump T a lam γ (rows n)
      let b : Fin m → Fin d → ℝ → ℝ := fun n => bJump T a lam γ (rows n)
      let Tr : Fin m → ℝ := fun n => T (rows n)
      let A := A0154 g b ρ α Tr t
      let V := V0150 (filtR S.ℱ t) S.μ (fun n => jumpSrc S kw T a lam γ X c (rows n))
      (∀ n, jumpSrc S kw T a lam γ X c (rows n) =ᵐ[S.μ] Yactual S kw X g b Tr n) ∧
      V =ᵐ[S.μ] V0150 (filtR S.ℱ t) S.μ (fun n => Yactual S kw X g b Tr n) ∧
      (let c' := fun j => (α j)^2*(t : ℝ)/2;
        S.μ.map V = (Q01513 c' x0).map A.mulVec ∧
        (S.μ.map V).support = cone0154 (A01514 A c' x0) (b01514 A 0 c' x0)) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        let c' := fun j => (α j)^2*((t : ℝ)-s)/2
        (∀ E, MeasurableSet E → Measurable[filtR S.ℱ s]
          (fun ω => ((Q01513 c' (stateR X s ω)).map A.mulVec) E)) ∧
        (∀ D, MeasurableSet[filtR S.ℱ s] D → ∀ E, MeasurableSet E →
          (S.μ.restrict D).map V E =
            ∫⁻ ω in D, ((Q01513 c' (stateR X s ω)).map A.mulVec) E ∂S.μ) ∧
        ∀ ω, ((Q01513 c' (stateR X s ω)).map A.mulVec).support =
          cone0154 (A01514 A c' (stateR X s ω)) (b01514 A 0 c' (stateR X s ω))

def statement : Prop :=
  extensionStatement ∧ zeroIntegralStatement ∧ itoStatement ∧ localizationStatement ∧
    localizationAeStatement ∧ transformStatement ∧ incrementStatement ∧
    twoDriverIsometryStatement ∧ crossFactorStatement ∧ coefficientStatement ∧
    actualIncrementStatement ∧ kernelIsometryStatement ∧ productRuleStatement ∧
    backwardWeightStatement ∧ centeredStatement ∧ assemblyStatement ∧
    meetingVarianceFromFieldsStatement ∧ productRuleACStatement ∧ centeredACStatement ∧
    assemblyACStatement ∧ meetingVarianceFromFieldsACStatement ∧ assemblyAeStatement ∧
    meetingVarianceFromFieldsAeStatement ∧ shortRateJumpStatement ∧
    fullMeetingVarianceFromFieldsStatement ∧ sourceMeetingVarianceStatement

end Standalone.ZeroMeanReversionUpstreamBridge

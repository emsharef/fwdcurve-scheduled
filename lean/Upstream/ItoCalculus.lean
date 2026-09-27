import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Hypothesis structure for AX-03 to AX-05 (`ledger/AXIOMS.md`)

One structure, `Upstream.ItoCalculus`, whose fields are, in the order of the ledger's
"Common setting for AX-03 to AX-07":

* the data (U1), (U2): a probability measure `μ`, the filtration `ℱ`, the number `m` of
  drivers, the drivers `B`, the covariation density `c` and the integral operator `I`;
* the standing hypotheses: the usual conditions (C1), the regularity of `c` and the driver
  properties (U2);
* the axiom fields of AX-03 (`int_elementary`, `int_linear`, `int_adapted`, `int_zero`,
  `int_continuous`, `int_martingale`, `int_product_martingale`), of AX-04
  (`stopped_martingale`, `int_stopped`) and of AX-05 (`ito_formula`).

AX-06 is represented separately by `Upstream.LipschitzSDE` in
`lean/Upstream/LipschitzSDE.lean`, for Claim 025. Its generic existence and uniqueness
fields require their own audit; they do not strengthen this structure. AX-07 and AX-08
are not represented here and no current Lean proof consumes them. The two optional AX-08 fields the
ledger names, `cir_transition` (AX-08a, positive mean reversion, the noncentral chi-square
transition law) and `sqrt_transition_zero` (AX-08b, zero mean reversion, Feller's fundamental
solution with `[feller1951singular]` as source of record since the amendment of 2026-09-22),
are not added: Claim 015 derives the (AX-08b) conditional transform in the filtration `ℱ s`,
not only in `σ(X s)`, from AX-03 to AX-05 through `H0152`
(`transformStatement` in `lean/Standalone/ZeroMeanReversionUpstreamBridge.lean`), so no
consumer needs the field. Confirming the ledger's decision of 2026-09-22, revisited after Q-03
was answered and standing (the paragraph before "Lean file" in the common setting): existence
of the square-root solution is not a field either; what Feller proves is the existence and
uniqueness of the transition function of the forward equation, not of a continuous adapted
solution of (13.2) on a given filtered space with a given driver, and Claims 013 and 015 are
conditional on given solutions, which enter the consuming `lean/Novel/` theorems as hypotheses
written with the operator `I`. Re-synced field by field on 2026-09-22 against the ledger as
amended at ffff1bb73: the statements of AX-03 to AX-05 are unchanged, and the entries now
carry `Audit: ok` (ledger/AUDIT_LOG.md 2026-09-22).

Spelling choices that the ledger left to Lean:

* Time is indexed by `ℝ≥0`, as the ledger prefers; Mathlib's `IsStronglyPredictable` needs an
  index with a bottom element, which rules out `ℝ`. Lebesgue integrals in time are Mathlib's
  interval integrals `∫ s in (0:ℝ)..t`, and a time process `H : ℝ≥0 → Ω → ℝ` is evaluated at
  `(Real.toNNReal s)`, which is `s` on `[0, t]`.
* (U4) and (U5) are the predicates `U4` and `U5` below, with the square integrals written as
  lower Lebesgue integrals so that `< ⊤` is exactly finiteness. The (U6) drift class is
  `LocallyIntegrableDrift`.
* Stopping times are `WithTop ℝ≥0`-valued as in Mathlib; the ledger's `τ : Ω → ℝ≥0` is coerced.
* In `int_martingale` the square integrability `MemLp (I k H t) 2 μ` is asserted for `t ≤ T`,
  which is what the ledger's prose (AX-03c) says ("on `[0, T]`"); its informal Lean line wrote
  `∀ t`, which the source does not give for a (U5) integrand on a finite horizon.
* The driver-form process (U6) is `driverForm`, and the partial derivatives of AX-05 are
  `dT`, `dX`, `dXX` (Fréchet derivatives evaluated on the coordinate directions).

Non-vacuity instance: `ItoCalculus.zeroDriverInstance` is the instance the ledger's
non-vacuity paragraph contemplates and the Auditor's note of 2026-09-22 asked for: one driver
(`m = 1`) with zero covariation density `c ≡ 0`, zero driver `B ≡ 0` and zero integral operator
`I ≡ 0`, on the one-point space with the Dirac measure and the constant filtration. Every
field is exercised against this operator, which checks the conventions of `int_elementary`,
`int_zero`, `int_martingale` and `int_product_martingale` against each other;
`stopped_martingale` is the statement that a process constant in time stays constant when
stopped; and `ito_formula` is the chain rule for `f (t, x + ∫₀ᵗ K)` with `K` locally
integrable, proved in `chainRule_integral` by approximating `K` in `L¹` with continuous
functions, together with the predictability of `∂_i f (s, X_s) · H^{ik}` for a predictable
`H` (`predictable_const_mul`) and its local square integrability. After Q-04, the Auditor
passed this instance as degenerate under rule 6 as amended on 2026-09-22, because the fields
are cited textbook mathematics; the audits at 7f236f83b and fef7f3921 in
`ledger/AUDIT_LOG.md` confirm that standing. The instance is a genuine model of every field,
but its driver, covariation density and integral operator are identically zero. It is not
evidence that any field is non-trivially satisfiable.
Re-synced against the ledger at 99e79d64e (2026-09-23): AX-03 to AX-05
retain the same statements and fields. The new AX-09 entry is represented only by
`Upstream.Predictability` in `lean/Upstream/Predictability.lean`; it adds no field
to this structure and changes neither its hypotheses nor its instance.

Re-synced against the AX-06c/AX-10 ledger amendment at 10eda9f1f, merged on
2026-09-23: the data (U1), (U2), standing hypotheses (C1), (U2), the seven AX-03
fields, the two AX-04 fields and `ito_formula` (AX-05) retain their types above.
AX-01, AX-02 and AX-09 are unchanged as well, so `HJMScheduled` and
`Predictability` need no field or instance changes. AX-06c specifies that the
existence interface is instantiated with the chosen driver's completed natural
filtration and that filtration's integral operator. It does not identify that
operator with an integral in a larger filtration; this comparison remains an
obligation for Claim 025. AX-10 specifies a separate `ExponentialMartingale`
interface over this structure, not an additional field of `ItoCalculus`.
None of these ledger additions changes `zeroDriverInstance`. The AX-06 implementation
is a separate structure over this one, with its own degenerate consistency instance.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Upstream

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- (U4): predictable, with `∫₀ᵗ H² ds < ∞` almost surely for every `t`. -/
def U4 (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (H : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ H ∧ ∀ t : ℝ≥0, ∀ᵐ ω ∂μ,
    ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((H (Real.toNNReal s) ω) ^ 2) < ⊤

/-- (U5): (U4) together with `E ∫₀ᵀ H² ds < ∞` on the horizon `T`. -/
def U5 (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop :=
  U4 ℱ μ H ∧
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((H (Real.toNNReal s) ω) ^ 2)) ∂μ < ⊤

/-- (U6) drift class: progressively measurable with `∫₀ᵗ |K| ds < ∞` almost surely. -/
def LocallyIntegrableDrift (ℱ : Filtration ℝ≥0 m₀) (μ : Measure Ω) (K : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ K ∧ ∀ t : ℝ≥0, ∀ᵐ ω ∂μ,
    ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal |K (Real.toNNReal s) ω| < ⊤

/-- The driver-form process (U6): `X^i_t = x^i + ∑_k ∫₀ᵗ H^{ik} dB^k + ∫₀ᵗ K^i ds`. -/
noncomputable def driverForm {m n : ℕ} (I : Fin m → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (x : Fin n → ℝ) (H : Fin n → Fin m → ℝ≥0 → Ω → ℝ) (K : Fin n → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (i : Fin n) : ℝ :=
  x i + ∑ k, I k (H i k) t ω + ∫ s in (0 : ℝ)..t, K i (Real.toNNReal s) ω

/-- `∂_t f`. -/
noncomputable def dT {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  fderiv ℝ f p (1, 0)
/-- `∂_i f`. -/
noncomputable def dX {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) (i : Fin n) : ℝ :=
  fderiv ℝ f p (0, Pi.single i 1)
/-- `∂_i ∂_j f`. -/
noncomputable def dXX {n : ℕ} (f : ℝ × (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) (i j : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ f) p (0, Pi.single i 1) (0, Pi.single j 1)

/-- The hypotheses of AX-03, AX-04 and AX-05, field by field as in `ledger/AXIOMS.md`. -/
structure ItoCalculus (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  /-- The measure `Q` of (U1). -/
  μ : Measure Ω
  [isProbabilityMeasure : IsProbabilityMeasure μ]
  /-- The filtration `(F_t)_{t ≥ 0}` of (U1). -/
  ℱ : Filtration ℝ≥0 m₀
  /-- The number of drivers. -/
  m : ℕ
  /-- The drivers `B^1, …, B^m` of (U2). -/
  B : Fin m → ℝ≥0 → Ω → ℝ
  /-- The covariation density `c_{kl}` of (U2). -/
  c : Fin m → Fin m → ℝ≥0 → ℝ
  /-- The integral operator `H ↦ ∫ H dB^k`, the source's `H·M` (U7), (U8). -/
  I : Fin m → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ
  -- (C1) usual conditions
  usual_null : ∀ s : Set Ω, MeasurableSet s → μ s = 0 → MeasurableSet[ℱ 0] s
  usual_rightContinuous : ∀ t, ℱ t = ⨅ s, ⨅ (_ : t < s), ℱ s
  -- (U2) covariation density
  c_measurable : ∀ k l, Measurable (c k l)
  c_bounded_on_compacts : ∀ k l (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |c k l s| ≤ C
  c_symm : ∀ k l s, c k l s = c l k s
  -- (U2) drivers
  B_adapted : ∀ k, Adapted ℱ (B k)
  B_zero : ∀ k, B k 0 =ᵐ[μ] 0
  B_continuous : ∀ k, ∀ᵐ ω ∂μ, Continuous fun t => B k t ω
  B_memLp_two : ∀ k t, MemLp (B k t) 2 μ
  B_martingale : ∀ k, Martingale (B k) ℱ μ
  B_covariation : ∀ k l,
    Martingale (fun t ω => B k t ω * B l t ω - ∫ s in (0 : ℝ)..t, c k l (Real.toNNReal s)) ℱ μ
  -- AX-03
  /-- (AX-03a): the integral of `ξ 1_{(a,b]}` is `ξ (B^k_{t∧b} - B^k_{t∧a})`. -/
  int_elementary : ∀ k (a b : ℝ≥0) (ξ : Ω → ℝ), a ≤ b → Measurable[ℱ a] ξ →
    (∃ C, ∀ ω, |ξ ω| ≤ C) → ∀ t,
    (fun ω => I k (fun s ω => ξ ω * Set.indicator (Set.Ioc a b) 1 s) t ω) =ᵐ[μ]
      fun ω => ξ ω * (B k (min t b) ω - B k (min t a) ω)
  /-- (AX-03b): linearity on (U4). -/
  int_linear : ∀ k H K (a b : ℝ), U4 ℱ μ H → U4 ℱ μ K → ∀ t,
    I k (a • H + b • K) t =ᵐ[μ] a • I k H t + b • I k K t
  int_adapted : ∀ k H, U4 ℱ μ H → Adapted ℱ (I k H)
  int_zero : ∀ k H, U4 ℱ μ H → I k H 0 =ᵐ[μ] 0
  int_continuous : ∀ k H, U4 ℱ μ H → ∀ᵐ ω ∂μ, Continuous fun t => I k H t ω
  /-- (AX-03c), first half: on `[0, T]` the integral of a (U5) integrand is a square-integrable
  martingale. -/
  int_martingale : ∀ k H T, U5 ℱ μ H T →
    Martingale (fun t ω => I k H (min t T) ω) ℱ μ ∧ ∀ t, t ≤ T → MemLp (I k H t) 2 μ
  /-- (AX-03c), second half: the product minus `∫ H K c_{kl} ds` is a martingale on `[0, T]`. -/
  int_product_martingale : ∀ k l H K T, U5 ℱ μ H T → U5 ℱ μ K T →
    Martingale (fun t ω => I k H (min t T) ω * I l K (min t T) ω -
      ∫ s in (0 : ℝ)..(min t T : ℝ≥0), H (Real.toNNReal s) ω * K (Real.toNNReal s) ω * c k l (Real.toNNReal s)) ℱ μ
  -- AX-04
  /-- (AX-04a): optional stopping, `(i) ⇒ (iii)`, on a finite horizon. -/
  stopped_martingale : ∀ (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0),
    Martingale (fun t ω => X (min t T) ω) ℱ μ → (∀ᵐ ω ∂μ, Continuous fun t => X t ω) →
    IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) →
    Martingale (fun t ω => X (min (min t T) (τ ω)) ω) ℱ μ
  /-- (AX-04b): stopping the integral. -/
  int_stopped : ∀ k H (τ : Ω → ℝ≥0), U4 ℱ μ H → IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) →
    ∀ t, (fun ω => I k H (min t (τ ω)) ω) =ᵐ[μ]
      fun ω => I k (fun s ω => Set.indicator {s | s ≤ τ ω} (fun _ => (1 : ℝ)) s * H s ω) t ω
  -- AX-05
  /-- (AX-05): the multivariate Itô formula for driver-form processes. -/
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

/-! ### The chain rule for a locally integrable drift

`f (t, x + ∫₀ᵗ K) = f (0, x) + ∫₀ᵗ (∂_t f + ∑_i ∂_i f · K_i) ds` for `f ∈ C²` and `K ∈ L¹`,
proved by `L¹`-approximation of `K` with continuous functions, for which the identity is the
ordinary fundamental theorem of calculus. -/

section ChainRule

variable {n : ℕ}

lemma clm_apply_one_vec (L : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) (k : Fin n → ℝ) :
    L (1, k) = L (1, 0) + ∑ i, L (0, Pi.single i 1) * k i := by
  classical
  have h1 : ((1 : ℝ), k) = (1, 0) + ∑ i, k i • ((0 : ℝ), (Pi.single i 1 : Fin n → ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [h1, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma pi_norm_le_sum_abs (k : Fin n → ℝ) : ‖k‖ ≤ ∑ i, |k i| := by
  have h0 : 0 ≤ ∑ i, |k i| := Finset.sum_nonneg fun i _ => abs_nonneg (k i)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |k j|) (fun j _ => abs_nonneg (k j)) (Finset.mem_univ i)

lemma norm_one_vec_le (k : Fin n → ℝ) : ‖((1 : ℝ), k)‖ ≤ 1 + ∑ i, |k i| := by
  have h0 : 0 ≤ ∑ i, |k i| := Finset.sum_nonneg fun i _ => abs_nonneg (k i)
  rw [Prod.norm_def, norm_one]
  apply max_le (by linarith)
  linarith [pi_norm_le_sum_abs k]

lemma norm_zero_vec_le (k : Fin n → ℝ) : ‖((0 : ℝ), k)‖ ≤ ∑ i, |k i| := by
  rw [Prod.norm_def, norm_zero]
  exact max_le (Finset.sum_nonneg fun i _ => abs_nonneg (k i)) (pi_norm_le_sum_abs k)

lemma expand_bound (L L' : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) (a b : Fin n → ℝ) (M : ℝ) (hL : ‖L‖ ≤ M) :
    |L (1, a) - L' (1, b)| ≤ ‖L - L'‖ * (1 + ∑ i, |b i|) + M * ∑ i, |a i - b i| := by
  have he : L (1, a) - L' (1, b) = (L - L') (1, b) + L (0, a - b) := by
    have : ((1 : ℝ), a) = (1, b) + (0, a - b) := by ext <;> simp
    rw [this, map_add, sub_apply]
    ring
  have hM0 : 0 ≤ M := (norm_nonneg L).trans hL
  have h1 : |(L - L') (1, b)| ≤ ‖L - L'‖ * (1 + ∑ i, |b i|) := by
    rw [← Real.norm_eq_abs]
    exact ((L - L').le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_one_vec_le b) (norm_nonneg _))
  have h2 : |L (0, a - b)| ≤ M * ∑ i, |a i - b i| := by
    rw [← Real.norm_eq_abs]
    exact (L.le_opNorm _).trans (mul_le_mul hL (norm_zero_vec_le (a - b)) (norm_nonneg _) hM0)
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The chain rule `f (t, x + ∫₀ᵗ K) = f (0, x) + ∫₀ᵗ (∂_t f + ∑ ∂_i f K_i)` for `f ∈ C²` and
integrable `K`. -/
theorem chainRule_integral (x : Fin n → ℝ) (K : Fin n → ℝ → ℝ) (hK : ∀ i, Integrable (K i))
    (f : ℝ × (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0 ≤ t) :
    f (t, fun i => x i + ∫ s in (0 : ℝ)..t, K i s) = f (0, x) +
      ∫ s in (0 : ℝ)..t, (dT f (s, fun i => x i + ∫ u in (0 : ℝ)..s, K i u) +
        ∑ i, dX f (s, fun i => x i + ∫ u in (0 : ℝ)..s, K i u) i * K i s) := by
  classical
  -- continuous approximants of `K`
  have hex : ∀ (i : Fin n) (N : ℕ), ∃ g : ℝ → ℝ, Continuous g ∧ Integrable g ∧
      ∫ u, ‖K i u - g u‖ ≤ 1 / ((N : ℝ) + 1) := fun i N => by
    obtain ⟨g, -, hg, hgc, hgi⟩ := (hK i).exists_hasCompactSupport_integral_sub_le
      (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1))
    exact ⟨g, hgc, hgi, hg⟩
  choose g hgc hgi hg using hex
  set F : ℝ → Fin n → ℝ := fun s i => x i + ∫ u in (0 : ℝ)..s, K i u with hF
  set Fn : ℕ → ℝ → Fin n → ℝ := fun N s i => x i + ∫ u in (0 : ℝ)..s, g i N u with hFn
  have hεlim : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hε1 : ∀ N : ℕ, 1 / ((N : ℝ) + 1) ≤ 1 := fun N => by
    rw [div_le_one (by positivity)]; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  -- (a) uniform closeness on `[0, t]`
  have hclose : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ i, |Fn N s i - F s i| ≤ 1 / ((N : ℝ) + 1) := by
    intro N s hs i
    simp only [hFn, hF, add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub (hgi i N).intervalIntegrable (hK i).intervalIntegrable]
    calc |∫ u in (0 : ℝ)..s, (g i N u - K i u)|
        ≤ ∫ u in (0 : ℝ)..s, |g i N u - K i u| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (f := fun u => g i N u - K i u) hs.1
      _ ≤ ∫ u, |g i N u - K i u| := by
          rw [intervalIntegral.integral_of_le hs.1]
          exact setIntegral_le_integral (((hgi i N).sub (hK i)).norm)
            (Eventually.of_forall fun _ => abs_nonneg _)
      _ = ∫ u, ‖K i u - g i N u‖ := by simp only [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ 1 / ((N : ℝ) + 1) := hg i N
  have hcloseNorm : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t, ‖Fn N s - F s‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N s hs
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hclose N s hs i
  -- (b) the approximants are differentiable with derivative `g`
  have hderivFn : ∀ N s, HasDerivAt (Fn N) (fun i => g i N s) s := by
    intro N s
    rw [hasDerivAt_pi]
    intro i
    exact (intervalIntegral.integral_hasDerivAt_right ((hgc i N).intervalIntegrable 0 s)
      ((hgc i N).stronglyMeasurableAtFilter volume _) (hgc i N).continuousAt).const_add (x i)
  have hcontFn : ∀ N, Continuous (Fn N) := fun N =>
    continuous_iff_continuousAt.2 fun s => (hderivFn N s).continuousAt
  have hcontF : Continuous F := by
    refine continuous_pi fun i => continuous_const.add ?_
    exact intervalIntegral.continuous_primitive (fun a b => (hK i).intervalIntegrable) 0
  have hFn0 : ∀ N, Fn N 0 = x := fun N => by funext i; simp [hFn]
  have hcont_fderiv : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hderivG : ∀ N s, HasDerivAt (fun s => f (s, Fn N s))
      (fderiv ℝ f (s, Fn N s) (1, fun i => g i N s)) s := by
    intro N s
    have h1 : HasDerivAt (fun s => (s, Fn N s)) ((1 : ℝ), fun i => g i N s) s :=
      (hasDerivAt_id s).prodMk (hderivFn N s)
    have h2 : HasFDerivAt f (fderiv ℝ f (s, Fn N s)) (s, Fn N s) :=
      (hf.differentiable (by norm_num) _).hasFDerivAt
    exact h2.comp_hasDerivAt s h1
  have hGn_cont : ∀ N, Continuous (fun s => fderiv ℝ f (s, Fn N s) (1, fun i => g i N s)) := by
    intro N
    have h1 : Continuous (fun s => fderiv ℝ f (s, Fn N s)) :=
      hcont_fderiv.comp (continuous_id.prodMk (hcontFn N))
    have h2 : Continuous (fun s => ((1 : ℝ), fun i => g i N s)) :=
      continuous_const.prodMk (continuous_pi fun i => hgc i N)
    exact h1.clm_apply h2
  have hFTC : ∀ N, f (t, Fn N t) - f (0, x) =
      ∫ s in (0 : ℝ)..t, fderiv ℝ f (s, Fn N s) (1, fun i => g i N s) := by
    intro N
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderivG N s)
      ((hGn_cont N).intervalIntegrable 0 t), hFn0]
  -- (c) a compact set containing all the trajectories, and a bound on `‖fderiv f‖` there
  set R : ℝ := 1 + ∑ i, ∫ u, |K i u| with hR
  have hsum0 : 0 ≤ ∑ i, ∫ u, |K i u| :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun u => abs_nonneg (K i u)
  have hR1 : 1 ≤ R := by
    simp only [hR]
    linarith
  have hFball : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖F s - x‖ ≤ R - 1 := by
    intro s hs
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    simp only [Pi.sub_apply, hF, add_sub_cancel_left, Real.norm_eq_abs, hR, add_sub_cancel_left]
    calc |∫ u in (0 : ℝ)..s, K i u| ≤ ∫ u in (0 : ℝ)..s, |K i u| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (f := K i) hs.1
      _ ≤ ∫ u, |K i u| := by
          rw [intervalIntegral.integral_of_le hs.1]
          exact setIntegral_le_integral (hK i).norm (Eventually.of_forall fun _ => abs_nonneg _)
      _ ≤ ∑ j, ∫ u, |K j u| :=
          Finset.single_le_sum (f := fun j => ∫ u, |K j u|)
            (fun j _ => integral_nonneg fun u => abs_nonneg (K j u)) (Finset.mem_univ i)
  have hFnball : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t, ‖Fn N s - x‖ ≤ R := by
    intro N s hs
    calc ‖Fn N s - x‖ = ‖(Fn N s - F s) + (F s - x)‖ := by congr 1; abel
      _ ≤ ‖Fn N s - F s‖ + ‖F s - x‖ := norm_add_le _ _
      _ ≤ 1 / ((N : ℝ) + 1) + (R - 1) := add_le_add (hcloseNorm N s hs) (hFball s hs)
      _ ≤ R := by linarith [hε1 N]
  set C : Set (ℝ × (Fin n → ℝ)) := Set.Icc 0 t ×ˢ Metric.closedBall x R with hC
  have hCcomp : IsCompact C := isCompact_Icc.prod (isCompact_closedBall x R)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ C, ‖fderiv ℝ f p‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hCcomp.image_of_continuousOn hcont_fderiv.norm.continuousOn).bddAbove
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  have hM0 : 0 ≤ M := by
    have := hM (0, x) ⟨⟨le_rfl, ht⟩, Metric.mem_closedBall_self (by linarith)⟩
    exact (norm_nonneg _).trans this
  have hFC : ∀ s ∈ Set.Icc (0 : ℝ) t, (s, F s) ∈ C := fun s hs =>
    ⟨hs, by rw [Metric.mem_closedBall, dist_eq_norm]; linarith [hFball s hs]⟩
  have hFnC : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t, (s, Fn N s) ∈ C := fun N s hs =>
    ⟨hs, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hFnball N s hs⟩
  -- the limit integrand and the approximating integrands, in expanded form
  set G : ℝ → ℝ := fun s => dT f (s, F s) + ∑ i, dX f (s, F s) i * K i s with hG
  have hGeq : ∀ s, G s = fderiv ℝ f (s, F s) (1, fun i => K i s) := fun s => by
    simp only [hG, dT, dX]
    rw [clm_apply_one_vec (fderiv ℝ f (s, F s)) (fun i => K i s)]
  -- (d) pointwise bound of the difference on `[0, t]`
  set Δ : ℕ → ℝ → ℝ := fun N s => ‖fderiv ℝ f (s, Fn N s) - fderiv ℝ f (s, F s)‖ with hΔ
  have hdiff : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t,
      |fderiv ℝ f (s, Fn N s) (1, fun i => g i N s) - G s| ≤
        Δ N s * (1 + ∑ i, |K i s|) + M * ∑ i, |g i N s - K i s| := by
    intro N s hs
    rw [hGeq]
    exact expand_bound _ _ _ _ M (hM _ (hFnC N s hs))
  have hΔle : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) t, Δ N s ≤ 2 * M := by
    intro N s hs
    simp only [hΔ]
    calc ‖fderiv ℝ f (s, Fn N s) - fderiv ℝ f (s, F s)‖
        ≤ ‖fderiv ℝ f (s, Fn N s)‖ + ‖fderiv ℝ f (s, F s)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM _ (hFnC N s hs)) (hM _ (hFC s hs))
      _ = 2 * M := by ring
  have hΔcont : ∀ N, Continuous (Δ N) := fun N =>
    ((hcont_fderiv.comp (continuous_id.prodMk (hcontFn N))).sub
      (hcont_fderiv.comp (continuous_id.prodMk hcontF))).norm
  have hΔlim : ∀ s ∈ Set.Icc (0 : ℝ) t, Tendsto (fun N => Δ N s) atTop (𝓝 0) := by
    intro s hs
    have hFnlim : Tendsto (fun N => Fn N s) atTop (𝓝 (F s)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hcloseNorm N s hs) hεlim
    have h1 : Tendsto (fun N => fderiv ℝ f (s, Fn N s)) atTop (𝓝 (fderiv ℝ f (s, F s))) :=
      (hcont_fderiv.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hFnlim)
    have h2 := (h1.sub (tendsto_const_nhds (x := fderiv ℝ f (s, F s)))).norm
    simpa only [hΔ, sub_self, norm_zero] using h2
  -- integrability facts on `[0, t]`
  have hKabs : ∀ i, IntegrableOn (fun s => |K i s|) (Set.Ioc 0 t) := fun i =>
    ((hK i).norm).integrableOn
  have hsumK : IntegrableOn (fun s => 1 + ∑ i, |K i s|) (Set.Ioc 0 t) :=
    (integrableOn_const (by simp)).add (integrable_finsetSum _ fun i _ => hKabs i)
  have hgK : ∀ N i, IntegrableOn (fun s => |g i N s - K i s|) (Set.Ioc 0 t) := fun N i =>
    (((hgi i N).sub (hK i)).norm).integrableOn
  have hGint : IntegrableOn G (Set.Ioc 0 t) := by
    have hm : AEStronglyMeasurable G (volume.restrict (Set.Ioc 0 t)) := by
      have h1 : Continuous (fun s => dT f (s, F s)) :=
        (hcont_fderiv.comp (continuous_id.prodMk hcontF)).clm_apply continuous_const
      have h2 : ∀ i, Continuous (fun s => dX f (s, F s) i) := fun i =>
        (hcont_fderiv.comp (continuous_id.prodMk hcontF)).clm_apply continuous_const
      have h3 : AEStronglyMeasurable (∑ i, fun s => dX f (s, F s) i * K i s)
          (volume.restrict (Set.Ioc 0 t)) :=
        Finset.aestronglyMeasurable_sum _ fun i _ =>
          (h2 i).aestronglyMeasurable.mul (hK i).aestronglyMeasurable.restrict
      exact h1.aestronglyMeasurable.add
        (h3.congr (Eventually.of_forall fun s => by simp only [Finset.sum_apply]))
    refine (hsumK.const_mul M).mono' hm (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, hGeq]
    calc |fderiv ℝ f (s, F s) (1, fun i => K i s)|
        ≤ ‖fderiv ℝ f (s, F s)‖ * ‖((1 : ℝ), fun i => K i s)‖ :=
          (fderiv ℝ f (s, F s)).le_opNorm _
      _ ≤ M * (1 + ∑ i, |K i s|) := mul_le_mul (hM _ (hFC s hs')) (norm_one_vec_le _)
          (norm_nonneg _) hM0
  have hGnint : ∀ N, IntegrableOn (fun s => fderiv ℝ f (s, Fn N s) (1, fun i => g i N s))
      (Set.Ioc 0 t) := fun N => (hGn_cont N).integrableOn_Ioc
  have hΔK : ∀ N, IntegrableOn (fun s => Δ N s * (1 + ∑ i, |K i s|)) (Set.Ioc 0 t) := by
    intro N
    refine (hsumK.const_mul (2 * M)).mono' ((hΔcont N).aestronglyMeasurable.mul
      hsumK.aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
    exact mul_le_mul_of_nonneg_right (hΔle N s hs') (by positivity)
  have hbnd : ∀ N, IntegrableOn (fun s => Δ N s * (1 + ∑ i, |K i s|) +
      M * ∑ i, |g i N s - K i s|) (Set.Ioc 0 t) := fun N =>
    (hΔK N).add ((integrable_finsetSum _ fun i _ => hgK N i).const_mul M)
  -- (e) the bound integrals tend to zero
  have hbound1 : Tendsto (fun N => ∫ s in Set.Ioc (0 : ℝ) t, Δ N s * (1 + ∑ i, |K i s|)) atTop
      (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Ioc (0 : ℝ) t))
      (F := fun N s => Δ N s * (1 + ∑ i, |K i s|)) (f := fun _ => 0)
      (bound := fun s => 2 * M * (1 + ∑ i, |K i s|))
      (fun N => (hΔK N).aestronglyMeasurable)
      (hsumK.const_mul (2 * M))
      (fun N => ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
        have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
        exact mul_le_mul_of_nonneg_right (hΔle N s hs') (by positivity))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
        have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
        simpa using (hΔlim s hs').mul_const (1 + ∑ i, |K i s|))
    simpa using h
  have hbound2 : Tendsto (fun N => ∫ s in Set.Ioc (0 : ℝ) t, M * ∑ i, |g i N s - K i s|) atTop
      (𝓝 0) := by
    have hle : ∀ N, ∫ s in Set.Ioc (0 : ℝ) t, M * ∑ i, |g i N s - K i s| ≤
        M * ((n : ℝ) * (1 / ((N : ℝ) + 1))) := by
      intro N
      rw [integral_const_mul, integral_finsetSum _ fun i _ => hgK N i]
      refine mul_le_mul_of_nonneg_left ?_ hM0
      calc ∑ i, ∫ s in Set.Ioc (0 : ℝ) t, |g i N s - K i s|
          ≤ ∑ _i : Fin n, 1 / ((N : ℝ) + 1) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc ∫ s in Set.Ioc (0 : ℝ) t, |g i N s - K i s| ≤ ∫ s, |g i N s - K i s| :=
                  setIntegral_le_integral (((hgi i N).sub (hK i)).norm)
                    (Eventually.of_forall fun _ => abs_nonneg _)
              _ = ∫ s, ‖K i s - g i N s‖ := by simp only [Real.norm_eq_abs, abs_sub_comm]
              _ ≤ 1 / ((N : ℝ) + 1) := hg i N
        _ = (n : ℝ) * (1 / ((N : ℝ) + 1)) := by simp
    have hge : ∀ N, 0 ≤ ∫ s in Set.Ioc (0 : ℝ) t, M * ∑ i, |g i N s - K i s| := fun N =>
      integral_nonneg fun s => mul_nonneg hM0 (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hlim : Tendsto (fun N : ℕ => M * ((n : ℝ) * (1 / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using (hεlim.const_mul (n : ℝ)).const_mul M
    exact squeeze_zero hge hle hlim
  -- (f) convergence of the approximating integrals
  have hint_lim : Tendsto (fun N => ∫ s in (0 : ℝ)..t, fderiv ℝ f (s, Fn N s) (1, fun i => g i N s))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, G s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using hbound1.add hbound2)
    rw [← intervalIntegral.integral_sub ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 (hGnint N))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hGint)]
    calc ‖∫ s in (0 : ℝ)..t, (fderiv ℝ f (s, Fn N s) (1, fun i => g i N s) - G s)‖
        ≤ ∫ s in (0 : ℝ)..t, ‖fderiv ℝ f (s, Fn N s) (1, fun i => g i N s) - G s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ = ∫ s in Set.Ioc (0 : ℝ) t, |fderiv ℝ f (s, Fn N s) (1, fun i => g i N s) - G s| := by
          rw [intervalIntegral.integral_of_le ht]; simp only [Real.norm_eq_abs]
      _ ≤ ∫ s in Set.Ioc (0 : ℝ) t, (Δ N s * (1 + ∑ i, |K i s|) + M * ∑ i, |g i N s - K i s|) := by
          refine setIntegral_mono_on ((hGnint N).sub hGint).norm (hbnd N) measurableSet_Ioc
            fun s hs => ?_
          simpa only [Real.norm_eq_abs] using hdiff N s ⟨hs.1.le, hs.2⟩
      _ = (∫ s in Set.Ioc (0 : ℝ) t, Δ N s * (1 + ∑ i, |K i s|)) +
          ∫ s in Set.Ioc (0 : ℝ) t, M * ∑ i, |g i N s - K i s| :=
          integral_add (hΔK N) ((integrable_finsetSum _ fun i _ => hgK N i).const_mul M)
  -- (g) conclusion by uniqueness of limits
  have hlhs : Tendsto (fun N => f (t, Fn N t) - f (0, x)) atTop (𝓝 (f (t, F t) - f (0, x))) := by
    have hFnlim : Tendsto (fun N => Fn N t) atTop (𝓝 (F t)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hcloseNorm N t ⟨ht, le_rfl⟩) hεlim
    exact ((hf.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hFnlim)).sub
      tendsto_const_nhds
  have heq : f (t, F t) - f (0, x) = ∫ s in (0 : ℝ)..t, G s :=
    tendsto_nhds_unique (by simpa only [hFTC] using hlhs) hint_lim
  simp only [hF, hG] at heq
  linarith [heq]

end ChainRule

/-! ### Non-vacuity instance: the deterministic model with no drivers -/

namespace ItoCalculus

/-- On the one-point space with the Dirac measure, a process is a martingale for any filtration
iff it is constant in time. -/
lemma martingale_unit_iff (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit))
    (f : ℝ≥0 → Unit → ℝ) :
    Martingale f ℱ (Measure.dirac ()) ↔ ∀ i j, i ≤ j → f j () = f i () := by
  have hconst : ∀ j, f j = fun _ => f j () := fun j => funext fun u => by
    rw [Subsingleton.elim u ()]
  have hsm : ∀ i j, StronglyMeasurable[ℱ i] (f j) := fun i j => by
    rw [hconst j]; exact stronglyMeasurable_const
  have hint : ∀ j, Integrable (f j) (Measure.dirac ()) := fun j => by
    rw [hconst j]; exact integrable_const _
  constructor
  · rintro ⟨-, h⟩ i j hij
    have := h i j hij
    rw [condExp_of_stronglyMeasurable (ℱ.le i) (hsm i j) (hint j), ae_dirac_eq,
      Filter.EventuallyEq, Filter.eventually_pure] at this
    exact this
  · intro h
    refine ⟨fun i => hsm i i, fun i j hij => ?_⟩
    rw [condExp_of_stronglyMeasurable (ℱ.le i) (hsm i j) (hint j), ae_dirac_eq]
    exact Filter.eventually_pure.2 (h i j hij)

/-- Deterministic Borel functions of time are measurable for the predictable σ-algebra. -/
lemma measurable_fst_predictable {Ω' : Type*} {m' : MeasurableSpace Ω'} (ℱ : Filtration ℝ≥0 m') :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω' => p.1) := by
  have hgen : @Measurable (ℝ≥0 × Ω') ℝ≥0 ℱ.predictable
      (MeasurableSpace.generateFrom (Set.range (Set.Ioi : ℝ≥0 → Set ℝ≥0))) (fun p => p.1) := by
    refine @measurable_generateFrom (ℝ≥0 × Ω') ℝ≥0 ℱ.predictable _ _ ?_
    rintro _ ⟨a, rfl⟩
    have h : (fun p : ℝ≥0 × Ω' => p.1) ⁻¹' Set.Ioi a = Set.Ioi a ×ˢ Set.univ := by
      ext p
      simp
    rw [h]
    exact measurableSet_predictable_Ioi_prod MeasurableSet.univ
  exact hgen.mono le_rfl
    ((BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Ioi ℝ≥0)).le

/-- A deterministic Borel function of time times a predictable process is predictable. -/
lemma predictable_const_mul {Ω' : Type*} {m' : MeasurableSpace Ω'} (ℱ : Filtration ℝ≥0 m')
    (g : ℝ≥0 → ℝ) (hg : Measurable g) (H : ℝ≥0 → Ω' → ℝ) (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (fun s ω => g s * H s ω) := by
  have h1 : StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω' => g p.1) :=
    (hg.comp (measurable_fst_predictable ℱ)).stronglyMeasurable
  exact h1.mul hH

/-- The zero-driver instance: one driver with zero covariation density, zero paths and zero
integral operator, on the one-point space with the Dirac measure and the constant filtration.
Every field's shape is exercised against an actual operator; only the driver's quadratic
variation is trivial. -/
noncomputable def zeroDriverInstance : ItoCalculus Unit where
  μ := Measure.dirac ()
  ℱ := Filtration.const ℝ≥0 inferInstance le_rfl
  m := 1
  B := fun _ _ _ => 0
  c := fun _ _ _ => 0
  I := fun _ _ _ _ => 0
  usual_null := fun _ _ _ => MeasurableSpace.measurableSet_top
  usual_rightContinuous := fun t => by
    show (inferInstance : MeasurableSpace Unit) =
      ⨅ s, ⨅ (_ : t < s), (inferInstance : MeasurableSpace Unit)
    exact le_antisymm (le_iInf₂ fun _ _ => le_rfl) (iInf₂_le (t + 1) (lt_add_one t))
  c_measurable := fun _ _ => measurable_const
  c_bounded_on_compacts := fun _ _ _ => ⟨0, fun _ _ => by simp⟩
  c_symm := fun _ _ _ => rfl
  B_adapted := fun _ _ => measurable_const
  B_zero := fun _ => Filter.Eventually.of_forall fun _ => rfl
  B_continuous := fun _ => Filter.Eventually.of_forall fun _ => continuous_const
  B_memLp_two := fun _ _ => memLp_const 0
  B_martingale := fun _ => martingale_const _ _ 0
  B_covariation := fun _ _ => (martingale_unit_iff _ _).mpr fun _ _ _ => by simp
  int_elementary := fun _ _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun _ => by simp
  int_linear := fun _ _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun _ => by simp
  int_adapted := fun _ _ _ _ => measurable_const
  int_zero := fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl
  int_continuous := fun _ _ _ => Filter.Eventually.of_forall fun _ => continuous_const
  int_martingale := fun _ _ _ _ => ⟨martingale_const _ _ 0, fun _ _ => memLp_const 0⟩
  int_product_martingale := fun _ _ _ _ _ _ _ =>
    (martingale_unit_iff _ _).mpr fun _ _ _ => by simp
  stopped_martingale := fun X T τ hX _ _ => by
    rw [martingale_unit_iff] at hX ⊢
    have hconst : ∀ u, u ≤ T → X u () = X 0 () := fun u hu => by
      have := hX 0 u (zero_le : (0 : ℝ≥0) ≤ u)
      rwa [min_eq_left hu, min_eq_left (zero_le : (0 : ℝ≥0) ≤ T)] at this
    intro i j _
    rw [hconst _ (min_le_of_left_le (min_le_right _ _)),
      hconst _ (min_le_of_left_le (min_le_right _ _))]
  int_stopped := fun _ _ _ _ _ _ => Filter.Eventually.of_forall fun _ => rfl
  ito_formula := fun n x H K f hH hK hf => by
    have hK' : ∀ i (t : ℝ), 0 ≤ t →
        IntegrableOn (fun s : ℝ => K i (Real.toNNReal s) ()) (Set.Icc 0 t) := by
      intro i t ht
      have hfin := (hK i).2 t.toNNReal
      rw [ae_dirac_eq, Filter.eventually_pure, Real.coe_toNNReal t ht] at hfin
      have hmeas : AEStronglyMeasurable (fun s : ℝ => K i (Real.toNNReal s) ())
          (volume.restrict (Set.Icc 0 t)) := by
        have hp := ((hK i).1 t.toNNReal).measurable
        have hφ : Measurable (fun s : ℝ =>
            ((⟨min (Real.toNNReal s) t.toNNReal, Set.mem_Iic.mpr (min_le_right _ _)⟩ :
              Set.Iic t.toNNReal), ())) :=
          (measurable_real_toNNReal.min measurable_const).subtype_mk.prodMk measurable_const
        have hc : Measurable (fun s : ℝ => K i (min (Real.toNNReal s) t.toNNReal) ()) :=
          hp.comp hφ
        refine hc.aestronglyMeasurable.congr ?_
        exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs => by
          simp only [min_eq_left (Real.toNNReal_le_toNNReal hs.2)]
      exact ⟨hmeas, by rw [hasFiniteIntegral_iff_norm]; simpa only [Real.norm_eq_abs] using hfin⟩
    -- the deterministic state path is continuous in time
    have hXcont : ∀ i, Continuous
        (fun s : ℝ≥0 => driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s () i) := by
      intro i
      simp only [driverForm, Finset.sum_const_zero, add_zero]
      refine continuous_const.add ?_
      rw [continuous_iff_continuousAt]
      intro s
      have hI : IntegrableOn (fun u : ℝ => K i (Real.toNNReal u) ()) (Set.uIcc 0 ((s : ℝ) + 1)) := by
        rw [Set.uIcc_of_le (by positivity)]
        exact hK' i _ (by positivity)
      have hprim := intervalIntegral.continuousOn_primitive_interval hI
      rw [Set.uIcc_of_le (by positivity)] at hprim
      have hmaps : Set.MapsTo (fun u : ℝ≥0 => (u : ℝ)) (Set.Iic (s + 1))
          (Set.Icc 0 ((s : ℝ) + 1)) := by
        intro u hu
        refine ⟨u.coe_nonneg, ?_⟩
        have : u ≤ s + 1 := Set.mem_Iic.mp hu
        exact_mod_cast this
      exact (hprim.comp NNReal.continuous_coe.continuousOn hmaps).continuousAt
        (Iic_mem_nhds (lt_add_one s))
    have hcont_fderiv : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have hX : Continuous (fun s : ℝ≥0 => driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s ()) :=
      continuous_pi hXcont
    have hg : ∀ i, Continuous (fun s : ℝ≥0 =>
        dX f ((s : ℝ), driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s ()) i) := fun i =>
      (hcont_fderiv.comp (NNReal.continuous_coe.prodMk hX)).clm_apply continuous_const
    refine ⟨fun i k => ?_, Filter.Eventually.of_forall fun ω t => ?_⟩
    · have hfun : (fun (s : ℝ≥0) (ω : Unit) =>
          dX f ((s : ℝ), driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s ω) i * H i k s ω) =
          fun (s : ℝ≥0) ω =>
            dX f ((s : ℝ), driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s ()) i * H i k s ω := by
        funext s ω
        cases ω
        rfl
      rw [hfun]
      refine ⟨predictable_const_mul _ _ (hg i).measurable _ (hH i k).1, fun t => ?_⟩
      have hfin := (hH i k).2 t
      rw [ae_dirac_eq, Filter.eventually_pure] at hfin ⊢
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : ℝ≥0, s ≤ t →
          |dX f ((s : ℝ), driverForm (fun _ _ _ _ => (0 : ℝ)) x H K s ()) i| ≤ C := by
        obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image_of_continuousOn
          (hg i).norm.continuousOn).bddAbove
        refine ⟨C, fun s hs => ?_⟩
        have := hC ⟨s, ⟨(zero_le : (0 : ℝ≥0) ≤ s), hs⟩, rfl⟩
        simpa only [Real.norm_eq_abs] using this
      calc ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal
            ((dX f (((Real.toNNReal s : ℝ≥0) : ℝ),
              driverForm (fun _ _ _ _ => (0 : ℝ)) x H K (Real.toNNReal s) ()) i *
              H i k (Real.toNNReal s) ()) ^ 2)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (C ^ 2) *
              ENNReal.ofReal ((H i k (Real.toNNReal s) ()) ^ 2) := by
            refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
            rw [← ENNReal.ofReal_mul (sq_nonneg C)]
            apply ENNReal.ofReal_le_ofReal
            have hs' : Real.toNNReal s ≤ t :=
              (Real.toNNReal_le_toNNReal hs.2).trans_eq (Real.toNNReal_coe)
            have hb := abs_le.mp (hC _ hs')
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (sq_le_sq' hb.1 hb.2) (sq_nonneg _)
        _ = ENNReal.ofReal (C ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((H i k (Real.toNNReal s) ()) ^ 2) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    · cases ω
      have hmain := chainRule_integral x
        (fun i => (Set.Icc (0 : ℝ) t).indicator (fun s => K i (Real.toNNReal s) ()))
        (fun i => (hK' i t t.coe_nonneg).integrable_indicator measurableSet_Icc) f hf t t.coe_nonneg
      have hFeq : ∀ s ∈ Set.Icc (0 : ℝ) t,
          (fun i => x i + ∫ u in (0 : ℝ)..s,
            (Set.Icc (0 : ℝ) t).indicator (fun u => K i (Real.toNNReal u) ()) u) =
          driverForm (fun _ _ _ _ => (0 : ℝ)) x H K (Real.toNNReal s) () := by
        intro s hs
        funext i
        simp only [driverForm, Finset.sum_const_zero, add_zero, Real.coe_toNNReal s hs.1]
        congr 1
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hs.1] at hu
        have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨hu.1, hu.2.trans hs.2⟩
        exact Set.indicator_of_mem hu' _
      have hFeqT : (fun i => x i + ∫ u in (0 : ℝ)..t,
            (Set.Icc (0 : ℝ) t).indicator (fun u => K i (Real.toNNReal u) ()) u) =
          driverForm (fun _ _ _ _ => (0 : ℝ)) x H K t () := by
        have := hFeq (t : ℝ) (Set.mem_Icc.mpr ⟨t.coe_nonneg, le_rfl⟩)
        rwa [Real.toNNReal_coe] at this
      simp only [Finset.sum_const_zero, mul_zero, add_zero]
      rw [← hFeqT, hmain]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      beta_reduce
      rw [hFeq s hs]
      simp only [Set.indicator_of_mem hs]

end ItoCalculus

end Upstream

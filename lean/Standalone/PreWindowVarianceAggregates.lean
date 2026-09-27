import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Standalone.LateAmericanExercise

/-! # Claim 020: contracts settled after a date see the earlier variances only through their sum

Partial target. It states, in Claim 011's explicit Gaussian model: (a) the post-window curve
identity (20.3) and the jump identity; (b) the discount density (20.5) has expectation one,
the normalized earlier state has the centered Gaussian law of variance `V_k`, and the
change-of-measure identity (20.6) for every measurable integrand of the earlier state and the
unrevealed shocks; (e) exact compounding across a partition with no meeting strictly inside a
fixing interval, integrability of the compounded rate, and the initial quote formula (20.11);
(c) the bank-account ratio after the observation date as an explicit function of the
post-window state, and the time-zero price (20.7) of every integrable payoff of that state
settled after the date; (f), identification: with a common unrevealed block, equal
`(V_k, H_k)` give equal quote exponents for every window opening after the revealed meetings,
equal quotes are equal exponents, and two windows with distinct closes recover `(V_k, H_k)`;
(f), bounds: for three revealed meetings the polytope (20.12) is nonempty iff
`T_1 V ≤ H ≤ T_3 V`, every point satisfies the bounds (20.13), both endpoints of the middle
coordinate are attained at the displayed points, and the example pair at dates `(1, 2, 3)`
lies in the polytope with `s_* = 7ε`; (f), pair equality for (c): two variance vectors with a
common unrevealed block and equal `V_k` give equal time-zero prices for every contract of
(c); and (f), the general polytope: for any number of revealed meetings with nondecreasing
dates and nonnegative `V`, the polytope (20.12) is nonempty iff `T_1 V ≤ H ≤ T_k V`, with a
point supported on the first and last coordinates. and (b), residuals: for `V_k > 0` the residuals `ξ_i` are jointly Gaussian under the
discounted measure, independent of `(y, Z_{>k})`, and recover the revealed shocks with `y`.
It also states the exact σ-algebra identity (20.4), that the curve on `[A, t]` generates the
same σ-algebra as `(y, Z_i : k < i ≤ j(t))`, and the degenerate case `V_k = 0`, in which
every revealed shock and `y` vanish almost surely under the discounted measure; and the
σ-algebra form of the residual statement, `σ(Z_1, …, Z_k) = σ(y, ξ_1, …, ξ_k)` exactly for
`V_k > 0`; and, for the general polytope, that each coordinate's values are dominated above
and below at points with at most two nonzero coordinates, so its extremes are attained there.
Of part (d) it states the state-rule half: for payoffs with the bound (20.8), every admissible
exercise time has an integrable discounted payoff bounded by the discounted bound, every rule
consulting only the post-window state is admissible with the auxiliary value of (20.10), the
state-rule value is a lower bound for the American value (20.9), and it depends on the
revealed variances only through `V_k`; and, as the first step of the sectioning argument,
the product realization of the discounted measure under `ω ↦ (ξ, (y, Z_{>k}))` with its
measurable inverse. The reverse inequality of (20.10), the sectioning of exercise times
along the residuals, is not yet asserted.
-/
open MeasureTheory ProbabilityTheory Set
namespace Standalone.PreWindowVarianceAggregates
abbrev Ω (N : ℕ) := Fin N → ℝ
noncomputable def Q {N : ℕ} (v : Fin N → NNReal) : Measure (Ω N) :=
  Measure.infinitePi fun i => gaussianReal 0 (v i)
def filt {N : ℕ} (τ : ℕ → ℝ) : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N)) where
  seq t := ⨆ (i : Fin N) (_ : τ (i.val + 1) ≤ t),
    MeasurableSpace.comap (fun ω : Ω N => ω i) inferInstance
  mono' := fun _ _ hst => iSup_mono fun _ => iSup_mono' fun h => ⟨h.trans hst, le_rfl⟩
  le' := fun _ => iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

noncomputable def r {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val + 1) ≤ t then ω i + (v i : ℝ) * (t - τ (i.val + 1)) else 0
noncomputable def Δr {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (i : Fin N) (ω : Ω N) : ℝ :=
  r τ v (τ (i.val+1)) ω - Function.leftLim (fun t => r τ v t ω) (τ (i.val+1))
noncomputable def logB {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) (ω : Ω N) : ℝ :=
  ∫ u in (0 : ℝ)..t, r τ v u ω
noncomputable def f {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val+1) ≤ t then ω i+(v i : ℝ)*(U-τ (i.val+1)) else 0
noncomputable def P {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  Real.exp (-(∫ u in t..U, f τ v t u ω))
noncomputable def L0202 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (j : Fin J) (ω : Ω N) : ℝ :=
  ((P τ v (u j.castSucc) (u j.succ) ω)⁻¹-1)/(u j.succ-u j.castSucc)
noncomputable def R0202 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (ω : Ω N) : ℝ :=
  ((∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0202 τ v u j ω))-1)/(u (Fin.last J)-u 0)

/-- The meetings revealed at `A` (the claim's `1, …, k`). -/
noncomputable def past {N : ℕ} (τ : ℕ → ℝ) (A : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => τ (i.val+1) ≤ A
/-- The meetings unrevealed at `A`, as an index set. -/
def later (N : ℕ) (τ : ℕ → ℝ) (A : ℝ) : Set (Fin N) := {i | A < τ (i.val+1)}
/-- `V_k = ∑_{i ≤ k} v_i` of (20.2). -/
noncomputable def Vk {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) : ℝ :=
  ∑ i ∈ past τ A, (v i : ℝ)
/-- `H_k = ∑_{i ≤ k} T_i v_i` of (20.2). -/
noncomputable def Hk {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) : ℝ :=
  ∑ i ∈ past τ A, τ (i.val+1) * (v i : ℝ)
/-- `Q̃ = B_A^{-1} · Q` of (b). -/
noncomputable def Qtilde {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (Real.exp (-logB τ v A ω)))
/-- The law of the unrevealed shocks `Z_{>k}`. -/
noncomputable def Qlater {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) :
    Measure (later N τ A → ℝ) :=
  Measure.infinitePi fun i : later N τ A => gaussianReal 0 (v i.1)

/-- (a): the curve and short rate after `A` (20.3), and the jump identity. -/
def curveStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), StrictMonoOn τ (Iic N) →
    ∀ A t U : ℝ, A ≤ t → t ≤ U → ∀ ω : Ω N,
    f τ v t U ω = r τ v A ω + Vk τ v A * (U - A) +
      ∑ i ∈ Finset.univ.filter (fun i => A < τ (i.val+1) ∧ τ (i.val+1) ≤ t),
        (ω i + (v i : ℝ) * (U - τ (i.val+1))) ∧
    r τ v t ω = r τ v A ω + Vk τ v A * (t - A) +
      ∑ i ∈ Finset.univ.filter (fun i => A < τ (i.val+1) ∧ τ (i.val+1) ≤ t),
        (ω i + (v i : ℝ) * (t - τ (i.val+1))) ∧
    ∀ i, Δr τ v i ω = ω i

/-- (b): the discount density (20.5), the normalized law of `y = r_A`, and (20.6). -/
def discountStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A : ℝ, 0 ≤ A →
    (∫ ω, Real.exp (-logB τ v A ω) ∂Q v) = 1 ∧
    IsProbabilityMeasure (Qtilde τ v A) ∧
    HasLaw (r τ v A) (gaussianReal 0 (∑ i ∈ past τ A, v i)) (Qtilde τ v A) ∧
    (∀ Φ : ℝ × (later N τ A → ℝ) → ℝ, Measurable Φ →
      Integrable (fun ω => Real.exp (-logB τ v A ω) *
        Φ (r τ v A ω, (later N τ A).domRestrict ω)) (Q v) →
      (∫ ω, Real.exp (-logB τ v A ω) * Φ (r τ v A ω, (later N τ A).domRestrict ω) ∂Q v) =
        ∫ y, ∫ z, Φ (y, z) ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i))

/-- (e): exact compounding with meetings allowed at partition points, and the initial quote
(20.11) as the `Q`-expectation of the compounded rate. -/
def futuresStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) → 0 < J →
    ∀ u : Fin (J+1) → ℝ, StrictMono u → 0 ≤ u 0 →
    (∀ (j : Fin J) (i : Fin N), ¬ (u j.castSucc < τ (i.val+1) ∧ τ (i.val+1) < u j.succ)) →
    (∀ ω, (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0202 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) ∧
    Integrable (R0202 τ v u) (Q v) ∧
    (∫ ω, R0202 τ v u ω ∂Q v) =
      (Real.exp (∑ i, (if τ (i.val+1) ≤ u 0 then
          (u (Fin.last J)-u 0)*(v i : ℝ)*(u (Fin.last J)-τ (i.val+1))
        else if τ (i.val+1) ≤ u (Fin.last J) then (v i : ℝ)*(u (Fin.last J)-τ (i.val+1))^2
        else 0))-1)/(u (Fin.last J)-u 0)

/-- A vector of unrevealed coordinates extended by zero to all meetings. -/
noncomputable def extLater {N : ℕ} (τ : ℕ → ℝ) (A : ℝ) (z : later N τ A → ℝ) (i : Fin N) : ℝ :=
  if h : A < τ (i.val+1) then z ⟨i, h⟩ else 0
/-- The accrued bank-account exponent `∫_A^S r_s ds` as a function of the post-window state
`(y, Z_{>k})`, by (20.3). -/
noncomputable def accrualAfter {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S : ℝ)
    (y : ℝ) (z : later N τ A → ℝ) : ℝ :=
  y*(S-A) + Vk τ v A*(S-A)^2/2 +
    ∑ i, (if A < τ (i.val+1) ∧ τ (i.val+1) ≤ S then
      extLater τ A z i*(S-τ (i.val+1)) + (v i : ℝ)*(S-τ (i.val+1))^2/2 else 0)

/-- (c): the bank-account ratio after `A` is the explicit function `accrualAfter` of the
post-window state, and the time-zero price (20.7) of a payoff of that state settled at `S`. -/
def priceStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    (∀ ω : Ω N, logB τ v S ω - logB τ v A ω =
      accrualAfter τ v A S (r τ v A ω) ((later N τ A).domRestrict ω)) ∧
    ∀ Ψ : ℝ × (later N τ A → ℝ) → ℝ, Measurable Ψ →
      Integrable (fun ω => Real.exp (-logB τ v S ω) *
        Ψ (r τ v A ω, (later N τ A).domRestrict ω)) (Q v) →
      (∫ ω, Real.exp (-logB τ v S ω) * Ψ (r τ v A ω, (later N τ A).domRestrict ω) ∂Q v) =
        ∫ y, ∫ z, Real.exp (-accrualAfter τ v A S y z) * Ψ (y, z)
          ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i)

/-- The exponent of the initial quote (20.11). -/
noncomputable def quoteExponent {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (a b : ℝ) : ℝ :=
  ∑ i, (if τ (i.val+1) ≤ a then (b-a)*(v i : ℝ)*(b-τ (i.val+1))
    else if τ (i.val+1) ≤ b then (v i : ℝ)*(b-τ (i.val+1))^2 else 0)

/-- (f), identification: with a common unrevealed block, equal `(V_k, H_k)` give equal quote
exponents for every window opening after the revealed meetings; equal quotes are equal
exponents; and two windows with distinct closes recover `(V_k, H_k)`. -/
def identificationStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal) (A : ℝ),
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) →
    (Vk τ v A = Vk τ v' A → Hk τ v A = Hk τ v' A →
      ∀ a b : ℝ, (∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a) →
        quoteExponent τ v a b = quoteExponent τ v' a b) ∧
    (∀ a b : ℝ, a < b →
      ((Real.exp (quoteExponent τ v a b)-1)/(b-a) = (Real.exp (quoteExponent τ v' a b)-1)/(b-a) ↔
        quoteExponent τ v a b = quoteExponent τ v' a b)) ∧
    (∀ a b a' b' : ℝ, a < b → a' < b' → b ≠ b' →
      (∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a) → (∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a') →
      quoteExponent τ v a b = quoteExponent τ v' a b →
      quoteExponent τ v a' b' = quoteExponent τ v' a' b' →
      Vk τ v A = Vk τ v' A ∧ Hk τ v A = Hk τ v' A)

/-- `s_*` of (20.13). -/
noncomputable def sStar (T1 T2 T3 V H : ℝ) : ℝ :=
  min ((H - T1*V)/(T2-T1)) ((T3*V - H)/(T3-T2))

/-- (f), the polytope (20.12) for three revealed meetings: it is nonempty iff
`T_1 V ≤ H ≤ T_3 V`, every point satisfies the bounds (20.13), and both endpoints of the middle
coordinate are attained at points with the displayed coordinates; and the example pair of
(20.13) at dates `(1, 2, 3)`. -/
def boundsStatement : Prop :=
  ∀ T1 T2 T3 V H : ℝ, T1 < T2 → T2 < T3 →
    ((∃ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = V ∧
        T1*x 0 + T2*x 1 + T3*x 2 = H) ↔ (T1*V ≤ H ∧ H ≤ T3*V)) ∧
    (T1*V ≤ H → H ≤ T3*V →
      0 ≤ sStar T1 T2 T3 V H ∧
      (∀ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) → x 0 + x 1 + x 2 = V →
        T1*x 0 + T2*x 1 + T3*x 2 = H →
        x 1 ≤ sStar T1 T2 T3 V H ∧
        (T3*V - H - (T3-T2)*sStar T1 T2 T3 V H)/(T3-T1) ≤ x 0 ∧
        x 0 ≤ (T3*V - H)/(T3-T1) ∧
        (H - T1*V - (T2-T1)*sStar T1 T2 T3 V H)/(T3-T1) ≤ x 2 ∧
        x 2 ≤ (H - T1*V)/(T3-T1)) ∧
      (∃ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = V ∧
        T1*x 0 + T2*x 1 + T3*x 2 = H ∧ x 1 = 0 ∧
        x 0 = (T3*V - H)/(T3-T1) ∧ x 2 = (H - T1*V)/(T3-T1)) ∧
      (∃ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = V ∧
        T1*x 0 + T2*x 1 + T3*x 2 = H ∧ x 1 = sStar T1 T2 T3 V H ∧
        x 0 = (T3*V - H - (T3-T2)*sStar T1 T2 T3 V H)/(T3-T1) ∧
        x 2 = (H - T1*V - (T2-T1)*sStar T1 T2 T3 V H)/(T3-T1)))

/-- The example pair of (f): at dates `(1, 2, 3)` the vectors `(2,3,2)ε` and `(3,1,3)ε` are
distinct, strictly positive, share `V = 7ε` and `H = 14ε`, and `s_* = 7ε`. -/
def exampleBoundsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    let x : Fin 3 → ℝ := ![2*ε, 3*ε, 2*ε]
    let x' : Fin 3 → ℝ := ![3*ε, ε, 3*ε]
    x ≠ x' ∧ (∀ i, 0 < x i ∧ 0 < x' i) ∧
    x 0 + x 1 + x 2 = 7*ε ∧ x' 0 + x' 1 + x' 2 = 7*ε ∧
    1*x 0 + 2*x 1 + 3*x 2 = 14*ε ∧ 1*x' 0 + 2*x' 1 + 3*x' 2 = 14*ε ∧
    sStar 1 2 3 (7*ε) (14*ε) = 7*ε

/-- (f), pair equality for (c): two variance vectors with a common unrevealed block and equal
`V_k` give equal time-zero prices for every contract of (c). -/
def pairPriceStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A →
    ∀ Ψ : ℝ × (later N τ A → ℝ) → ℝ, Measurable Ψ →
      Integrable (fun ω => Real.exp (-logB τ v S ω) *
        Ψ (r τ v A ω, (later N τ A).domRestrict ω)) (Q v) →
      Integrable (fun ω => Real.exp (-logB τ v' S ω) *
        Ψ (r τ v' A ω, (later N τ A).domRestrict ω)) (Q v') →
      (∫ ω, Real.exp (-logB τ v S ω) * Ψ (r τ v A ω, (later N τ A).domRestrict ω) ∂Q v) =
        ∫ ω, Real.exp (-logB τ v' S ω) * Ψ (r τ v' A ω, (later N τ A).domRestrict ω) ∂Q v'

/-- (f), the general polytope (20.12): with nondecreasing dates and `0 ≤ V`, it is nonempty
iff `T_1 V ≤ H ≤ T_k V`, and then contains a point supported on the first and last dates. -/
def polytopeStatement : Prop :=
  ∀ (m : ℕ) (T : Fin (m+1) → ℝ) (V H : ℝ), Monotone T → 0 ≤ V →
    ((∃ x : Fin (m+1) → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = V ∧ ∑ i, T i * x i = H) ↔
      (T 0 * V ≤ H ∧ H ≤ T (Fin.last m) * V)) ∧
    (T 0 * V ≤ H → H ≤ T (Fin.last m) * V →
      ∃ x : Fin (m+1) → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = V ∧ ∑ i, T i * x i = H ∧
        ∀ i, i ≠ 0 → i ≠ Fin.last m → x i = 0)

/-- The meetings revealed at `A`, as an index set. -/
def earlier (N : ℕ) (τ : ℕ → ℝ) (A : ℝ) : Set (Fin N) := {i | τ (i.val+1) ≤ A}
/-- The residuals `ξ_i = Z_i + v_i h_i − (v_i/V_k) y` of (b). -/
noncomputable def resid {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) (i : earlier N τ A)
    (ω : Ω N) : ℝ :=
  ω i.1 + (v i.1 : ℝ) * (A - τ (i.1.val+1)) - ((v i.1 : ℝ) / Vk τ v A) * r τ v A ω

/-- (b), residuals: for `V_k > 0`, under `Q̃` the residuals are jointly Gaussian and independent
of `(y, Z_{>k})`, and each revealed shock is recovered from its residual and `y`. -/
def residualStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A : ℝ, 0 ≤ A → 0 < Vk τ v A →
    HasGaussianLaw (fun ω (i : earlier N τ A) => resid τ v A i ω) (Qtilde τ v A) ∧
    IndepFun (fun ω (i : earlier N τ A) => resid τ v A i ω)
      (fun ω => (r τ v A ω, (later N τ A).domRestrict ω)) (Qtilde τ v A) ∧
    ∀ (i : earlier N τ A) (ω : Ω N), ω i.1 + (v i.1 : ℝ) * (A - τ (i.1.val+1)) =
      resid τ v A i ω + ((v i.1 : ℝ) / Vk τ v A) * r τ v A ω

/-- The meetings revealed in `(A, t]`. -/
def revealedIn (N : ℕ) (τ : ℕ → ℝ) (A t : ℝ) : Set (Fin N) :=
  {i | A < τ (i.val+1) ∧ τ (i.val+1) ≤ t}
/-- The σ-algebra generated by the curve on `[A, t]`. -/
noncomputable def curveAlg {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A t : ℝ) : MeasurableSpace (Ω N) :=
  ⨆ (s : ℝ) (_ : s ∈ Icc A t) (U : ℝ), MeasurableSpace.comap (f τ v s U) inferInstance
/-- The σ-algebra generated by the post-window state `(y, Z_i : k < i ≤ j(t))`. -/
noncomputable def stateAlg {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A t : ℝ) : MeasurableSpace (Ω N) :=
  MeasurableSpace.comap (fun ω => (r τ v A ω, (revealedIn N τ A t).domRestrict ω)) inferInstance

/-- (20.4), exactly: the σ-algebra generated by the curve on `[A, t]` equals the one generated
by the post-window state `(y, Z_i : k < i ≤ j(t))`; the identity with the null sets adjoined
follows. -/
def sigmaAlgebraStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), StrictMonoOn τ (Iic N) →
    ∀ A t : ℝ, A ≤ t → curveAlg τ v A t = stateAlg τ v A t

/-- (b), the degenerate case `V_k = 0`: under `Q̃` every revealed shock and `y` vanish almost
surely. -/
def degenerateStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A : ℝ, 0 ≤ A → Vk τ v A = 0 →
    (∀ i : earlier N τ A, ∀ᵐ ω ∂Qtilde τ v A, ω i.1 = 0) ∧ (∀ᵐ ω ∂Qtilde τ v A, r τ v A ω = 0)

/-- The σ-algebra generated by the revealed shocks `Z_1, …, Z_k`. -/
noncomputable def revealedAlg {N : ℕ} (τ : ℕ → ℝ) (A : ℝ) : MeasurableSpace (Ω N) :=
  MeasurableSpace.comap (earlier N τ A).domRestrict inferInstance
/-- The σ-algebra generated by `(y, ξ_1, …, ξ_k)`. -/
noncomputable def residAlg {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) :
    MeasurableSpace (Ω N) :=
  MeasurableSpace.comap (fun ω => (r τ v A ω, fun i : earlier N τ A => resid τ v A i ω))
    inferInstance

/-- (b), the σ-algebra form of the residual statement: for `V_k > 0`,
`σ(Z_1, …, Z_k) = σ(y, ξ_1, …, ξ_k)` exactly. -/
def residualAlgebraStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ), 0 < Vk τ v A →
    revealedAlg τ A = residAlg τ v A

/-- (f), the general polytope: every value of a coordinate at a point of the polytope (20.12)
is dominated above and below by its values at points of the polytope with at most two
nonzero coordinates, so each coordinate's extremes over the polytope are attained at such
points. -/
def extremeStatement : Prop :=
  ∀ (m : ℕ) (T : Fin (m+1) → ℝ) (x : Fin (m+1) → ℝ), (∀ j, 0 ≤ x j) → ∀ i : Fin (m+1),
    (∃ x' : Fin (m+1) → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (∃ a b, ∀ j, j ≠ a → j ≠ b → x' j = 0) ∧ x i ≤ x' i) ∧
    (∃ x' : Fin (m+1) → ℝ, (∀ j, 0 ≤ x' j) ∧ ∑ j, x' j = ∑ j, x j ∧
      ∑ j, T j * x' j = ∑ j, T j * x j ∧ (∃ a b, ∀ j, j ≠ a → j ≠ b → x' j = 0) ∧ x' i ≤ x i)

section American
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)

/-- The post-window state map `ω ↦ (y, Z_{>k})`. -/
noncomputable def stateMap {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) (ω : Ω N) :
    ℝ × (later N τ A → ℝ) :=
  (r τ v A ω, (later N τ A).domRestrict ω)

/-- The coordinates of the post-window state: `none` is `y`, `some i` is the shock `Z_i`. -/
def stateProj (N : ℕ) (τ : ℕ → ℝ) (A : ℝ) : Option (later N τ A) → ℝ × (later N τ A → ℝ) → ℝ
  | none => Prod.fst
  | some i => fun p => p.2 i
/-- Whether a state coordinate is revealed by `t`: `y` always, `Z_i` when `T_i ≤ t`. -/
def revealedBy (N : ℕ) (τ : ℕ → ℝ) (A : ℝ) : Option (later N τ A) → ℝ → Prop
  | none => fun _ => True
  | some i => fun t => τ (i.1.val+1) ≤ t
lemma revealedBy_mono {N : ℕ} {τ : ℕ → ℝ} {A : ℝ} (i : Option (later N τ A)) {s t : ℝ}
    (hst : s ≤ t) (h : revealedBy N τ A i s) : revealedBy N τ A i t := by
  cases i with
  | none => trivial
  | some i => exact le_trans h hst
lemma stateProj_measurable {N : ℕ} {τ : ℕ → ℝ} {A : ℝ} (i : Option (later N τ A)) :
    Measurable (stateProj N τ A i) := by
  cases i with
  | none => exact measurable_fst
  | some i => exact (measurable_pi_apply i).comp measurable_snd
/-- The filtration of the post-window state: `y` together with the unrevealed shocks revealed
by `t`, the exact form of `G_t` in (20.4) on the state space. -/
noncomputable def stateFilt (N : ℕ) (τ : ℕ → ℝ) (A : ℝ) :
    Filtration ℝ (inferInstance : MeasurableSpace (ℝ × (later N τ A → ℝ))) where
  seq t := ⨆ (i : Option (later N τ A)) (_ : revealedBy N τ A i t),
    MeasurableSpace.comap (stateProj N τ A i) inferInstance
  mono' := fun _ _ hst => iSup_mono fun i => iSup_mono' fun h => ⟨revealedBy_mono i hst h, le_rfl⟩
  le' := fun _ => iSup₂_le fun i _ => (stateProj_measurable i).comap_le

/-- Exercise rules that consult only the post-window state: measurable stopping times of the
state filtration with values in `[A, S]`, the rules `ρ ∈ 𝒯̃[A, S]` of (20.10). -/
def stateRules (N : ℕ) (τ : ℕ → ℝ) (A S : ℝ) : Set (ℝ × (later N τ A → ℝ) → ℝ) :=
  {ρ | Measurable ρ ∧ (∀ p, ρ p ∈ Icc A S) ∧
    IsStoppingTime (stateFilt N τ A) (fun p => (ρ p : WithTop ℝ))}

/-- The discounted payoff `B_σ^{-1} Φ(σ, y, Z_{>k})` of (d) at an exercise time `σ`. -/
noncomputable def pay020 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (σ : Ωc v → ℝ) (ω : Ωc v) : ℝ :=
  Real.exp (-logB τ v (σ ω) ω) * Φ (σ ω, stateMap τ v A ω)

/-- The American value (20.9): the supremum over all admissible exercise times. -/
noncomputable def U020 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S : ℝ)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) : ℝ :=
  sSup ((fun σ => ∫ ω, pay020 τ v A Φ σ ω ∂Qc v) '' T0183 τ v A S)

/-- The value over the state rules, the right side of (20.10) realized on the model. -/
noncomputable def Ustate020 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S : ℝ)
    (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) : ℝ :=
  sSup ((fun ρ => ∫ ω, pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω ∂Qc v) ''
    stateRules N τ A S)

/-- (d), the state-rule half: for a payoff of the exercise time and the post-window state
with the bound (20.8), every admissible exercise time has an integrable discounted payoff
bounded by the discounted bound, so the American value is finite; every state rule is an
admissible exercise time whose value is the auxiliary integral of (20.10); and the state-rule
value is a lower bound for the American value. -/
def americanStateStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    (∀ σ ∈ T0183 τ v A S, Integrable (pay020 τ v A Φ σ) (Qc v) ∧
      |∫ ω, pay020 τ v A Φ σ ω ∂Qc v| ≤
        ∫ ω, Real.exp (-logB τ v A ω) * D (stateMap τ v A ω) ∂Q v) ∧
    (∀ ρ ∈ stateRules N τ A S, (fun ω : Ωc v => ρ (stateMap τ v A ω)) ∈ T0183 τ v A S ∧
      (∫ ω, pay020 τ v A Φ (fun ω => ρ (stateMap τ v A ω)) ω ∂Qc v) =
        ∫ y, ∫ z, Real.exp (-accrualAfter τ v A (ρ (y, z)) y z) * Φ (ρ (y, z), (y, z))
          ∂Qlater τ v A ∂gaussianReal 0 (∑ i ∈ past τ A, v i)) ∧
    Ustate020 τ v A S Φ ≤ U020 τ v A S Φ

/-- (d), the aggregate dependence of the state-rule value: with a common unrevealed block and
equal `V_k`, the state-rule values agree. -/
def americanAggregateStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    Integrable (fun ω => Real.exp (-logB τ v' A ω) * D (stateMap τ v' A ω)) (Q v') →
    Ustate020 τ v A S Φ = Ustate020 τ v' A S Φ

/-- The residual vector `ξ = (ξ_i)_{i ≤ k}`. -/
noncomputable def residMap {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) (ω : Ω N) :
    earlier N τ A → ℝ :=
  fun i => resid τ v A i ω
/-- The realization map `ω ↦ (ξ, (y, Z_{>k}))` of the sectioning argument. -/
noncomputable def realize {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) (ω : Ω N) :
    (earlier N τ A → ℝ) × (ℝ × (later N τ A → ℝ)) :=
  (residMap τ v A ω, stateMap τ v A ω)
/-- Its inverse for `V_k > 0`: `Z_i = ξ_i + (v_i/V_k) y − v_i h_i` on the revealed meetings and
`Z_i` itself on the unrevealed ones. -/
noncomputable def unrealize {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ)
    (q : (earlier N τ A → ℝ) × (ℝ × (later N τ A → ℝ))) : Ω N :=
  fun i => if h : τ (i.val+1) ≤ A then
      q.1 ⟨i, h⟩ + ((v i : ℝ) / Vk τ v A) * q.2.1 - (v i : ℝ) * (A - τ (i.val+1))
    else if h' : A < τ (i.val+1) then q.2.2 ⟨i, h'⟩ else 0

/-- (d), the product realization of the sectioning argument: for `V_k > 0` the realization map
is a measurable injection with a measurable left inverse, the post-window state has under `Q̃`
the product law `N(0, V_k) ⊗ ⊗_{i>k} N(0, v_i)`, and the realization has the product of the
residual law with that law. -/
def realizationStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A : ℝ, 0 ≤ A → 0 < Vk τ v A →
    (∀ ω, unrealize τ v A (realize τ v A ω) = ω) ∧
    Measurable (realize τ v A) ∧ Measurable (unrealize τ v A) ∧
    (Qtilde τ v A).map (stateMap τ v A) =
      (gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A) ∧
    (Qtilde τ v A).map (realize τ v A) = ((Qtilde τ v A).map (residMap τ v A)).prod
      ((gaussianReal 0 (∑ i ∈ past τ A, v i)).prod (Qlater τ v A))

/-- (d), the sectioning half for `V_k > 0`: every admissible exercise time is dominated by a
state rule, so the American value (20.9) equals the state-rule value (20.10). The proof
replaces the exercise time by a stopping time of the raw reveal filtration built from its
rational-time events, sections it along the residuals through the realization, and bounds its
value by Fubini over the residual law. -/
def sectioningStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S → 0 < Vk τ v A →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    U020 τ v A S Φ = Ustate020 τ v A S Φ

/-- (d) in full for `V_k > 0`: with a common unrevealed block and equal `V_k`, the American
values (20.9) agree. -/
def americanFullStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A → 0 < Vk τ v A →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    Integrable (fun ω => Real.exp (-logB τ v' A ω) * D (stateMap τ v' A ω)) (Q v') →
    U020 τ v A S Φ = U020 τ v' A S Φ

/-- (d), the sectioning half in full: without any sign condition on `V_k`, the American value
(20.9) equals the state-rule value (20.10); for `V_k = 0` the residuals are dropped, every
revealed shock vanishing almost surely. -/
def sectioningFullStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    U020 τ v A S Φ = Ustate020 τ v A S Φ

/-- (d) in full: with a common unrevealed block and equal `V_k`, the American values (20.9)
agree. -/
def americanGeneralStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S : ℝ, 0 ≤ A → A ≤ S →
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A →
    ∀ (Φ : ℝ × (ℝ × (later N τ A → ℝ)) → ℝ) (D : ℝ × (later N τ A → ℝ) → ℝ),
    Measurable Φ → Measurable D →
    (∀ t ∈ Icc A S, ∀ p, |Real.exp (-accrualAfter τ v A t p.1 p.2) * Φ (t, p)| ≤ D p) →
    Integrable (fun ω => Real.exp (-logB τ v A ω) * D (stateMap τ v A ω)) (Q v) →
    Integrable (fun ω => Real.exp (-logB τ v' A ω) * D (stateMap τ v' A ω)) (Q v') →
    U020 τ v A S Φ = U020 τ v' A S Φ

end American

def statement : Prop := curveStatement ∧ discountStatement ∧ futuresStatement ∧
  priceStatement ∧ identificationStatement ∧ boundsStatement ∧ exampleBoundsStatement ∧
  pairPriceStatement ∧ polytopeStatement ∧ residualStatement ∧ sigmaAlgebraStatement ∧
  degenerateStatement ∧ residualAlgebraStatement ∧ extremeStatement ∧
  americanStateStatement ∧ americanAggregateStatement ∧ realizationStatement ∧
  sectioningStatement ∧ americanFullStatement ∧ sectioningFullStatement ∧
  americanGeneralStatement
end Standalone.PreWindowVarianceAggregates

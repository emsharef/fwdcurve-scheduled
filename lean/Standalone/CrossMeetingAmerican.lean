import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.CondVar

/-! # Claim 019: American cash exercise across one unrevealed meeting

The target proves the discount maximizer, Gaussian endpoint inequality, actual
conditional futures versions, bank-account ratios and admissibility of the
proposed rule in the completed Gaussian model, the normalized Gaussian discount
law of the earlier state, the conditional waiting value, the integrability and
upper bound of every admissible discounted exercise payoff, attainment of the
cash stopping supremum by the strict-preference/ties-wait rule, the resulting
Gaussian cash-value formula (19.7), and the positive four-meeting pair (19.8)
with equal initial curves, initial futures quotes and cash values but different
actual event variances.
-/
open MeasureTheory ProbabilityTheory Set
namespace Standalone.CrossMeetingAmerican
abbrev Ω (N : ℕ) := Fin N → ℝ
noncomputable def Q {N : ℕ} (v : Fin N → NNReal) : Measure (Ω N) :=
  Measure.infinitePi fun i => gaussianReal 0 (v i)
def filt {N : ℕ} (τ : ℕ → ℝ) : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Ω N)) where
  seq t := ⨆ (i : Fin N) (_ : τ (i.val + 1) ≤ t),
    MeasurableSpace.comap (fun ω : Ω N => ω i) inferInstance
  mono' := fun _ _ hst => iSup_mono fun _ => iSup_mono' fun h => ⟨h.trans hst, le_rfl⟩
  le' := fun _ => iSup₂_le fun i _ => (measurable_pi_apply i).comap_le
abbrev Ωc {N : ℕ} (v : Fin N → NNReal) := NullMeasurableSpace (Ω N) (Q v)
noncomputable def Qc {N : ℕ} (v : Fin N → NNReal) : Measure (Ωc v) := (Q v).completion
/-- The reveal filtration augmented by every subset of an ambient null set. -/
noncomputable def completedFilt {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) :
    Filtration ℝ (inferInstance : MeasurableSpace (Ωc v)) where
  seq t := eventuallyMeasurableSpace (filt τ t) (ae (Q v))
  mono' := by
    intro s t hst A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨B, (filt τ).mono hst B hB, hAB⟩
  le' := by
    intro t A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨B, (filt τ).le t B hB, hAB⟩

noncomputable def r {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val + 1) ≤ t then ω i + (v i : ℝ) * (t - τ (i.val + 1)) else 0
noncomputable def logB {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) (ω : Ω N) : ℝ :=
  ∫ u in (0 : ℝ)..t, r τ v u ω
noncomputable def f {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val+1) ≤ t then ω i+(v i : ℝ)*(U-τ (i.val+1)) else 0
noncomputable def P {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  Real.exp (-(∫ u in t..U, f τ v t u ω))


noncomputable def V {N : ℕ} (v : Fin N → NNReal) : ℝ := ∑ i, (v i : ℝ)
noncomputable def H {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) : ℝ :=
  ∑ i, τ (i.val+1)*(v i : ℝ)
noncomputable def L0192 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (j : Fin J) (ω : Ω N) : ℝ :=
  ((P τ v (u j.castSucc) (u j.succ) ω)⁻¹-1)/(u j.succ-u j.castSucc)
noncomputable def R0192 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (ω : Ω N) : ℝ :=
  ((∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0192 τ v u j ω))-1)/(u (Fin.last J)-u 0)

noncomputable def Q01912 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (Real.exp (-logB τ v A ω)))

noncomputable def VMinus019 {N : ℕ} (v : Fin (N+1) → NNReal) : ℝ :=
  ∑ i : Fin N, (v i.castSucc : ℝ)


noncomputable def u0194 (q d z : ℝ) : ℝ :=
  if 0 < q then min d (max 0 (-z/q)) else if 0 ≤ z then 0 else d
noncomputable def D0194 (q d z : ℝ) : ℝ :=
  Real.exp (-z*u0194 q d z-q*(u0194 q d z)^2/2)
noncomputable def fMinus0193 (q w A T a b x : ℝ) : ℝ :=
  (Real.exp ((b-a)*(x+q*((a+b)/2-A)+w*(b-T)))-1)/(b-a)
noncomputable def fPlus0193 (V T a b y : ℝ) : ℝ :=
  (Real.exp ((b-a)*(y+V*((a+b)/2-T)))-1)/(b-a)
noncomputable def p0195 (q w A T a b K x : ℝ) : ℝ :=
  max (fMinus0193 q w A T a b x-K) 0 * D0194 q (T-A) x
noncomputable def c0195 (q : ℝ) (w : NNReal) (A T S a b K x : ℝ) : ℝ :=
  Real.exp (-x*(T-A)-q*(T-A)^2/2) *
    ∫ z, max (fPlus0193 (q+w) T a b (x+q*(T-A)+z)-K) 0 *
      D0194 (q+w) (S-T) (x+q*(T-A)+z) ∂gaussianReal 0 w
noncomputable def τ019 {Ω : Type} (q : ℝ) (w : NNReal) (A T S a b K : ℝ)
    (x y : Ω → ℝ) (ω : Ω) : ℝ :=
  if p0195 q w A T a b K (x ω) > c0195 q w A T S a b K (x ω)
  then A+u0194 q (T-A) (x ω) else T+u0194 (q+w) (S-T) (y ω)

/-- A simultaneous futures version on the specified exercise window. -/
noncomputable def F0192 {N : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (A a b t : ℝ) (ω : Ω (N+1)) : ℝ :=
  if t < τ (N+1) then fMinus0193 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) a b (r τ v A ω)
  else fPlus0193 (V v) (τ (N+1)) a b (r τ v (τ (N+1)) ω)

def optimizationStatement : Prop :=
  ∀ q d : ℝ, 0 ≤ q → 0 ≤ d → Measurable (u0194 q d) ∧ Measurable (D0194 q d) ∧
    ∀ z, u0194 q d z ∈ Icc 0 d ∧
      (∀ u ∈ Icc 0 d, Real.exp (-z*u-q*u^2/2) ≤ D0194 q d z) ∧
      1 ≤ D0194 q d z ∧ D0194 q d z ≤ Real.exp (d*|z|)

def endpointStatement : Prop :=
  ∀ (q : ℝ) (w : NNReal) (A T S a b K : ℝ),
    0 ≤ q → A < T → T ≤ S → a < b →
    Measurable (p0195 q w A T a b K) ∧ Measurable (c0195 q w A T S a b K) ∧
    ∀ x,
      Integrable (fun z => max (fPlus0193 (q+w) T a b (x+q*(T-A)+z)-K) 0 *
        D0194 (q+w) (S-T) (x+q*(T-A)+z)) (gaussianReal 0 w) ∧
      (∫ z, fPlus0193 (q+w) T a b (x+q*(T-A)+z) ∂gaussianReal 0 w) =
        fMinus0193 q w A T a b x ∧
      Real.exp (-x*(T-A)-q*(T-A)^2/2) * max (fMinus0193 q w A T a b x-K) 0 ≤
        c0195 q w A T S a b K x ∧
      (c0195 q w A T S a b K x < p0195 q w A T a b K x →
        u0194 q (T-A) x < T-A)

/-- Admissibility and the information needed to bound arbitrary stopping times.
The state measurability and frozen pre-meeting filtration are explicit here;
modelStatement below verifies them for the completed Gaussian model. -/
def stoppingStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Filtration ℝ mΩ)
    (q : ℝ) (w : NNReal) (A T S a b K : ℝ) (x y : Ω → ℝ),
    0 ≤ q → A < T → T ≤ S → a < b →
    Measurable[F A] x → Measurable[F T] y →
    (∀ ω, τ019 q w A T S a b K x y ω ∈ Icc A S) ∧
    IsStoppingTime F (fun ω => (τ019 q w A T S a b K x y ω : WithTop ℝ)) ∧
    (∀ (τ : Ω → ℝ), IsStoppingTime F (fun ω => (τ ω : WithTop ℝ)) →
      (∀ ω, A ≤ τ ω) → (∀ t ∈ Ico A T, F t = F A) →
      MeasurableSet[F A] {ω | τ ω < T})

/-- Model specialization of the futures process and the admissible exercise rule.
The discounted stopping supremum and equal cash values are not yet asserted. -/
def modelStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal),
    τ 0 = 0 → StrictMonoOn τ (Iic (N+1)) → 0 < J →
    ∀ (u : Fin (J+1) → ℝ), StrictMono u → ∀ A S : ℝ,
    τ N ≤ A → A < τ (N+1) → τ (N+1) < S → S ≤ u 0 →
    (∀ t ∈ Ico A (τ (N+1)), completedFilt τ v t = completedFilt τ v A) ∧
    (∀ ω, r τ v (τ (N+1)) ω = r τ v A ω + VMinus019 v*(τ (N+1)-A) + ω (Fin.last N)) ∧
    (∀ ω, (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0192 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) ∧
    Integrable (fun ω : Ωc v => R0192 τ v u ω) (Qc v) ∧
    ((Qc v)[fun ω : Ωc v => R0192 τ v u ω | completedFilt τ v 0] =ᵐ[Qc v]
      fun _ => (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v))-1)/(u (Fin.last J)-u 0)) ∧
    (∀ t ∈ Icc A S,
      Measurable[completedFilt τ v t] (fun ω : Ωc v => F0192 τ v A (u 0) (u (Fin.last J)) t ω) ∧
      (Qc v)[fun ω : Ωc v => R0192 τ v u ω | completedFilt τ v t] =ᵐ[Qc v]
        fun ω => F0192 τ v A (u 0) (u (Fin.last J)) t ω) ∧
    (∀ (K : ℝ) (ω : Ωc v), τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J))
      K (r τ v A) (r τ v (τ (N+1))) ω ∈ Icc A S) ∧
    (∀ K : ℝ, IsStoppingTime (completedFilt τ v)
      (fun ω : Ωc v => (τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S
        (u 0) (u (Fin.last J)) K (r τ v A) (r τ v (τ (N+1))) ω : WithTop ℝ))) ∧
    (∀ σ : Ωc v → ℝ, IsStoppingTime (completedFilt τ v) (fun ω => (σ ω : WithTop ℝ)) →
      (∀ ω, A ≤ σ ω) → MeasurableSet[completedFilt τ v A] {ω | σ ω < τ (N+1)}) ∧
    (∀ t ∈ Icc A (τ (N+1)), ∀ ω,
      logB τ v t ω = logB τ v A ω + r τ v A ω*(t-A) + VMinus019 v*(t-A)^2/2) ∧
    (∀ t, τ (N+1) ≤ t → ∀ ω,
      logB τ v t ω = logB τ v (τ (N+1)) ω + r τ v (τ (N+1)) ω*(t-τ (N+1)) + V v*(t-τ (N+1))^2/2) ∧
    HasLaw (r τ v A) (gaussianReal 0 (∑ i : Fin N, v i.castSucc)) (Q01912 τ v A) ∧
    IsProbabilityMeasure (Q01912 τ v A)

/-- The post-meeting cash payoff at the largest remaining discount factor. -/
noncomputable def g0195 (V T S a b K y : ℝ) : ℝ :=
  max (fPlus0193 V T a b y-K) 0 * D0194 V (S-T) y
noncomputable def Δr {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (i : Fin N) (ω : Ω N) : ℝ :=
  r τ v (τ (i.val+1)) ω - Function.leftLim (fun t => r τ v t ω) (τ (i.val+1))
/-- Admissible exercise times: every stopping time of the completed filtration with values in [A,S]. -/
def T0193 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S : ℝ) : Set (Ωc v → ℝ) :=
  {σ | (∀ ω, σ ω ∈ Icc A S) ∧
    IsStoppingTime (completedFilt τ v) (fun ω => (σ ω : WithTop ℝ))}
/-- The American cash value (19.2): the supremum over admissible exercise times of the
discounted payoff on the simultaneous futures version. -/
noncomputable def U0193 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal)
    (A S : ℝ) (u : Fin (J+1) → ℝ) (K : ℝ) : ℝ :=
  sSup ((fun σ => ∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω) *
    max (F0192 τ v A (u 0) (u (Fin.last J)) (σ ω) ω-K) 0 ∂Qc v) '' T0193 τ v A S)

/-- Conditional waiting value, integrability and upper bound for every admissible exercise
time, attainment by the strict-preference/ties-wait rule, and the cash-value formula (19.7). -/
def valuationStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin (N+1) → NNReal),
    τ 0 = 0 → StrictMonoOn τ (Iic (N+1)) → 0 < J →
    ∀ (u : Fin (J+1) → ℝ), StrictMono u → ∀ A S K : ℝ,
    τ N ≤ A → A < τ (N+1) → τ (N+1) < S → S ≤ u 0 →
    ((Qc v)[fun ω : Ωc v => Real.exp (-r τ v A ω*(τ (N+1)-A)-VMinus019 v*(τ (N+1)-A)^2/2) *
        g0195 (V v) (τ (N+1)) S (u 0) (u (Fin.last J)) K (r τ v (τ (N+1)) ω) | completedFilt τ v A]
      =ᵐ[Qc v] fun ω => c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K
        (r τ v A ω)) ∧
    (∀ σ ∈ T0193 τ v A S,
      Integrable (fun ω : Ωc v => Real.exp (-logB τ v (σ ω) ω) *
        max (F0192 τ v A (u 0) (u (Fin.last J)) (σ ω) ω-K) 0) (Qc v) ∧
      (∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω) *
        max (F0192 τ v A (u 0) (u (Fin.last J)) (σ ω) ω-K) 0 ∂Qc v) ≤ U0193 τ v A S u K) ∧
    (∃ σ ∈ T0193 τ v A S,
      (∀ ω, σ ω = τ019 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K
        (r τ v A) (r τ v (τ (N+1))) ω) ∧
      (∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω) *
        max (F0192 τ v A (u 0) (u (Fin.last J)) (σ ω) ω-K) 0 ∂Qc v) = U0193 τ v A S u K) ∧
    U0193 τ v A S u K =
      ∫ x, max (p0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) (u 0) (u (Fin.last J)) K x)
        (c0195 (VMinus019 v) (v (Fin.last N)) A (τ (N+1)) S (u 0) (u (Fin.last J)) K x)
        ∂gaussianReal 0 (∑ i : Fin N, v i.castSucc)

noncomputable def v0198 (ε : NNReal) : Fin (3+1) → NNReal := ![2*ε, 3*ε, 2*ε, ε]
noncomputable def v0198' (ε : NNReal) : Fin (3+1) → NNReal := ![3*ε, ε, 3*ε, ε]

/-- The positive pair (19.8) has equal initial curves, equal initial futures quotes for
every accrual window after the last meeting, and equal American cash values for every
exercise window crossing exactly the last meeting, while its actual individual event
variances differ and the crossed variance agrees. -/
def exampleStatement : Prop :=
  ∀ ε : NNReal, 0 < ε →
    (∀ i, 0 < v0198 ε i ∧ 0 < v0198' ε i) ∧ v0198 ε ≠ v0198' ε ∧
    v0198 ε (Fin.last 3) = v0198' ε (Fin.last 3) ∧
    (∀ (v : Fin 4 → NNReal) (U : ℝ) (ω : Ω 4), P (fun n : ℕ => (n : ℝ)) v 0 U ω = 1) ∧
    (∀ (v : Fin 4 → NNReal) (i : Fin 4),
      Var[Δr (fun n : ℕ => (n : ℝ)) v i; Q v] = (v i : ℝ) ∧
      ∀ t : ℝ, t < ((i.val+1 : ℕ) : ℝ) →
        Var[fun ω : Ωc v => Δr (fun n : ℕ => (n : ℝ)) v i ω; Qc v |
          completedFilt (fun n : ℕ => (n : ℝ)) v t] =ᵐ[Qc v] fun _ => (v i : ℝ)) ∧
    (∀ (J : ℕ), 0 < J → ∀ u : Fin (J+1) → ℝ, StrictMono u → 4 ≤ u 0 → ∃ c : ℝ,
      ((Qc (v0198 ε))[fun ω : Ωc (v0198 ε) => R0192 (fun n : ℕ => (n : ℝ)) (v0198 ε) u ω |
        completedFilt (fun n : ℕ => (n : ℝ)) (v0198 ε) 0] =ᵐ[Qc (v0198 ε)] fun _ => c) ∧
      ((Qc (v0198' ε))[fun ω : Ωc (v0198' ε) => R0192 (fun n : ℕ => (n : ℝ)) (v0198' ε) u ω |
        completedFilt (fun n : ℕ => (n : ℝ)) (v0198' ε) 0] =ᵐ[Qc (v0198' ε)] fun _ => c)) ∧
    (∀ (J : ℕ), 0 < J → ∀ u : Fin (J+1) → ℝ, StrictMono u →
      ∀ A S K : ℝ, 3 ≤ A → A < 4 → 4 < S → S ≤ u 0 →
      U0193 (fun n : ℕ => (n : ℝ)) (v0198 ε) A S u K =
      U0193 (fun n : ℕ => (n : ℝ)) (v0198' ε) A S u K)

def statement : Prop := optimizationStatement ∧ endpointStatement ∧ stoppingStatement ∧
  modelStatement ∧ valuationStatement ∧ exampleStatement
end Standalone.CrossMeetingAmerican

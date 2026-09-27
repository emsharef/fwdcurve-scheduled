import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.CondVar
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Claim 018: late American cash exercise and exact discrete compounding

The target uses the actual finite Gaussian model, completed reveal filtration,
bond-implied fixings and supremum over all admissible late stopping times.
-/
open MeasureTheory ProbabilityTheory
namespace Standalone.LateAmericanExercise
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
noncomputable def Δr {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (i : Fin N) (ω : Ω N) : ℝ :=
  r τ v (τ (i.val+1)) ω - Function.leftLim (fun t => r τ v t ω) (τ (i.val+1))
noncomputable def logB {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t : ℝ) (ω : Ω N) : ℝ :=
  ∫ u in (0 : ℝ)..t, r τ v u ω
noncomputable def f {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val+1) ≤ t then ω i+(v i : ℝ)*(U-τ (i.val+1)) else 0
noncomputable def P {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  Real.exp (-(∫ u in t..U, f τ v t u ω))


noncomputable def V {N : ℕ} (v : Fin N → NNReal) : ℝ := ∑ i, (v i : ℝ)
noncomputable def H {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) : ℝ :=
  ∑ i, τ (i.val+1)*(v i : ℝ)
noncomputable def L0182 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (j : Fin J) (ω : Ω N) : ℝ :=
  ((P τ v (u j.castSucc) (u j.succ) ω)⁻¹-1)/(u j.succ-u j.castSucc)
noncomputable def R0182 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (u : Fin (J+1) → ℝ) (ω : Ω N) : ℝ :=
  ((∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0182 τ v u j ω))-1)/(u (Fin.last J)-u 0)
noncomputable def u0186 (V L x : ℝ) : ℝ := min L (max 0 (-x/V))
noncomputable def D0187 (V L x : ℝ) : ℝ :=
  Real.exp (-x*u0186 V L x-V*(u0186 V L x)^2/2)
noncomputable def τ0186 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (A S : ℝ) (ω : Ω N) : ℝ := A+u0186 (V v) (S-A) (r τ v A ω)

noncomputable def Q0188 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A : ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (Real.exp (-logB τ v A ω)))
noncomputable def p0188 (V L δ c K x : ℝ) : ℝ :=
  max ((Real.exp (δ*x+c)-1)/δ-K) 0 * D0187 V L x
def T0183 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S : ℝ) : Set (Ωc v → ℝ) :=
  {σ | (∀ ω, σ ω ∈ Set.Icc A S) ∧
    IsStoppingTime (completedFilt τ v) (fun ω => (σ ω : WithTop ℝ))}
noncomputable def U0183 {N J : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal)
    (A S : ℝ) (u : Fin (J+1) → ℝ) (K : ℝ) : ℝ :=
  sSup ((fun σ => ∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0 ∂Qc v)
    '' T0183 τ v A S)

/-- Actual fixing factors, exact compounding, and the constant conditional futures
version for all deterministic times at or after the last meeting. -/
def compoundingStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → 0 < J →
    ∀ (u : Fin (J+1) → ℝ), StrictMono u → ∀ A : ℝ, 0 ≤ A →
      (∀ i : Fin N, τ (i.val+1) ≤ A) → A ≤ u 0 →
      (∀ j ω, 0 < 1+(u j.succ-u j.castSucc)*L0182 τ v u j ω) ∧
      (∀ ω, (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0182 τ v u j ω)) =
        Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) ∧
      (∀ ω, R0182 τ v u ω =
        (Real.exp ((u (Fin.last J)-u 0)*r τ v A ω+
          (u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A))-1)/(u (Fin.last J)-u 0)) ∧
      Integrable (fun ω : Ωc v => R0182 τ v u ω) (Qc v) ∧
      Measurable[completedFilt τ v A] (fun ω : Ωc v => R0182 τ v u ω) ∧
      (∀ t, A ≤ t → (Qc v)[fun ω : Ωc v => R0182 τ v u ω | completedFilt τ v t] =
        (fun ω : Ωc v => R0182 τ v u ω)) ∧
      (∫ ω : Ωc v, R0182 τ v u ω ∂Qc v) =
        (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v))-1)/(u (Fin.last J)-u 0)

/-- The clipped quadratic minimizer, its exact cases, and a global linear-exponential bound. -/
def optimizationStatement : Prop :=
  ∀ V L x : ℝ, 0 < V → 0 ≤ L →
    u0186 V L x ∈ Set.Icc 0 L ∧
    (∀ u ∈ Set.Icc 0 L, Real.exp (-x*u-V*u^2/2) ≤ D0187 V L x) ∧
    D0187 V L x = (if 0 ≤ x then 1 else if x ≤ -V*L then
      Real.exp (-x*L-V*L^2/2) else Real.exp (x^2/(2*V))) ∧
    D0187 V L x ≤ Real.exp (L*|x|) ∧
    1 ≤ D0187 V L x ∧ D0187 V 0 x = 1

/-- The actual model's clipped exercise time is admissible and dominates every
allowed exercise time pathwise, with equality at that stopping time. -/
def exerciseStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
    0 < V v → ∀ (A S : ℝ), A ≤ S →
    (∀ i : Fin N, τ (i.val+1) ≤ A) →
    (∀ ω, τ0186 τ v A S ω ∈ Set.Icc A S) ∧
    IsStoppingTime (completedFilt τ v)
      (fun ω : Ωc v => (τ0186 τ v A S ω : WithTop ℝ)) ∧
    ∀ (u : Fin (J+1) → ℝ) (K : ℝ) (ω : Ω N),
      (∀ t ∈ Set.Icc A S,
        Real.exp (-logB τ v t ω)*max (R0182 τ v u ω-K) 0 ≤
          Real.exp (-logB τ v A ω)*max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω)) ∧
      Real.exp (-logB τ v (τ0186 τ v A S ω) ω)*max (R0182 τ v u ω-K) 0 =
        Real.exp (-logB τ v A ω)*max (R0182 τ v u ω-K) 0*D0187 (V v) (S-A) (r τ v A ω)

/-- Discounted Gaussian valuation, integrability for every admissible stopping
 time, attainment and the strict premium over mandatory exercise at S. -/
def valuationStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal),
    τ 0 = 0 → StrictMonoOn τ (Set.Iic N) → 0 < J →
    ∀ (u : Fin (J+1) → ℝ), StrictMono u → ∀ A S K : ℝ, 0 ≤ A → A ≤ S → S ≤ u 0 →
    (∀ i : Fin N, τ (i.val+1) ≤ A) →
    (Qc v)[fun ω : Ωc v => R0182 τ v u ω | completedFilt τ v 0] =ᵐ[Qc v]
      (fun _ => (Real.exp ((u (Fin.last J)-u 0)*(u (Fin.last J)*V v-H τ v))-1)/(u (Fin.last J)-u 0)) ∧
    HasLaw (r τ v A) (gaussianReal 0 (∑ i, v i)) (Q0188 τ v A) ∧
    (∫ ω, Real.exp (-logB τ v A ω) ∂Q v) = 1 ∧
    (∀ σ ∈ T0183 τ v A S,
      Integrable (fun ω : Ωc v => Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0) (Qc v) ∧
      (∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) ≤ U0183 τ v A S u K) ∧
    (∃ σ ∈ T0183 τ v A S,
      (∀ ω, σ ω = if V v = 0 then A else τ0186 τ v A S ω) ∧
      (∫ ω : Ωc v, Real.exp (-logB τ v (σ ω) ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) = U0183 τ v A S u K) ∧
    U0183 τ v A S u K =
      (∫ x, p0188 (V v) (S-A) (u (Fin.last J)-u 0)
        ((u (Fin.last J)-u 0)*V v*((u 0+u (Fin.last J))/2-A)) K x ∂gaussianReal 0 (∑ i, v i)) ∧
    (0 < V v → A < S →
      (∫ ω : Ωc v, Real.exp (-logB τ v S ω)*max (R0182 τ v u ω-K) 0 ∂Qc v) < U0183 τ v A S u K)

/-- Zero total variance gives the simultaneous deterministic model and cash value. -/
def zeroStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), V v = 0 →
    (∀ i, v i = 0) ∧
    (∀ᵐ ω : Ωc v ∂Qc v, (∀ i, ω i = 0) ∧
      (∀ t, r τ v t ω = 0 ∧ Real.exp (-logB τ v t ω) = 1) ∧
      ∀ u : Fin (J+1) → ℝ, R0182 τ v u ω = 0) ∧
    (∀ A S : ℝ, A ≤ S → ∀ (u : Fin (J+1) → ℝ) (K : ℝ), U0183 τ v A S u K = max (-K) 0)

noncomputable def v0189 (ε : NNReal) : Fin 3 → NNReal := ![2*ε, 3*ε, 2*ε]
noncomputable def v0189' (ε : NNReal) : Fin 3 → NNReal := ![3*ε, ε, 3*ε]

/-- The positive pair has equal curves, all specified futures quotes and all late
American cash prices, while its actual individual jump variances differ. -/
def exampleStatement : Prop :=
  ∀ ε : NNReal, 0 < ε →
    (∀ i, 0 < v0189 ε i ∧ 0 < v0189' ε i) ∧ v0189 ε ≠ v0189' ε ∧
    (∀ (v : Fin 3 → NNReal) (U : ℝ) (ω : Ω 3), P (fun n : ℕ => (n : ℝ)) v 0 U ω = 1) ∧
    (∀ (v : Fin 3 → NNReal) (i : Fin 3),
      Var[Δr (fun n : ℕ => (n : ℝ)) v i; Q v] = (v i : ℝ) ∧
      ∀ t : ℝ, t < ((i.val+1 : ℕ) : ℝ) →
        Var[fun ω : Ωc v => Δr (fun n : ℕ => (n : ℝ)) v i ω; Qc v |
          completedFilt (fun n : ℕ => (n : ℝ)) v t] =ᵐ[Qc v] fun _ => (v i : ℝ)) ∧
    (∀ (J : ℕ), 0 < J → ∀ u : Fin (J+1) → ℝ, StrictMono u → 3 ≤ u 0 →
      (∫ ω : Ωc (v0189 ε), R0182 (fun n : ℕ => (n : ℝ)) (v0189 ε) u ω ∂Qc (v0189 ε)) =
      (∫ ω : Ωc (v0189' ε), R0182 (fun n : ℕ => (n : ℝ)) (v0189' ε) u ω ∂Qc (v0189' ε))) ∧
    (∀ (J : ℕ), 0 < J → ∀ u : Fin (J+1) → ℝ, StrictMono u →
      ∀ A S K : ℝ, 3 ≤ A → A ≤ S → S ≤ u 0 →
      U0183 (fun n : ℕ => (n : ℝ)) (v0189 ε) A S u K =
      U0183 (fun n : ℕ => (n : ℝ)) (v0189' ε) A S u K)

def statement : Prop := compoundingStatement ∧ optimizationStatement ∧ exerciseStatement ∧
  valuationStatement ∧ zeroStatement ∧ exampleStatement
end Standalone.LateAmericanExercise

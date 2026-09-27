import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.CondVar
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Claim 015: conditional support and deterministic image results

The generic image statements retain explicit support premises. The concrete
Poisson/exponential construction now gives a measurable full vector transition
kernel, including zero-scale constants and zero-start absorption, its exact
support, moments and independence. The joint conditional transform identifies
this kernel and its affine image as conditional laws. Their support, affine
equalities, covariance rank and atom are proved with the starting-state-dependent
active columns. The actual conditional meeting variances are now identified with
this image from Claim 013's five explicit Lean premises. Those premises and the
joint transform are not derived from the SDE. The backward exponential calculus
and bounded localization are proved separately: an explicit stopped-martingale
premise now yields the joint transforms, state laws and actual variance supports.
The stopped martingales have not been constructed from the SDE. The bounded
hitting times are now constructed from continuous adapted paths, with stopping-time
measurability, monotonicity, eventual equality to the horizon and no overshoot.
The explicit stopped integrands are jointly measurable and square integrable for
the time/probability product measure, with the expected bound in (15.23), without
a state-moment or H0152 premise. Their predictability and progressive
measurability on the finite horizon are proved from continuous adapted paths.
Finite elementary Brownian sums now have proved conditional means, orthogonality
and isometry, using the Gaussian increment law and independence from the supplied
full filtration. Their continuous-time processes are square-integrable
martingales with almost-surely continuous paths and an isometry at every time.
Cauchy sequences of elementary terminal values now yield a square-integrable
martingale limit with uniform-in-time L² error bounds. Explicit predictable-step
coefficients now approximate the stopped integrands in mean square for the
time/probability product measure. The overlap calculation now proves the
cross-partition isometry and transfers a mean-square Cauchy criterion on finite
step integrands to terminal Brownian sums. Applying this criterion to the
explicit stopped-integrand approximations, continuous versions of the limit,
and the stochastic-integral identity are not proved. The actual
state process is now proved square integrable and a martingale on the finite
time interval, with conditional moments, terminal-coordinate independence,
zero-scale constants and absorption derived from the identified laws. Continuous
adapted paths and an integrable deterministic kernel now give the conditional
integration identity in the fifth Claim 013 premise by Fubini; the other four
premises remain explicit in the new full-kernel assembly. Bounded measurable
coefficients now imply full-kernel integrability, with explicit backward-integral
and kernel bounds; a further assembly uses these coefficient conditions directly.
The calendar count and source formulas (13.3)–(13.4) now construct g and b,
with measurability and bounds derived from the primitive coefficient conditions.
The printed three-factor table is instantiated for these kernel consequences.
Initial values give the initial affine-image point law, while conditioning a
measurable vector on the same information gives its point law. The latter is
also proved for the actual vector of conditional future-jump variances.
The factor index in the image statements contains only active columns;
the deterministic contribution is `b`. Empty active sets are allowed.
-/
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology
namespace Standalone.ZeroMeanReversionVarianceSupport

def cone0154 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ) :
    Set (Fin m → ℝ) := {y | ∃ x : Fin d → ℝ, (∀ j, 0 ≤ x j) ∧ y = b + A.mulVec x}

noncomputable def cov0157 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (q : Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ := A * diagonal q * A.transpose

def supportStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
    (∀ i j, 0 ≤ A i j) →
    IsClosed (cone0154 A b) ∧
    (affineSpan ℝ (cone0154 A b) : Set (Fin m → ℝ)) =
      (fun x => b + x) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ d ∧
    m - d ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin) ∧
    (∀ μ : Measure (Fin d → ℝ), μ.support = {x | ∀ j, 0 ≤ x j} →
      (μ.map (fun x => b + A.mulVec x)).support = cone0154 A b) ∧
    (∀ μ : Measure (Fin m → ℝ), μ.support = cone0154 A b →
      ∀ w, (∀ᵐ y ∂μ, dotProduct w (y - b) = 0) ↔ A.transpose.mulVec w = 0) ∧
    (∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j) →
      (b + A.mulVec x = b ↔ ∀ j, (∃ i, A i j ≠ 0) → x j = 0))

def covarianceStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (q : Fin d → ℝ),
    (∀ j, 0 < q j) →
    (∀ w, dotProduct w ((cov0157 A q).mulVec w) =
      ∑ j, q j * (A.transpose.mulVec w j) ^ 2) ∧
    LinearMap.ker (cov0157 A q).mulVecLin = LinearMap.ker A.transpose.mulVecLin ∧
    (cov0157 A q).rank = A.rank

def productStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
    (∀ i j, 0 ≤ A i j) →
    ∀ (μ : Fin d → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j, (μ j).support = Ici 0) →
      (Measure.pi μ).support = {x | ∀ j, 0 ≤ x j} ∧
      ((Measure.pi μ).map (fun x => b + A.mulVec x)).support = cone0154 A b ∧
      ((Measure.pi μ).map (fun x => b + A.mulVec x)) {b} =
        ∏ j, if (∃ i, A i j ≠ 0) then μ j {0} else 1

def momentStatement : Prop :=
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
      (X : Fin d → Ω → ℝ) (q : Fin d → ℝ),
      (∀ j, MemLp (X j) 2 μ) → iIndepFun X μ → (∀ j, Var[X j; μ] = q j) →
      ∀ i k, cov[fun ω => b i + ∑ j, A i j * X j ω,
        fun ω => b k + ∑ j, A k j * X j ω; μ] = cov0157 A q i k

def atomStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
    (∀ i j, 0 ≤ A i j) →
    ∀ (μ : Fin d → Measure ℝ) (r : Fin d → ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j, (μ j).support = Ici 0) → (∀ j, μ j {0} = ENNReal.ofReal (Real.exp (-r j))) →
      ((Measure.pi μ).map (fun x => b + A.mulVec x)) {b} =
        ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, A i j ≠ 0) then r j else 0)))

/-- Joint Laplace transforms determine finite measures, including restricted laws. -/
def laplaceStatement : Prop :=
  (∀ (d : ℕ) (μ ν : Measure (Fin d → NNReal)), IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ l : Fin d → NNReal,
      (∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂μ) =
      ∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂ν) → μ = ν) ∧
  (∀ (d : ℕ) (μ ν : Measure (Fin d → ℝ)), IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ᵐ x ∂μ, ∀ j, 0 ≤ x j) → (∀ᵐ x ∂ν, ∀ j, 0 ≤ x j) →
    (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ x, Real.exp (-(∑ j, l j * x j)) ∂μ) =
      ∫ x, Real.exp (-(∑ j, l j * x j)) ∂ν) → μ = ν)

/-- Independence is a consequence of the displayed transform, not a separate premise. -/
def independenceStatement : Prop :=
  ∀ (d : ℕ) (μ : Measure (Fin d → NNReal)), IsProbabilityMeasure μ →
    ∀ v c : Fin d → ℝ,
      (∀ l : Fin d → NNReal,
        (∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂μ) =
          Real.exp (-(∑ j, v j * l j / (1 + c j * l j)))) →
      iIndepFun (fun j (x : Fin d → NNReal) => x j) μ

/-- Measurability in the conditioning information and agreement on every conditioning event. -/
def conditionalLaw01513 {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [_mΩ : MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin d → NNReal)
    (κ : Kernel Ω (Fin d → NNReal)) : Prop :=
  (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
    ∀ D, MeasurableSet[G] D → (μ.restrict D).map X = κ ∘ₘ μ.restrict D

/-- The conditional transform identifies a supplied measurable probability kernel. -/
def conditionalLaplaceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsFiniteMeasure μ → G ≤ mΩ →
    ∀ (X : Ω → Fin d → NNReal), Measurable X →
      ∀ (κ : Kernel Ω (Fin d → NNReal)), IsMarkovKernel κ →
        (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) →
        (∀ l : Fin d → NNReal,
          μ[fun ω => Real.exp (-(∑ j, (l j : ℝ) * X ω j)) | G] =ᵐ[μ]
            fun ω => ∫ y, Real.exp (-(∑ j, (l j : ℝ) * y j)) ∂κ ω) →
        conditionalLaw01513 G μ X κ

/-- The Poisson averaging calculation in (15.10), including zero starting mass. -/
def poissonStatement : Prop :=
  (∀ (r : NNReal) (z : ℝ),
    (∫ n, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1))) ∧
  (∀ c x l : ℝ, 0 < c → 0 ≤ x → 0 ≤ l →
    (∫ n, ((1 + c * l)⁻¹) ^ n ∂poissonMeasure (x / c).toNNReal) =
      Real.exp (-x * l / (1 + c * l)))

/-- Sum of `n` independent exponential variables with mean `c`. -/
noncomputable def S0153 (c : ℝ) : Kernel ℕ ℝ := Kernel.ofFunOfCountable
  (fun n => (Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map (fun x => ∑ j, x j))

/-- The Poisson mixture of finite exponential sums, with count rate `r`. -/
noncomputable def P0153 (c : ℝ) (r : NNReal) : Measure ℝ := S0153 c ∘ₘ poissonMeasure r

/-- The scalar transition-law candidate in (15.13), at starting value `x`. -/
noncomputable def K01513 (c : ℝ) (x : NNReal) : Measure ℝ :=
  P0153 c ((x : ℝ) / c).toNNReal

/-- Concrete scalar law construction; it is not a theorem about solutions of (15.1). -/
def scalarTransitionStatement : Prop :=
  ∀ c : ℝ, 0 < c → Measurable (K01513 c) ∧
    (∀ x : NNReal, IsProbabilityMeasure (K01513 c x)) ∧
    K01513 c 0 = Measure.dirac 0 ∧
    (∀ x : NNReal,
      (∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-l * y) ∂K01513 c x) =
        Real.exp (-(x : ℝ) * l / (1 + c * l))) ∧
      K01513 c x {0} = ENNReal.ofReal (Real.exp (-(x : ℝ) / c)) ∧
      (0 < x → (K01513 c x).support = Ici 0)) ∧
    (∀ (x : NNReal) (μ : Measure ℝ), IsFiniteMeasure μ →
      (∀ᵐ y ∂μ, 0 ≤ y) →
      (∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-l * y) ∂μ) =
        Real.exp (-(x : ℝ) * l / (1 + c * l))) → μ = K01513 c x)

/-- The actual scalar candidate is a conditional law whenever (15.13) holds. -/
def scalarConditionalStatement : Prop :=
  ∀ (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsFiniteMeasure μ → G ≤ mΩ →
    ∀ c : ℝ, 0 < c → ∀ S : Ω → NNReal, Measurable[G] S →
      ∀ X : Ω → ℝ, Measurable X → (∀ᵐ ω ∂μ, 0 ≤ X ω) →
        (∀ l : ℝ, 0 ≤ l → μ[fun ω => Real.exp (-l * X ω) | G] =ᵐ[μ]
          fun ω => Real.exp (-(S ω : ℝ) * l / (1 + c * l))) →
        (∀ B, MeasurableSet B → Measurable[G] (fun ω => K01513 c (S ω) B)) ∧
          ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
            (μ.restrict D).map X B = ∫⁻ ω in D, K01513 c (S ω) B ∂μ

/-- Actual first and second moments of the constructed scalar transition law. -/
def scalarMomentStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ x : NNReal,
    MemLp (fun y : ℝ => y) 2 (K01513 c x) ∧
      (∫ y : ℝ, y ∂K01513 c x) = x ∧ Var[fun y : ℝ => y; K01513 c x] = 2 * c * x

/-- Scalar candidate with a constant coordinate when the scale is zero. -/
noncomputable def T01513 (c : ℝ) (x : NNReal) : Measure ℝ :=
  if c = 0 then Measure.dirac (x : ℝ) else K01513 c x
/-- Full product transition-law candidate in (15.13). -/
noncomputable def Q01513 {d : ℕ} (c : Fin d → ℝ) (x : Fin d → NNReal) :
    Measure (Fin d → ℝ) := Measure.pi (fun j => T01513 (c j) (x j))
/-- Columns retained in (15.14); zero scale and zero starting value remove a column. -/
noncomputable def A01514 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (c : Fin d → ℝ) (x : Fin d → NNReal) : Matrix (Fin m) (Fin d) ℝ :=
  fun i j => if c j = 0 ∨ x j = 0 then 0 else A i j
/-- Deterministic contribution in (15.14), with an optional additional translation. -/
noncomputable def b01514 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (c : Fin d → ℝ) (x : Fin d → NNReal) : Fin m → ℝ :=
  b + A.mulVec (fun j => if c j = 0 ∨ x j = 0 then (x j : ℝ) else 0)
/-- The full vector candidate, including constant and absorbed coordinates. -/
def vectorTransitionStatement : Prop :=
  ∀ (d : ℕ) (c : Fin d → ℝ), (∀ j, 0 ≤ c j) → Measurable (Q01513 c) ∧
    ∀ x : Fin d → NNReal, IsProbabilityMeasure (Q01513 c x) ∧
      (∀ᵐ y ∂Q01513 c x, ∀ j, 0 ≤ y j) ∧
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        (∫ y, Real.exp (-(∑ j, l j * y j)) ∂Q01513 c x) =
          Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j)))) ∧
      iIndepFun (fun j (y : Fin d → ℝ) => y j) (Q01513 c x) ∧
      (∀ j, MemLp (fun y => y j) 2 (Q01513 c x) ∧
        (∫ y, y j ∂Q01513 c x) = x j ∧
        Var[fun y => y j; Q01513 c x] = 2 * c j * x j) ∧
      (Q01513 c x).support =
        {y | ∀ j, if c j = 0 ∨ x j = 0 then y j = (x j : ℝ) else 0 ≤ y j} ∧
      (∀ μ : Measure (Fin d → ℝ), IsFiniteMeasure μ →
        (∀ᵐ y ∂μ, ∀ j, 0 ≤ y j) →
        (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
          (∫ y, Real.exp (-(∑ j, l j * y j)) ∂μ) =
            Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j)))) → μ = Q01513 c x)

/-- Both the vector and its affine image are conditional laws from the joint transform.
No measurability, independence or conditional-distribution premise is imposed on the candidate. -/
def vectorConditionalStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsFiniteMeasure μ → G ≤ mΩ →
    ∀ (c : Fin d → ℝ), (∀ j, 0 ≤ c j) →
      ∀ S : Ω → Fin d → NNReal, Measurable[G] S →
        ∀ X : Ω → Fin d → ℝ, Measurable X → (∀ᵐ ω ∂μ, ∀ j, 0 ≤ X ω j) →
          (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
            μ[fun ω => Real.exp (-(∑ j, l j * X ω j)) | G] =ᵐ[μ]
              fun ω => Real.exp (-(∑ j, (S ω j : ℝ) * l j / (1 + c j * l j)))) →
          ((∀ B, MeasurableSet B → Measurable[G] (fun ω => Q01513 c (S ω) B)) ∧
            ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
              (μ.restrict D).map X B = ∫⁻ ω in D, Q01513 c (S ω) B ∂μ) ∧
          ∀ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
            (∀ B, MeasurableSet B → Measurable[G]
              (fun ω => ((Q01513 c (S ω)).map (fun y => b + A.mulVec y)) B)) ∧
            ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
              (μ.restrict D).map (fun ω => b + A.mulVec (X ω)) B =
                ∫⁻ ω in D, ((Q01513 c (S ω)).map (fun y => b + A.mulVec y)) B ∂μ

/-- Exact image support, affine equalities, covariance and atom for every starting vector.
At `x = S ω` these describe the conditional kernel above, including its varying active set. -/
def vectorImageStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
    (∀ i j, 0 ≤ A i j) → ∀ (c : Fin d → ℝ), (∀ j, 0 ≤ c j) →
      ∀ x : Fin d → NNReal,
        let B := A01514 A c x
        let b' := b01514 A b c x
        ((Q01513 c x).map (fun y => b + A.mulVec y)).support = cone0154 B b' ∧
        IsClosed (cone0154 B b') ∧
        (affineSpan ℝ (cone0154 B b') : Set (Fin m → ℝ)) =
          (fun y => b' + y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
        (∀ w, (∀ᵐ y ∂(Q01513 c x).map (fun y => b + A.mulVec y),
          dotProduct w (y - b') = 0) ↔ B.transpose.mulVec w = 0) ∧
        B.rank ≤ (Finset.univ.filter (fun j => c j ≠ 0 ∧ x j ≠ 0)).card ∧
        LinearMap.ker (cov0157 A (fun j => 2 * c j * x j)).mulVecLin =
          LinearMap.ker B.transpose.mulVecLin ∧
        (cov0157 A (fun j => 2 * c j * x j)).rank = B.rank ∧
        (∀ i, (∫ y, b i + ∑ j, A i j * y j ∂Q01513 c x) = b i + ∑ j, A i j * x j) ∧
        (∀ i k, cov[fun y => b i + ∑ j, A i j * y j,
          fun y => b k + ∑ j, A k j * y j; Q01513 c x] =
            cov0157 A (fun j => 2 * c j * x j) i k) ∧
        ((Q01513 c x).map (fun y => b + A.mulVec y)) {b'} =
          ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, B i j ≠ 0)
            then (x j : ℝ) / c j else 0)))

/-- Printed constant volatility-of-volatility parameters in Claim 015(c). -/
noncomputable def α0159 : Fin 3 → ℝ := ![157 / 100, 82 / 100, 0]
/-- Positive-time or positive-lag scales for the printed constant parameters. -/
noncomputable def c0159 (t : ℝ) : Fin 3 → ℝ := fun j => α0159 j ^ 2 * t / 2
/-- The first two columns in (15.9), in the printed factor order. -/
noncomputable def A0159 {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) : Matrix (Fin m) (Fin 2) ℝ :=
  fun i j => A i j.castSucc

/-- The printed constant parameters give two possible active columns, never a rank-two premise.
The conditional candidate below uses an earlier state with third coordinate one. -/
def tableStatement : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 3) ℝ), (∀ i j, 0 ≤ A i j) →
    (∀ y : Fin 3 → ℝ, y 2 = 1 →
      A.mulVec y = fun i => A i 2 + A i 0 * y 0 + A i 1 * y 1) ∧
    ∀ t : ℝ, 0 < t →
      (0 < c0159 t 0 ∧ 0 < c0159 t 1 ∧ c0159 t 2 = 0) ∧
      ((Q01513 (c0159 t) 1).map A.mulVec).support = cone0154 (A0159 A) (fun i => A i 2) ∧
      IsClosed (cone0154 (A0159 A) (fun i => A i 2)) ∧
      (affineSpan ℝ (cone0154 (A0159 A) (fun i => A i 2)) : Set (Fin m → ℝ)) =
        (fun y => (fun i => A i 2) + y) ''
          (LinearMap.range (A0159 A).mulVecLin : Set (Fin m → ℝ)) ∧
      (A0159 A).rank ≤ 2 ∧
      m - 2 ≤ Module.finrank ℝ (LinearMap.ker (A0159 A).transpose.mulVecLin) ∧
      (∀ w, (∀ᵐ y ∂(Q01513 (c0159 t) 1).map A.mulVec,
        dotProduct w (y - (fun i => A i 2)) = 0) ↔ (A0159 A).transpose.mulVec w = 0) ∧
      ∀ x : Fin 3 → NNReal, x 2 = 1 →
        ((Q01513 (c0159 t) x).map A.mulVec).support =
          cone0154 (A01514 A (c0159 t) x) (fun i => A i 2) ∧
        (affineSpan ℝ (cone0154 (A01514 A (c0159 t) x) (fun i => A i 2)) : Set (Fin m → ℝ)) =
          (fun y => (fun i => A i 2) + y) ''
            (LinearMap.range (A01514 A (c0159 t) x).mulVecLin : Set (Fin m → ℝ)) ∧
        (A01514 A (c0159 t) x).rank ≤ 2 ∧
        m - 2 ≤ Module.finrank ℝ (LinearMap.ker (A01514 A (c0159 t) x).transpose.mulVecLin) ∧
        (∀ w, (∀ᵐ y ∂(Q01513 (c0159 t) x).map A.mulVec,
          dotProduct w (y - (fun i => A i 2)) = 0) ↔
            (A01514 A (c0159 t) x).transpose.mulVec w = 0)

/-- Vector of actual conditional variances of the supplied future jumps. -/
noncomputable def V0150 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (G : MeasurableSpace Ω)
    (μ : @Measure Ω mΩ) (Y : Fin d → Ω → ℝ) : Ω → Fin d → ℝ :=
  fun ω j => Var[Y j; μ | G] ω

/-- Zero scale and zero starting vector give point laws. Initial-time conclusions use
only the stated initial value; the same-time conditional law uses measurability. -/
def boundaryStatement : Prop :=
  (∀ (d : ℕ) (x : Fin d → NNReal), Q01513 0 x = Measure.dirac (fun j => (x j : ℝ))) ∧
  (∀ (d : ℕ) (c : Fin d → ℝ), (∀ j, 0 ≤ c j) → Q01513 c 0 = Measure.dirac 0) ∧
  (∀ (d m : ℕ) (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ X : Ω → Fin d → ℝ, (∀ᵐ ω ∂μ, X ω = 1) → ∀ A : Matrix (Fin m) (Fin d) ℝ,
      μ.map (fun ω => A.mulVec (X ω)) = Measure.dirac (fun i => ∑ j, A i j) ∧
      (μ.map (fun ω => A.mulVec (X ω))).support = {fun i => ∑ j, A i j}) ∧
  (∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    G ≤ mΩ → ∀ Y : Ω → Fin d → ℝ, Measurable[G] Y →
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => Measure.dirac (Y ω) B)) ∧
      (∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
        (μ.restrict D).map Y B = ∫⁻ ω in D, Measure.dirac (Y ω) B ∂μ) ∧
      (∀ ω, (Measure.dirac (Y ω)).support = {Y ω}) ∧
      (IsFiniteMeasure μ → (∀ j, Integrable (fun ω => Y ω j) μ) →
        ∀ j, μ[fun ω => Y ω j | G] = (fun ω => Y ω j) ∧ Var[fun ω => Y ω j; μ | G] = 0)) ∧
  (∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    G ≤ mΩ → ∀ Y : Fin d → Ω → ℝ,
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => Measure.dirac (V0150 G μ Y ω) B)) ∧
      (∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
        (μ.restrict D).map (V0150 G μ Y) B = ∫⁻ ω in D, Measure.dirac (V0150 G μ Y ω) B ∂μ) ∧
      (∀ ω, (Measure.dirac (V0150 G μ Y ω)).support = {V0150 G μ Y ω}))

/-- Full zero-mean-reversion kernel, retaining the random-drift and correlation terms. -/
noncomputable def K0154 {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (n : Fin m) (j : Fin d) (u : ℝ) : ℝ :=
  (g n j u) ^ 2 + 2 * ρ j u * g n j u * α j * (∫ s in u..T n, b n j s) +
    (α j) ^ 2 * (∫ s in u..T n, b n j s) ^ 2
/-- The meeting matrix obtained by integrating the full kernel in (15.4). -/
noncomputable def A0154 {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  fun n j => ∫ u in t..T n, K0154 g b ρ α T n j u

/-- The five explicit premises of Claim 013's Lean conditional-variance assembly,
specialized to zero mean reversion. No affine variance identity or state law is assumed.
The SDE derivation of these premises is not proved here. -/
def H0154 {m d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : @Measure Ω mΩ) (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ) : Prop :=
  (∀ n i j, Integrable (fun ω => Z n i ω * Z n j ω) μ) ∧
  (∀ n, Y n - μ[Y n | G] =ᵐ[μ] fun ω => ∑ j, Z n j ω) ∧
  (∀ n j, μ[fun ω => Z n j ω ^ 2 | G] =ᵐ[μ] μ[I01314 n j | G]) ∧
  (∀ n i j, i ≠ j → μ[fun ω => Z n i ω * Z n j ω | G] =ᵐ[μ] 0) ∧
  (∀ n j, μ[I01314 n j | G] =ᵐ[μ] fun ω =>
    ∫ u in t..T n, K0154 g b ρ α T n j u * v ω j)

/-- Connect the actual meeting variances to the full-kernel image. The five Claim 013
Lean premises in `H0154` and the joint transforms remain explicit; neither is derived
from the SDE here. `G` is current model information and `H` is earlier information. -/
def meetingVarianceStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (G H : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsProbabilityMeasure μ → G ≤ mΩ → H ≤ G →
    ∀ (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
      (v : Ω → Fin d → NNReal), Measurable[G] v →
      ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ)
        (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ),
        (∀ n, t ≤ T n) → (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
        H0154 G μ Y Z I01314 v g b ρ α T t →
        let A := A0154 g b ρ α T t
        (∀ n j, 0 ≤ A n j) ∧
        (V0150 G μ Y =ᵐ[μ] fun ω => A.mulVec (fun j => (v ω j : ℝ))) ∧
        ∀ c : Fin d → ℝ, (∀ j, 0 ≤ c j) →
          (∀ x : Fin d → NNReal,
            (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
              (∫ ω, Real.exp (-(∑ j, l j * v ω j)) ∂μ) =
                Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j)))) →
            let B := A01514 A c x
            let b' := b01514 A 0 c x
            μ.map (V0150 G μ Y) = (Q01513 c x).map A.mulVec ∧
            (μ.map (V0150 G μ Y)).support = cone0154 B b' ∧
            IsClosed (cone0154 B b') ∧
            (affineSpan ℝ (cone0154 B b') : Set (Fin m → ℝ)) =
              (fun y => b' + y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
            (∀ w, (∀ᵐ y ∂μ.map (V0150 G μ Y), dotProduct w (y - b') = 0) ↔ B.transpose.mulVec w = 0) ∧
            (∀ i, MemLp (fun ω => V0150 G μ Y ω i) 2 μ ∧
              (∫ ω, V0150 G μ Y ω i ∂μ) = ∑ j, A i j * x j) ∧
            (∀ i k, cov[fun ω => V0150 G μ Y ω i, fun ω => V0150 G μ Y ω k; μ] =
              cov0157 A (fun j => 2 * c j * x j) i k) ∧
            LinearMap.ker (cov0157 A (fun j => 2 * c j * x j)).mulVecLin =
              LinearMap.ker B.transpose.mulVecLin ∧
            (cov0157 A (fun j => 2 * c j * x j)).rank = B.rank ∧
            (μ.map (V0150 G μ Y)) {b'} =
              ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, B i j ≠ 0) then (x j : ℝ) / c j else 0)))) ∧
          (∀ S : Ω → Fin d → NNReal, Measurable[H] S →
            (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
              μ[fun ω => Real.exp (-(∑ j, l j * v ω j)) | H] =ᵐ[μ]
                fun ω => Real.exp (-(∑ j, (S ω j : ℝ) * l j / (1 + c j * l j)))) →
            (∀ B, MeasurableSet B → Measurable[H]
              (fun ω => ((Q01513 c (S ω)).map A.mulVec) B)) ∧
            (∀ D, MeasurableSet[H] D → ∀ B, MeasurableSet B →
              (μ.restrict D).map (V0150 G μ Y) B =
                ∫⁻ ω in D, ((Q01513 c (S ω)).map A.mulVec) B ∂μ) ∧
            ∀ ω,
              ((Q01513 c (S ω)).map A.mulVec).support =
                cone0154 (A01514 A c (S ω)) (b01514 A 0 c (S ω)))

/-- Backward exponential in the proof of (15.2) and (15.13). -/
noncomputable def q0152 (α T l s : ℝ) : ℝ := l / (1 + (α^2*(T-s)/2)*l)
noncomputable def E0152 {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-(∑ j, q0152 (α j) T (l j) s * x j))
noncomputable def M0152 {d : ℕ} {Ω : Type} (α l : Fin d → ℝ) (T : ℝ)
    (X : ℝ → Ω → Fin d → NNReal) (s : ℝ) (ω : Ω) : ℝ :=
  E0152 α l T s (fun j => (X s ω j : ℝ))
def filt0152 {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ mΩ) (T : NNReal) :
    Filtration (Set.Icc (0 : ℝ) T) mΩ where
  seq s := F s.val
  mono' := fun _ _ h => F.mono h
  le' := fun s => F.le s.val

/-- Explicit stochastic premise still requiring the SDE/Itô construction:
the stopped backward exponentials are martingales, with localizers eventually
past the finite terminal time. No conditional transform is assumed. -/
def H0152 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℝ mΩ) (α l : Fin d → ℝ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) : Prop :=
  ∃ σ : ℕ → Ω → Set.Icc (0 : ℝ) T,
    (∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, σ n ω = ⟨T, T.coe_nonneg, le_rfl⟩) ∧
    ∀ n, Martingale (fun (s : Set.Icc (0 : ℝ) T) ω => M0152 α l T X (min (s : ℝ) (σ n ω : ℝ)) ω) (filt0152 F T) μ

/-- The ordinary derivatives used in the diagonal Itô cancellation, and the bound
needed for localization. This is a calculus result, not an Itô formula. -/
def analyticStatement : Prop :=
  ∀ (d : ℕ) (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ),
    (∀ j, 0 ≤ l j) → s ≤ T →
      (∀ j, HasDerivAt (q0152 (α j) T (l j))
        ((α j)^2*(q0152 (α j) T (l j) s)^2/2) s) ∧
      ((∀ j, 0 ≤ x j) → 0 < E0152 α l T s x ∧ E0152 α l T s x ≤ 1) ∧
      deriv (fun u => E0152 α l T u x) s +
        ∑ j, ((α j)^2*x j/2) *
          deriv (deriv (fun u => E0152 α l T s (Function.update x j u))) (x j) = 0

/-- Joint transforms and transition laws from the explicit stopped-martingale
premise `H0152`, including conditioning in the full supplied filtration. -/
def localizedTransitionStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (T : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) T, Measurable[F s] (X s)) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X) →
      (∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
        μ.map (fun ω j => (X T ω j : ℝ)) = Q01513 (fun j => (α j)^2*(T : ℝ)/2) x) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
          μ[fun ω => Real.exp (-(∑ j, l j * X T ω j)) | F s] =ᵐ[μ]
            fun ω => Real.exp (-(∑ j, (X s ω j : ℝ)*l j/(1+((α j)^2*((T : ℝ)-s)/2)*l j)))) ∧
        (∀ B, MeasurableSet B → Measurable[F s]
          (fun ω => Q01513 (fun j => (α j)^2*((T : ℝ)-s)/2) (X s ω) B)) ∧
        ∀ D, MeasurableSet[F s] D → ∀ B, MeasurableSet B →
          (μ.restrict D).map (fun ω j => (X T ω j : ℝ)) B =
            ∫⁻ ω in D, Q01513 (fun j => (α j)^2*((T : ℝ)-s)/2) (X s ω) B ∂μ

/-- Actual meeting-variance laws and their exact support without an assumed state
transform. `H0152` and Claim 013's five premises `H0154` are still hypotheses. -/
def localizedMeetingVarianceStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (t : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[F s] (X s)) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l t X) →
      ∀ (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
        (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ),
        (∀ n, (t : ℝ) ≤ T n) → (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
        H0154 (F t) μ Y Z I01314 (X t) g b ρ α T t →
        let A := A0154 g b ρ α T t
        (∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
          let c := fun j => (α j)^2*(t : ℝ)/2
          μ.map (V0150 (F t) μ Y) = (Q01513 c x).map A.mulVec ∧
          (μ.map (V0150 (F t) μ Y)).support =
            cone0154 (A01514 A c x) (b01514 A 0 c x)) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t,
          let c := fun j => (α j)^2*((t : ℝ)-s)/2
          (∀ B, MeasurableSet B → Measurable[F s]
            (fun ω => ((Q01513 c (X s ω)).map A.mulVec) B)) ∧
          (∀ D, MeasurableSet[F s] D → ∀ B, MeasurableSet B →
            (μ.restrict D).map (V0150 (F t) μ Y) B =
              ∫⁻ ω in D, ((Q01513 c (X s ω)).map A.mulVec) B ∂μ) ∧
          ∀ ω, ((Q01513 c (X s ω)).map A.mulVec).support =
            cone0154 (A01514 A c (X s ω)) (b01514 A 0 c (X s ω))

/-- Moments, martingale and absorption of the actual state process from `H0152`.
No additional independence, integrability or conditional-moment premises are assumed.
The SDE derivation of `H0152` remains outside this target. -/
def localizedStateMomentStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (T : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) T, Measurable[F s] (X s)) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X) →
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
        iIndepFun (fun j ω => (X T ω j : ℝ)) μ ∧ ∀ j : Fin d,
        MemLp (fun ω => (X T ω j : ℝ)) 2 μ ∧
        (∫ ω, (X T ω j : ℝ) ∂μ) = x j ∧
        Var[fun ω => (X T ω j : ℝ); μ] = (α j)^2*(T : ℝ)*x j ∧
        Martingale (fun (s : Set.Icc (0 : ℝ) T) ω => (X s.val ω j : ℝ)) (filt0152 F T) μ ∧
        (α j = 0 → ∀ᵐ ω ∂μ, X T ω j = x j) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T,
          MemLp (fun ω => (X s ω j : ℝ)) 2 μ ∧
          (μ[fun ω => (X T ω j : ℝ) | F s] =ᵐ[μ] fun ω => (X s ω j : ℝ)) ∧
          (μ[fun ω => (X T ω j : ℝ)^2 | F s] =ᵐ[μ]
            fun ω => (X s ω j : ℝ)^2+(α j)^2*((T : ℝ)-s)*X s ω j) ∧
          (Var[fun ω => (X T ω j : ℝ); μ | F s] =ᵐ[μ]
            fun ω => (α j)^2*((T : ℝ)-s)*X s ω j) ∧
          (∀ᵐ ω ∂μ, X s ω j = 0 → X T ω j = 0)

/-- The actual deterministic weighted state integral in the zero-mean-reversion
conditional-isometry calculation; its conditional expectation is proved below. -/
noncomputable def I0154 {m d : ℕ} {Ω : Type}
    (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ)
    (T : Fin m → ℝ) (t : ℝ) (X : ℝ → Ω → Fin d → NNReal) : Fin m → Fin d → Ω → ℝ :=
  fun n j ω => ∫ u in t..T n, K0154 g b ρ α T n j u * X u ω j

/-- Conditional integration from continuous adapted paths and `H0152`.
Weighted-integral integrability and the conditional-integral identity are conclusions. -/
def localizedIntegrationStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (U : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[F s] (X s)) →
      (∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) U => (X s.val ω j : ℝ))) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l U X) →
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ U → ∀ (j : Fin d) (K : ℝ → ℝ),
        IntervalIntegrable K volume a b →
        Integrable (fun ω => ∫ u in a..b, K u*X u ω j) μ ∧
        (μ[fun ω => ∫ u in a..b, K u*X u ω j | F a] =ᵐ[μ]
          fun ω => ∫ u in a..b, K u*X a ω j)

/-- Specialize conditional Fubini to the full kernel. The first four Claim 013
premises remain explicit; the fifth is derived for the actual state integral. -/
def integrationAssemblyStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (U : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[F s] (X s)) →
      (∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) U => (X s.val ω j : ℝ))) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l U X) →
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
      ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ),
        0 ≤ t → (∀ n, t ≤ T n ∧ T n ≤ U) →
        (∀ n j, IntervalIntegrable (K0154 g b ρ α T n j) volume t (T n)) →
        ∀ (Y : Fin m → Ω → ℝ) (Z : Fin m → Fin d → Ω → ℝ),
          (∀ n i j, Integrable (fun ω => Z n i ω*Z n j ω) μ) →
          (∀ n, Y n-μ[Y n | F t] =ᵐ[μ] fun ω => ∑ j, Z n j ω) →
          (∀ n j, μ[fun ω => Z n j ω^2 | F t] =ᵐ[μ]
            μ[I0154 g b ρ α T t X n j | F t]) →
          (∀ n i j, i ≠ j → μ[fun ω => Z n i ω*Z n j ω | F t] =ᵐ[μ] 0) →
          H0154 (F t) μ Y Z (I0154 g b ρ α T t X) (X t) g b ρ α T t ∧
          (V0150 (F t) μ Y =ᵐ[μ] fun ω => (A0154 g b ρ α T t).mulVec (fun j => (X t ω j : ℝ)))

/-- Regularity and an explicit bound for the complete kernel from bounded measurable
coefficients on the integration interval. No continuity of g, b or ρ is assumed. -/
def kernelRegularityStatement : Prop :=
  ∀ (m d : ℕ) (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ)
    (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ), (∀ n, t ≤ T n) →
    (∀ n j, AEStronglyMeasurable (g n j) (volume.restrict (Icc t (T n)))) →
    (∀ n j, AEStronglyMeasurable (b n j) (volume.restrict (Icc t (T n)))) →
    (∀ n j, AEStronglyMeasurable (ρ j) (volume.restrict (Icc t (T n)))) →
    ∀ G B : Fin m → Fin d → ℝ,
      (∀ n j u, u ∈ Icc t (T n) → |g n j u| ≤ G n j) →
      (∀ n j u, u ∈ Icc t (T n) → |b n j u| ≤ B n j) →
      (∀ n j u, u ∈ Icc t (T n) → |ρ j u| ≤ 1) → ∀ n j,
      ContinuousOn (fun u => ∫ s in u..T n, b n j s) (Icc t (T n)) ∧
      IntervalIntegrable (K0154 g b ρ α T n j) volume t (T n) ∧
      (∀ u ∈ Icc t (T n), |∫ s in u..T n, b n j s| ≤ B n j*(T n-t)) ∧
      (∀ u ∈ Icc t (T n), 0 ≤ K0154 g b ρ α T n j u ∧
        K0154 g b ρ α T n j u ≤ (G n j+|α j| * (B n j*(T n-t)))^2)

/-- The full-kernel assembly with coefficient regularity in place of a kernel-integrability
premise. The actual SDE construction and first four stochastic premises remain explicit. -/
def regularIntegrationAssemblyStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (U : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[F s] (X s)) →
      (∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) U => (X s.val ω j : ℝ))) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l U X) →
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
      ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ),
        0 ≤ t → (∀ n, t ≤ T n ∧ T n ≤ U) →
        (∀ n j, AEStronglyMeasurable (g n j) (volume.restrict (Icc t (T n)))) →
        (∀ n j, AEStronglyMeasurable (b n j) (volume.restrict (Icc t (T n)))) →
        (∀ n j, AEStronglyMeasurable (ρ j) (volume.restrict (Icc t (T n)))) →
        (∀ n j, ∃ G B : ℝ, ∀ u ∈ Icc t (T n), |g n j u| ≤ G ∧ |b n j u| ≤ B) →
        (∀ n j u, u ∈ Icc t (T n) → |ρ j u| ≤ 1) →
        ∀ (Y : Fin m → Ω → ℝ) (Z : Fin m → Fin d → Ω → ℝ),
          (∀ n i j, Integrable (fun ω => Z n i ω*Z n j ω) μ) →
          (∀ n, Y n-μ[Y n | F t] =ᵐ[μ] fun ω => ∑ j, Z n j ω) →
          (∀ n j, μ[fun ω => Z n j ω^2 | F t] =ᵐ[μ]
            μ[I0154 g b ρ α T t X n j | F t]) →
          (∀ n i j, i ≠ j → μ[fun ω => Z n i ω*Z n j ω | F t] =ᵐ[μ] 0) →
          (∀ n j, IntervalIntegrable (K0154 g b ρ α T n j) volume t (T n)) ∧
          H0154 (F t) μ Y Z (I0154 g b ρ α T t X) (X t) g b ρ α T t ∧
          (V0150 (F t) μ Y =ᵐ[μ] fun ω => (A0154 g b ρ α T t).mulVec (fun j => (X t ω j : ℝ)))


/-- Number of calendar meetings at or before s; the Fin index lists meetings 1 through N. -/
noncomputable def j01530 {N : ℕ} (T : Fin N → ℝ) (s : ℝ) : ℕ :=
  ∑ i, if T i ≤ s then 1 else 0
noncomputable def G01530 (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, γ (i+1)
/-- Claim 013 (13.3), with the ordinal cumulative loading and actual decay integral. -/
noncomputable def h01530 {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (s u : ℝ) : ℝ :=
  a s * Real.exp (-(∫ q in s..u, lam q)) * G01530 γ (j01530 T u-j01530 T s)
/-- Claim 013 (13.4); n.val + 1 is the paper meeting index. -/
noncomputable def g01530 {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (n : Fin N) (s : ℝ) : ℝ :=
  a s * Real.exp (-(∫ q in s..T n, lam q)) * γ (n.val+1-j01530 T s)
/-- The full drift coefficient in (13.4), using the actual maturity integral. -/
noncomputable def b01530 {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (n : Fin N) (s : ℝ) : ℝ :=
  g01530 T a lam γ n s * ∫ u in s..T n, h01530 T a lam γ s u

/-- Source-formula coefficient regularity and full-kernel integrability from the primitive
measurable, locally bounded deterministic coefficients; no supplied g or b is assumed. -/
def sourceCoefficientStatement : Prop :=
  ∀ (N m d : ℕ) (T : Fin N → ℝ) (rows : Fin m → Fin N) (a lam ρ : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
    (α : Fin d → ℝ) (t : ℝ), (∀ n, t ≤ T (rows n)) →
    (∀ j, Measurable (a j)) → (∀ j, Measurable (lam j)) → (∀ j, Measurable (ρ j)) →
    (∀ j u, 0 ≤ lam j u) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Icc l r, |lam j u| ≤ B) →
    (∀ n j, ∃ A : ℝ, ∀ u ∈ Icc t (T (rows n)), |a j u| ≤ A) →
    (∀ n j u, u ∈ Icc t (T (rows n)) → |ρ j u| ≤ 1) →
    (∀ n j, Measurable (g01530 T (a j) (lam j) (γ j) (rows n)) ∧
      Measurable (b01530 T (a j) (lam j) (γ j) (rows n))) ∧
    (∀ n j, ∃ G B : ℝ, ∀ u ∈ Icc t (T (rows n)),
      |g01530 T (a j) (lam j) (γ j) (rows n) u| ≤ G ∧
      |b01530 T (a j) (lam j) (γ j) (rows n) u| ≤ B) ∧
    (∀ n j, IntervalIntegrable
      (K0154 (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) n j) volume t (T (rows n)))

/-- Actual conditional-variance assembly with g and b constructed from the source inputs.
The retained rows index the full calendar, so past meetings still enter the ordinal count.
H0152 and the first four stochastic premises still require an SDE derivation. -/
def sourceIntegrationAssemblyStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (α : Fin d → ℝ) (U : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ s ∈ Set.Icc (0 : ℝ) U, Measurable[F s] (X s)) →
      (∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) U => (X s.val ω j : ℝ))) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l U X) →
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
      ∀ (N : ℕ) (a lam ρ : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ)
        (T : Fin N → ℝ) (rows : Fin m → Fin N) (t : ℝ),
        0 ≤ t → (∀ n, t ≤ T (rows n) ∧ T (rows n) ≤ U) →
    (∀ j, Measurable (a j)) → (∀ j, Measurable (lam j)) → (∀ j, Measurable (ρ j)) →
    (∀ j u, 0 ≤ lam j u) →
    (∀ j l r, ∃ B : ℝ, ∀ u ∈ Icc l r, |lam j u| ≤ B) →
    (∀ n j, ∃ A : ℝ, ∀ u ∈ Icc t (T (rows n)), |a j u| ≤ A) →
    (∀ n j u, u ∈ Icc t (T (rows n)) → |ρ j u| ≤ 1) →
        ∀ (Y : Fin m → Ω → ℝ) (Z : Fin m → Fin d → Ω → ℝ),
          (∀ n i j, Integrable (fun ω => Z n i ω*Z n j ω) μ) →
          (∀ n, Y n-μ[Y n | F t] =ᵐ[μ] fun ω => ∑ j, Z n j ω) →
          (∀ n j, μ[fun ω => Z n j ω^2 | F t] =ᵐ[μ]
            μ[I0154 (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) t X n j | F t]) →
          (∀ n i j, i ≠ j → μ[fun ω => Z n i ω*Z n j ω | F t] =ᵐ[μ] 0) →
          (∀ n j, IntervalIntegrable (K0154 (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) n j) volume t (T (rows n))) ∧
          H0154 (F t) μ Y Z (I0154 (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) t X) (X t) (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) t ∧
          (V0150 (F t) μ Y =ᵐ[μ] fun ω => (A0154 (fun n j => g01530 T (a j) (lam j) (γ j) (rows n)) (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ α (fun n => T (rows n)) t).mulVec (fun j => (X t ω j : ℝ)))

/-- The bounded first time the largest variance coordinate reaches n+2, or T if it does not. -/
noncomputable def σ01521 {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (ω : Ω) : Icc (0 : ℝ) T := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  exact sInf {s : Icc (0 : ℝ) T | (n+2 : NNReal) ≤ Finset.univ.sup (X s.val ω)}

/-- Construct the localizers in (15.21) from the actual continuous adapted process.
Only the martingale identity for the explicit stopped exponentials remains a premise
when using this construction to establish H0152. -/
def localizerConstructionStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Filtration ℝ mΩ)
    (T : NNReal) (X : ℝ → Ω → Fin d → NNReal),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ n, IsStoppingTime (filt0152 F T)
      (fun ω => (σ01521 T X n ω : WithTop (Icc (0 : ℝ) T)))) ∧
    (∀ ω, Monotone (fun n => σ01521 T X n ω)) ∧
    (∀ ω, ∀ᶠ n in Filter.atTop, σ01521 T X n ω = ⟨T, T.coe_nonneg, le_rfl⟩) ∧
    (∀ ω, (∀ j, X 0 ω j ≤ 1) → ∀ n (s : Icc (0 : ℝ) T),
      s ≤ σ01521 T X n ω → ∀ j, X s.val ω j ≤ n+2) ∧
    (∀ (μ : @Measure Ω mΩ) (α l : Fin d → ℝ),
      (∀ n, Martingale (fun (s : Icc (0 : ℝ) T) ω =>
        M0152 α l T X (min s.val (σ01521 T X n ω).val) ω) (filt0152 F T) μ) →
      H0152 μ F α l T X)

/-- Pointwise squared-integrand bound for (15.23), including the stopping indicator.
This is not a stochastic-integral construction or an Itô formula. -/
def localizedIntegrandBoundStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal),
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    ∀ ω, (∀ j, X 0 ω j ≤ 1) → ∀ (n : ℕ) (α l : Fin d → ℝ),
    (∀ j, 0 ≤ l j) → ∀ (s : Icc (0 : ℝ) T) (j : Fin d),
    0 ≤ (if s ≤ σ01521 T X n ω then
      (M0152 α l T X s.val ω)^2*(q0152 (α j) T (l j) s.val)^2*(α j)^2*X s.val ω j else 0) ∧
    (if s ≤ σ01521 T X n ω then
      (M0152 α l T X s.val ω)^2*(q0152 (α j) T (l j) s.val)^2*(α j)^2*X s.val ω j else 0)
      ≤ (l j)^2*(α j)^2*(n+2)

/-- The ordinary integrand in the stopped Brownian integral (15.22), extended by zero
outside the bounded stopping interval. No stochastic integral is defined here. -/
noncomputable def B01522 {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (s : ℝ) (ω : Ω) : ℝ :=
  if s ∈ Icc (0 : ℝ) (σ01521 T X n ω).val then
    M0152 α l T X s ω * q0152 (α j) T (l j) s * α j * Real.sqrt (X s ω j) else 0

/-- Measurability, square integrability and the expected bound (15.23) for the explicit
stopped integrands, without an H0152, state-moment or stochastic-integral premise. -/
def stoppedIntegrandIntegrabilityStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) → (∀ j, 0 ≤ l j) → ∀ n,
    (∀ j, Measurable (Function.uncurry (B01522 T X n α l j)) ∧
      MemLp (Function.uncurry (B01522 T X n α l j)) 2
        ((volume.restrict (Icc (0 : ℝ) T)).prod μ) ∧
      Integrable (fun ω => ∫ s in Icc (0 : ℝ) T, (B01522 T X n α l j s ω)^2) μ) ∧
    0 ≤ (∫ ω, ∑ j, ∫ s in Icc (0 : ℝ) T, (B01522 T X n α l j s ω)^2 ∂volume ∂μ) ∧
    (∫ ω, ∑ j, ∫ s in Icc (0 : ℝ) T, (B01522 T X n α l j s ω)^2 ∂volume ∂μ)
      ≤ T * (n+2) * ∑ j, (α j)^2 * (l j)^2

/-- Predictability of the actual ordinary integrands in (15.22) on the finite horizon.
No stopping-indicator, predictability, H0152 or initial-value premise is added. -/
def stoppedIntegrandPredictabilityStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Filtration ℝ mΩ)
    (T : NNReal) (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ j, 0 ≤ l j) →
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    ∀ n j, IsStronglyPredictable (filt0152 F T)
      (fun s ω => B01522 T X n α l j s.val ω) ∧
      IsStronglyProgressive (filt0152 F T) (fun s ω => B01522 T X n α l j s.val ω)

/-- One elementary Brownian-integral contribution in (15.22). -/
noncomputable def J01522 {Ω : Type} (B : NNReal → Ω → ℝ) (H : Ω → ℝ)
    (a b : NNReal) (ω : Ω) : ℝ := H ω * (B b ω-B a ω)
/-- The finite sum for coefficients known at the left endpoints of the intervals. -/
noncomputable def S01522 {Ω : Type} {N : ℕ} (B : NNReal → Ω → ℝ)
    (H : Fin N → Ω → ℝ) (t : Fin (N+1) → NNReal) (ω : Ω) : ℝ :=
  ∑ i, J01522 B (H i) (t i.castSucc) (t i.succ) ω

/-- Elementary Brownian sums: conditional means and isometry from the Gaussian
increment law and independence from the supplied full filtration. The latter is
explicit because Mathlib's Brownian path-law predicate alone does not encode it.
No stochastic-integral isometry or martingale premise is assumed. -/
def elementaryBrownianIntegralStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ), IsProbabilityMeasure μ →
    ∀ (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ t, Measurable[F t] (B t)) →
    (∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) →
    ∀ (N : ℕ) (t : Fin (N+1) → NNReal) (H : Fin N → Ω → ℝ), Monotone t →
    (∀ i, Measurable[F (t i.castSucc)] (H i)) → (∀ i, MemLp (H i) 2 μ) →
    (∀ i, MemLp (J01522 B (H i) (t i.castSucc) (t i.succ)) 2 μ ∧
      μ[J01522 B (H i) (t i.castSucc) (t i.succ) | F (t i.castSucc)] =ᵐ[μ] 0 ∧
      μ[fun ω => (J01522 B (H i) (t i.castSucc) (t i.succ) ω)^2 | F (t i.castSucc)] =ᵐ[μ]
        fun ω => ((t i.succ : ℝ)-t i.castSucc) * (H i ω)^2) ∧
    (∀ i j, i < j → (∫ ω, J01522 B (H i) (t i.castSucc) (t i.succ) ω *
      J01522 B (H j) (t j.castSucc) (t j.succ) ω ∂μ) = 0) ∧
    MemLp (S01522 B H t) 2 μ ∧ μ[S01522 B H t | F (t 0)] =ᵐ[μ] 0 ∧
    (∫ ω, (S01522 B H t ω)^2 ∂μ) =
      ∑ i, ((t i.succ : ℝ)-t i.castSucc) * ∫ ω, (H i ω)^2 ∂μ

/-- The contribution of one elementary integrand up to time s. -/
noncomputable def P01522 {Ω : Type} (B : NNReal → Ω → ℝ) (H : Ω → ℝ)
    (a b s : NNReal) : Ω → ℝ := J01522 B H (min s a) (min s b)

/-- The elementary integral process associated with the finite sum S01522. -/
noncomputable def R01522 {Ω : Type} {N : ℕ} (B : NNReal → Ω → ℝ)
    (H : Fin N → Ω → ℝ) (t : Fin (N+1) → NNReal) (s : NNReal) (ω : Ω) : ℝ :=
  ∑ i, P01522 B (H i) (t i.castSucc) (t i.succ) s ω

/-- Continuous-time elementary Brownian integrals in the supplied full filtration.
The martingale and all-time isometry conclusions are derived, not assumed. -/
def elementaryBrownianProcessStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ), IsProbabilityMeasure μ →
    ∀ (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ t, Measurable[F t] (B t)) →
    (∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) →
    ∀ (N : ℕ) (t : Fin (N+1) → NNReal) (H : Fin N → Ω → ℝ), Monotone t →
    (∀ i, Measurable[F (t i.castSucc)] (H i)) → (∀ i, MemLp (H i) 2 μ) →
    Martingale (R01522 B H t) F μ ∧
    (∀ᵐ ω ∂μ, Continuous (fun s => R01522 B H t s ω)) ∧
    (∀ s, MemLp (R01522 B H t s) 2 μ ∧
      μ[S01522 B H t | F s] =ᵐ[μ] R01522 B H t s ∧
      (∫ ω, (R01522 B H t s ω)^2 ∂μ) =
        ∑ i, ((min s (t i.succ) : ℝ)-min s (t i.castSucc)) * ∫ ω, (H i ω)^2 ∂μ) ∧
    (∀ s, s ≤ t 0 → R01522 B H t s = 0) ∧
    (∀ s, t (Fin.last N) ≤ s → R01522 B H t s = S01522 B H t)

/-- A Cauchy sequence of elementary terminal values defines a square-integrable
martingale by conditional expectation. Approximation is uniform in deterministic
time in L². The Cauchy condition is explicit; density of elementary integrands
and continuous versions of the limiting process are not asserted here. -/
def elementaryBrownianLimitStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ), IsProbabilityMeasure μ →
    ∀ (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ t, Measurable[F t] (B t)) →
    (∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) →
    ∀ (N : ℕ → ℕ) (t : ∀ n, Fin (N n+1) → NNReal) (H : ∀ n, Fin (N n) → Ω → ℝ),
    (∀ n, Monotone (t n)) → (∀ n i, Measurable[F (t n i.castSucc)] (H n i)) →
    (∀ n i, MemLp (H n i) 2 μ) →
    ∀ X : ℕ → Lp ℝ 2 μ, (∀ n, (X n : Ω → ℝ) =ᵐ[μ] S01522 B (H n) (t n)) →
    CauchySeq X → ∃ Z : Lp ℝ 2 μ, Tendsto X atTop (𝓝 Z) ∧
      Martingale (fun s => μ[(Z : Ω → ℝ) | F s]) F μ ∧
      μ[(Z : Ω → ℝ) | F 0] =ᵐ[μ] 0 ∧
      (∀ s, MemLp (μ[(Z : Ω → ℝ) | F s]) 2 μ) ∧
      (∀ n s, eLpNorm (R01522 B (H n) (t n) s - μ[(Z : Ω → ℝ) | F s]) 2 μ ≤ edist (X n) Z) ∧
      (∀ ε : ENNReal, 0 < ε → ∀ᶠ n in atTop, ∀ s,
        eLpNorm (R01522 B (H n) (t n) s - μ[(Z : Ω → ℝ) | F s]) 2 μ < ε)

/-- Deterministic mesh times used for (15.22), capped at the horizon. -/
noncomputable def r01522 (T : NNReal) (m k : ℕ) : Icc (0 : ℝ) T :=
  ⟨min T ((k : ℝ)/(m+1)), le_min T.coe_nonneg (by positivity), min_le_left _ _⟩

/-- Earlier mesh time, with the value at an endpoint taken from its left. -/
noncomputable def a01522 (T : NNReal) (m : ℕ) (s : ℝ) : Icc (0 : ℝ) T :=
  r01522 T m (Nat.ceil (s*(m+1))-1)

/-- Step approximation to the explicit stopped integrand, zero off [0,T]. -/
noncomputable def D01522 {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (m : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  if s ∈ Icc (0 : ℝ) T then B01522 T X n α l j (a01522 T m s).val ω else 0

/-- Explicit step approximation of B01522 in mean square for time times probability.
This does not yet identify limits of Brownian sums with a stochastic integral. -/
def stoppedIntegrandApproximationStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) → (∀ j, 0 ≤ l j) → ∀ n j,
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    (∀ m, Monotone (r01522 T m) ∧
      (r01522 T m (Nat.ceil ((T : ℝ)*(m+1)))).val = T ∧
      (∀ k (s : Icc (0 : ℝ) T), s ∈ Ioc (r01522 T m k) (r01522 T m (k+1)) →
        D01522 T X n α l j m s.val = B01522 T X n α l j (r01522 T m k).val) ∧
      (∀ k, Measurable[F (r01522 T m k).val] (B01522 T X n α l j (r01522 T m k).val) ∧
        MemLp (B01522 T X n α l j (r01522 T m k).val) 2 μ) ∧
      Measurable (Function.uncurry (D01522 T X n α l j m)) ∧
      MemLp (Function.uncurry (D01522 T X n α l j m)) 2
        ((volume.restrict (Icc (0 : ℝ) T)).prod μ) ∧
      IsStronglyPredictable (filt0152 F T) (fun s ω => D01522 T X n α l j m s.val ω)) ∧
    (∀ s ∈ Icc (0 : ℝ) T, ∀ ω, Tendsto (fun m => D01522 T X n α l j m s ω)
      atTop (𝓝 (B01522 T X n α l j s ω))) ∧
    Tendsto (fun m => ∫ p : ℝ × Ω,
      (D01522 T X n α l j m p.1 p.2 - B01522 T X n α l j p.1 p.2)^2
        ∂((volume.restrict (Icc (0 : ℝ) T)).prod μ)) atTop (𝓝 0)

/-- The ordinary step integrand corresponding to S01522, using intervals (a,b]. -/
noncomputable def Q01522 {Ω : Type} {N : ℕ} (H : Fin N → Ω → ℝ)
    (t : Fin (N+1) → NNReal) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ i, (Ioc (t i.castSucc : ℝ) (t i.succ)).indicator (fun _ => H i ω) s

/-- Cross-partition isometry for elementary integrals against the same Brownian motion.
The right side uses actual Lebesgue integrals of the ordinary step functions. -/
def elementaryBrownianComparisonStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ), IsProbabilityMeasure μ →
    ∀ (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ t, Measurable[F t] (B t)) →
    (∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) →
    ∀ (N M : ℕ) (t : Fin (N+1) → NNReal) (u : Fin (M+1) → NNReal)
      (H : Fin N → Ω → ℝ) (K : Fin M → Ω → ℝ), Monotone t → Monotone u →
    (∀ i, Measurable[F (t i.castSucc)] (H i)) → (∀ j, Measurable[F (u j.castSucc)] (K j)) →
    (∀ i, MemLp (H i) 2 μ) → (∀ j, MemLp (K j) 2 μ) →
    Integrable (fun ω => S01522 B H t ω * S01522 B K u ω) μ ∧
    (∀ ω, Integrable (fun s => Q01522 H t s ω * Q01522 K u s ω) volume) ∧
    Integrable (fun ω => ∫ s, Q01522 H t s ω * Q01522 K u s ω) μ ∧
    (∫ ω, S01522 B H t ω * S01522 B K u ω ∂μ) =
      ∑ i, ∑ j, max 0 (min (t i.succ : ℝ) (u j.succ) - max (t i.castSucc : ℝ) (u j.castSucc)) *
        ∫ ω, H i ω * K j ω ∂μ ∧
    (∫ ω, S01522 B H t ω * S01522 B K u ω ∂μ) =
      ∫ ω, ∫ s, Q01522 H t s ω * Q01522 K u s ω ∂volume ∂μ ∧
    Integrable (fun ω => ∫ s, (Q01522 H t s ω - Q01522 K u s ω)^2) μ ∧
    (∫ ω, (S01522 B H t ω - S01522 B K u ω)^2 ∂μ) =
      ∫ ω, ∫ s, (Q01522 H t s ω - Q01522 K u s ω)^2 ∂volume ∂μ

/-- Transfer a mean-square Cauchy criterion on ordinary step integrands to actual
L² terminal Brownian sums, without a terminal-Cauchy premise. -/
def elementaryBrownianCauchyStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ), IsProbabilityMeasure μ →
    ∀ (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ t, Measurable[F t] (B t)) →
    (∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) →
    ∀ (N : ℕ → ℕ) (t : ∀ n, Fin (N n+1) → NNReal) (H : ∀ n, Fin (N n) → Ω → ℝ),
    (∀ n, Monotone (t n)) → (∀ n i, Measurable[F (t n i.castSucc)] (H n i)) →
    (∀ n i, MemLp (H n i) 2 μ) →
    (∀ ε : ℝ, 0 < ε → ∃ k, ∀ n ≥ k, ∀ m ≥ k,
      (∫ ω, ∫ s, (Q01522 (H n) (t n) s ω - Q01522 (H m) (t m) s ω)^2 ∂volume ∂μ) < ε) →
    ∃ X : ℕ → Lp ℝ 2 μ, (∀ n, (X n : Ω → ℝ) =ᵐ[μ] S01522 B (H n) (t n)) ∧ CauchySeq X

/-- Number of intervals in the finite mesh for (15.22). -/
noncomputable def N01522 (T : NNReal) (m : ℕ) : ℕ := Nat.ceil ((T : ℝ)*(m+1))

/-- The finite nonnegative mesh underlying D01522. -/
noncomputable def t01522 (T : NNReal) (m : ℕ) (i : Fin (N01522 T m+1)) : NNReal :=
  ⟨(r01522 T m i.val).val, (r01522 T m i.val).property.1⟩

/-- Left-endpoint coefficients of the explicit stopped integrand. -/
noncomputable def H01522 {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (m : ℕ) (i : Fin (N01522 T m)) : Ω → ℝ :=
  B01522 T X n α l j (r01522 T m i.val).val

/-- The supplied real-time filtration restricted to nonnegative times. -/
def F01522 {Ω : Type} {mΩ : MeasurableSpace Ω} (F : Filtration ℝ mΩ) :
    Filtration NNReal mΩ where
  seq s := F (s : ℝ)
  mono' := fun _ _ h => F.mono h
  le' := fun s => F.le (s : ℝ)

/-- L² Brownian integrals of the actual stopped integrands in (15.22), constructed
from the explicit finite meshes. No convergence or stochastic-integral premise is
assumed. Conditional increment isometries, the terminal-time identity and continuity
as an L²-valued process are included. A continuous martingale version is
constructed by almost-sure uniform convergence along a subsequence, with a
whole-interval approximation bound. Its square minus the accumulated squared
integrand is a martingale; the latter integral is adapted and has almost-sure
continuous nondecreasing paths. The Itô identity is not asserted. -/
def stoppedBrownianLimitStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) → (∀ j, 0 ≤ l j) →
    ∀ (B : NNReal → Ω → ℝ), IsBrownianReal B μ →
    (∀ s : NNReal, Measurable[F (s : ℝ)] (B s)) →
    (∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ) → ∀ n j,
    (∀ m, ∀ᵐ s ∂(volume : Measure ℝ), ∀ ω,
      Q01522 (H01522 T X n α l j m) (t01522 T m) s ω = D01522 T X n α l j m s ω) ∧
    (∀ ε : ℝ, 0 < ε → ∃ k, ∀ a ≥ k, ∀ b ≥ k,
      (∫ ω, ∫ s, (Q01522 (H01522 T X n α l j a) (t01522 T a) s ω -
        Q01522 (H01522 T X n α l j b) (t01522 T b) s ω)^2 ∂volume ∂μ) < ε) ∧
    ∃ (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ),
      (∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m)) ∧
      Tendsto Y atTop (𝓝 Z) ∧
      Martingale (fun s : NNReal => μ[(Z : Ω → ℝ) | F (s : ℝ)]) (F01522 F) μ ∧
      μ[(Z : Ω → ℝ) | F 0] =ᵐ[μ] 0 ∧
      (∀ s : NNReal, MemLp (μ[(Z : Ω → ℝ) | F (s : ℝ)]) 2 μ) ∧
      (∀ m s, eLpNorm (R01522 B (H01522 T X n α l j m) (t01522 T m) s -
        μ[(Z : Ω → ℝ) | F (s : ℝ)]) 2 μ ≤ edist (Y m) Z) ∧
      (∀ ε : ENNReal, 0 < ε → ∀ᶠ m in atTop, ∀ s,
        eLpNorm (R01522 B (H01522 T X n α l j m) (t01522 T m) s -
          μ[(Z : Ω → ℝ) | F (s : ℝ)]) 2 μ < ε) ∧
      (∫ ω, (Z ω)^2 ∂μ) = (∫ ω, ∫ s in Icc (0 : ℝ) T,
        (B01522 T X n α l j s ω)^2 ∂volume ∂μ) ∧
      (∫ ω, (Z ω)^2 ∂μ) ≤ T * ((l j)^2*(α j)^2*(n+2)) ∧
      (∀ s : NNReal,
        Integrable (fun ω => ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) μ ∧
        μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 | F (s : ℝ)] =ᵐ[μ]
          μ[fun ω => ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2 | F (s : ℝ)]) ∧
      (∀ s : NNReal, T ≤ s → μ[(Z : Ω → ℝ) | F (s : ℝ)] =ᵐ[μ] Z) ∧
      (∀ s t : NNReal, s ≤ t → t ≤ T →
        Integrable (fun ω => ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2) μ ∧
        μ[fun ω => (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 | F (s : ℝ)] =ᵐ[μ]
          μ[fun ω => ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2 | F (s : ℝ)] ∧
        (∫ ω, (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 ∂μ) ≤
          ((t : ℝ)-s)*((l j)^2*(α j)^2*(n+2))) ∧
      Continuous (fun s : Icc (0 : NNReal) T =>
        (condExpL2 ℝ ℝ (F.le (s.val : ℝ)) Z : Lp ℝ 2 μ)) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : NNReal → Ω → ℝ,
        Martingale C (F01522 F) μ ∧
        (∀ s, C s =ᵐ[μ] μ[(Z : Ω → ℝ) | F (s : ℝ)]) ∧
        (∀ᵐ ω ∂μ, Continuous (fun s => C s ω)) ∧
        (∀ U : NNReal, ∀ᵐ ω ∂μ,
          TendstoUniformly (fun m (s : Icc (0 : NNReal) U) =>
            R01522 B (H01522 T X n α l j (φ m)) (t01522 T (φ m)) s.val ω)
            (fun s => C s.val ω) atTop) ∧
        (∀ m (U ε : NNReal),
          (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) U,
            (ε : ℝ) < |R01522 B (H01522 T X n α l j m) (t01522 T m) s ω-C s ω|} ≤ edist (Y m) Z) ∧
        (∀ (U ε : NNReal), 0 < ε →
          Tendsto (fun m => μ {ω | ∃ s ∈ Icc (0 : NNReal) U,
            (ε : ℝ) < |R01522 B (H01522 T X n α l j m) (t01522 T m) s ω-C s ω|}) atTop (𝓝 0)) ∧
        Martingale (fun s : Icc (0 : ℝ) T => fun ω =>
          (C ⟨s.val, s.property.1⟩ ω)^2-
            ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) (filt0152 F T) μ ∧
        (∀ᵐ ω ∂μ,
          Continuous (fun s : Icc (0 : ℝ) T =>
            ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) ∧
          Monotone (fun s : Icc (0 : ℝ) T =>
            ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2)) ∧
        (∀ᵐ ω ∂μ, C 0 ω = 0 ∧ ∀ s : NNReal, T ≤ s → C s ω = Z ω) ∧
        (∀ D : NNReal → Ω → ℝ,
          (∀ᵐ ω ∂μ, Continuous (fun s => D s ω)) →
          (∀ s, D s =ᵐ[μ] μ[(Z : Ω → ℝ) | F (s : ℝ)]) →
          ∀ᵐ ω ∂μ, ∀ s, C s ω = D s ω))

/-- Conditional orthogonality of the actual stopped integrals for independent
Brownian coordinates. Joint future-increment independence from the full filtration
and independence of the two increments are explicit Brownian conditions. The
coefficients can depend on both coordinates and all other information. No integral
orthogonality, product-martingale or stochastic-integral convergence premise is used. -/
def stoppedBrownianOrthogonalityStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    IsProbabilityMeasure μ → ∀ (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ),
    (∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s)) →
    (∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) →
    (∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) → (∀ j, 0 ≤ l j) →
    ∀ (B C : NNReal → Ω → ℝ), IsBrownianReal B μ → IsBrownianReal C μ →
    (∀ s : NNReal, Measurable[F (s : ℝ)] (B s)) →
    (∀ s : NNReal, Measurable[F (s : ℝ)] (C s)) →
    (∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => (B b ω-B a ω, C b ω-C a ω)) inferInstance) μ) →
    (∀ a b : NNReal, a ≤ b → IndepFun (fun ω => B b ω-B a ω) (fun ω => C b ω-C a ω) μ) →
    ∀ n i j,
    ∃ (Y₁ Y₂ : ℕ → Lp ℝ 2 μ) (Z W : Lp ℝ 2 μ) (U V : NNReal → Ω → ℝ),
      (∀ m, (Y₁ m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l i m) (t01522 T m)) ∧
      (∀ m, (Y₂ m : Ω → ℝ) =ᵐ[μ] S01522 C (H01522 T X n α l j m) (t01522 T m)) ∧
      Tendsto Y₁ atTop (𝓝 Z) ∧ Tendsto Y₂ atTop (𝓝 W) ∧
      Martingale U (F01522 F) μ ∧ Martingale V (F01522 F) μ ∧
      (∀ s, U s =ᵐ[μ] μ[(Z : Ω → ℝ) | F (s : ℝ)]) ∧
      (∀ s, V s =ᵐ[μ] μ[(W : Ω → ℝ) | F (s : ℝ)]) ∧
      (∀ᵐ ω ∂μ, Continuous (fun s => U s ω) ∧ Continuous (fun s => V s ω)) ∧
      Martingale (fun s ω => U s ω*V s ω) (F01522 F) μ ∧
      (∀ s, Integrable (fun ω => (Z ω-U s ω)*(W ω-V s ω)) μ ∧
        μ[fun ω => (Z ω-U s ω)*(W ω-V s ω) | F (s : ℝ)] =ᵐ[μ] 0)

def statement : Prop := supportStatement ∧ covarianceStatement ∧ productStatement ∧
  momentStatement ∧ atomStatement ∧ laplaceStatement ∧ independenceStatement ∧
  conditionalLaplaceStatement ∧ poissonStatement ∧ scalarTransitionStatement ∧
  scalarConditionalStatement ∧ scalarMomentStatement ∧ vectorTransitionStatement ∧
  vectorConditionalStatement ∧ vectorImageStatement ∧ tableStatement ∧ boundaryStatement ∧
  meetingVarianceStatement ∧ analyticStatement ∧ localizedTransitionStatement ∧
  localizedMeetingVarianceStatement ∧ localizedStateMomentStatement ∧
  localizedIntegrationStatement ∧ integrationAssemblyStatement ∧
  kernelRegularityStatement ∧ regularIntegrationAssemblyStatement ∧
  sourceCoefficientStatement ∧ sourceIntegrationAssemblyStatement ∧
  localizerConstructionStatement ∧ localizedIntegrandBoundStatement ∧
  stoppedIntegrandIntegrabilityStatement ∧ stoppedIntegrandPredictabilityStatement ∧
  elementaryBrownianIntegralStatement ∧ elementaryBrownianProcessStatement ∧
  elementaryBrownianLimitStatement ∧ stoppedIntegrandApproximationStatement ∧
  elementaryBrownianComparisonStatement ∧ elementaryBrownianCauchyStatement ∧
  stoppedBrownianLimitStatement ∧ stoppedBrownianOrthogonalityStatement
end Standalone.ZeroMeanReversionVarianceSupport

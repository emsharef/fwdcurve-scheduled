import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.CondVar
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Order.LeftRightLim

/-! # Claim 017: compounded-rate futures and ideal European calls

The finite Gaussian model and coordinate filtration are stated explicitly and
identified with Claim 011 in the proof. `G` is the positive version whose equality
to the conditional expectation of the actual accrual is proved. No Gaussian-law,
pricing-formula or identification premise is assumed.
-/
open MeasureTheory ProbabilityTheory
namespace Standalone.CompoundedFuturesIdentification
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
noncomputable def w (a b T : ℝ) : ℝ := max (b-T) 0 - max (a-T) 0
noncomputable def d (a b T : ℝ) : ℝ := ((max (b-T) 0)^2 - (max (a-T) 0)^2)/2
noncomputable def h (a b T : ℝ) : ℝ := d a b T + (w a b T)^2/2
noncomputable def j (S a b T : ℝ) : ℝ := if T ≤ S then w a b T * (S-T) else 0
noncomputable def k (S a b T : ℝ) : ℝ := if T ≤ S then (w a b T)^2 else 0
noncomputable def p {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (a b : ℝ) : ℝ :=
  ∑ i, h a b (τ (i.val+1)) * v i
noncomputable def z {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b : ℝ) : ℝ :=
  ∑ i, j S a b (τ (i.val+1)) * v i
noncomputable def q {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b : ℝ) : NNReal :=
  ∑ i, if τ (i.val+1) ≤ S then v i * ((w a b (τ (i.val+1)))^2).toNNReal else 0
noncomputable def m {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b : ℝ) : ℝ :=
  Real.exp (p τ v a b - z τ v S a b)
noncomputable def L0175 {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t a b : ℝ) (ω : Ω N) : ℝ :=
  p τ v a b - (q τ v t a b : ℝ)/2 + ∑ i, if τ (i.val+1) ≤ t then w a b (τ (i.val+1))*ω i else 0
noncomputable def G {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t a b : ℝ) (ω : Ω N) : ℝ :=
  Real.exp (L0175 τ v t a b ω)
noncomputable def F {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t a b : ℝ) (ω : Ω N) : ℝ :=
  (G τ v t a b ω - 1)/(b-a)
noncomputable def C {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b K : ℝ) : ℝ :=
  ∫ ω, Real.exp (-logB τ v S ω) * max (G τ v S a b ω-K) 0 ∂Q v
noncomputable def QS {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (S : ℝ) : Measure (Ω N) :=
  (Q v).withDensity (fun ω => ENNReal.ofReal (Real.exp (-logB τ v S ω)))
noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

noncomputable def C0177 (m : ℝ) (q : NNReal) (K : ℝ) : ℝ :=
  ∫ x, max (Real.exp x-K) 0 ∂gaussianReal (Real.log m - (q : ℝ)/2) q
noncomputable def q0178 (m price : ℝ) : ℝ :=
  4 * (Function.invFun Φ ((1+price/m)/2))^2

noncomputable def M0179 {N L : ℕ} (τ : ℕ → ℝ) (S a b : Fin L → ℝ) :
    Matrix (Fin L × Fin 3) (Fin N) ℝ :=
  fun row i => ![h (a row.1) (b row.1) (τ (i.val+1)),
    j (S row.1) (a row.1) (b row.1) (τ (i.val+1)),
    k (S row.1) (a row.1) (b row.1) (τ (i.val+1))] row.2

noncomputable def H0179 {N : ℕ} (τ : ℕ → ℝ) (b : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun row i => h (τ (row.val+1)) (b row) (τ (i.val+1))
noncomputable def v0179 {N : ℕ} (δ : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  (x i - if hi : i.val = 0 then 0 else x ⟨i.val-1, by omega⟩)/δ^2
noncomputable def v01710 (ε : NNReal) : Fin 3 → NNReal := ![2*ε, 3*ε, 2*ε]
noncomputable def v01710' (ε : NNReal) : Fin 3 → NNReal := ![3*ε, ε, 3*ε]
noncomputable def f {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  ∑ i, if τ (i.val+1) ≤ t then ω i+(v i : ℝ)*(U-τ (i.val+1)) else 0
noncomputable def P {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (t U : ℝ) (ω : Ω N) : ℝ :=
  Real.exp (-(∫ u in t..U, f τ v t u ω))

/-- Actual accrual, conditional futures and discounted call law in the finite model. -/
def modelStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    ∀ a b : ℝ, 0 ≤ a → a < b →
      (∀ ω, (∫ u in a..b, r τ v u ω) =
        ∑ i, (w a b (τ (i.val+1))*ω i + d a b (τ (i.val+1))*(v i : ℝ))) ∧
      Integrable (fun ω => Real.exp (∫ u in a..b, r τ v u ω)) (Q v) ∧
      (∀ t, (Q v)[fun ω => Real.exp (∫ u in a..b, r τ v u ω) | filt τ t] =ᵐ[Q v] G τ v t a b) ∧
      Martingale (fun t => G τ v t a b) (filt τ) (Q v) ∧
      (∀ t ω, G τ v t a b ω = Real.exp
        ((∑ i, if τ (i.val+1) ≤ t then w a b (τ (i.val+1))*ω i else 0) +
        (∑ i, d a b (τ (i.val+1))*(v i : ℝ)) +
        (∑ i, if τ (i.val+1) ≤ t then 0 else (w a b (τ (i.val+1)))^2*(v i : ℝ))/2)) ∧
      (∀ ω, G τ v 0 a b ω = Real.exp (p τ v a b)) ∧
      (∀ S, 0 ≤ S →
        (QS τ v S) Set.univ = 1 ∧
        HasLaw (fun ω => Real.log (G τ v S a b ω))
          (gaussianReal (Real.log (m τ v S a b)-(q τ v S a b : ℝ)/2) (q τ v S a b)) (QS τ v S) ∧
        (∀ K, Integrable (fun ω => Real.exp (-logB τ v S ω) * max (G τ v S a b ω-K) 0) (Q v)) ∧
        (∀ K, C τ v S a b K = C0177 (m τ v S a b) (q τ v S a b) K) ∧
        (S ≤ b → 1 ≤ m τ v S a b) ∧
        (∀ v' : Fin N → NNReal,
          ((∀ K, 0 < K → C τ v S a b K = C τ v' S a b K) ↔
            m τ v S a b = m τ v' S a b ∧ q τ v S a b = q τ v' S a b)))

/-- The call integral, including the zero-variance boundary and recovery from a surface. -/
def callStatement : Prop :=
  ∀ M : ℝ, 0 < M →
    (∀ K, C0177 M 0 K = max (M-K) 0) ∧
    (∀ (R : NNReal) (K : ℝ), 0 < R → 0 < K →
      C0177 M R K = M * Φ ((Real.log (M/K)+(R : ℝ)/2)/Real.sqrt R) -
        K * Φ (((Real.log (M/K)+(R : ℝ)/2)/Real.sqrt R)-Real.sqrt R)) ∧
    (∀ R : NNReal, C0177 M R M / M = 2*Φ (Real.sqrt R/2)-1) ∧
    (∀ R : NNReal, Filter.Tendsto (C0177 M R) (nhdsWithin 0 (Set.Ioi 0)) (nhds M)) ∧
    (∀ R : NNReal, q0178 M (C0177 M R M) = (R : ℝ)) ∧
    (∀ (M' : ℝ) (R R' : NNReal), 0 < M' →
      ((∀ K, 0 < K → C0177 M R K = C0177 M' R' K) ↔ M = M' ∧ R = R'))

/-- The exact matrix equations and their global and interior injectivity consequences. -/
def linearStatement : Prop :=
  (∀ (N L : ℕ) (τ : ℕ → ℝ) (S a b : Fin L → ℝ), τ 0 = 0 →
    StrictMonoOn τ (Set.Iic N) → (∀ l, 0 ≤ S l) →
    ∀ (v v' : Fin N → NNReal) (ω : Ω N),
      ((∀ l, G τ v 0 (a l) (b l) ω = G τ v' 0 (a l) (b l) ω ∧
        ∀ K, 0 < K → C τ v (S l) (a l) (b l) K = C τ v' (S l) (a l) (b l) K) ↔
      Matrix.mulVec (M0179 τ S a b) (fun i => (v i : ℝ)) =
        Matrix.mulVec (M0179 τ S a b) (fun i => (v' i : ℝ)))) ∧
  (∀ (N : ℕ) (J : Type) [Fintype J] (A : Matrix J (Fin N) ℝ),
    (Function.Injective (fun x : Fin N → NNReal => A.mulVec (fun i => (x i : ℝ))) ↔ A.rank = N) ∧
    (A.rank ≠ N → ∀ x : Fin N → NNReal, (∀ i, 0 < x i) →
      ∃ y : Fin N → NNReal, (∀ i, 0 < y i) ∧ y ≠ x ∧
        A.mulVec (fun i => (y i : ℝ)) = A.mulVec (fun i => (x i : ℝ))))

/-- The two constructive collections in (b), with their stated recovery formulas. -/
def recoveryStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
  (∀ a b : ℝ, a < b → ∀ ω, Real.log (1+(b-a)*F τ v 0 a b ω) = p τ v a b) ∧
  (∀ (S : Fin N → ℝ), (∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2))) →
    ∀ a b : ℝ, τ N ≤ a → a < b →
      (∀ i, (q τ v (S i) a b : ℝ) = (b-a)^2 * ∑ j, if j ≤ i then (v j : ℝ) else 0) ∧
      (∀ i, v0179 (b-a) (fun j => (q τ v (S j) a b : ℝ)) i = (v i : ℝ)) ∧
      (∀ v' : Fin N → NNReal, (∀ i K, 0 < K → C τ v (S i) a b K = C τ v' (S i) a b K) → v = v')) ∧
  (∀ (b : Fin N → ℝ), (∀ i, τ (i.val+1) < b i ∧ (i.val+1 < N → b i < τ (i.val+2))) →
    (∀ i j, H0179 τ b i j = if j ≤ i then (b i-τ (i.val+1))*(b i-τ (j.val+1)) else 0) ∧
    (∀ i, (v i : ℝ) = (p τ v (τ (i.val+1)) (b i) -
      (b i-τ (i.val+1)) * ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i),
        (b i-τ (j.val+1))*(v j : ℝ)) / (b i-τ (i.val+1))^2) ∧
    (∀ (v' : Fin N → NNReal) (ω : Ω N),
      (∀ i, F τ v 0 (τ (i.val+1)) (b i) ω = F τ v' 0 (τ (i.val+1)) (b i) ω) → v = v'))

/-- The explicit pair in (c), including the common initial bond curve. -/
def exampleStatement : Prop :=
  ∀ ε : NNReal, 0 < ε →
    (∀ i, 0 < v01710 ε i ∧ 0 < v01710' ε i) ∧ v01710 ε ≠ v01710' ε ∧
    (∀ (v : Fin 3 → NNReal) (U : ℝ) (ω : Ω 3), P (fun n : ℕ => (n : ℝ)) v 0 U ω = 1) ∧
    (∀ a b : ℝ, 3 ≤ a → a < b → ∀ ω,
      F (fun n : ℕ => (n : ℝ)) (v01710 ε) 0 a b ω = F (fun n : ℕ => (n : ℝ)) (v01710' ε) 0 a b ω) ∧
    (∀ S a b K : ℝ, 3 ≤ S → S ≤ a → a < b →
      C (fun n : ℕ => (n : ℝ)) (v01710 ε) S a b K = C (fun n : ℕ => (n : ℝ)) (v01710' ε) S a b K)

/-- Global two-fixed-strike identification, including zero variance, and its panel equations. -/
def finiteStrikeStatement : Prop :=
  (∀ (M M' K : ℝ) (R R' : NNReal), 1 ≤ M → 1 ≤ M' → 1 < K →
    ((C0177 M R 1 = C0177 M' R' 1 ∧ C0177 M R K = C0177 M' R' K) ↔ M = M' ∧ R = R')) ∧
  (∀ (N L : ℕ) (τ : ℕ → ℝ) (S a b K : Fin L → ℝ), τ 0 = 0 →
    StrictMonoOn τ (Set.Iic N) → (∀ l, 0 ≤ S l) → (∀ l, a l ≤ b l) →
    (∀ l, S l ≤ b l) → (∀ l, 1 < K l) →
    ∀ (v v' : Fin N → NNReal) (ω : Ω N),
      ((∀ l, G τ v 0 (a l) (b l) ω = G τ v' 0 (a l) (b l) ω ∧
        C τ v (S l) (a l) (b l) 1 = C τ v' (S l) (a l) (b l) 1 ∧
        C τ v (S l) (a l) (b l) (K l) = C τ v' (S l) (a l) (b l) (K l)) ↔
      Matrix.mulVec (M0179 τ S a b) (fun i => (v i : ℝ)) =
        Matrix.mulVec (M0179 τ S a b) (fun i => (v' i : ℝ))))

/-- Completion of the ambient measure and reveal filtration preserves valuation. -/
def completionStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Set.Iic N) →
    ∀ a b : ℝ, 0 ≤ a → a < b →
    (∀ t, (Qc v)[fun ω => Real.exp (∫ u in a..b, r τ v u ω) | completedFilt τ v t] =ᵐ[Qc v]
      (fun ω : Ωc v => G τ v t a b ω)) ∧
    Martingale (fun t (ω : Ωc v) => G τ v t a b ω) (completedFilt τ v) (Qc v) ∧
    (∀ S K : ℝ, 0 ≤ S →
      (∫ ω, Real.exp (-logB τ v S ω)*max (G τ v S a b ω-K) 0 ∂Qc v) = C τ v S a b K)

/-- The inverse argument and conversion to rate units. -/
def unitsStatement : Prop :=
  (∀ (M : ℝ) (R : NNReal), 0 < M → (1+C0177 M R M/M)/2 ∈ Set.Ico (1/2 : ℝ) 1) ∧
  (∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal) (S a b K : ℝ), a < b →
    (∀ ω, max (F τ v S a b ω-(K-1)/(b-a)) 0 = max (G τ v S a b ω-K) 0/(b-a)) ∧
    (∫ ω, Real.exp (-logB τ v S ω)*max (F τ v S a b ω-(K-1)/(b-a)) 0 ∂Q v) = C τ v S a b K/(b-a))

/-- The identified parameters are the actual short-rate meeting variances. -/
def eventStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), StrictMonoOn τ (Set.Iic N) →
    (∀ i ω, Δr τ v i ω = ω i) ∧
    (∀ i, Var[Δr τ v i; Q v] = (v i : ℝ)) ∧
    (∀ i t, t < τ (i.val+1) → Var[Δr τ v i; Q v | filt τ t] =ᵐ[Q v] fun _ => (v i : ℝ)) ∧
    (∀ i, HasLaw (fun ω : Ω N => ω i) (gaussianReal 0 (v i)) (Q v)) ∧
    iIndepFun (fun i (ω : Ω N) => ω i) (Q v)

def statement : Prop := modelStatement ∧ callStatement ∧ linearStatement ∧ recoveryStatement ∧
  exampleStatement ∧ finiteStrikeStatement ∧ completionStatement ∧ unitsStatement ∧ eventStatement
end Standalone.CompoundedFuturesIdentification

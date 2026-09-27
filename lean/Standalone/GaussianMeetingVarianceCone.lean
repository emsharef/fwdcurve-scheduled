import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Claim 012: deterministic conclusions conditional on the variance formula

No stochastic integral or short-rate process is postulated here. The integral-to-matrix
theorem is explicitly conditional on the deterministic variance representation (12.3).
The matrix results and the one-factor determinant are unconditional deterministic results.
Rows `n : Fin m` have absolute meeting number `k₀ + n.val + 1`; a time piece `k`
therefore uses the ordinal loading `γ (k₀ + n.val + 1 - k)`.
-/

open MeasureTheory Matrix

namespace Standalone.GaussianMeetingVarianceCone

noncomputable def H (lam T a b : ℝ) : ℝ :=
  if lam = 0 then b - a else
    (Real.exp (-2 * lam * (T - b)) - Real.exp (-2 * lam * (T - a))) / (2 * lam)

noncomputable def A {m d : ℕ} (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ)
    (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ) : Matrix (Fin m) (Fin d) ℝ := fun n j =>
  ∑ k ∈ Finset.Ico k₀ (k₀ + n.val + 1), γ (k₀ + n.val + 1 - k) j ^ 2 *
    H (lam j) (τ (k₀ + n.val + 1)) (max t (τ k)) (τ (k + 1))

noncomputable def cone {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) : Set (ι → ℝ) :=
  {V | ∃ q : κ → ℝ, (∀ j, 0 ≤ q j) ∧ M.mulVec q = V}

noncomputable def A0126 {m d K : ℕ} (t : ℝ) (T : Fin m → ℝ) (b : ℕ → ℝ)
    (g : Fin m → Fin d → ℝ → ℝ) : Matrix (Fin m) (Fin d × Fin K) ℝ := fun n p =>
  ∫ s in Set.Ioc t (T n) ∩ Set.Ioc (b p.2.val) (b (p.2.val + 1)), g n p.1 s

noncomputable def A0127 {N : ℕ} (τ γ : ℕ → ℝ) (lam : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun n k => if k ≤ n then γ (n.val + 1 - k.val) ^ 2 *
    H lam (τ (n.val + 1)) (τ k.val) (τ (k.val + 1)) else 0

noncomputable def integral0127 {N : ℕ} (τ γ : ℕ → ℝ) (lam : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun n k => ∫ s in Set.Ioc (τ 0) (τ (n.val + 1)) ∩ Set.Ioc (τ k.val) (τ (k.val + 1)),
    γ (n.val + 1 - k.val) ^ 2 * Real.exp (-2 * lam * (τ (n.val + 1) - s))

/-- Conditional deterministic formulation of (12.3) leading to (12.4)–(12.5).
`g` is the variance integrand, with the required ordinal index on every scheduled piece. -/
def integralStatement : Prop :=
  ∀ (m d k₀ : ℕ) (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ)
    (t : ℝ) (q : Fin d → ℝ) (g : Fin m → Fin d → ℝ → ℝ) (V : Fin m → ℝ),
    StrictMonoOn τ (Set.Iic (k₀ + m)) → τ k₀ ≤ t → t ≤ τ (k₀ + 1) →
    (∀ n j k, k ∈ Finset.Ico k₀ (k₀ + n.val + 1) →
      ∀ s ∈ Set.Ioo (max t (τ k)) (τ (k + 1)),
        g n j s = (q j * γ (k₀ + n.val + 1 - k) j ^ 2) *
          Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s))) →
    (∀ n, V n = ∑ j, ∫ s in t..τ (k₀ + n.val + 1), g n j s) →
    V = (A τ γ lam t k₀).mulVec q

/-- The `d K` columns for piecewise constant squared scales in (12.6).
`g n j` is the unscaled deterministic kernel in (12.3). -/
def partitionStatement : Prop :=
  ∀ (m d K : ℕ) (t : ℝ) (T : Fin m → ℝ) (b : ℕ → ℝ)
    (g : Fin m → Fin d → ℝ → ℝ) (q : Fin d × Fin K → ℝ) (V : Fin m → ℝ),
    (∀ n, t ≤ T n) → (∀ n j, IntegrableOn (g n j) (Set.Ioc t (T n))) →
    (∀ n, V n = ∑ j, ∫ s in t..T n,
      ∑ l : Fin K, q (j, l) * (Set.Ioc (b l.val) (b (l.val + 1))).indicator (g n j) s) →
    V = (A0126 t T b g).mulVec q ∧ (A0126 (K := K) t T b g).rank ≤ d * K

def statement : Prop :=
  integralStatement ∧ partitionStatement ∧
  (∀ lam T a b, ∫ s in a..b, Real.exp (-2 * lam * (T - s)) = H lam T a b) ∧
  (∀ (m d : ℕ) (M : Matrix (Fin m) (Fin d) ℝ),
    Set.range (fun a : Fin d → NNReal => M.mulVec (fun j => (a j : ℝ) ^ 2)) = cone M ∧
    (∀ w, (∀ V ∈ cone M, dotProduct w V = 0) ↔ M.transpose.mulVec w = 0) ∧
    (∀ V, (∀ w, M.transpose.mulVec w = 0 → dotProduct w V = 0) ↔
      V ∈ LinearMap.range M.mulVecLin) ∧
    M.rank ≤ d ∧
    m - d ≤ Module.finrank ℝ (LinearMap.ker M.transpose.mulVecLin)) ∧
  (∀ (N : ℕ) (τ γ : ℕ → ℝ) (lam : ℝ), StrictMonoOn τ (Set.Iic N) → γ 1 ≠ 0 →
    integral0127 (N := N) τ γ lam = A0127 τ γ lam ∧
    (A0127 (N := N) τ γ lam).det =
      ∏ n : Fin N, γ 1 ^ 2 * H lam (τ (n.val + 1)) (τ n.val) (τ (n.val + 1)) ∧
    0 < (A0127 (N := N) τ γ lam).det ∧
    (interior (cone (A0127 (N := N) τ γ lam))).Nonempty ∧
    (∀ w, (∀ V ∈ cone (A0127 (N := N) τ γ lam), dotProduct w V = 0) → w = 0))

end Standalone.GaussianMeetingVarianceCone

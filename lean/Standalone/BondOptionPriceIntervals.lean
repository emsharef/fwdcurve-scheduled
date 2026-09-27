import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Claim 016: finite cumulative variances with explicit absent upper bounds

Index zero is the fixed cumulative variance zero. Upper bounds use `WithTop ℝ`;
all model coordinates, witnesses, and individual variances are real and finite.
-/
open Set
open scoped Topology
namespace Standalone.BondOptionPriceIntervals

noncomputable def L {N : ℕ} (l : Fin (N+1) → ℝ) (n : Fin (N+1)) : ℝ :=
  (Finset.Iic n).sup' ⟨n, by simp⟩ l

noncomputable def R {N : ℕ} (u : Fin (N+1) → WithTop ℝ) (n : Fin (N+1)) : WithTop ℝ :=
  (Finset.Ici n).inf' ⟨n, by simp⟩ u

def feasible {N : ℕ} (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ)
    (z : Fin (N+1) → ℝ) : Prop :=
  z 0 = 0 ∧ Monotone z ∧ ∀ i, l i ≤ z i ∧ (z i : WithTop ℝ) ≤ u i

def compatible {N : ℕ} (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ) : Prop :=
  ∀ i, (L l i : WithTop ℝ) ≤ R u i

def sequenceStatement : Prop :=
  ∀ (N : ℕ) (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ),
    l 0 = 0 → u 0 = 0 →
    ((∃ z, feasible l u z) ↔ compatible l u) ∧
    (compatible l u → feasible l u (L l)) ∧
    (∀ z, feasible l u z ↔ z 0 = 0 ∧ Monotone z ∧
      ∀ i, L l i ≤ z i ∧ (z i : WithTop ℝ) ≤ R u i)

def projectionStatement : Prop :=
  ∀ (N : ℕ) (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ),
    l 0 = 0 → u 0 = 0 → compatible l u →
    ∀ (n : Fin N) (r : ℝ),
      (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = r) ↔
        0 ≤ r ∧ (L l n.succ : WithTop ℝ) ≤ R u n.castSucc + (r : WithTop ℝ) ∧
        (L l n.castSucc + r : ℝ) ≤ R u n.succ

noncomputable def lower0165 {N : ℕ} (l : Fin (N+1) → ℝ)
    (u : Fin (N+1) → WithTop ℝ) (n : Fin N) : ℝ :=
  if R u n.castSucc = ⊤ then 0 else max 0 (L l n.succ - (R u n.castSucc).untopD 0)

noncomputable def upper0166 {N : ℕ} (l : Fin (N+1) → ℝ)
    (u : Fin (N+1) → WithTop ℝ) (n : Fin N) : WithTop ℝ :=
  R u n.succ + ((-L l n.castSucc : ℝ) : WithTop ℝ)

def endpointStatement : Prop :=
  ∀ (N : ℕ) (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ),
    l 0 = 0 → u 0 = 0 → compatible l u → ∀ n : Fin N,
    (∀ r : ℝ, (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = r) ↔
      lower0165 l u n ≤ r ∧ (r : WithTop ℝ) ≤ upper0166 l u n) ∧
    (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = lower0165 l u n) ∧
    (∀ b : ℝ, upper0166 l u n = b → ∃ z, feasible l u z ∧ z n.succ - z n.castSucc = b) ∧
    (upper0166 l u n = ⊤ → ∀ M : ℝ,
      ∃ z, feasible l u z ∧ M < z n.succ - z n.castSucc)

noncomputable def P0161 (h z : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (h * Real.sqrt z / 2) - 1

noncomputable def y0167 (c : ℝ) : ℝ :=
  Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) ((1+c)/2)

noncomputable def H0162 (h c : ℝ) : ℝ := 4 * (y0167 c)^2 / h^2

noncomputable def φ0167 (y : ℝ) : ℝ := Real.exp (-y^2/2) / Real.sqrt (2*Real.pi)

noncomputable def k0167 (h c : ℝ) : ℝ := 4 * y0167 c / (h^2 * φ0167 (y0167 c))

noncomputable def cumulative0161 {N : ℕ} (v : Fin N → NNReal) (i : Fin (N+1)) : ℝ :=
  ∑ j : Fin N, if j.val < i.val then (v j : ℝ) else 0

noncomputable def l0162 {N : ℕ} (h a : Fin (N+1) → ℝ) (i : Fin (N+1)) : ℝ :=
  H0162 (h i) (a i)

noncomputable def u0162 {N : ℕ} (h b : Fin (N+1) → ℝ) (i : Fin (N+1)) : WithTop ℝ :=
  if b i = 1 then ⊤ else ↑(H0162 (h i) (b i))

def fits0161 {N : ℕ} (h a b : Fin (N+1) → ℝ) (v : Fin N → NNReal) : Prop :=
  ∀ i, a i ≤ P0161 (h i) (cumulative0161 v i) ∧ P0161 (h i) (cumulative0161 v i) ≤ b i

def pricingStatement : Prop :=
  ∀ h : ℝ, 0 < h → H0162 h 0 = 0 ∧ k0167 h 0 = 0 ∧
    (∀ z : ℝ, 0 ≤ z → P0161 h z ∈ Ico (0:ℝ) 1 ∧ H0162 h (P0161 h z) = z) ∧
    (∀ c ∈ Ico (0:ℝ) 1, 0 ≤ H0162 h c ∧ P0161 h (H0162 h c) = c) ∧
    StrictMonoOn (H0162 h) (Ico (0:ℝ) 1) ∧
    (∀ a b z : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → a < 1 → 0 ≤ z →
      (a ≤ P0161 h z ∧ P0161 h z ≤ b ↔ H0162 h a ≤ z ∧ (b < 1 → z ≤ H0162 h b))) ∧
    (∀ c ∈ Ico (0:ℝ) 1, HasDerivAt (H0162 h) (k0167 h c) c) ∧
    (∀ β ∈ Ico (0:ℝ) 1, ∀ a ∈ Icc (0:ℝ) β, ∀ b ∈ Icc (0:ℝ) β,
      |H0162 h b-H0162 h a| ≤ k0167 h β * |b-a|) ∧
    Filter.Tendsto (H0162 h) (𝓝[<] (1:ℝ)) Filter.atTop ∧
    Filter.Tendsto (k0167 h) (𝓝[<] (1:ℝ)) Filter.atTop ∧
    ¬ (∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Ico (0:ℝ) 1, ∀ b ∈ Ico (0:ℝ) 1,
      |H0162 h b-H0162 h a| ≤ K*|b-a|)

def modelStatement : Prop :=
  ∀ (N : ℕ) (h a b : Fin (N+1) → ℝ), (∀ i, 0 < h i) →
    (∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 ∧ a i < 1) → a 0 = 0 → b 0 = 0 →
    ((∃ v : Fin N → NNReal, fits0161 h a b v) ↔ compatible (l0162 h a) (u0162 h b)) ∧
    (compatible (l0162 h a) (u0162 h b) → ∀ (n : Fin N) (r : ℝ),
      (∃ v : Fin N → NNReal, fits0161 h a b v ∧ (v n : ℝ) = r) ↔
        lower0165 (l0162 h a) (u0162 h b) n ≤ r ∧
        (r : WithTop ℝ) ≤ upper0166 (l0162 h a) (u0162 h b) n) ∧
    (∀ z, z 0 = 0 → Monotone z → ∃ v : Fin N → NNReal, cumulative0161 v = z)

def stabilityStatement : Prop :=
  ∀ (N : ℕ) (v w : Fin N → NNReal) (h β ε : Fin (N+1) → ℝ),
    (∀ i, 0 < h i) → (∀ i, β i ∈ Ico (0:ℝ) 1) →
    (∀ i, P0161 (h i) (cumulative0161 v i) ∈ Icc (0:ℝ) (β i)) →
    (∀ i, P0161 (h i) (cumulative0161 w i) ∈ Icc (0:ℝ) (β i)) →
    (∀ i, |P0161 (h i) (cumulative0161 v i)-P0161 (h i) (cumulative0161 w i)| ≤ ε i) →
    ∀ n : Fin N, |(v n : ℝ)-(w n : ℝ)| ≤ k0167 (h n.succ) (β n.succ)*ε n.succ +
      k0167 (h n.castSucc) (β n.castSucc)*ε n.castSucc

def statement : Prop := sequenceStatement ∧ projectionStatement ∧ endpointStatement ∧
  pricingStatement ∧ modelStatement ∧ stabilityStatement
end Standalone.BondOptionPriceIntervals

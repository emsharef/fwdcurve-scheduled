import Standalone.SpliceQuasiExponentialCross
import Mathlib.Analysis.Analytic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Claim 035: blocks and the block `E_1`

A block for Claim 035 (`Block035 c A b E`) is as in Claim 033: a finite-dimensional space `E` of
real-analytic functions on `ℝ`, invariant under the forward shifts `g ↦ g(· + h)`, `h ≥ 0`, which
here contains `λ` and `λΛ` (`SpliceQuasiExponentialCross.lam035`, `Lam035`).

`E1 c A b` is the smallest block containing `λ`, `x λ(x)` and `λΛ`: the infimum of all blocks
that also contain `x λ(x)`.

`e1Statement`: for `A` invertible, `E_1` is a block, it contains `x λ(x)`, and it lies in every
block containing `x λ(x)`. The family of such blocks is not empty: the span of the functions
`φ_i(x) = (e^{Ax} b)_i`, `x φ_i(x)` and `φ_i φ_j` is one, since each of `λ`, `x λ(x)` and `λΛ`
spans a finite-dimensional space of translates.

`blockPartStatement` is (a)'s step for the block part of the drift: in any block `E`, the time
integral `∫_0^t σ^B S^B(u, T) du = ∫_0^t λΛ(T − u) du`, as a function of `x = T − t`, lies in `E`.
A finite-dimensional forward-shift invariant space of continuous functions is closed under
integrals of its translates, since the coordinates of `g(· + h)` in a basis are continuous in `h`.
-/

open Matrix NormedSpace Set
namespace Standalone.SpliceQuasiExponentialBlock
open Standalone.SpliceQuasiExponentialCross

variable {r : ℕ}

/-- A block for Claim 035. -/
structure Block035 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) : Prop where
  finiteDimensional : FiniteDimensional ℝ E
  analytic : ∀ g ∈ E, AnalyticOnNhd ℝ g univ
  shift : ∀ g ∈ E, ∀ h : ℝ, 0 ≤ h → (fun x => g (x + h)) ∈ E
  lam_mem : lam035 c A b ∈ E
  lamLam_mem : (fun x => lam035 c A b x * Lam035 c A b x) ∈ E

/-- `E_1`: the smallest block containing `λ`, `x λ(x)` and `λΛ`. -/
noncomputable def E1 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    Submodule ℝ (ℝ → ℝ) :=
  sInf {E | Block035 c A b E ∧ (fun x => x * lam035 c A b x) ∈ E}

def e1Statement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), IsUnit A.det →
  ∀ (b c : Fin r → ℝ), Block035 c A b (E1 c A b) ∧ (fun x => x * lam035 c A b x) ∈ E1 c A b ∧
    ∀ E : Submodule ℝ (ℝ → ℝ), Block035 c A b E → (fun x => x * lam035 c A b x) ∈ E →
      E1 c A b ≤ E

def blockPartStatement : Prop := ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ)
  (E : Submodule ℝ (ℝ → ℝ)), Block035 c A b E → ∀ t : ℝ, 0 ≤ t →
  (fun x => ∫ u in (0:ℝ)..t, lam035 c A b (x + (t - u)) * Lam035 c A b (x + (t - u))) ∈ E

def statement : Prop := e1Statement ∧ blockPartStatement

end Standalone.SpliceQuasiExponentialBlock

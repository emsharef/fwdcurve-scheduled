import Standalone.SpliceVaryingExponents
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Claim 043: polynomial parts in the uncorrelated splice

The block (43.1) is `F(x, z) = p_0(x) + ∑_i p_i(x) e^{−β_i x}`, with a full polynomial part
`p_0(x) = ∑_{μ ≤ d} z_{0,μ} x^μ` and the exponential components of BEP(K, n), including varying
exponents (Claim 042's `SpliceVaryingExponents`). The parameters are indexed by
`Fin (d + 1) ⊕ (Σ i, Fin (n i + 2))`: `inl μ` is `z_{0,μ}`, and `inr I` is a BEP parameter.

`dF43`, `d2F43` are the parameter derivatives. `F` is linear in `z_0`, so every second derivative
involving `z_0` vanishes. `derivStatement` certifies them. `residual43` is (3). "Alone" means
`R = 0`, "splice" means `R` affine in `x` on `[0, ∞)` (Claim 037(a)). `m = ⌊(d − 1)/2⌋`.

* `sameStatement` is (a): for `d ≥ 1`, `R` is affine for `(a, b)` if and only if `R = 0` for some
  `(a, b')` with `b'` equal to `b` except at `b_{0,0}` and `b_{0,1}`.
* `rowsStatement` is (b): for `d ≥ 1`, positive exponents and `a` nonnegative definite, if `R` is
  affine then `a_{(0,μ),(0,ν)} = 0` unless `μ, ν ≤ m`.
* `attainedStatement` is (c): for a polynomial block (`K = 0`), every `a` supported on
  `{(0,μ),(0,ν) : μ, ν ≤ m}` is admissible alone, so also in the splice, with a suitable `b`.
* `levelStatement` is (d): for `d = 0`, `R = 0` forces `a_{(0,0),(0,0)} = 0`. In the splice, for a
  pure level (`K = 0`), `R` is affine for every `a` and `b`.
-/

open Polynomial Set
namespace Standalone.SplicePolynomialParts
open Standalone.SpliceVaryingExponents

variable {d K : ℕ} {n : Fin K → ℕ}

/-- The parameter index: `inl μ` is `z_{0,μ}`, `inr I` a BEP parameter. -/
abbrev Idx (d K : ℕ) (n : Fin K → ℕ) := Fin (d + 1) ⊕ (Σ i : Fin K, Fin (n i + 2))

/-- `F(x, z) = p_0(x) + ∑_i p_i(x) e^{−β_i x}`. -/
noncomputable def F43 (z : Idx d K n → ℝ) (x : ℝ) : ℝ :=
  ∑ μ : Fin (d + 1), z (Sum.inl μ) * x ^ (μ : ℕ) + FBEP (fun I => z (Sum.inr I)) x

/-- `∂F/∂z_I`. -/
noncomputable def dF43 (z : Idx d K n → ℝ) : Idx d K n → ℝ → ℝ :=
  Sum.elim (fun μ x => x ^ (μ : ℕ)) fun I x => dF (fun J => z (Sum.inr J)) I x

/-- `∂²F/∂z_I ∂z_J`. -/
noncomputable def d2F43 (z : Idx d K n → ℝ) : Idx d K n → Idx d K n → ℝ → ℝ
  | Sum.inr I, Sum.inr J => fun x => d2F (fun L => z (Sum.inr L)) I J x
  | _, _ => fun _ => 0

/-- The difference of the two sides of (3). -/
noncomputable def residual43 (z : Idx d K n → ℝ) (a : Idx d K n → Idx d K n → ℝ)
    (b : Idx d K n → ℝ) (x : ℝ) : ℝ :=
  ∑ I, b I * dF43 z I x + (1 / 2) * ∑ I, ∑ J, a I J * d2F43 z I J x -
    ∑ I, ∑ J, a I J * dF43 z I x * (∫ η in (0:ℝ)..x, dF43 z J η) - deriv (F43 z) x

def derivStatement : Prop := ∀ (d K : ℕ) (n : Fin K → ℕ) (z : Idx d K n → ℝ) (I : Idx d K n)
  (x : ℝ), HasDerivAt (fun w => F43 (Function.update z I w) x) (dF43 z I x) (z I) ∧
  ∀ J : Idx d K n, HasDerivAt (fun w => dF43 (Function.update z J w) I x) (d2F43 z I J x) (z J)

def sameStatement : Prop := ∀ (d K : ℕ) (n : Fin K → ℕ) (hd : 1 ≤ d) (z : Idx d K n → ℝ)
  (a : Idx d K n → Idx d K n → ℝ) (b : Idx d K n → ℝ),
  (∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residual43 z a b x = c₀ + c₁ * x) ↔
    ∃ b' : Idx d K n → ℝ, (∀ I, I ≠ Sum.inl 0 → I ≠ Sum.inl ⟨1, by omega⟩ → b' I = b I) ∧
      ∀ x : ℝ, 0 ≤ x → residual43 z a b' x = 0

def rowsStatement : Prop := ∀ (d K : ℕ) (n : Fin K → ℕ), 1 ≤ d → ∀ (z : Idx d K n → ℝ),
  (∀ i, 0 < expo (fun I => z (Sum.inr I)) i) →
  ∀ (a : Matrix (Idx d K n) (Idx d K n) ℝ) (b : Idx d K n → ℝ), a.PosSemidef →
  (∃ c₀ c₁ : ℝ, ∀ x : ℝ, 0 ≤ x → residual43 z a b x = c₀ + c₁ * x) →
  ∀ μ ν : Fin (d + 1), ((d - 1) / 2 < (μ : ℕ) ∨ (d - 1) / 2 < (ν : ℕ)) →
    a (Sum.inl μ) (Sum.inl ν) = 0

def attainedStatement : Prop := ∀ (d : ℕ) (n : Fin 0 → ℕ), 1 ≤ d → ∀ (z : Idx d 0 n → ℝ)
  (a : Idx d 0 n → Idx d 0 n → ℝ),
  (∀ μ ν : Fin (d + 1), ((d - 1) / 2 < (μ : ℕ) ∨ (d - 1) / 2 < (ν : ℕ)) →
    a (Sum.inl μ) (Sum.inl ν) = 0) →
  ∃ b : Idx d 0 n → ℝ, ∀ x : ℝ, residual43 z a b x = 0

def levelStatement : Prop :=
  (∀ (K : ℕ) (n : Fin K → ℕ) (z : Idx 0 K n → ℝ), (∀ i, 0 < expo (fun I => z (Sum.inr I)) i) →
    ∀ (a : Matrix (Idx 0 K n) (Idx 0 K n) ℝ) (b : Idx 0 K n → ℝ),
    (∀ x : ℝ, 0 ≤ x → residual43 z a b x = 0) → a (Sum.inl 0) (Sum.inl 0) = 0) ∧
  (∀ (n : Fin 0 → ℕ) (z : Idx 0 0 n → ℝ) (a : Idx 0 0 n → Idx 0 0 n → ℝ) (b : Idx 0 0 n → ℝ),
    ∃ c₀ c₁ : ℝ, ∀ x : ℝ, residual43 z a b x = c₀ + c₁ * x)

def statement : Prop := derivStatement ∧ sameStatement ∧ rowsStatement ∧ attainedStatement ∧
  levelStatement

end Standalone.SplicePolynomialParts

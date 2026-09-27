import Standalone.SpliceSeveralFactorsAX01
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Data.Matrix.Block

/-! # Claim 041 (b): several block factors with distinct exponents

The block is `F(x, z) = ∑_j c_j e^{A_j x} z_j = C e^{𝒜x} z` (41.2), with `𝒜 = diag(A_1, …, A_J)`
(`Matrix.blockDiagonal' A`, indexed by `Σ j, Fin r_j`) and `C = (c_1, …, c_J)` (`blockC c`).
`Observable A c` means `c e^{Ax} y = 0` for all `x` only for `y = 0`.

* `pbhStatement`: suppose each `(A_j, c_j)` is observable and the complex spectra of the `A_j` are
  pairwise disjoint. Then `(𝒜, C)` is observable. The proof avoids complexification. Each `A_j` is
  annihilated by its characteristic polynomial `p_j`. Disjoint spectra make `p_j` coprime to
  `q_j = ∏_{i≠j} p_i`. The unobservable set is invariant under every polynomial in `𝒜`, and
  `q_j(𝒜)` kills every block but the `j`-th. Bezout then gives `y_j = 0`.
* `reindexStatement`: observability is invariant under reindexing, so (a) applies to the
  block-diagonal model on `Fin (∑ r_j)`.
* `blockwiseStatement` is (b)'s conclusion. Under AX-01 for the reindexed block-diagonal model,
  (41.3) holds block by block: every `z_j`-component of `H^Z G_m^T` vanishes almost everywhere
  before every meeting.
-/

open Matrix NormedSpace MeasureTheory Set
namespace Standalone.SpliceSeveralFactorsBlocks
open Standalone.SpliceSeveralFactorsAX01

/-- `(A, c)` is observable. -/
def Observable {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (c : ι → ℝ) : Prop :=
  ∀ y : ι → ℝ, (∀ x : ℝ, c ⬝ᵥ (exp (x • A) *ᵥ y) = 0) → y = 0

/-- `C = (c_1, …, c_J)`. -/
def blockC {J : ℕ} {r : Fin J → ℕ} (c : (j : Fin J) → Fin (r j) → ℝ) :
    (Σ j, Fin (r j)) → ℝ := fun p => c p.1 p.2

def pbhStatement : Prop := ∀ (J : ℕ) (r : Fin J → ℕ)
  (A : (j : Fin J) → Matrix (Fin (r j)) (Fin (r j)) ℝ) (c : (j : Fin J) → Fin (r j) → ℝ),
  (∀ j, Observable (A j) (c j)) →
  (∀ i j, i ≠ j → Disjoint (spectrum ℂ ((A i).map (algebraMap ℝ ℂ)))
    (spectrum ℂ ((A j).map (algebraMap ℝ ℂ)))) →
  Observable (blockDiagonal' A) (blockC c)

def reindexStatement : Prop := ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℝ) (c : ι → ℝ),
  Observable A c → Observable (reindex e e A) (c ∘ e.symm)

def blockwiseStatement : Prop := ∀ (J : ℕ) (r : Fin J → ℕ)
  (A : (j : Fin J) → Matrix (Fin (r j)) (Fin (r j)) ℝ) (c : (j : Fin J) → Fin (r j) → ℝ),
  (∀ j, Observable (A j) (c j)) →
  (∀ i j, i ≠ j → Disjoint (spectrum ℂ ((A i).map (algebraMap ℝ ℂ)))
    (spectrum ℂ ((A j).map (algebraMap ℝ ℂ)))) →
  ∀ (n : ℕ) (e : (Σ j, Fin (r j)) ≃ Fin n), IsUnit (reindex e e (blockDiagonal' A)).det →
  ∀ (k L : ℕ) (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ) (HZ : ℝ → Fin n → Fin k → ℝ)
    (dL dC : ℕ → ℝ → ℝ) (bZ z : ℝ → Fin n → ℝ) (Tm : Finset ℝ) (H : ℝ),
  PathData041 s HS HZ dL dC bZ z H →
  AX01Path041 s HS HZ dL dC bZ z Tm (blockC c ∘ e.symm) (reindex e e (blockDiagonal' A)) H →
  ∀ τ ∈ Tm, τ < H → ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
    ∀ (j : Fin J) (a : Fin (r j)), W041 s HS HZ Tm τ u (e ⟨j, a⟩) = 0

def statement : Prop := pbhStatement ∧ reindexStatement ∧ blockwiseStatement

end Standalone.SpliceSeveralFactorsBlocks

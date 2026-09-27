import Standalone.GaussianMeetingVarianceCone

/-! # Claim 024: the restrictions on event variances that survive every scale calibration

Started early while the claim was under review and completed after approval. In the deterministic model of
Claim 012 it states: (a) the fixed direction of the kernel on a meeting interval
(`fixedDirectionStatement`): for any measurable scale whose square is integrable against the
exponential weight on the interval, the scaled integral of the kernel is a nonnegative multiple,
independent of the row, of Claim 012's unscaled column `H`, so measurable scales attain nothing
beyond Claim 012's cone; (b) the dual cone (`dualStatement`): for a nonnegative matrix, a linear
inequality holds on the cone if and only if it holds on the generating columns, and a vector lies
in the cone if and only if it satisfies every such inequality, by the separation theorem for
the closed convex cone; and (c) the consecutive-meeting ratio bounds (24.4)
(`ratioBoundStatement`): for Claim 012's matrix with constant ordinal loadings, each row is the
previous row scaled by `e^{−2λ_j Δ_n}` plus a nonnegative diagonal term, so every vector of the
cone satisfies `V_n ≥ e^{−2λ_max Δ_n} V_{n−1}` and `V_{k₀+1} ≥ 0`; the one-factor recursion
(24.3) with its irredundancy (`recursionStatement`): Claim 012's one-factor matrix (12.7) with
nonzero first loading is lower triangular with positive diagonal, every `V` has a unique
preimage `q`, given by the recursion, `V` lies in the cone if and only if that `q` is
nonnegative, the rows of the inverse are linearly independent, and a linear inequality holds
on the cone if and only if its row is a nonnegative combination of the rows of the inverse; the
attainment converse of (c) (`attainmentStatement`): in the one-factor setting with a constant
loading, the rows below the diagonal are the previous row scaled by `e^{−2λ Δ_n}`, and every
`V` with `V_1 ≥ 0` and `V_n ≥ e^{−2λ Δ_n} V_{n−1}` lies in the cone, with the recursion reading
`q_n = (V_n − e^{−2λ Δ_n} V_{n−1})/A_{nn}`; and the diagonal case of (d)
(`diagonalStatement`): with the nearest-meeting loading only, the one-factor matrix is diagonal
with positive entries and every nonnegative vector lies in the cone; and the decay cases of (d)
(`closureStatement`): in the same setting every cone lies in the orthant, the closure of the
union of the cones over all decays is the whole orthant, and with decays bounded by `Λ` the bounds
(24.4) with `Λ` hold on every cone and characterize the cone with decay `Λ`; and the piecewise
cone of (24.2) (`piecewiseConeStatement`): Claim 012's per-factor cone lies in the cone `K(t)`
of the matrix with one column per factor and piece, and with constant ordinal loadings every
vector of `K(t)` satisfies (24.4) with `λ_max`, while every vector satisfying (24.4) lies in
`K(t)` when some factor with a nonzero loading has decay `λ_max`, the multi-factor form of (c);
and (a) assembled (`attainableStatement`): the variance vectors (24.1) of admissible measurable
scales, with the piecewise ordinal index, are exactly the vectors of `K(t)`, every admissible
scale giving a vector of the cone and every vector of the cone being attained by scales constant
on each piece; and (d) on the piecewise cone (`piecewiseClosureStatement`): every `K(t)` lies in
the orthant and the closure of the union over all nonnegative decay vectors is the orthant. With
this every part of the claim is asserted.
-/

open MeasureTheory Matrix
open Standalone.GaussianMeetingVarianceCone

namespace Standalone.SurvivingScaleRestrictions

/-- (a): on an interval `[α, β]`, the kernel `s ↦ e^{−2λ(T − s)}` scaled by any measurable `a²`
integrates to a nonnegative multiple, independent of `T`, of Claim 012's `H λ T α β`. -/
def fixedDirectionStatement : Prop :=
  ∀ (lam α β : ℝ) (a : ℝ → ℝ), α < β → Measurable a →
    IntegrableOn (fun s => a s ^ 2 * Real.exp (2 * lam * s)) (Set.Ioc α β) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T, (∫ s in α..β, a s ^ 2 * Real.exp (-2 * lam * (T - s))) = c * H lam T α β

/-- (b): the dual of a finitely generated cone with nonnegative generators, and Farkas'
lemma for it. -/
def dualStatement : Prop :=
  ∀ (m d : ℕ) (M : Matrix (Fin m) (Fin d) ℝ), (∀ i j, 0 ≤ M i j) →
    (∀ w : Fin m → ℝ, (∀ V ∈ cone M, 0 ≤ dotProduct w V) ↔ ∀ j, 0 ≤ M.transpose.mulVec w j) ∧
    (∀ V : Fin m → ℝ, V ∈ cone M ↔
      ∀ w : Fin m → ℝ, (∀ j, 0 ≤ M.transpose.mulVec w j) → 0 ≤ dotProduct w V) ∧
    (∀ w : Fin m → ℝ, (∀ V ∈ cone M, dotProduct w V = 0) ↔ M.transpose.mulVec w = 0)

/-- (c): with constant ordinal loadings `γ i j = γ' j`, each row of Claim 012's matrix `A` is
the previous row scaled by `e^{−2λ_j Δ_n}` plus a nonnegative diagonal term, and every vector of
the cone satisfies the consecutive-meeting ratio bounds (24.4) with `λ_max`. -/
def ratioBoundStatement : Prop :=
  ∀ (m d k₀ : ℕ) (τ : ℕ → ℝ) (γ' : Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ),
    StrictMonoOn τ (Set.Iic (k₀ + m)) → τ k₀ ≤ t → t ≤ τ (k₀ + 1) → (∀ j, 0 ≤ lam j) →
    let A := A (m := m) τ (fun _ => γ') lam t k₀
    (∀ (n : Fin m) (j : Fin d), 0 ≤ A n j) ∧
    (∀ (n : Fin m) (j : Fin d) (hn : 0 < n.val),
      A n j = Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
        A ⟨n.val - 1, by omega⟩ j +
        γ' j ^ 2 * H (lam j) (τ (k₀ + n.val + 1)) (max t (τ (k₀ + n.val))) (τ (k₀ + n.val + 1))) ∧
    ∀ lamMax : ℝ, (∀ j, lam j ≤ lamMax) →
      ∀ V ∈ cone A, (∀ n : Fin m, 0 ≤ V n) ∧
        ∀ (n : Fin m) (hn : 0 < n.val),
          Real.exp (-2 * lamMax * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
            V ⟨n.val - 1, by omega⟩ ≤ V n

/-- (b), one factor: Claim 012's one-factor matrix (12.7) with `γ 1 ≠ 0` is lower triangular
with positive diagonal; every `V` has a unique preimage `q`, which is the recursion (24.3); `V`
lies in the cone if and only if that `q` is nonnegative; the rows of the inverse are linearly
independent, so the `N` inequalities are irredundant; and a linear inequality `wᵀV ≥ 0` holds on
the cone if and only if `w` is a nonnegative combination of the rows of the inverse. -/
def recursionStatement : Prop :=
  ∀ (N : ℕ) (τ γ : ℕ → ℝ) (lam : ℝ), StrictMonoOn τ (Set.Iic N) → γ 1 ≠ 0 →
    let M := A0127 (N := N) τ γ lam
    (∀ n k : Fin N, n < k → M n k = 0) ∧ (∀ n : Fin N, 0 < M n n) ∧
    (∀ V : Fin N → ℝ, ∃! q : Fin N → ℝ, M.mulVec q = V) ∧
    (∀ V q : Fin N → ℝ, M.mulVec q = V →
      (∀ k : Fin N, q k = (V k - ∑ l ∈ Finset.univ.filter (· < k), M k l * q l) / M k k) ∧
      (V ∈ cone M ↔ ∀ k, 0 ≤ q k)) ∧
    LinearIndependent ℝ M⁻¹.row ∧
    (∀ w : Fin N → ℝ, (∀ V ∈ cone M, 0 ≤ dotProduct w V) ↔
      ∃ c : Fin N → ℝ, (∀ k, 0 ≤ c k) ∧ w = M⁻¹.transpose.mulVec c)

/-- (c), the attainment converse, in the one-factor setting of (12.7) with the constant loading
`γ'`: below the diagonal each row is the previous row scaled by `e^{−2λ Δ_n}`, and every `V` with
`V_1 ≥ 0` and `V_n ≥ e^{−2λ Δ_n} V_{n−1}` lies in the cone, the recursion (24.3) reading
`q_1 = V_1/A_{11}` and `q_n = (V_n − e^{−2λ Δ_n} V_{n−1})/A_{nn}`. -/
def attainmentStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (γ' lam : ℝ), StrictMonoOn τ (Set.Iic N) → γ' ≠ 0 →
    let M := A0127 (N := N) τ (fun _ => γ') lam
    (∀ (n k : Fin N), k < n →
      M n k = Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) * M ⟨n.val - 1, by omega⟩ k) ∧
    ∀ V : Fin N → ℝ, (∀ n : Fin N, n.val = 0 → 0 ≤ V n) →
      (∀ (n : Fin N), 0 < n.val →
        Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) * V ⟨n.val - 1, by omega⟩ ≤ V n) →
      V ∈ cone M ∧
      ∀ q : Fin N → ℝ, M.mulVec q = V →
        (∀ n : Fin N, n.val = 0 → q n = V n / M n n) ∧
        ∀ (n : Fin N), 0 < n.val →
          q n = (V n - Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) *
            V ⟨n.val - 1, by omega⟩) / M n n

/-- (d), the diagonal case: with the nearest-meeting loading only, `γ 1 ≠ 0` and `γ i = 0` for
`i ≥ 2`, the one-factor matrix is diagonal with positive entries and every nonnegative vector
lies in the cone. -/
def diagonalStatement : Prop :=
  ∀ (N : ℕ) (τ γ : ℕ → ℝ) (lam : ℝ), StrictMonoOn τ (Set.Iic N) → γ 1 ≠ 0 →
    (∀ i, 2 ≤ i → γ i = 0) →
    let M := A0127 (N := N) τ γ lam
    (∀ n k : Fin N, n ≠ k → M n k = 0) ∧ (∀ n : Fin N, 0 < M n n) ∧
    ∀ V : Fin N → ℝ, (∀ n, 0 ≤ V n) → V ∈ cone M

/-- The nonnegative orthant, the only restriction surviving unbounded decays. -/
def orthant (N : ℕ) : Set (Fin N → ℝ) := {V | ∀ n, 0 ≤ V n}

/-- (d), the decay cases, in the one-factor setting of (12.7) with a constant loading: every
cone lies in the orthant; the closure of the union of the cones over all decays `λ ≥ 0` is the
whole orthant, so nothing beyond `V ≥ 0` survives unbounded decays; and with the decays bounded
by `Λ`, every vector of every cone with `0 ≤ λ ≤ Λ` satisfies (24.4) with `Λ` in place of
`λ_max`, and every vector satisfying (24.4) with `Λ` lies in the cone with decay `Λ`. -/
def closureStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (γ' : ℝ), StrictMonoOn τ (Set.Iic N) → γ' ≠ 0 →
    (∀ lam : ℝ, cone (A0127 (N := N) τ (fun _ => γ') lam) ⊆ orthant N) ∧
    closure (⋃ lam ∈ Set.Ici (0 : ℝ), cone (A0127 (N := N) τ (fun _ => γ') lam)) = orthant N ∧
    ∀ Λ : ℝ, 0 ≤ Λ →
      (∀ lam, 0 ≤ lam → lam ≤ Λ → ∀ V ∈ cone (A0127 (N := N) τ (fun _ => γ') lam),
        (∀ n : Fin N, n.val = 0 → 0 ≤ V n) ∧
        ∀ (n : Fin N), 0 < n.val →
          Real.exp (-2 * Λ * (τ (n.val + 1) - τ n.val)) * V ⟨n.val - 1, by omega⟩ ≤ V n) ∧
      (∀ V : Fin N → ℝ, (∀ n : Fin N, n.val = 0 → 0 ≤ V n) →
        (∀ (n : Fin N), 0 < n.val →
          Real.exp (-2 * Λ * (τ (n.val + 1) - τ n.val)) * V ⟨n.val - 1, by omega⟩ ≤ V n) →
        V ∈ cone (A0127 (N := N) τ (fun _ => γ') Λ))

/-- The matrix (24.2) with one column per factor and time piece: column `(j, k)` is factor `j`'s
unscaled kernel over the piece `(max t τ_{k₀+k}, τ_{k₀+k+1}]`, on the rows `n` whose meeting
`τ_{k₀+n+1}` lies after the piece, with the ordinal loading `γ_{n+1−k, j}`. Claim 012's matrix
`A` sums these columns over `k`. -/
noncomputable def Apw {m d : ℕ} (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ)
    (k₀ : ℕ) : Matrix (Fin m) (Fin d × Fin m) ℝ := fun n p =>
  if p.2 ≤ n then γ (n.val + 1 - p.2.val) p.1 ^ 2 *
    H (lam p.1) (τ (k₀ + n.val + 1)) (max t (τ (k₀ + p.2.val))) (τ (k₀ + p.2.val + 1)) else 0

/-- (a)–(c) on the piecewise cone `K(t) = {A(t) q : q ≥ 0}` of (24.2): Claim 012's per-factor
matrix applied to `q` is the piecewise matrix applied to the scales constant in the piece, so
Claim 012's cone lies in `K(t)`; and with constant ordinal loadings and decays bounded by
`λ_max`, every vector of `K(t)` satisfies the ratio bounds (24.4), and, when some factor with a
nonzero loading has decay `λ_max`, every vector satisfying (24.4) lies in `K(t)`, already by the
scales of that factor. -/
def piecewiseConeStatement : Prop :=
  ∀ (m d k₀ : ℕ) (τ : ℕ → ℝ) (lam : Fin d → ℝ) (t : ℝ),
    StrictMonoOn τ (Set.Iic (k₀ + m)) → τ k₀ ≤ t → t < τ (k₀ + 1) → (∀ j, 0 ≤ lam j) →
    (∀ (γ : ℕ → Fin d → ℝ) (q : Fin d → ℝ),
      (A (m := m) τ γ lam t k₀).mulVec q = (Apw (m := m) τ γ lam t k₀).mulVec (fun p => q p.1)) ∧
    (∀ γ : ℕ → Fin d → ℝ, cone (A (m := m) τ γ lam t k₀) ⊆ cone (Apw (m := m) τ γ lam t k₀)) ∧
    ∀ (γ' : Fin d → ℝ) (lamMax : ℝ), (∀ j, lam j ≤ lamMax) →
      let B := Apw (m := m) τ (fun _ => γ') lam t k₀
      (∀ V ∈ cone B, (∀ n : Fin m, 0 ≤ V n) ∧
        ∀ (n : Fin m), 0 < n.val →
          Real.exp (-2 * lamMax * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
            V ⟨n.val - 1, by omega⟩ ≤ V n) ∧
      ((∃ j, lam j = lamMax ∧ γ' j ≠ 0) →
        ∀ V : Fin m → ℝ, (∀ n : Fin m, n.val = 0 → 0 ≤ V n) →
          (∀ (n : Fin m), 0 < n.val →
            Real.exp (-2 * lamMax * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
              V ⟨n.val - 1, by omega⟩ ≤ V n) →
          V ∈ cone B)

/-! ### (a) assembled: the attainable set over measurable scales -/

/-- The time piece `k` of `(t, T]`: `(max(t, τ_{k₀+k}), τ_{k₀+k+1}]`. -/
def piece (τ : ℕ → ℝ) (t : ℝ) (k₀ k : ℕ) : Set ℝ := Set.Ioc (max t (τ (k₀ + k))) (τ (k₀ + k + 1))

/-- The kernel of (24.1) for the row `n` and the factor `j`, with the piecewise ordinal index:
on the piece `k` it is `e^{−2λ_j(T_n − s)} γ_{n+1−k, j}²`, and it vanishes off the pieces. -/
noncomputable def kernel {m d : ℕ} (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ)
    (k₀ : ℕ) (n : Fin m) (j : Fin d) (s : ℝ) : ℝ :=
  ∑ k : Fin m, (piece τ t k₀ k.val).indicator
    (fun s => γ (n.val + 1 - k.val) j ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s))) s

/-- The variance vector (24.1) of the scales `a`: `V_n(t) = Σ_j ∫_t^{T_n} a_j(s)² kernel ds`. -/
noncomputable def scaledVariance {m d : ℕ} (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ)
    (t : ℝ) (k₀ : ℕ) (a : Fin d → ℝ → ℝ) : Fin m → ℝ := fun n =>
  ∑ j, ∫ s in Set.Ioc t (τ (k₀ + n.val + 1)), a j s ^ 2 * kernel τ γ lam t k₀ n j s

/-- Admissible scales: measurable, with the square integrable against the exponential weight on
every piece. -/
def Admissible {d : ℕ} (m : ℕ) (τ : ℕ → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (a : Fin d → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (a j)) ∧
  ∀ (j : Fin d) (k : Fin m), IntegrableOn (fun s => a j s ^ 2 * Real.exp (2 * lam j * s))
    (piece τ t k₀ k.val)

/-- (a): the set of variance vectors (24.1) attained by admissible scales is exactly the cone
`K(t) = {A(t) q : q ≥ 0}` of (24.2): every admissible scale gives a vector of the cone, and every
vector of the cone is attained, by scales constant on each piece. -/
def attainableStatement : Prop :=
  ∀ (m d k₀ : ℕ) (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ),
    StrictMonoOn τ (Set.Iic (k₀ + m)) → τ k₀ ≤ t → t < τ (k₀ + 1) →
    (∀ a : Fin d → ℝ → ℝ, Admissible m τ lam t k₀ a →
      scaledVariance (m := m) τ γ lam t k₀ a ∈ cone (Apw (m := m) τ γ lam t k₀)) ∧
    (∀ V ∈ cone (Apw (m := m) τ γ lam t k₀), ∃ a : Fin d → ℝ → ℝ,
      Admissible m τ lam t k₀ a ∧ scaledVariance (m := m) τ γ lam t k₀ a = V)

/-- (d) on the piecewise cone: with constant ordinal loadings, one of them nonzero, every cone
`K(t)` lies in the orthant and the closure of the union of the cones over all nonnegative decay
vectors is the whole orthant, so nothing beyond `V ≥ 0` survives unbounded decays; the bounded
case is `piecewiseConeStatement` with `λ_max = Λ`. -/
def piecewiseClosureStatement : Prop :=
  ∀ (m d k₀ : ℕ) (τ : ℕ → ℝ) (γ' : Fin d → ℝ) (t : ℝ),
    StrictMonoOn τ (Set.Iic (k₀ + m)) → τ k₀ ≤ t → t < τ (k₀ + 1) → (∃ j, γ' j ≠ 0) →
    (∀ lam : Fin d → ℝ, cone (Apw (m := m) τ (fun _ => γ') lam t k₀) ⊆ orthant m) ∧
    closure (⋃ lam ∈ {lam : Fin d → ℝ | ∀ j, 0 ≤ lam j},
      cone (Apw (m := m) τ (fun _ => γ') lam t k₀)) = orthant m

def statement : Prop := fixedDirectionStatement ∧ dualStatement ∧ ratioBoundStatement ∧
  recursionStatement ∧ attainmentStatement ∧ diagonalStatement ∧ closureStatement ∧
  piecewiseConeStatement ∧ attainableStatement ∧ piecewiseClosureStatement

end Standalone.SurvivingScaleRestrictions

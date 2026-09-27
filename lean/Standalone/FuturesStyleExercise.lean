import Standalone.CompoundedFuturesIdentification
import Standalone.LateAmericanExercise
import Standalone.PreWindowVarianceAggregates

/-! # Claim 021: futures-style American options on the compounded rate

Partial target, formalized early while the claim is under review. In Claim 011's explicit
Gaussian model it states: (a) exact compounding across a partition with no meeting strictly
inside a fixing interval, the accrual identity (21.3), and that Claim 017's conditional
futures rate `F` is the version (21.4) of the conditional expectation of the compounded rate:
measurable for the reveal filtration, constant between meetings, square integrable, a
martingale, with the mean identity of (a); (c) in integral form, the futures-style European
value `E[(F(S) − K)^+]` is Claim 017's Gaussian call integral `C0177` at the forward
`1 + δ F(0)`, variance `σ_S²` and strike `1 + δ K`, and is nonincreasing in the strike; and
(d), the aggregate dependence: with a common unrevealed block and a window opening after the
revealed meetings, equal `(V_k, H_k)` give equal `p`, equal `σ_S²` for every `S ≥ A`, equal
quotes and equal futures-style European values; and (b), the no-early-exercise theorem
(`noEarlyExerciseStatement`): every admissible exercise time of the completed reveal filtration
has futures-style value at most the European value at the last date, so the American value
(21.2) is the European value (21.5), for every window `A ≤ S` crossing any number of unrevealed
meetings; and the closed form (21.6) (`closedFormStatement`): the Black-type formula with `Φ`
for `σ_S > 0` and `K' > 0`, the affine value for `K' ≤ 0`, the intrinsic value for `σ_S = 0`, and
the continuity and monotonicity of the value in the strike; (d), the identification converse
(`identificationStatement`): with a common unrevealed block and a window opening after the
revealed meetings, equal `(V_k, H_k)` give equal futures-style American values; the surface at
an expiry together with the quote identifies `σ_S²`, through the at-the-money price; between two
expiries with exactly one meeting between them, the difference of `σ_S²` is `c_n² v_n`, so the
variance of a meeting strictly inside the window is identified by two such surfaces; and a
variance at or after `b` enters neither the quote nor any surface; and the equal pair of (e)
(`pairStatement`): on the dates `(1, 2, 3, 4, 5)` with `3 ≤ A < 4`, the vectors
`(2, 3, 2, w_4, w_5)ε` and `(3, 1, 3, w_4, w_5)ε` give identical quotes and identical
futures-style values at every window `a ≥ A`, expiry and strike; and the separated pair of (e)
(`separationStatement`): the vectors `(2, 3, 2, 3, 2)ε` and `(2, 3, 2, 1, 2)ε` with `ε > 0`, at
every expiry `S ∈ [4, 5)` and window `a < 4 < b`, differ in `σ_S²` by exactly `(b − 4)² · 2ε` and
in the quote exponent by `(b − 4)² · 2ε`, both larger for the first, the quotes differ, and the
futures-style value of the first is strictly larger at every strike, since the value is
nondecreasing in the variance and strictly increasing in the forward.
-/
open MeasureTheory ProbabilityTheory Set
open Standalone.CompoundedFuturesIdentification (Ω Q filt r w d h p q L0175 G F C0177 Φ)
open Standalone.LateAmericanExercise (Ωc Qc completedFilt T0183)
open Standalone.PreWindowVarianceAggregates (L0202 R0202 Vk Hk past)

namespace Standalone.FuturesStyleExercise

/-- The futures-style American value (21.2): the supremum over all admissible exercise times
of the undiscounted expected payoff on the conditional futures rate. -/
noncomputable def Ufut {N : ℕ} (τ : ℕ → ℝ) (v : Fin N → NNReal) (A S a b K : ℝ) : ℝ :=
  sSup ((fun σ => ∫ ω : Ωc v, max (F τ v (σ ω) a b ω - K) 0 ∂Qc v) '' T0183 τ v A S)

/-- (a): exact compounding, the accrual identity (21.3), and the conditional futures version
(21.4) with its measurability, constancy between meetings, square integrability, martingale
property and mean. -/
def conditionalStatement : Prop :=
  ∀ (N J : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) → 0 < J →
    ∀ u : Fin (J+1) → ℝ, StrictMono u → 0 ≤ u 0 →
    (∀ (j : Fin J) (i : Fin N), ¬ (u j.castSucc < τ (i.val+1) ∧ τ (i.val+1) < u j.succ)) →
    (∀ ω, (∏ j : Fin J, (1+(u j.succ-u j.castSucc)*L0202 τ v u j ω)) =
      Real.exp (∫ s in u 0..u (Fin.last J), r τ v s ω)) ∧
    (∀ ω, (∫ s in u 0..u (Fin.last J), r τ v s ω) =
      ∑ i, (w (u 0) (u (Fin.last J)) (τ (i.val+1)) * ω i +
        d (u 0) (u (Fin.last J)) (τ (i.val+1)) * (v i : ℝ))) ∧
    (∀ t, (Q v)[fun ω => R0202 τ v u ω | filt τ t] =ᵐ[Q v] F τ v t (u 0) (u (Fin.last J))) ∧
    (∀ t, Measurable[filt τ t] (F τ v t (u 0) (u (Fin.last J)))) ∧
    (∀ t t', (∀ i : Fin N, τ (i.val+1) ≤ t ↔ τ (i.val+1) ≤ t') →
      F τ v t (u 0) (u (Fin.last J)) = F τ v t' (u 0) (u (Fin.last J))) ∧
    (∀ t, MemLp (F τ v t (u 0) (u (Fin.last J))) 2 (Q v)) ∧
    (∀ t s, t ≤ s → (Q v)[F τ v s (u 0) (u (Fin.last J)) | filt τ t] =ᵐ[Q v]
      F τ v t (u 0) (u (Fin.last J))) ∧
    (∀ ω, F τ v 0 (u 0) (u (Fin.last J)) ω =
      (Real.exp (p τ v (u 0) (u (Fin.last J))) - 1)/(u (Fin.last J) - u 0)) ∧
    (∀ t, (∫ ω, F τ v t (u 0) (u (Fin.last J)) ω ∂Q v) =
      (Real.exp (p τ v (u 0) (u (Fin.last J))) - 1)/(u (Fin.last J) - u 0))

/-- (c) in integral form: the futures-style European value is the Gaussian call integral at
the forward `exp p = 1 + δ F(0)`, variance `σ_S² = q` and strike `1 + δ K`, divided by `δ`;
and it is nonincreasing in the strike. -/
def europeanStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ a b S : ℝ, a < b → 0 ≤ S →
    (∀ K, (∫ ω, max (F τ v S a b ω - K) 0 ∂Q v) =
      C0177 (Real.exp (p τ v a b)) (q τ v S a b) (1 + (b-a)*K) / (b-a)) ∧
    Antitone (fun K => ∫ ω, max (F τ v S a b ω - K) 0 ∂Q v)

/-- (d), the aggregate dependence: for a window opening after the revealed meetings, `p` and
`σ_S²` for `S ≥ A` depend on the revealed variances only through `(V_k, H_k)`, so two vectors
with a common unrevealed block and equal `(V_k, H_k)` give equal quotes and equal
futures-style European values. -/
def aggregateStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A a b : ℝ, 0 ≤ a → a < b → (∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a) →
    (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A → Hk τ v A = Hk τ v' A →
    p τ v a b = p τ v' a b ∧ (∀ S, A ≤ S → q τ v S a b = q τ v' S a b) ∧
    (∀ ω, F τ v 0 a b ω = F τ v' 0 a b ω) ∧
    ∀ S K, A ≤ S → 0 ≤ S →
      (∫ ω, max (F τ v S a b ω - K) 0 ∂Q v) = ∫ ω, max (F τ v' S a b ω - K) 0 ∂Q v'

/-- (b), no early-exercise value: for every admissible exercise time `σ ∈ 𝒯[A, S]` the
futures-style value `E[(F(σ) − K)^+]` is at most the European value `E[(F(S) − K)^+]`, so
`τ = S` is optimal and (21.5) holds, for every `0 ≤ A ≤ S`. -/
def noEarlyExerciseStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S a b K : ℝ, 0 ≤ A → A ≤ S → 0 ≤ a → a < b →
    (∀ σ ∈ T0183 τ v A S, (∫ ω : Ωc v, max (F τ v (σ ω) a b ω - K) 0 ∂Qc v) ≤
      ∫ ω, max (F τ v S a b ω - K) 0 ∂Q v) ∧
    Ufut τ v A S a b K = ∫ ω, max (F τ v S a b ω - K) 0 ∂Q v

/-- (c), the closed form (21.6): with `G = exp p = 1 + δ F(0)`, `σ_S² = q` and `K' = 1 + δ K`,
the futures-style value is the Black-type formula when `σ_S > 0` and `K' > 0`, `(G − K')/δ`
when `K' ≤ 0`, and `(G − K')^+/δ` when `σ_S = 0`; it is finite, continuous and nonincreasing in
the strike. -/
def closedFormStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A S a b : ℝ, 0 ≤ A → A ≤ S → 0 ≤ a → a < b →
    let G := Real.exp (p τ v a b)
    let σ2 : ℝ := q τ v S a b
    (∀ K : ℝ, 0 < σ2 → 0 < 1 + (b-a)*K →
      Ufut τ v A S a b K = (G * Φ ((Real.log (G/(1 + (b-a)*K)) + σ2/2)/Real.sqrt σ2) -
        (1 + (b-a)*K) * Φ ((Real.log (G/(1 + (b-a)*K)) + σ2/2)/Real.sqrt σ2 - Real.sqrt σ2)) /
        (b-a)) ∧
    (∀ K : ℝ, 1 + (b-a)*K ≤ 0 → Ufut τ v A S a b K = (G - (1 + (b-a)*K))/(b-a)) ∧
    (∀ K : ℝ, σ2 = 0 → Ufut τ v A S a b K = max (G - (1 + (b-a)*K)) 0/(b-a)) ∧
    Continuous (fun K => Ufut τ v A S a b K) ∧ Antitone (fun K => Ufut τ v A S a b K)

/-- (d), the identification converse. -/
def identificationStatement : Prop :=
  ∀ (N : ℕ) (τ : ℕ → ℝ) (v v' : Fin N → NNReal), τ 0 = 0 → StrictMonoOn τ (Iic N) →
    ∀ A a b : ℝ, 0 ≤ A → 0 ≤ a → a < b →
    -- equal aggregates give equal futures-style American values
    ((∀ i : Fin N, τ (i.val+1) ≤ A → τ (i.val+1) ≤ a) →
      (∀ i : Fin N, A < τ (i.val+1) → v i = v' i) → Vk τ v A = Vk τ v' A → Hk τ v A = Hk τ v' A →
      ∀ S K, A ≤ S → Ufut τ v A S a b K = Ufut τ v' A S a b K) ∧
    -- the surface at `S` with the quote identifies `σ_S²`
    (∀ S, A ≤ S → p τ v a b = p τ v' a b →
      (∀ K, Ufut τ v A S a b K = Ufut τ v' A S a b K) → q τ v S a b = q τ v' S a b) ∧
    -- successive differences: exactly one meeting between the expiries
    (∀ (S₁ S₂ : ℝ) (n : Fin N), S₁ ≤ S₂ →
      (∀ i : Fin N, S₁ < τ (i.val+1) → τ (i.val+1) ≤ S₂ → i = n) →
      S₁ < τ (n.val+1) → τ (n.val+1) ≤ S₂ →
      (q τ v S₂ a b : ℝ) - q τ v S₁ a b = (w a b (τ (n.val+1)))^2 * v n) ∧
    -- hence a meeting strictly inside the window is identified by two such surfaces
    (∀ (S₁ S₂ : ℝ) (n : Fin N), S₁ ≤ S₂ →
      (∀ i : Fin N, S₁ < τ (i.val+1) → τ (i.val+1) ≤ S₂ → i = n) →
      S₁ < τ (n.val+1) → τ (n.val+1) ≤ S₂ → a < τ (n.val+1) → τ (n.val+1) < b →
      q τ v S₁ a b = q τ v' S₁ a b → q τ v S₂ a b = q τ v' S₂ a b → v n = v' n) ∧
    -- a variance at or after `b` enters neither the quote nor any surface
    (∀ n : Fin N, b ≤ τ (n.val+1) → (∀ i, i ≠ n → v i = v' i) →
      p τ v a b = p τ v' a b ∧ ∀ S, q τ v S a b = q τ v' S a b)

/-- The dates `(1, 2, 3, 4, 5)` of (e). -/
def τ5 : ℕ → ℝ := fun n => n
/-- The equal pair of (e): `(2, 3, 2, w_4, w_5)ε` and `(3, 1, 3, w_4, w_5)ε`. -/
noncomputable def v021 (ε w4 w5 : NNReal) : Fin 5 → NNReal := ![2*ε, 3*ε, 2*ε, w4, w5]
noncomputable def v021' (ε w4 w5 : NNReal) : Fin 5 → NNReal := ![3*ε, ε, 3*ε, w4, w5]

/-- (e), the equal pair: for `3 ≤ A < 4`, any window `a ≥ A`, and every expiry `S ≥ A` and strike,
the two vectors give identical quotes and identical futures-style American values. -/
def pairStatement : Prop :=
  ∀ (ε w4 w5 : NNReal) (A a b : ℝ), 3 ≤ A → A < 4 → A ≤ a → a < b →
    (∀ ω, F τ5 (v021 ε w4 w5) 0 a b ω = F τ5 (v021' ε w4 w5) 0 a b ω) ∧
    ∀ S K, A ≤ S → Ufut τ5 (v021 ε w4 w5) A S a b K = Ufut τ5 (v021' ε w4 w5) A S a b K

/-- (e), the separated pair: `(2, 3, 2, 3, 2)ε` and `(2, 3, 2, 1, 2)ε` share the revealed block
and the fifth variance and differ only at the fourth meeting; at every expiry `S ∈ [4, 5)` and
window `a < 4 < b` their `σ_S²` differ by `(b − 4)² · 2ε` and their quote exponents by
`(b − 4)² · 2ε`, the quotes differ, and the futures-style value of the first is strictly larger at
every strike and every `A ≤ S`. -/
def separationStatement : Prop :=
  ∀ (ε : NNReal) (a b S : ℝ), 0 < ε → 0 ≤ a → a < 4 → 4 < b → 4 ≤ S → S < 5 →
    (q τ5 (v021 ε (3*ε) (2*ε)) S a b : ℝ) - q τ5 (v021 ε ε (2*ε)) S a b = (b - 4)^2 * (2 * ε) ∧
    p τ5 (v021 ε (3*ε) (2*ε)) a b - p τ5 (v021 ε ε (2*ε)) a b = (b - 4)^2 * (2 * ε) ∧
    (∀ ω, F τ5 (v021 ε ε (2*ε)) 0 a b ω < F τ5 (v021 ε (3*ε) (2*ε)) 0 a b ω) ∧
    ∀ A K, 0 ≤ A → A ≤ S →
      Ufut τ5 (v021 ε ε (2*ε)) A S a b K < Ufut τ5 (v021 ε (3*ε) (2*ε)) A S a b K

def statement : Prop := conditionalStatement ∧ europeanStatement ∧ aggregateStatement ∧
  noEarlyExerciseStatement ∧ closedFormStatement ∧ identificationStatement ∧ pairStatement ∧
  separationStatement

end Standalone.FuturesStyleExercise

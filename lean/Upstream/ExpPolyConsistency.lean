import Upstream.LipschitzSDE
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Process.Stopping

/-!
# AX-16: exponents of a bounded exponential-polynomial family, given equation (3)

The fields specialize [filipovic2000exponential], Theorem 3.2 (with the constancy consequence and
both forms of its second part) and Corollaries 3.4–3.5, as recorded in `ledger/AXIOMS.md`, AX-16.
The source's hypothesis "Z is consistent with BEP(K, n)" is replaced by what its proofs use:
(H1) `Z_t ∈ 𝒵` for all `t`, almost surely, and (H2) equation (3) for all `x ≥ 0` at
`dt ⊗ dP`-almost every `(t, ω)`.

Notation follows the source. The parameters of BEP(K, n) are indexed by `Σ i, Fin (n i + 2)`:
`⟨i, μ⟩` with `μ ≤ n_i` is `z_{i,μ}` and `⟨i, n_i + 1⟩` is the exponent `z_{i,n_i+1}` (`ex i`).
`F`, its parameter derivatives `dF`, `d2F` and the residual of (3) are written out as in Claim
042's formalization (`lean/Standalone/SpliceVaryingExponents.lean`), body for body. With `a = σσ^T`
symmetric, the residual equals the source's symmetrized form of (3).
* `pNZ z i` is `p_i(z) ≠ 0`. `pBrNZ z i` is `p_[i](z) ≠ 0`, with the class `[i]` of (6) and
  the coefficients `z_{[i],μ}` of (7).
* `inA`, `inB`, `inC`, `inD`, `inD'` are membership in `A_i`, `B`, `C`, `D`, `D'`.
* `debutBC Z s ω` is the debut of `(B ∪ C) ∩ [s, ∞[` on the path `ω`, in `ℝ≥0∞`.
* `ItoProcess16` is the driver form: `Z_0` is `ℱ_0`-measurable, (U4) integrands, locally
  integrable drift, and the equation with the calculus's integral, almost surely for all `t`. The
  first premise is the adaptedness the source's `Z` has. Without it `Z_t := (B¹, 0)` for all `t`,
  with `b = σ = 0`, meets every premise under `BrownianDrivers6` and contradicts Corollary 3.5. `aeTP` is `dt ⊗ dP`-almost everywhere.

Every field assumes `BrownianDrivers6 h` (AX-06), the Itô process, (H1) and (H2).

The instance over `ItoCalculus.zeroDriverInstance` is vacuous. That base has covariation density
`c ≡ 0`, so the Brownian premise is false (`LipschitzSDE.zeroDriver_not_brownian`), and every
field holds without exercising Theorem 3.2. This is permitted by rule 6 as amended on 2026-09-23
(Q-06), only together with the separate checks below.
(1) `premises_check`: for `K = 1`, `n = (0)`, over the zero-driver base, the deterministic process
    `Z_t = (e^{−t}, 1)`, with drift `(−e^{−t}, 0)` and `σ = 0`, satisfies `ItoProcess16`
    (including the `ℱ_0`-measurability of `Z_0`), (H1) and (H2).
(2) `conclusions_check`: every field's conclusion holds for that process. This covers (12),
    (13), the constancy, both stopping-time forms at `τ = 0` (so their types are inhabited), and
    Corollaries 3.4–3.5.
(3) Every calculus of driver dimension zero satisfies `BrownianDrivers6`
    (`LipschitzSDE.brownianDrivers6_of_dimension_zero`).
These checks give no nontrivial Brownian model and no instance of Theorem 3.2's proof. A faithful
instance would reconstruct the source's §§4–6, forbidden by Lean role duty 3b.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Upstream
namespace ExpPoly16

variable {K : ℕ} {n : Fin K → ℕ}

/-- The parameter index of BEP(K, n). -/
abbrev Idx (K : ℕ) (n : Fin K → ℕ) := Σ i : Fin K, Fin (n i + 2)

/-- The exponent index `(i, n_i + 1)`. -/
def ex (i : Fin K) : Idx K n := ⟨i, Fin.last (n i + 1)⟩

/-- The exponent `z_{i,n_i+1}`. -/
def expo (z : Idx K n → ℝ) (i : Fin K) : ℝ := z ⟨i, Fin.last (n i + 1)⟩

/-- `p_i(x, z)`. -/
def poly (z : Idx K n → ℝ) (i : Fin K) (x : ℝ) : ℝ :=
  ∑ μ : Fin (n i + 1), z ⟨i, μ.castSucc⟩ * x ^ (μ : ℕ)

/-- `F(x, z)`, (5). -/
noncomputable def FBEP (z : Idx K n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, poly z i x * Real.exp (-expo z i * x)

/-- `∂F/∂z_I`. -/
noncomputable def dF (z : Idx K n → ℝ) (I : Idx K n) (x : ℝ) : ℝ :=
  if (I.2 : ℕ) < n I.1 + 1 then x ^ (I.2 : ℕ) * Real.exp (-expo z I.1 * x)
  else -(x * poly z I.1 x) * Real.exp (-expo z I.1 * x)

/-- `∂²F/∂z_I ∂z_J`. -/
noncomputable def d2F (z : Idx K n → ℝ) (I J : Idx K n) (x : ℝ) : ℝ :=
  if I.1 = J.1 then
    if (I.2 : ℕ) < n I.1 + 1 then
      (if (J.2 : ℕ) < n J.1 + 1 then 0 else -(x ^ ((I.2 : ℕ) + 1)) * Real.exp (-expo z I.1 * x))
    else
      (if (J.2 : ℕ) < n J.1 + 1 then -(x ^ ((J.2 : ℕ) + 1)) * Real.exp (-expo z I.1 * x)
        else x ^ 2 * poly z I.1 x * Real.exp (-expo z I.1 * x))
  else 0

/-- The difference of the two sides of (3). -/
noncomputable def residual (z : Idx K n → ℝ) (a : Idx K n → Idx K n → ℝ) (b : Idx K n → ℝ)
    (x : ℝ) : ℝ :=
  ∑ I, b I * dF z I x + (1 / 2) * ∑ I, ∑ J, a I J * d2F z I J x -
    ∑ I, ∑ J, a I J * dF z I x * (∫ η in (0:ℝ)..x, dF z J η) - deriv (FBEP z) x

/-- Equation (3) at a point, for all `x ≥ 0`. -/
def Eq3 (z : Idx K n → ℝ) (a : Idx K n → Idx K n → ℝ) (b : Idx K n → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → residual z a b x = 0

/-- `z ∈ 𝒵`: `sup_{x ≥ 0} |F(x, z)| < ∞`. -/
def Bounded (z : Idx K n → ℝ) : Prop := BddAbove ((fun x => |FBEP z x|) '' Set.Ici 0)

/-- `p_i(z) ≠ 0`. -/
def pNZ (z : Idx K n → ℝ) (i : Fin K) : Prop := ∃ μ : Fin (n i + 1), z ⟨i, μ.castSucc⟩ ≠ 0

/-- `z_{[i],μ} = ∑_{j ∈ [i], n_j ≥ μ} z_{j,μ}`, (7). -/
noncomputable def zBr (z : Idx K n → ℝ) (i : Fin K) (μ : ℕ) : ℝ :=
  ∑ j, if h : expo z j = expo z i ∧ μ ≤ n j then z ⟨j, ⟨μ, by omega⟩⟩ else 0

/-- `p_[i](z) ≠ 0`. -/
def pBrNZ (z : Idx K n → ℝ) (i : Fin K) : Prop := ∃ μ : ℕ, zBr z i μ ≠ 0

def inA (z : Idx K n → ℝ) (i : Fin K) : Prop := ¬ pNZ z i ∨ ¬ pBrNZ z i
def inB (z : Idx K n → ℝ) : Prop := ∃ i j : Fin K, i ≠ j ∧ expo z i = expo z j
def inC (z : Idx K n → ℝ) : Prop := ∃ i j : Fin K, i ≠ j ∧ 2 * expo z i = expo z j
def inD (z : Idx K n → ℝ) : Prop := (∀ i, ¬ inA z i) ∧ ¬ inB z ∧ ¬ inC z
def inD' (z : Idx K n → ℝ) : Prop := ¬ inB z ∧ ¬ inC z

/-- The debut of `(B ∪ C) ∩ [s, ∞[` on one path. -/
noncomputable def debutBC {Ω : Type*} (Z : ℝ≥0 → Ω → Idx K n → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : s ≤ t ∧ (inB (Z t ω) ∨ inC (Z t ω))), (t : ℝ≥0∞)

/-- The dynamics of the second part of Theorem 3.2 at `τ = s`, time `t` later. -/
def Dyn {Ω : Type*} (Z : ℝ≥0 → Ω → Idx K n → ℝ) (ω : Ω) (s t : ℝ≥0) : Prop :=
  ∀ i : Fin K,
    (∀ μ : Fin (n i), Z (s + t) ω ⟨i, ⟨μ, by omega⟩⟩ =
      Z s ω ⟨i, ⟨μ, by omega⟩⟩ * Real.exp (-expo (Z s ω) i * t) +
        Z s ω ⟨i, ⟨(μ : ℕ) + 1, by omega⟩⟩ * t * Real.exp (-expo (Z s ω) i * t)) ∧
    Z (s + t) ω ⟨i, ⟨n i, by omega⟩⟩ =
      Z s ω ⟨i, ⟨n i, by omega⟩⟩ * Real.exp (-expo (Z s ω) i * t)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `a = σσ^T`. -/
def aMat {m : ℕ} (σ : Idx K n → Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (j k : Idx K n) : ℝ :=
  ∑ l, σ j l t ω * σ k l t ω

/-- `dt ⊗ dP`-almost everywhere, over `t ≥ 0`. -/
def aeTP (h : ItoCalculus Ω) (P : ℝ≥0 → Ω → Prop) : Prop :=
  ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Set.Ici 0)).prod h.μ), P (Real.toNNReal p.1) p.2

/-- `Z` is an Itô process in driver form, started from an `ℱ_0`-measurable `Z_0`. -/
def ItoProcess16 (h : ItoCalculus Ω) (Z : ℝ≥0 → Ω → Idx K n → ℝ)
    (b : Idx K n → ℝ≥0 → Ω → ℝ) (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ j, Measurable[h.ℱ 0] fun ω => Z 0 ω j) ∧ (∀ j l, U4 h.ℱ h.μ (σ j l)) ∧ (∀ j, LocallyIntegrableDrift h.ℱ h.μ (b j)) ∧
  ∀ᵐ ω ∂h.μ, ∀ (t : ℝ≥0) (j : Idx K n), Z t ω j = Z 0 ω j + ∑ l, h.I l (σ j l) t ω +
    ∫ s in (0 : ℝ)..t, b j (Real.toNNReal s) ω

/-- The common premises: the Itô process, (H1) and (H2). -/
def Premises16 (h : ItoCalculus Ω) (Z : ℝ≥0 → Ω → Idx K n → ℝ)
    (b : Idx K n → ℝ≥0 → Ω → ℝ) (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ) : Prop :=
  ItoProcess16 h Z b σ ∧ (∀ᵐ ω ∂h.μ, ∀ t, Bounded (Z t ω)) ∧
    aeTP h fun t ω => Eq3 (Z t ω) (aMat σ t ω) (fun j => b j t ω)

end ExpPoly16

open ExpPoly16

/-- AX-16 over an existing calculus structure. -/
structure ExpPolyConsistency {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop where
  /-- (12). -/
  exponent_diffusion_zero : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ → ∀ i : Fin K,
    aeTP h fun t ω => pNZ (Z t ω) i → aMat σ t ω (ex i) (ex i) = 0
  /-- (13). -/
  exponent_drift_zero : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ → ∀ i : Fin K,
    aeTP h fun t ω => pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i → b (ex i) t ω = 0
  /-- The constancy consequence of (12)–(13). -/
  exponent_constant : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ → ∀ i : Fin K,
    ∀ᵐ ω ∂h.μ, ∀ u v : ℝ≥0, u ≤ v →
      (∀ t, u < t → t < v → pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i) →
      ∀ t, u ≤ t → t ≤ v → Z t ω (ex i) = Z u ω (ex i)
  /-- The second part, with `D'`. -/
  dynamics_after_stopping : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime h.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD' (Z s ω)) →
    ∀ᵐ ω ∂h.μ, ∀ s : ℝ≥0, τ ω = s → (s : ℝ≥0∞) < debutBC Z s ω ∧
      ∀ t : ℝ≥0, ((s + t : ℝ≥0) : ℝ≥0∞) < debutBC Z s ω → Dyn Z ω s t
  /-- The second part, with `D`: `τ' = ∞` and the exponents are constant. -/
  dynamics_regular : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime h.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD (Z s ω)) →
    ∀ᵐ ω ∂h.μ, ∀ s : ℝ≥0, τ ω = s → ∀ t : ℝ≥0,
      inD (Z (s + t) ω) ∧ Dyn Z ω s t ∧ ∀ i, Z (s + t) ω (ex i) = Z s ω (ex i)
  /-- Corollary 3.4. -/
  corollary_3_4 : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ → ∀ i : Fin K,
    aeTP h (fun t ω => pNZ (Z t ω) i) → aeTP h (fun t ω => pBrNZ (Z t ω) i) →
    ∀ᵐ ω ∂h.μ, ∀ t, Z t ω (ex i) = Z 0 ω (ex i)
  /-- Corollary 3.5. -/
  corollary_3_5 : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → Idx K n → ℝ) (b : Idx K n → ℝ≥0 → Ω → ℝ)
    (σ : Idx K n → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    (∀ᵐ ω ∂h.μ, (∀ i, pNZ (Z 0 ω) i) ∧ ¬ inB (Z 0 ω) ∧ ¬ inC (Z 0 ω)) →
    (∀ t : ℝ≥0, ∃ Y : Ω → Idx K n → ℝ, Measurable[h.ℱ 0] Y ∧ Z t =ᵐ[h.μ] Y) ∧
      ∀ᵐ ω ∂h.μ, ∀ t i, Z t ω (ex i) = Z 0 ω (ex i)

namespace ExpPolyConsistency

/-- A genuine, but vacuous, model of the fields over the zero-driver base: its Brownian premise
is false. No conclusion of Theorem 3.2 is obtained from this instance. -/
theorem zeroDriverInstance : ExpPolyConsistency ItoCalculus.zeroDriverInstance where
  exponent_diffusion_zero := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  exponent_drift_zero := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  exponent_constant := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  dynamics_after_stopping := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  dynamics_regular := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  corollary_3_4 := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim
  corollary_3_5 := fun h => (LipschitzSDE.zeroDriver_not_brownian h).elim

/-! ### The separate checks -/

section Checks
open ExpPoly16

/-- `K = 1`, `n = (0)`. -/
abbrev n1 : Fin 1 → ℕ := fun _ => 0

/-- The coefficient index `(1, 0)`. -/
def zc : Idx 1 n1 := ⟨0, 0⟩

lemma ex_ne_zc : (ex 0 : Idx 1 n1) ≠ zc := by decide

/-- The check process `Z_t = (e^{−t}, 1)`. -/
noncomputable def Zex : ℝ≥0 → Unit → Idx 1 n1 → ℝ :=
  fun t _ j => if j = zc then Real.exp (-(t : ℝ)) else 1

/-- Its drift `(−e^{−t}, 0)`. -/
noncomputable def bex : Idx 1 n1 → ℝ≥0 → Unit → ℝ :=
  fun j t _ => if j = zc then -Real.exp (-(t : ℝ)) else 0

/-- Its diffusion, zero. -/
def σex : Idx 1 n1 → Fin ItoCalculus.zeroDriverInstance.m → ℝ≥0 → Unit → ℝ := fun _ _ _ _ => 0

lemma sum_idx (f : Idx 1 n1 → ℝ) : ∑ j, f j = f zc + f (ex 0) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_one, Fin.sum_univ_two]
  rfl

lemma Zex_zc (t : ℝ≥0) (ω : Unit) : Zex t ω zc = Real.exp (-(t : ℝ)) := by simp [Zex]

lemma Zex_ex (t : ℝ≥0) (ω : Unit) : Zex t ω (ex 0) = 1 := by simp [Zex, ex_ne_zc]

lemma expo_Zex (t : ℝ≥0) (ω : Unit) : expo (Zex t ω) 0 = 1 := Zex_ex t ω

lemma poly_Zex (t : ℝ≥0) (ω : Unit) (x : ℝ) : poly (Zex t ω) 0 x = Real.exp (-(t : ℝ)) := by
  have e : (⟨0, (0 : Fin 1).castSucc⟩ : Idx 1 n1) = zc := rfl
  show ∑ μ : Fin 1, Zex t ω ⟨0, μ.castSucc⟩ * x ^ (μ : ℕ) = _
  rw [Fin.sum_univ_one, e, Zex_zc]
  simp

lemma FBEP_Zex (t : ℝ≥0) (ω : Unit) (x : ℝ) :
    FBEP (Zex t ω) x = Real.exp (-(t : ℝ)) * Real.exp (-x) := by
  simp only [FBEP, Fin.sum_univ_one, poly_Zex, expo_Zex, neg_mul, one_mul]

lemma U4_zero_check : U4 ItoCalculus.zeroDriverInstance.ℱ ItoCalculus.zeroDriverInstance.μ
    (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) := by
  refine ⟨stronglyMeasurable_const, fun t => Filter.Eventually.of_forall fun ω => ?_⟩
  simp

lemma drift_check (j : Idx 1 n1) :
    LocallyIntegrableDrift ItoCalculus.zeroDriverInstance.ℱ ItoCalculus.zeroDriverInstance.μ
      (bex j) := by
  have hg : Measurable fun t : ℝ≥0 => (if j = zc then -Real.exp (-(t : ℝ)) else 0 : ℝ) := by
    split_ifs
    · exact (Real.continuous_exp.comp (continuous_neg.comp NNReal.continuous_coe)).neg.measurable
    · exact measurable_const
  refine ⟨fun i => (hg.comp (measurable_subtype_coe.comp measurable_fst)).stronglyMeasurable,
    fun t => Filter.Eventually.of_forall fun ω => ?_⟩
  have hb : ∀ s, ENNReal.ofReal |bex j (Real.toNNReal s) ω| ≤ 1 := fun s => by
    refine ENNReal.ofReal_le_one.2 ?_
    simp only [bex]
    split_ifs
    · rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      simp
    · simp
  calc (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal |bex j (Real.toNNReal s) ω|)
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) t, 1 := setLIntegral_mono measurable_const fun s _ => hb s
    _ < ⊤ := by simp

lemma equation_check (t : ℝ≥0) (ω : Unit) (j : Idx 1 n1) :
    Zex t ω j = Zex 0 ω j + ∑ l, ItoCalculus.zeroDriverInstance.I l (σex j l) t ω +
      ∫ s in (0 : ℝ)..t, bex j (Real.toNNReal s) ω := by
  have hI : ∑ l, ItoCalculus.zeroDriverInstance.I l (σex j l) t ω = 0 := by
    simp [ItoCalculus.zeroDriverInstance]
  rw [hI, add_zero]
  by_cases hj : j = zc
  · subst hj
    have hcongr : (∫ s in (0 : ℝ)..t, bex zc (Real.toNNReal s) ω) =
        ∫ s in (0 : ℝ)..t, -Real.exp (-s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs0 : 0 ≤ s := by
        rcases Set.mem_uIcc.1 hs with h | h
        · exact h.1
        · linarith [h.1, NNReal.coe_nonneg t]
      simp [bex, Real.coe_toNNReal _ hs0]
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-s)) s := fun s _ => by
      simpa using (hasDerivAt_neg s).exp
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_exp.comp continuous_neg).neg.intervalIntegrable _ _)]
    simp [Zex]
  · simp [Zex, bex, hj]

lemma bounded_check (t : ℝ≥0) (ω : Unit) : Bounded (Zex t ω) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  show |FBEP (Zex t ω) x| ≤ 1
  rw [FBEP_Zex, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  calc Real.exp (-(t : ℝ)) * Real.exp (-x) ≤ 1 * 1 :=
        mul_le_mul (Real.exp_le_one_iff.2 (by simp)) (Real.exp_le_one_iff.2 (by simpa using hx))
          (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

lemma eq3_check (t : ℝ≥0) (ω : Unit) :
    Eq3 (Zex t ω) (aMat σex t ω) (fun j => bex j t ω) := by
  intro x _
  have hd : deriv (FBEP (Zex t ω)) x = -(Real.exp (-(t : ℝ)) * Real.exp (-x)) := by
    have e : FBEP (Zex t ω) = fun x => Real.exp (-(t : ℝ)) * Real.exp (-x) :=
      funext (FBEP_Zex t ω)
    rw [e]
    have := ((hasDerivAt_neg x).exp).const_mul (Real.exp (-(t : ℝ)))
    rw [this.deriv]
    ring
  have hdF : dF (Zex t ω) zc x = Real.exp (-x) := by
    simp [dF, zc, expo_Zex]
  simp only [ExpPoly16.residual, aMat, σex, mul_zero, Finset.sum_const_zero, zero_mul, sub_zero, add_zero,
    hd]
  rw [sum_idx]
  simp only [bex, ex_ne_zc, zero_mul, add_zero, hdF, ↓reduceIte]
  ring

/-- Check (1): every premise but the Brownian one holds for the check process. -/
lemma premises_check : Premises16 ItoCalculus.zeroDriverInstance Zex bex σex :=
  ⟨⟨fun _ => Subsingleton.measurable, fun _ _ => U4_zero_check, drift_check,
      Filter.Eventually.of_forall fun ω t j => equation_check t ω j⟩,
    Filter.Eventually.of_forall fun ω t => bounded_check t ω,
    Filter.Eventually.of_forall fun _ => eq3_check _ _⟩

lemma noB (z : Idx 1 n1 → ℝ) : ¬ inB z := fun ⟨i, j, hij, _⟩ => hij (Subsingleton.elim i j)
lemma noC (z : Idx 1 n1 → ℝ) : ¬ inC z := fun ⟨i, j, hij, _⟩ => hij (Subsingleton.elim i j)

lemma debut_top (s : ℝ≥0) (ω : Unit) : debutBC Zex s ω = ⊤ := by
  simp [debutBC, noB, noC]

lemma dyn_check (ω : Unit) (s t : ℝ≥0) : Dyn Zex ω s t := by
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  refine ⟨fun μ => μ.elim0, ?_⟩
  have e : (⟨0, ⟨n1 0, by omega⟩⟩ : Idx 1 n1) = zc := rfl
  rw [e, Zex_zc, Zex_zc, expo_Zex, NNReal.coe_add, ← Real.exp_add]
  ring_nf

lemma inD_check (t : ℝ≥0) (ω : Unit) : inD (Zex t ω) := by
  refine ⟨fun i hA => ?_, noB _, noC _⟩
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hne : Zex t ω zc ≠ 0 := by rw [Zex_zc]; exact (Real.exp_pos _).ne'
  rcases hA with hA | hA
  · exact hA ⟨0, hne⟩
  · refine hA ⟨0, ?_⟩
    have e : zBr (Zex t ω) 0 0 = Zex t ω zc := by
      simp [zBr, zc]
    rw [e]
    exact hne

/-- Check (2): every field's conclusion holds for the check process; the stopping-time forms
at `τ = 0`, whose premises also hold. -/
lemma conclusions_check :
    (aeTP ItoCalculus.zeroDriverInstance fun t ω =>
      pNZ (Zex t ω) 0 → aMat σex t ω (ex 0) (ex 0) = 0) ∧
    (aeTP ItoCalculus.zeroDriverInstance fun t ω =>
      pNZ (Zex t ω) 0 ∧ pBrNZ (Zex t ω) 0 → bex (ex 0) t ω = 0) ∧
    (∀ᵐ ω ∂ItoCalculus.zeroDriverInstance.μ, ∀ u v : ℝ≥0, u ≤ v →
      (∀ t, u < t → t < v → pNZ (Zex t ω) 0 ∧ pBrNZ (Zex t ω) 0) →
      ∀ t, u ≤ t → t ≤ v → Zex t ω (ex 0) = Zex u ω (ex 0)) ∧
    (IsStoppingTime ItoCalculus.zeroDriverInstance.ℱ (fun _ : Unit => ((0 : ℝ≥0) : WithTop ℝ≥0)) ∧
      (∀ (ω : Unit) (s : ℝ≥0), ((0 : ℝ≥0) : WithTop ℝ≥0) = s → inD' (Zex s ω)) ∧
      ∀ᵐ ω ∂ItoCalculus.zeroDriverInstance.μ, ∀ s : ℝ≥0, ((0 : ℝ≥0) : WithTop ℝ≥0) = s →
        (s : ℝ≥0∞) < debutBC Zex s ω ∧
        ∀ t : ℝ≥0, ((s + t : ℝ≥0) : ℝ≥0∞) < debutBC Zex s ω → Dyn Zex ω s t) ∧
    ((∀ (ω : Unit) (s : ℝ≥0), ((0 : ℝ≥0) : WithTop ℝ≥0) = s → inD (Zex s ω)) ∧
      ∀ᵐ ω ∂ItoCalculus.zeroDriverInstance.μ, ∀ s : ℝ≥0, ((0 : ℝ≥0) : WithTop ℝ≥0) = s →
        ∀ t : ℝ≥0, inD (Zex (s + t) ω) ∧ Dyn Zex ω s t ∧
          ∀ i, Zex (s + t) ω (ex i) = Zex s ω (ex i)) ∧
    (∀ᵐ ω ∂ItoCalculus.zeroDriverInstance.μ, ∀ t, Zex t ω (ex 0) = Zex 0 ω (ex 0)) ∧
    ((∀ t : ℝ≥0, ∃ Y : Unit → Idx 1 n1 → ℝ,
        Measurable[ItoCalculus.zeroDriverInstance.ℱ 0] Y ∧
        Zex t =ᵐ[ItoCalculus.zeroDriverInstance.μ] Y) ∧
      ∀ᵐ ω ∂ItoCalculus.zeroDriverInstance.μ, ∀ t (i : Fin 1), Zex t ω (ex i) = Zex 0 ω (ex i)) := by
  have hex : ∀ (i : Fin 1) (t : ℝ≥0) (ω : Unit), Zex t ω (ex i) = 1 := fun i t ω => by
    rw [Subsingleton.elim i 0, Zex_ex]
  refine ⟨Filter.Eventually.of_forall fun p _ => by simp [aMat, σex],
    Filter.Eventually.of_forall fun p _ => by simp [bex, ex_ne_zc],
    Filter.Eventually.of_forall fun ω u v _ _ t _ _ => by rw [hex, hex],
    ⟨isStoppingTime_const _ _, fun ω s _ => ⟨noB _, noC _⟩,
      Filter.Eventually.of_forall fun ω s _ => ⟨by rw [debut_top]; exact ENNReal.coe_lt_top,
        fun t _ => dyn_check ω s t⟩⟩,
    ⟨fun ω s _ => inD_check s ω, Filter.Eventually.of_forall fun ω s _ t =>
      ⟨inD_check _ ω, dyn_check ω s t, fun i => by rw [hex, hex]⟩⟩,
    Filter.Eventually.of_forall fun ω t => by rw [hex, hex],
    ⟨fun t => ⟨Zex t, measurable_const, Filter.EventuallyEq.rfl⟩,
      Filter.Eventually.of_forall fun ω t i => by rw [hex, hex]⟩⟩

/-- Check (3): every calculus of driver dimension zero satisfies the Brownian premise. -/
lemma brownianDrivers6_dimension_zero_check {Ω : Type*} [MeasurableSpace Ω]
    (h : ItoCalculus Ω) (hm : h.m = 0) : BrownianDrivers6 h :=
  LipschitzSDE.brownianDrivers6_of_dimension_zero h hm

end Checks

end ExpPolyConsistency
end Upstream

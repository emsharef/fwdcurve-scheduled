import Standalone.SpliceVaryingExponents
import Standalone.BoundedVarianceExistence
import Mathlib.Probability.Process.Stopping

/-! # Claim 042 (b): Filipović's exponent restrictions transfer to the splice

`ExpPolyConsistency` restates AX-16 (`Upstream.ExpPolyConsistency`) over the standalone calculus,
field for field, with the family, its derivatives and the residual of (3) from
`SpliceVaryingExponents`. It covers [filipovic2000exponential] Theorem 3.2 and Corollaries
3.4–3.5, under (H1) and (H2). The set predicates `pNZ`, `pBrNZ`, `inA`–`inD'`, the debut
`debutBC`, the dynamics `Dyn`, `aMat`, `aeTP`, `ItoProcess16` (with an `ℱ_0`-measurable `Z_0`)
and `Premises16` are the Upstream file's, restated.

`restrictionsStatement` is (b). Let `Z` be an Itô process in driver form for the block's
parameters, with (H1). Suppose (P) holds `dt ⊗ dP`-almost everywhere, and so does the splice's
AX-01, in the form of (a)'s hypothesis (the residual equals a polynomial on an open interval).
Then (H2) holds by (a), and every conclusion of AX-16 holds for `Z`:
* (12) and (13), and the constancy of the exponents;
* both forms of the second part of Theorem 3.2;
* Corollaries 3.4–3.5.
So the front end changes nothing in the block's exponent restrictions.
-/

open MeasureTheory ProbabilityTheory Set Polynomial
open scoped NNReal ENNReal
namespace Standalone.SpliceVaryingExponentsRestrictions
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.BoundedVarianceExistence
open Standalone.SpliceVaryingExponents

variable {K : ℕ} {n : Fin K → ℕ}

/-- The exponent index `(i, n_i + 1)`. -/
def ex (i : Fin K) : Σ i : Fin K, Fin (n i + 2) := ⟨i, Fin.last (n i + 1)⟩

/-- Equation (3) at a point, for all `x ≥ 0`. -/
def Eq3 (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (a : (Σ i : Fin K, Fin (n i + 2)) → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → residualBEP z a b x = 0

/-- `z ∈ 𝒵`. -/
def Bounded (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop :=
  BddAbove ((fun x => |FBEP z x|) '' Set.Ici 0)

def pNZ (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) : Prop :=
  ∃ μ : Fin (n i + 1), z ⟨i, μ.castSucc⟩ ≠ 0

noncomputable def zBr (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) (μ : ℕ) : ℝ :=
  ∑ j, if h : expo z j = expo z i ∧ μ ≤ n j then z ⟨j, ⟨μ, by omega⟩⟩ else 0

def pBrNZ (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) : Prop := ∃ μ : ℕ, zBr z i μ ≠ 0

def inA (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) : Prop := ¬ pNZ z i ∨ ¬ pBrNZ z i
def inB (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop :=
  ∃ i j : Fin K, i ≠ j ∧ expo z i = expo z j
def inC (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop :=
  ∃ i j : Fin K, i ≠ j ∧ 2 * expo z i = expo z j
def inD (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop := (∀ i, ¬ inA z i) ∧ ¬ inB z ∧ ¬ inC z
def inD' (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : Prop := ¬ inB z ∧ ¬ inC z

noncomputable def debutBC {Ω : Type*} (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : s ≤ t ∧ (inB (Z t ω) ∨ inC (Z t ω))), (t : ℝ≥0∞)

def Dyn {Ω : Type*} (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ) (ω : Ω) (s t : ℝ≥0) :
    Prop :=
  ∀ i : Fin K,
    (∀ μ : Fin (n i), Z (s + t) ω ⟨i, ⟨μ, by omega⟩⟩ =
      Z s ω ⟨i, ⟨μ, by omega⟩⟩ * Real.exp (-expo (Z s ω) i * t) +
        Z s ω ⟨i, ⟨(μ : ℕ) + 1, by omega⟩⟩ * t * Real.exp (-expo (Z s ω) i * t)) ∧
    Z (s + t) ω ⟨i, ⟨n i, by omega⟩⟩ =
      Z s ω ⟨i, ⟨n i, by omega⟩⟩ * Real.exp (-expo (Z s ω) i * t)

variable {Ω : Type*} [MeasurableSpace Ω]

def aMat {m : ℕ} (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (j k : Σ i : Fin K, Fin (n i + 2)) : ℝ :=
  ∑ l, σ j l t ω * σ k l t ω

def aeTP (h : ItoCalculus Ω) (P : ℝ≥0 → Ω → Prop) : Prop :=
  ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Set.Ici 0)).prod h.μ), P (Real.toNNReal p.1) p.2

def ItoProcess16 (h : ItoCalculus Ω) (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ j, Measurable[h.ℱ 0] fun ω => Z 0 ω j) ∧ (∀ j l, U4 h.ℱ h.μ (σ j l)) ∧ (∀ j, LocallyIntegrableDrift h.ℱ h.μ (b j)) ∧
  ∀ᵐ ω ∂h.μ, ∀ (t : ℝ≥0) (j : Σ i : Fin K, Fin (n i + 2)),
    Z t ω j = Z 0 ω j + ∑ l, h.I l (σ j l) t ω + ∫ s in (0 : ℝ)..t, b j (Real.toNNReal s) ω

def Premises16 (h : ItoCalculus Ω) (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ) : Prop :=
  ItoProcess16 h Z b σ ∧ (∀ᵐ ω ∂h.μ, ∀ t, Bounded (Z t ω)) ∧
    aeTP h fun t ω => Eq3 (Z t ω) (aMat σ t ω) (fun j => b j t ω)

/-- AX-16 over the standalone calculus. -/
structure ExpPolyConsistency {Ω : Type*} [MeasurableSpace Ω] (h : ItoCalculus Ω) : Prop where
  exponent_diffusion_zero : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ i : Fin K, aeTP h fun t ω => pNZ (Z t ω) i → aMat σ t ω (ex i) (ex i) = 0
  exponent_drift_zero : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ i : Fin K, aeTP h fun t ω => pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i → b (ex i) t ω = 0
  exponent_constant : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ i : Fin K, ∀ᵐ ω ∂h.μ, ∀ u v : ℝ≥0, u ≤ v →
      (∀ t, u < t → t < v → pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i) →
      ∀ t, u ≤ t → t ≤ v → Z t ω (ex i) = Z u ω (ex i)
  dynamics_after_stopping : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime h.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD' (Z s ω)) →
    ∀ᵐ ω ∂h.μ, ∀ s : ℝ≥0, τ ω = s → (s : ℝ≥0∞) < debutBC Z s ω ∧
      ∀ t : ℝ≥0, ((s + t : ℝ≥0) : ℝ≥0∞) < debutBC Z s ω → Dyn Z ω s t
  dynamics_regular : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime h.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD (Z s ω)) →
    ∀ᵐ ω ∂h.μ, ∀ s : ℝ≥0, τ ω = s → ∀ t : ℝ≥0,
      inD (Z (s + t) ω) ∧ Dyn Z ω s t ∧ ∀ i, Z (s + t) ω (ex i) = Z s ω (ex i)
  corollary_3_4 : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    ∀ i : Fin K, aeTP h (fun t ω => pNZ (Z t ω) i) → aeTP h (fun t ω => pBrNZ (Z t ω) i) →
    ∀ᵐ ω ∂h.μ, ∀ t, Z t ω (ex i) = Z 0 ω (ex i)
  corollary_3_5 : BrownianDrivers6 h → ∀ (K : ℕ) (n : Fin K → ℕ)
    (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
    (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin h.m → ℝ≥0 → Ω → ℝ), Premises16 h Z b σ →
    (∀ᵐ ω ∂h.μ, (∀ i, pNZ (Z 0 ω) i) ∧ ¬ inB (Z 0 ω) ∧ ¬ inC (Z 0 ω)) →
    (∀ t : ℝ≥0, ∃ Y : Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ,
      Measurable[h.ℱ 0] Y ∧ Z t =ᵐ[h.μ] Y) ∧
      ∀ᵐ ω ∂h.μ, ∀ t i, Z t ω (ex i) = Z 0 ω (ex i)

/-- (b): under (P) and the splice's AX-01, both `dt ⊗ dP`-a.e., AX-16's premises hold for `Z`
and so do its conclusions. -/
def restrictionsStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω),
  ExpPolyConsistency S → BrownianDrivers6 S → ∀ (K : ℕ) (n : Fin K → ℕ)
  (Z : ℝ≥0 → Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
  (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ≥0 → Ω → ℝ)
  (σ : (Σ i : Fin K, Fin (n i + 2)) → Fin S.m → ℝ≥0 → Ω → ℝ),
  ItoProcess16 S Z b σ → (∀ᵐ ω ∂S.μ, ∀ t, Bounded (Z t ω)) →
  aeTP S (fun t ω => ∀ i, 0 < expo (Z t ω) i) →
  aeTP S (fun t ω => ∃ (P : ℝ[X]) (c d : ℝ), c < d ∧
    ∀ x ∈ Ioo c d, residualBEP (Z t ω) (aMat σ t ω) (fun j => b j t ω) x = P.eval x) →
  Premises16 S Z b σ ∧
  (∀ i, aeTP S fun t ω => pNZ (Z t ω) i → aMat σ t ω (ex i) (ex i) = 0) ∧
  (∀ i, aeTP S fun t ω => pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i → b (ex i) t ω = 0) ∧
  (∀ i, ∀ᵐ ω ∂S.μ, ∀ u v : ℝ≥0, u ≤ v →
    (∀ t, u < t → t < v → pNZ (Z t ω) i ∧ pBrNZ (Z t ω) i) →
    ∀ t, u ≤ t → t ≤ v → Z t ω (ex i) = Z u ω (ex i)) ∧
  (∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime S.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD' (Z s ω)) →
    ∀ᵐ ω ∂S.μ, ∀ s : ℝ≥0, τ ω = s → (s : ℝ≥0∞) < debutBC Z s ω ∧
      ∀ t : ℝ≥0, ((s + t : ℝ≥0) : ℝ≥0∞) < debutBC Z s ω → Dyn Z ω s t) ∧
  (∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime S.ℱ τ →
    (∀ (ω : Ω) (s : ℝ≥0), τ ω = s → inD (Z s ω)) →
    ∀ᵐ ω ∂S.μ, ∀ s : ℝ≥0, τ ω = s → ∀ t : ℝ≥0,
      inD (Z (s + t) ω) ∧ Dyn Z ω s t ∧ ∀ i, Z (s + t) ω (ex i) = Z s ω (ex i)) ∧
  (∀ i, aeTP S (fun t ω => pNZ (Z t ω) i) → aeTP S (fun t ω => pBrNZ (Z t ω) i) →
    ∀ᵐ ω ∂S.μ, ∀ t, Z t ω (ex i) = Z 0 ω (ex i)) ∧
  ((∀ᵐ ω ∂S.μ, (∀ i, pNZ (Z 0 ω) i) ∧ ¬ inB (Z 0 ω) ∧ ¬ inC (Z 0 ω)) →
    (∀ t : ℝ≥0, ∃ Y : Ω → (Σ i : Fin K, Fin (n i + 2)) → ℝ,
      Measurable[S.ℱ 0] Y ∧ Z t =ᵐ[S.μ] Y) ∧
      ∀ᵐ ω ∂S.μ, ∀ t i, Z t ω (ex i) = Z 0 ω (ex i))

def statement : Prop := restrictionsStatement

end Standalone.SpliceVaryingExponentsRestrictions

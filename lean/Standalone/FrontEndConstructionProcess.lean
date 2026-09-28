import Standalone.ZeroMeanReversionUpstreamBridge
import Standalone.FrontEndConstructionMatching

/-! # Claim 055 (a)–(b): the matching drifts at process level, and the front-end processes

**Conditional on the cited calculus** `Upstream.ItoCalculus` (AX-03 to AX-05), restated verbatim
in `Standalone.ZeroMeanReversionUpstreamBridge`, whose only instance is degenerate. Time is `ℝ≥0`, as in that structure. There are `IC.m` drivers, at least
one.

*The block (given).* Its state `Z = (z_{0,0}, …, z_{0,d}, ζ)` is the driver-form process
`driverForm IC.I x₀ HB KB`, with coordinates `Fin (d + 1 + r)`: `z_{0,μ}` is coordinate `pIdx μ` and
`ζ_i` is coordinate `zIdx i`. The rows `HB` are in (U4) and the drifts `KB` in the (U6) class
`LocallyIntegrableDrift`, on all of `[0, ∞)`. This is the alternative Red's note 4 allows: the
claim's truncation `1_{[0,H]} · (·)` of given coefficients satisfies it, and changes nothing on
`[0, H]`.

*The front-end noises (given).* `V m`, `m ∈ ℕ`, rows in (U4). Only `m ≤ |S|` ever enters. Setting
`V m = 0` for `m > |S|` meets the hypothesis for the others.

*The pointwise data.* `pt … u ω : Pt049` collects the values at `(u, ω)` of the rows, drifts, state
and noises (Claims 049–050's `D(u, ω)`), with the front-end drift fields set to `0`. The matching
drifts `ℓ_m`, `c_m` (`dL050`, `dC050`) do not read those fields.

Statements:
* `driftStatement`, (a): for `m ≤ |S|`, `ℓ_m` and `c_m`, truncated to `[0, H]` (`ell`, `cee`), are in
  the (U6) class `LocallyIntegrableDrift`. They are progressively measurable, and almost surely
  `∫_0^t |·| < ∞` for every `t`, so `∫_0^H (|ℓ_m| + |c_m|) < ∞`.
* `processStatement`, (b): for deterministic initial values, `L_m = driverForm(l₀; V_m; ℓ_m)` and
  `C_m = driverForm(c₀; 0; c_m)` (`Lproc`, `Cproc`) are predictable, hence adapted, and almost
  surely continuous. Almost surely, `C_m(t) = c₀ + ∫_0^t c_m` for every `t`, so `C_m` has no
  Brownian part and is an integral of an integrable function, of finite variation.

(c), the representation (2.2), is in `FrontEndConstructionRepresentation`.
-/

open MeasureTheory Set Matrix
open scoped NNReal

namespace Standalone.FrontEndConstructionProcess
open Standalone.ZeroMeanReversionUpstreamBridge (ItoCalculus U4 LocallyIntegrableDrift driverForm)
open Standalone.UnifiedSpliceStep0 Standalone.SpliceLocalizationConverse

/-- The block coordinate of `z_{0,μ}`. -/
def pIdx {d r : ℕ} (μ : Fin (d + 1)) : Fin (d + 1 + r) := Fin.castAdd r μ

/-- The block coordinate of `ζ_i`. -/
def zIdx {d r : ℕ} (i : Fin r) : Fin (d + 1 + r) := Fin.natAdd (d + 1) i

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pointwise data `D(u, ω)`: the block's rows, drifts and state `Z = driverForm IC.I x₀ HB KB`,
and the noises `V`, at time `u`, with the front-end drift fields `0`. -/
noncomputable def pt (IC : ItoCalculus Ω) {d r : ℕ} (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : Pt049 IC.m r where
  Hp μ l := if h : μ < d + 1 then HB (pIdx ⟨μ, h⟩) l u.toNNReal ω else 0
  Hz := Matrix.of fun i l => HB (zIdx i) l u.toNNReal ω
  bP μ := if h : μ < d + 1 then KB (pIdx ⟨μ, h⟩) u.toNNReal ω else 0
  zP μ := if h : μ < d + 1 then driverForm IC.I x₀ HB KB u.toNNReal ω (pIdx ⟨μ, h⟩) else 0
  bZ i := KB (zIdx i) u.toNNReal ω
  z i := driverForm IC.I x₀ HB KB u.toNNReal ω (zIdx i)
  V m l := V m l u.toNNReal ω
  dL _ := 0
  dC _ := 0

/-- The level drift `ℓ_m(t) = dL050(D(t), t, m)`, truncated to `[0, H]`. -/
noncomputable def ell (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ) ≤ H then dL050 c A d S (pt IC x₀ HB KB V t ω) t m else 0

/-- The slope drift `c_m(t) = dC050(D(t), t, m)`, truncated to `[0, H]`. -/
noncomputable def cee (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ) ≤ H then dC050 c A d S (pt IC x₀ HB KB V t ω) t m else 0

/-- `L_m = driverForm(l₀; noise V_m; drift ℓ_m)`. -/
noncomputable def Lproc (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (m : ℕ) (l₀ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  driverForm IC.I (fun _ : Fin 1 => l₀) (fun _ => V m)
    (fun _ => ell IC c A S H x₀ HB KB V m) t ω 0

/-- `C_m = driverForm(c₀; noise 0; drift c_m)`. -/
noncomputable def Cproc (IC : ItoCalculus Ω) {d r : ℕ} (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ) (x₀ : Fin (d + 1 + r) → ℝ)
    (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ) (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ)
    (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) (m : ℕ) (c₀ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  driverForm IC.I (fun _ : Fin 1 => c₀) (fun _ _ _ _ => 0)
    (fun _ => cee IC c A S H x₀ HB KB V m) t ω 0

/-- The Setting's hypotheses on the given coefficients. -/
def Setting (IC : ItoCalculus Ω) {n : ℕ} (HB : Fin n → Fin IC.m → ℝ≥0 → Ω → ℝ)
    (KB : Fin n → ℝ≥0 → Ω → ℝ) (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ) : Prop :=
  0 < IC.m ∧ (∀ j l, U4 IC.ℱ IC.μ (HB j l)) ∧ (∀ j, LocallyIntegrableDrift IC.ℱ IC.μ (KB j)) ∧
    ∀ m l, U4 IC.ℱ IC.μ (V m l)

def driftStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (IC : ItoCalculus Ω) (d r : ℕ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ)
  (x₀ : Fin (d + 1 + r) → ℝ) (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ)
  (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ) (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ), Setting IC HB KB V →
  ∀ m ≤ S.card, LocallyIntegrableDrift IC.ℱ IC.μ (ell IC c A S H x₀ HB KB V m) ∧
    LocallyIntegrableDrift IC.ℱ IC.μ (cee IC c A S H x₀ HB KB V m)

def processStatement : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (IC : ItoCalculus Ω) (d r : ℕ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (H : ℝ)
  (x₀ : Fin (d + 1 + r) → ℝ) (HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ)
  (KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ) (V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ), Setting IC HB KB V →
  ∀ m ≤ S.card, ∀ l₀ c₀ : ℝ,
    IsStronglyPredictable IC.ℱ (Lproc IC c A S H x₀ HB KB V m l₀) ∧
    IsStronglyPredictable IC.ℱ (Cproc IC c A S H x₀ HB KB V m c₀) ∧
    (∀ᵐ ω ∂IC.μ, Continuous fun t => Lproc IC c A S H x₀ HB KB V m l₀ t ω) ∧
    (∀ᵐ ω ∂IC.μ, Continuous fun t => Cproc IC c A S H x₀ HB KB V m c₀ t ω) ∧
    ∀ᵐ ω ∂IC.μ, ∀ t, Cproc IC c A S H x₀ HB KB V m c₀ t ω =
      c₀ + ∫ s in (0 : ℝ)..t, cee IC c A S H x₀ HB KB V m s.toNNReal ω

def statement : Prop := driftStatement ∧ processStatement

end Standalone.FrontEndConstructionProcess

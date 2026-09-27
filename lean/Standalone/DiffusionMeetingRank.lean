import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic

/-! # Claim 046 (c): the rank criterion through the meeting-free gaps

`N` meeting dates `T i > 0`, a partition of the diffusion into `P` cells `[c p, c (p+1))`, and `L`
option expiries `0 = S 0 < S 1 < … < S L`. The gap `ℓ` is `G_ℓ = (S ℓ, S (ℓ+1)]`, and
`lam lo hi c₀ c₁ = |(lo, hi] ∩ [c₀, c₁)|` is `λ_p`. The panel matrix (46.7) is `panel`, with rows
`Q(S_ℓ) = Σ_{T_i ≤ S_ℓ} v_i + Σ_p λ_p((0, S_ℓ]) u_p`, and `lamE` is `Λ_E`, the rows of the
meeting-free gaps.

* `injectiveStatement`: the panel identifies `θ = (v, u)` (the map `θ ↦ 𝒜θ` is injective) iff its
  rank is `N + P`; and if not, every strictly positive `θ` has a distinct strictly positive `θ′`
  with the same panel.
* `rankStatement` is (46.8): `𝒜` is injective iff (i) every meeting is at or before the last
  expiry, (ii) no gap contains two meetings, and (iii) `Λ_E` is injective (`rank Λ_E = P`).
-/

open Matrix

namespace Standalone.DiffusionMeetingRank

/-- `|(lo, hi] ∩ [c₀, c₁)|`. -/
noncomputable def lam (lo hi c₀ c₁ : ℝ) : ℝ := max 0 (min hi c₁ - max lo c₀)

variable {N P L : ℕ}

/-- The panel matrix (46.7): row `ℓ` is `Q(S (ℓ+1))`. -/
noncomputable def panel (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) :
    Matrix (Fin L) (Fin N ⊕ Fin P) ℝ :=
  fun ℓ k => Sum.elim (fun i => if T i ≤ S ℓ.succ then 1 else 0)
    (fun p => lam 0 (S ℓ.succ) (c p.castSucc) (c p.succ)) k

/-- The gap `(S ℓ, S (ℓ+1)]` contains no meeting. -/
def MeetingFree (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ) (ℓ : Fin L) : Prop :=
  ∀ i, ¬ (S ℓ.castSucc < T i ∧ T i ≤ S ℓ.succ)

/-- `Λ_E`: the diffusion lengths of the meeting-free gaps. -/
noncomputable def lamE (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) :
    Matrix {ℓ : Fin L // MeetingFree T S ℓ} (Fin P) ℝ :=
  fun ℓ p => lam (S ℓ.1.castSucc) (S ℓ.1.succ) (c p.castSucc) (c p.succ)

def injectiveStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ)
  (S : Fin (L + 1) → ℝ),
  ((panel T c S).rank = N + P ↔ Function.Injective (panel T c S).mulVec) ∧
  (¬ Function.Injective (panel T c S).mulVec → ∀ θ : Fin N ⊕ Fin P → ℝ, (∀ k, 0 < θ k) →
    ∃ θ' : Fin N ⊕ Fin P → ℝ, (∀ k, 0 < θ' k) ∧ θ' ≠ θ ∧
      (panel T c S).mulVec θ' = (panel T c S).mulVec θ)

def rankStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ)
  (S : Fin (L + 1) → ℝ), StrictMono S → S 0 = 0 → (∀ i, 0 < T i) →
  (Function.Injective (panel T c S).mulVec ↔
    (∀ i, T i ≤ S (Fin.last L)) ∧
    (∀ (ℓ : Fin L) (i j : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
      S ℓ.castSucc < T j → T j ≤ S ℓ.succ → i = j) ∧
    Function.Injective (lamE T c S).mulVec)

def statement : Prop := injectiveStatement ∧ rankStatement

end Standalone.DiffusionMeetingRank

import Standalone.DiffusionMeetingCalendar
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Claim 046 (d4): the futures rows

With the futures quotes, the panel gains the rows `z(S_ℓ)/δ_ℓ = Σ_{T_i ≤ S_ℓ} (S_ℓ − T_i) v_i +
∫_0^{S_ℓ} σ(s)²(S_ℓ − s) ds` of (46.6). For `σ² = u_p` on `[c_p, c_{p+1})` the diffusion part is
`Σ_p u_p mom1 0 S_ℓ c_p c_{p+1}`, where `mom1 lo hi c₀ c₁ = ∫_{(lo, hi] ∩ [c₀, c₁)} (hi − s) ds`
in closed form. `stacked` is the (Q, z) matrix.

* `momStatement`: the closed form is that integral.
* `stackedStatement` is (d4): the stacked matrix has full column rank for the quarterly partition
  (24 unknowns), the meeting-date partition (33) and the per-gap partition (40, one cell per gap).
-/

open Matrix

namespace Standalone.DiffusionMeetingFutures
open Standalone.DiffusionMeetingRank Standalone.ListedSr3Identification
open Standalone.DiffusionMeetingCalendar

/-- `∫_{(lo, hi] ∩ [c₀, c₁)} (hi − s) ds`. -/
noncomputable def mom1 (lo hi c₀ c₁ : ℝ) : ℝ :=
  if max lo c₀ < min hi c₁ then ((hi - max lo c₀) ^ 2 - (hi - min hi c₁) ^ 2) / 2 else 0

variable {N P L : ℕ}

/-- The futures rows `z(S_ℓ)/δ_ℓ`. -/
noncomputable def zrow (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) :
    Matrix (Fin L) (Fin N ⊕ Fin P) ℝ :=
  fun ℓ k => Sum.elim (fun i => if T i ≤ S ℓ.succ then S ℓ.succ - T i else 0)
    (fun p => mom1 0 (S ℓ.succ) (c p.castSucc) (c p.succ)) k

/-- The stacked (Q, z) matrix. -/
noncomputable def stacked (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ) :
    Matrix (Fin L ⊕ Fin L) (Fin N ⊕ Fin P) ℝ :=
  Matrix.fromRows (panel T c S) (zrow T c S)

/-- The per-gap partition: one cell per gap. -/
def cGap : Fin 25 → ℕ :=
  ![2, 16, 44, 72, 100, 135, 163, 191, 226, 254, 289, 317, 345, 380, 408, 436, 471, 499, 527,
    562, 590, 618, 653, 681, 709]

def momStatement : Prop := ∀ lo hi c₀ c₁ : ℝ, lo ≤ hi → c₀ ≤ c₁ →
  mom1 lo hi c₀ c₁ = ∫ s in lo..hi, (Set.Ico c₀ c₁).indicator (fun s => hi - s) s

def stackedStatement : Prop :=
  (stacked TCal (cells cQuarter) SCal).rank = 24 ∧
  (stacked TCal (cells cMeeting) SCal).rank = 33 ∧
  (stacked TCal (cells cGap) SCal).rank = 40

def statement : Prop := momStatement ∧ stackedStatement

end Standalone.DiffusionMeetingFutures

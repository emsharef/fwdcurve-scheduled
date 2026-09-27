import Standalone.DiffusionMeetingRank

/-! # Claim 047 (c): the rank criterion with arbitrary diffusion columns

As in `DiffusionMeetingRank`: `N` meeting dates `T i > 0` and `L` option expiries
`0 = S 0 < S 1 < … < S L`, the gap `ℓ` being `G_ℓ = (S ℓ, S (ℓ+1)]`. The diffusion columns are now
**any** real numbers `D n p` (`n` the expiry, `p` the cell), with `D 0 = 0`; for Claim 047,
`D_{ℓ,p} = ∫_{(0, S_ℓ] ∩ [c_{p−1}, c_p)} β_ℓ²`. `panelD` is `𝒜`, with the prefix-indicator meeting
columns of (46.7), `lamT` is `Λ̃_{ℓ,p} = D_{ℓ,p} − D_{ℓ−1,p}`, and `lamTE` its rows at the
meeting-free gaps. `Qp θ n = Σ_{T_i ≤ S_n} v_i + Σ_p D_{n,p} u_p` is the panel entry at `S_n`.

* `injectiveStatement`: the panel identifies `θ = (v, u)` iff `rank 𝒜 = N + P`; otherwise every
  strictly positive `θ` has a distinct strictly positive `θ′` with the same panel.
* `rankStatement` is (47.5): `𝒜` is injective iff (i) every meeting is at or before the last
  expiry, (ii) no gap contains two meetings, and (iii) `Λ̃_E` is injective (`rank Λ̃_E = P`).
* `inversionStatement`: `Λ̃_E u = (Q(S_ℓ) − Q(S_{ℓ−1}))_{ℓ ∈ E}`, with `u` its only solution when
  `Λ̃_E` is injective, and `v_i = Q(S_ℓ) − Q(S_{ℓ−1}) − Σ_p Λ̃_{ℓ,p} u_p` for the meeting alone in
  `G_ℓ`; and `P ≤ |E|` whenever the panel identifies.
-/

namespace Standalone.MaturityShapeRank
open Standalone.DiffusionMeetingRank

variable {N P L : ℕ}

/-- The panel matrix: row `ℓ` is `Q(S (ℓ+1))`, with diffusion columns `D (ℓ+1)`. -/
noncomputable def panelD (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ) (D : Fin (L + 1) → Fin P → ℝ) :
    Matrix (Fin L) (Fin N ⊕ Fin P) ℝ :=
  fun ℓ k => Sum.elim (fun i => if T i ≤ S ℓ.succ then 1 else 0) (fun p => D ℓ.succ p) k

/-- `Λ̃_{ℓ,p} = D_{ℓ,p} − D_{ℓ−1,p}` for the gap `ℓ`. -/
def lamT (D : Fin (L + 1) → Fin P → ℝ) : Matrix (Fin L) (Fin P) ℝ :=
  fun ℓ p => D ℓ.succ p - D ℓ.castSucc p

/-- `Λ̃_E`: the rows of `Λ̃` at the meeting-free gaps. -/
def lamTE (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ) (D : Fin (L + 1) → Fin P → ℝ) :
    Matrix {ℓ : Fin L // MeetingFree T S ℓ} (Fin P) ℝ :=
  fun ℓ p => lamT D ℓ.1 p

/-- `Q(S_n)` for `θ = (v, u)`. -/
noncomputable def Qp (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ) (D : Fin (L + 1) → Fin P → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (n : Fin (L + 1)) : ℝ :=
  ∑ i, (if T i ≤ S n then θ (Sum.inl i) else 0) + ∑ p, D n p * θ (Sum.inr p)

def injectiveStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ)
  (D : Fin (L + 1) → Fin P → ℝ),
  ((panelD T S D).rank = N + P ↔ Function.Injective (panelD T S D).mulVec) ∧
  (¬ Function.Injective (panelD T S D).mulVec → ∀ θ : Fin N ⊕ Fin P → ℝ, (∀ k, 0 < θ k) →
    ∃ θ' : Fin N ⊕ Fin P → ℝ, (∀ k, 0 < θ' k) ∧ θ' ≠ θ ∧
      (panelD T S D).mulVec θ' = (panelD T S D).mulVec θ)

def rankStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ)
  (D : Fin (L + 1) → Fin P → ℝ), StrictMono S → S 0 = 0 → (∀ i, 0 < T i) → D 0 = 0 →
  (Function.Injective (panelD T S D).mulVec ↔
    (∀ i, T i ≤ S (Fin.last L)) ∧
    (∀ (ℓ : Fin L) (i j : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
      S ℓ.castSucc < T j → T j ≤ S ℓ.succ → i = j) ∧
    Function.Injective (lamTE T S D).mulVec)

def inversionStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (S : Fin (L + 1) → ℝ)
  (D : Fin (L + 1) → Fin P → ℝ), StrictMono S → S 0 = 0 → (∀ i, 0 < T i) → D 0 = 0 →
  (∀ θ : Fin N ⊕ Fin P → ℝ,
    Qp T S D θ 0 = 0 ∧
    (∀ ℓ, (panelD T S D).mulVec θ ℓ = Qp T S D θ ℓ.succ) ∧
    (∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ}, (lamTE T S D).mulVec (fun p => θ (Sum.inr p)) ℓ =
      Qp T S D θ ℓ.1.succ - Qp T S D θ ℓ.1.castSucc) ∧
    (Function.Injective (lamTE T S D).mulVec → ∀ u : Fin P → ℝ,
      (∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ},
        (lamTE T S D).mulVec u ℓ = Qp T S D θ ℓ.1.succ - Qp T S D θ ℓ.1.castSucc) →
      u = fun p => θ (Sum.inr p)) ∧
    (∀ (ℓ : Fin L) (i : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
      (∀ j, S ℓ.castSucc < T j → T j ≤ S ℓ.succ → j = i) →
      θ (Sum.inl i) = Qp T S D θ ℓ.succ - Qp T S D θ ℓ.castSucc -
        ∑ p, lamT D ℓ p * θ (Sum.inr p))) ∧
  (Function.Injective (panelD T S D).mulVec → P ≤ Nat.card {ℓ : Fin L // MeetingFree T S ℓ})

def statement : Prop := injectiveStatement ∧ rankStatement ∧ inversionStatement

end Standalone.MaturityShapeRank

import Standalone.DiffusionMeetingRank
import Standalone.DiffusionMeetingPricing

/-! # Claim 046 (b)–(c): the inversion formulas, and the bond-curve term

* `inversionStatement`, (c): with `Q(S_0) = 0` and the panel rows `Q(S_ℓ)`, each meeting-free gap
  gives a row of `Λ_E u = (Q(S_ℓ) − Q(S_{ℓ−1}))_{ℓ ∈ E}`, whose solution is `u` when `Λ_E` is
  injective ((46.8)(iii)); and the meeting `T_i` alone in the gap `G_ℓ` has
  `v_i = Q(S_ℓ) − Q(S_{ℓ−1}) − Σ_p u_p λ_p(G_ℓ)`.
* `bondStatement`, (b): `A = ∫_a^b f(0, u) du = log(P(0, a)/P(0, b))`, so the futures quote gives
  `p` once the bond curve is known.
-/

namespace Standalone.DiffusionMeetingInversion
open Standalone.DiffusionMeetingRank Standalone.DiffusionMeetingGauss
  Standalone.DiffusionMeetingPricing

variable {N P L : ℕ}

/-- `Q(S_n) = Σ_{T_i ≤ S_n} v_i + Σ_p λ_p((0, S_n]) u_p` for `θ = (v, u)`. -/
noncomputable def Qp (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ) (S : Fin (L + 1) → ℝ)
    (θ : Fin N ⊕ Fin P → ℝ) (n : Fin (L + 1)) : ℝ :=
  ∑ i, (if T i ≤ S n then θ (Sum.inl i) else 0) +
    ∑ p, lam 0 (S n) (c p.castSucc) (c p.succ) * θ (Sum.inr p)

def inversionStatement : Prop := ∀ (N P L : ℕ) (T : Fin N → ℝ) (c : Fin (P + 1) → ℝ)
  (S : Fin (L + 1) → ℝ), StrictMono S → S 0 = 0 → (∀ i, 0 < T i) → ∀ θ : Fin N ⊕ Fin P → ℝ,
    Qp T c S θ 0 = 0 ∧
    (∀ ℓ, (panel T c S).mulVec θ ℓ = Qp T c S θ ℓ.succ) ∧
    (∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ}, (lamE T c S).mulVec (fun p => θ (Sum.inr p)) ℓ =
      Qp T c S θ ℓ.1.succ - Qp T c S θ ℓ.1.castSucc) ∧
    (Function.Injective (lamE T c S).mulVec → ∀ u : Fin P → ℝ,
      (∀ ℓ : {ℓ : Fin L // MeetingFree T S ℓ},
        (lamE T c S).mulVec u ℓ = Qp T c S θ ℓ.1.succ - Qp T c S θ ℓ.1.castSucc) →
      u = fun p => θ (Sum.inr p)) ∧
    (∀ (ℓ : Fin L) (i : Fin N), S ℓ.castSucc < T i → T i ≤ S ℓ.succ →
      (∀ j, S ℓ.castSucc < T j → T j ≤ S ℓ.succ → j = i) →
      θ (Sum.inl i) = Qp T c S θ ℓ.succ - Qp T c S θ ℓ.castSucc -
        ∑ p, lam (S ℓ.castSucc) (S ℓ.succ) (c p.castSucc) (c p.succ) * θ (Sum.inr p))

def bondStatement : Prop := ∀ (Ω : Type) (N : ℕ) (M : DiffModel Ω N) (a b : ℝ),
  Measurable M.f0 → (∃ C, ∀ s, |M.f0 s| ≤ C) → Aint M a b = Real.log (P0 M a / P0 M b)

def statement : Prop := inversionStatement ∧ bondStatement

end Standalone.DiffusionMeetingInversion

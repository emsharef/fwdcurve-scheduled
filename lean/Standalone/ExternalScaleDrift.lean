import Standalone.RecurrentLoadingDrift

/-! # Claim 031 (a), (b): the drift with a stochastic scale, pathwise

On a fixed path the scale of (31.1) is a function of time, `h s = ψ(Z_s(ω))`,
which is continuous and bounded by `K_ψ` because `Z` has continuous paths and
`ψ` is bounded and Lipschitz. The volatility is `h s · σ̃(s,T)` with `σ̃` Claim
030's (30.1), and `alpha031` is its HJM drift `σ(s,T) ∫_s^T σ(s,u) du`.

`ax01Statement` is (a)'s AX-01 identity, at every time and maturity, for any
value of the scale. `driftStatement` is (31.5) for any bounded Borel scale path:
with `P^h_t = ∫_0^t h(s)^2 w(s,t) w(s,t)^T ds` and
`Q^h_t = ∫_0^t h(s)^2 w(s,t) J̃(s,t) ds`, the drift integral
`∫_0^t α(s, t+x) ds` is `k(x, D(t)) · (P^h_t K(x, D(t)) + Q^h_t)`. With `h ≡ 1`
this is Claim 030's (30.8). The state equations (31.2)–(31.3), the stochastic
state `Ξ` and the diffusion part of (31.4) are not in this target.
-/

open Matrix
namespace Standalone.ExternalScaleDrift
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift

variable {p r : ℕ}

/-- The HJM drift of the scaled volatility `h s · σ̃(s,T)`. -/
noncomputable def alpha031 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (s T : ℝ) : ℝ :=
  (h s * sigma030 Tm u v M c b A s T) * ∫ y in s..T, h s * sigma030 Tm u v M c b A s y

noncomputable def P031 (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (t : ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  fun ab cd => ∫ s in (0:ℝ)..t, h s ^ 2 * (w030 Tm v M b A s t ab * w030 Tm v M b A s t cd)

noncomputable def Q031 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → ℝ) (t : ℝ) :
    Fin p × Fin r → ℝ :=
  fun ab => ∫ s in (0:ℝ)..t, h s ^ 2 * (w030 Tm v M b A s t ab * J030 Tm u v M c b A s t)

def ax01Statement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (h : ℝ → ℝ) (s T : ℝ),
  (∫ y in s..T, alpha031 Tm u v M c b A h s y) =
    (∫ y in s..T, h s * sigma030 Tm u v M c b A s y) ^ 2 / 2

def driftStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
  (h : ℝ → ℝ), Measurable h → (∃ C, ∀ s, |h s| ≤ C) → ∀ t x : ℝ, 0 ≤ t → 0 ≤ x →
  (∫ s in (0:ℝ)..t, alpha031 Tm u v M c b A h s (t + x)) =
    k030 u M c A x (dist030 Tm t) ⬝ᵥ
      (P031 Tm v M b A h t *ᵥ Kvec030 u M c A x (dist030 Tm t) + Q031 Tm u v M c b A h t)

def statement : Prop := ax01Statement ∧ driftStatement

end Standalone.ExternalScaleDrift

import Standalone.RecurrentLoadingAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Claim 030: AX-01 and the drift identity (30.8)

`alpha030` is the HJM drift `α(s,T) = σ(s,T) ∫_s^T σ(s,u) du` of (30.1).
`Kvec030 x D = ∫_0^x k(y, D) dy` is `K(x, D)` of (30.2), `J030 s t` is
`J(s,t) = ∫_s^t σ(s,u) du`, and `P030 t`, `Q030 t` are the deterministic states
`P_t = ∫_0^t w(s,t) w(s,t)^T ds` and `Q_t = ∫_0^t w(s,t) J(s,t) ds` of (30.8).

`ax01Statement` is (a)'s AX-01 identity for (30.1), at every time and maturity.
`driftStatement` is (30.8): for `t, x ≥ 0`, the drift integral
`∫_0^t α(s, t+x) ds` equals `k(x, D(t)) · (P_t K(x, D(t)) + Q_t)`. The state
equations (30.3)–(30.4) for `P` and `Q`, and the stochastic state `Ξ`, are not in
this target.
-/

open Matrix
namespace Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingAlgebra

variable {p r : ℕ}

noncomputable def alpha030 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s T : ℝ) : ℝ :=
  sigma030 Tm u v M c b A s T * ∫ y in s..T, sigma030 Tm u v M c b A s y

noncomputable def Kvec030 (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (x : ℝ) (D : Finset ℝ) : Fin p × Fin r → ℝ :=
  fun ab => ∫ y in (0:ℝ)..x, k030 u M c A y D ab

noncomputable def J030 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s t : ℝ) : ℝ :=
  ∫ y in s..t, sigma030 Tm u v M c b A s y

noncomputable def P030 (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  fun ab cd => ∫ s in (0:ℝ)..t, w030 Tm v M b A s t ab * w030 Tm v M b A s t cd

noncomputable def Q030 (Tm : Finset ℝ) (u v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) : Fin p × Fin r → ℝ :=
  fun ab => ∫ s in (0:ℝ)..t, w030 Tm v M b A s t ab * J030 Tm u v M c b A s t

def ax01Statement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (s T : ℝ),
  (∫ y in s..T, alpha030 Tm u v M c b A s y) =
    (∫ y in s..T, sigma030 Tm u v M c b A s y) ^ 2 / 2

def driftStatement : Prop := ∀ (p r : ℕ) (Tm : Finset ℝ) (u v : Fin p → ℝ)
  (M : Matrix (Fin p) (Fin p) ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t x : ℝ),
  0 ≤ t → 0 ≤ x →
  (∫ s in (0:ℝ)..t, alpha030 Tm u v M c b A s (t + x)) =
    k030 u M c A x (dist030 Tm t) ⬝ᵥ
      (P030 Tm v M b A t *ᵥ Kvec030 u M c A x (dist030 Tm t) + Q030 Tm u v M c b A t)

def statement : Prop := ax01Statement ∧ driftStatement

end Standalone.RecurrentLoadingDrift

import Standalone.ApproximationConstants
import Novel.RecurrentApproxBondProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Claim 053: the published constants of the approximation theorem (proof)

(a) is Claim 048's `meanSquareS`, cited. (e), `gauss_ineq`, follows the Cauchy–Schwarz shape of
Claim 048's `price_ineq` with the maximum `max(e^{−2X}, e^{−2X'})` in place of the sum and the
one-sided `−2μ + 4v ≤ E` in place of the two-sided bounds. (b)–(c) take the Gaussian laws of `X`,
`X̃` and `D = X − X̃` from `Novel.RecurrentApproxBondProof.laws`, and replace the `H`-uniform bounds
of `boundS` by the pointwise (53.6)–(53.7): `mu_pt`, `mud_pt`, `U_sq`, `Ud_sq`, from
`|α(s, u)| ≤ Ā²Λ²(u − s)` (`alpha_pt`) and `∫_t^T ∫_0^t (u − s) ds du = tT(T − t)/2`
(`int_lin`, `int_quad`). (d) is `B_{t,T} ≤ C_H` and `E_{t,T} ≤ Ā²Λ²H³` (`bounds`), the second from
`H³ − tH(H − t) − 4t(H − t)² = (H − 2t)²(H − t) + Ht²`.

Reused, not reproved: `meanSquareS`; `laws`, `second_moment_gauss`; `boundS_aux` (the pointwise
bounds on `U`), `abs_int_le`, `inner_meas`, `int_exp`, `int_pow4`; `sig_bound`, `S_bound`,
`vol_aux`; `alpha_ii`; `ii_of_bound`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxPriceBounds Standalone.RecurrentApproxBond
  Standalone.ZeroMeanReversionUpstreamBridge Standalone.ApproximationConstants
open Novel.RecurrentApproxEstimatesProof (sig_bound S_bound vol_aux)
open Novel.RecurrentApproxPriceBoundsProof (abs_int_le inner_meas boundS_aux int_exp int_pow4)
open Novel.RecurrentApproxMeanSquareProof (alpha_ii)
open Novel.MaturityShapeIdentitiesProof (ii_of_bound)
open Novel.RecurrentApproxBondProof (Xq laws second_moment_gauss)

namespace Novel.ApproximationConstantsProof

/-! ### (a) -/

theorem forwardS : forwardStatement := Novel.RecurrentApproxMeanSquareProof.meanSquareS

/-! ### (e) the Gaussian price lemma -/

/-- `(e^{-x} − e^{-y})² ≤ (x − y)² max(e^{-2x}, e^{-2y})`, by the mean value theorem. -/
lemma exp_diff_sq_max (x y : ℝ) :
    (rexp (-x) - rexp (-y)) ^ 2 ≤ (x - y) ^ 2 * max (rexp (-2 * x)) (rexp (-2 * y)) := by
  have key : ∀ x y : ℝ, x ≤ y → (rexp (-x) - rexp (-y)) ^ 2 ≤ (x - y) ^ 2 * rexp (-2 * x) := by
    intro x y hxy
    have h1 : rexp (-y) = rexp (-x) * rexp (-(y - x)) := by rw [← Real.exp_add]; ring_nf
    have h2 : 1 - (y - x) ≤ rexp (-(y - x)) := by linarith [Real.add_one_le_exp (-(y - x))]
    have h3 : rexp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hx := Real.exp_pos (-x)
    have e : rexp (-2 * x) = rexp (-x) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have a0 : 0 ≤ rexp (-x) - rexp (-y) := by rw [h1]; nlinarith
    have a1 : rexp (-x) - rexp (-y) ≤ (y - x) * rexp (-x) := by rw [h1]; nlinarith
    rw [e]
    calc (rexp (-x) - rexp (-y)) ^ 2 ≤ ((y - x) * rexp (-x)) ^ 2 := pow_le_pow_left₀ a0 a1 2
      _ = _ := by ring
  rcases le_total x y with h | h
  · exact (key x y h).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
  · calc _ = (rexp (-y) - rexp (-x)) ^ 2 := by ring
      _ ≤ (y - x) ^ 2 * rexp (-2 * y) := key y x h
      _ = (x - y) ^ 2 * rexp (-2 * y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)

/-- (53.5). -/
theorem gauss_ineq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X X' : Ω → ℝ} (hXm : Measurable X) (hX'm : Measurable X') {μ μ' m E : ℝ} {v v' w : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) P) (hX' : HasLaw X' (gaussianReal μ' v') P)
    (hD : HasLaw (fun ω => X ω - X' ω) (gaussianReal m w) P)
    (hE : -2 * μ + 4 * v ≤ E) (hE' : -2 * μ' + 4 * v' ≤ E) :
    ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂P ≤ √6 * rexp E * (m ^ 2 + w) := by
  set D : Ω → ℝ := fun ω => X ω - X' ω
  set M : Ω → ℝ := fun ω => max (rexp (-2 * X ω)) (rexp (-2 * X' ω))
  have mD : Measurable D := hXm.sub hX'm
  have mM : Measurable M := ((hXm.const_mul (-2)).exp).max ((hX'm.const_mul (-2)).exp)
  obtain ⟨i4, h4⟩ := int_pow4 hD
  obtain ⟨e1, v1⟩ := int_exp hX (-4)
  obtain ⟨e2, v2⟩ := int_exp hX' (-4)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => (Real.exp_pos _).le.trans (le_max_left _ _)
  -- `M² ≤ e^{-4X} + e^{-4X'}`
  have hM2 : ∀ ω, M ω ^ 2 ≤ rexp (-4 * X ω) + rexp (-4 * X' ω) := fun ω => by
    have a : rexp (-4 * X ω) = rexp (-2 * X ω) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have b : rexp (-4 * X' ω) = rexp (-2 * X' ω) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [a, b]
    rcases le_total (rexp (-2 * X ω)) (rexp (-2 * X' ω)) with hle | hle
    · simp only [M, max_eq_right hle]; nlinarith [sq_nonneg (rexp (-2 * X ω))]
    · simp only [M, max_eq_left hle]; nlinarith [sq_nonneg (rexp (-2 * X' ω))]
  have iM2 : Integrable (fun ω => M ω ^ 2) P :=
    (e1.add e2).mono' (mM.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hM2 ω)
  have LD : MemLp (fun ω => D ω ^ 2) (ENNReal.ofReal 2) P := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq (mD.pow_const 2).aestronglyMeasurable]
    simpa [← pow_mul] using i4
  have LM : MemLp M (ENNReal.ofReal 2) P := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq mM.aestronglyMeasurable]; exact iM2
  have iDM : Integrable (fun ω => D ω ^ 2 * M ω) P :=
    ((i4.add iM2).div_const 2).mono' ((mD.pow_const 2).mul mM).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hM0 ω))]
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (D ω ^ 2 - M ω)])
  -- pointwise, then Cauchy–Schwarz
  have step1 : ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂P ≤ ∫ ω, D ω ^ 2 * M ω ∂P :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) iDM
      (Filter.Eventually.of_forall fun ω => exp_diff_sq_max _ _)
  have step2 := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => sq_nonneg (D ω)) (Filter.Eventually.of_forall hM0) LD LM
  have eD : ∫ ω, (D ω ^ 2) ^ (2:ℝ) ∂P = ∫ ω, D ω ^ 4 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only; rw [Real.rpow_two, ← pow_mul])
  have eM : ∫ ω, M ω ^ (2:ℝ) ∂P ≤ 2 * rexp (2 * E) := by
    simp_rw [Real.rpow_two]
    refine (integral_mono iM2 (e1.add e2) hM2).trans ?_
    simp only [Pi.add_apply]
    rw [integral_add e1 e2, v1, v2]
    have k1 : μ * -4 + v * (-4) ^ 2 / 2 ≤ 2 * E := by nlinarith
    have k2 : μ' * -4 + v' * (-4) ^ 2 / 2 ≤ 2 * E := by nlinarith
    linarith [Real.exp_le_exp.2 k1, Real.exp_le_exp.2 k2]
  rw [eD] at step2
  have hmw : 0 ≤ m ^ 2 + w := by positivity
  have r1 : (∫ ω, D ω ^ 4 ∂P) ^ (1 / (2:ℝ)) ≤ √3 * (m ^ 2 + w) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq hmw, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have r2 : (∫ ω, M ω ^ (2:ℝ) ∂P) ^ (1 / (2:ℝ)) ≤ √2 * rexp E := by
    rw [← Real.sqrt_eq_rpow]
    have : 2 * rexp (2 * E) = (√2 * rexp E) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul]; norm_num
    rw [this] at eM
    exact (Real.sqrt_le_sqrt eM).trans (Real.sqrt_sq (by positivity)).le
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ (√3 * (m ^ 2 + w)) * (√2 * rexp E) :=
        mul_le_mul r1 r2 (Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _)
          (by positivity)
    _ = _ := by rw [h6]; ring

theorem gaussS : gaussStatement := by
  intro Ω _ P hP X X' hXm hX'm μ μ' m E v v' w hX hX' hD hE hE'
  exact gauss_ineq hXm hX'm hX hX' hD hE hE'

/-! ### (53.6)–(53.7), the pointwise deterministic bounds -/

lemma int_lin (K u t : ℝ) : ∫ s in (0:ℝ)..t, K * (u - s) = K * (u * t - t ^ 2 / 2) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma int_quad (K t T : ℝ) : ∫ u in t..T, K * (u * t - t ^ 2 / 2) = K * (t * T * (T - t) / 2) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (intervalIntegral.intervalIntegrable_id.mul_const _) intervalIntegrable_const,
    intervalIntegral.integral_mul_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma lin_ii (K u x y : ℝ) : IntervalIntegrable (fun s => K * (u - s)) volume x y :=
  (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _

lemma quad_ii (K t x y : ℝ) : IntervalIntegrable (fun u => K * (u * t - t ^ 2 / 2)) volume x y :=
  (continuous_const.mul ((continuous_id.mul continuous_const).sub continuous_const)).intervalIntegrable
    _ _

/-- A bound `C` on `[0, t]` gives `∫_0^t g² ≤ C² t`. -/
lemma sq_int_le {t C : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ) (hg : ∀ s ∈ Icc 0 t, |g s| ≤ C) :
    ∫ s in (0:ℝ)..t, g s ^ 2 ≤ C ^ 2 * t := by
  have := abs_int_le ht (f := fun s => g s ^ 2) (C := C ^ 2) fun s hs => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hg s hs) 2
  rw [sub_zero] at this
  exact (le_abs_self _).trans this

section Bounds
variable {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam : ℝ → ℝ} {H Λ ε Abar : ℝ}
  (h : Hyp048 Tm a a' lam H Λ ε Abar)
include h

/-- `|α(s, u)| ≤ Ā²Λ²(u − s)` for `0 ≤ s ≤ u ≤ H`. -/
lemma alpha_pt (b₀ : ℕ → ℝ) (hb : b₀ = a ∨ b₀ = a') {s u : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u)
    (huH : u ≤ H) : |alpha048 Tm b₀ lam s u| ≤ Abar ^ 2 * Λ ^ 2 * (u - s) := by
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, hs0.trans (hsu.trans huH)⟩)
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have h1 := sig_bound h hsu (by linarith)
  have h2 := S_bound h hs0 hsu huH
  have e1 : |sig048 Tm b₀ lam s u| ≤ Abar * Λ := by
    rcases hb with rfl | rfl; exacts [h1.1, h1.2.1]
  have e2 : |S048 Tm b₀ lam s u| ≤ Abar * Λ * (u - s) := by
    rcases hb with rfl | rfl; exacts [h2.1, h2.2.1]
  rw [alpha048, abs_mul]
  calc _ ≤ Abar * Λ * (Abar * Λ * (u - s)) := mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg hA0 hl0)
    _ = _ := by ring

/-- `|∫_0^t α(s, u) ds| ≤ Ā²Λ²(ut − t²/2)` for `0 ≤ t ≤ u ≤ H`. -/
lemma inner_pt (b₀ : ℕ → ℝ) (hb : b₀ = a ∨ b₀ = a') {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (huH : u ≤ H) :
    |∫ s in (0:ℝ)..t, alpha048 Tm b₀ lam s u| ≤ Abar ^ 2 * Λ ^ 2 * (u * t - t ^ 2 / 2) := by
  have := intervalIntegral.norm_integral_le_of_norm_le (f := fun s => alpha048 Tm b₀ lam s u)
    ht (Filter.Eventually.of_forall fun s hs => alpha_pt h b₀ hb hs.1.le (hs.2.trans htu) huH)
    (lin_ii (Abar ^ 2 * Λ ^ 2) u 0 t)
  rwa [Real.norm_eq_abs, int_lin] at this

/-- `|∫_0^t (α − α̃)(s, u) ds| ≤ 2εĀΛ²(ut − t²/2)` for `0 ≤ t ≤ u ≤ H`. -/
lemma inner_diff_pt {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (huH : u ≤ H) :
    |∫ s in (0:ℝ)..t, (alpha048 Tm a lam s u - alpha048 Tm a' lam s u)| ≤
      2 * ε * Abar * Λ ^ 2 * (u * t - t ^ 2 / 2) := by
  have := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun s => alpha048 Tm a lam s u - alpha048 Tm a' lam s u) ht
    (Filter.Eventually.of_forall fun s hs => (vol_aux h hs.1.le (hs.2.trans htu) huH).2)
    (lin_ii (2 * ε * Abar * Λ ^ 2) u 0 t)
  rwa [Real.norm_eq_abs, int_lin] at this

/-- (53.6), first half: `|μ| ≤ ½Ā²Λ² tT(T − t)`. -/
lemma mu_pt (b₀ : ℕ → ℝ) (hb : b₀ = a ∨ b₀ = a') {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hTH : T ≤ H) : |mu048 Tm b₀ lam t T| ≤ Abar ^ 2 * Λ ^ 2 * (t * T * (T - t) / 2) := by
  have := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun u => ∫ s in (0:ℝ)..t, alpha048 Tm b₀ lam s u) htT
    (Filter.Eventually.of_forall fun u hu => inner_pt h b₀ hb ht hu.1.le (hu.2.trans hTH))
    (quad_ii (Abar ^ 2 * Λ ^ 2) t t T)
  rwa [Real.norm_eq_abs, int_quad] at this

/-- (53.6), second half: `|μ − μ̃| ≤ εĀΛ² tT(T − t)`. -/
lemma mud_pt {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    |mu048 Tm a lam t T - mu048 Tm a' lam t T| ≤ ε * Abar * Λ ^ 2 * (t * T * (T - t)) := by
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (htT.trans hTH)⟩)
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have ii : ∀ (b₀ : ℕ → ℝ), (b₀ = a ∨ b₀ = a') →
      IntervalIntegrable (fun u => ∫ s in (0:ℝ)..t, alpha048 Tm b₀ lam s u) volume t T :=
    fun b₀ hb => ii_of_bound (inner_meas Tm b₀ h.1 t) htT (M := Abar ^ 2 * Λ ^ 2 * (T * t))
      fun u hu => (inner_pt h b₀ hb ht hu.1 (hu.2.trans hTH)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith [hu.2]) (by positivity))
  rw [mu048, mu048, ← intervalIntegral.integral_sub (ii a (Or.inl rfl)) (ii a' (Or.inr rfl))]
  have := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun u => (∫ s in (0:ℝ)..t, alpha048 Tm a lam s u) -
      ∫ s in (0:ℝ)..t, alpha048 Tm a' lam s u) htT
    (Filter.Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs, ← intervalIntegral.integral_sub
        (alpha_ii h a (Or.inl rfl) ht hu.1.le (hu.2.trans hTH) hA0 hl0)
        (alpha_ii h a' (Or.inr rfl) ht hu.1.le (hu.2.trans hTH) hA0 hl0)]
      exact inner_diff_pt h ht hu.1.le (hu.2.trans hTH))
    (quad_ii (2 * ε * Abar * Λ ^ 2) t t T)
  rw [Real.norm_eq_abs, int_quad] at this
  linarith

/-- (53.7): `∫_0^t U², ∫_0^t Ũ² ≤ Ā²Λ² t(T − t)²` and `∫_0^t (U − Ũ)² ≤ ε²Λ² t(T − t)²`. -/
lemma U_sq {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    ∫ s in (0:ℝ)..t, U048 Tm a lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * (t * (T - t) ^ 2) ∧
    ∫ s in (0:ℝ)..t, U048 Tm a' lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * (t * (T - t) ^ 2) ∧
    ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2 ≤
      ε ^ 2 * Λ ^ 2 * (t * (T - t) ^ 2) := by
  have hU := (boundS_aux h ht htT hTH).1
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_int_le ht _ fun s hs => (hU s hs).1).trans (le_of_eq ?_); ring
  · refine (sq_int_le ht _ fun s hs => (hU s hs).2.1).trans (le_of_eq ?_); ring
  · refine (sq_int_le ht _ fun s hs => (hU s hs).2.2).trans (le_of_eq ?_); ring

end Bounds

/-! ### (b) and (c) -/

lemma core {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k : Fin S.m)
    (hBr : IsPreBrownianReal (S.B k) S.μ) {r : ℕ} {c b : Fin r → ℝ}
    {A : Matrix (Fin r) (Fin r) ℝ} {Tm : Finset ℝ} {a a' : ℕ → ℝ} {H Λ ε Abar : ℝ}
    (h : Hyp048 Tm a a' (shape030 c b A) H Λ ε Abar) {f0 : ℝ → ℝ} {F0 : ℝ} (hf0 : Measurable f0)
    (hF0 : ∀ x ∈ Icc 0 H, |f0 x| ≤ F0) (t : ℝ≥0) {T : ℝ} (htT : (t:ℝ) ≤ T) (hTH : T ≤ H) :
    ∫ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) - Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2
        ∂S.μ ≤ ε ^ 2 * B053 Λ Abar t T ∧
    ∫ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 ∂S.μ ≤
      √6 * rexp (2 * F0 * (T - t) + E053 Λ Abar t T) * (ε ^ 2 * B053 Λ Abar t T) := by
  have := S.isProbabilityMeasure
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have hH : 0 ≤ H := ht.trans (htT.trans hTH)
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, hH⟩)
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hF00 : 0 ≤ F0 := (abs_nonneg _).trans (hF0 0 ⟨le_rfl, hH⟩)
  set lam := shape030 c b A
  obtain ⟨hXm, lawX, lawD, hP⟩ := laws S k hBr h hf0 hF0 t htT hTH
  have hmu := mu_pt h a (Or.inl rfl) ht htT hTH
  have hmu' := mu_pt h a' (Or.inr rfl) ht htT hTH
  have hmud := mud_pt h ht htT hTH
  obtain ⟨hUa, hUa', hUd⟩ := U_sq h ht htT hTH
  set X := Xq S k t Tm a c b A T
  set X' := Xq S k t Tm a' c b A T
  set F := ∫ u in (t:ℝ)..T, f0 u
  set w : ℝ := ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2
  have hw0 : 0 ≤ w := intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _
  set m := mu048 Tm a lam t T - mu048 Tm a' lam t T
  have hED : ∫ ω, (X ω - X' ω) ^ 2 ∂S.μ = m ^ 2 + w := by
    rw [show (∫ ω, (X ω - X' ω) ^ 2 ∂S.μ) = S.μ[(fun x : ℝ => x ^ 2) ∘ fun ω => X ω - X' ω] from rfl,
      lawD.integral_comp (by fun_prop), second_moment_gauss, Real.coe_toNNReal _ hw0]
  -- (b): `E D² = (μ − μ̃)² + ∫(U − Ũ)² ≤ ε² B_{t,T}`
  have hmw : m ^ 2 + w ≤ ε ^ 2 * B053 Λ Abar t T := by
    have : m ^ 2 ≤ (ε * Abar * Λ ^ 2 * (t * T * (T - t))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hmud 2
    unfold B053
    nlinarith
  refine ⟨?_, ?_⟩
  · have e : ∀ ω, (Real.log (P048 S k f0 Tm a c b A t T ω) -
        Real.log (P048 S k f0 Tm a' c b A t T ω)) ^ 2 = (X ω - X' ω) ^ 2 := fun ω => by
      rw [hP a (Or.inl rfl), hP a' (Or.inr rfl), ← Real.exp_add, ← Real.exp_add, Real.log_exp,
        Real.log_exp]
      ring
    simp only [e, hED]
    exact hmw
  · -- (c)
    have e : ∀ ω, (P048 S k f0 Tm a c b A t T ω - P048 S k f0 Tm a' c b A t T ω) ^ 2 =
        rexp (-F) ^ 2 * (rexp (-X ω) - rexp (-X' ω)) ^ 2 := fun ω => by
      rw [hP a (Or.inl rfl), hP a' (Or.inr rfl)]; ring
    simp only [e]
    rw [integral_const_mul]
    have hv : ∀ (x C : ℝ), x ≤ C → 0 ≤ C → ((x.toNNReal : ℝ≥0) : ℝ) ≤ C := fun x C hx hC => by
      rw [Real.coe_toNNReal']; exact max_le hx hC
    have hC0 : 0 ≤ Abar ^ 2 * Λ ^ 2 * (t * (T - t) ^ 2) := by positivity
    have hE : ∀ (μ₀ : ℝ) (v₀ : ℝ≥0), |μ₀| ≤ Abar ^ 2 * Λ ^ 2 * (t * T * (T - t) / 2) →
        (v₀ : ℝ) ≤ Abar ^ 2 * Λ ^ 2 * (t * (T - t) ^ 2) → -2 * μ₀ + 4 * v₀ ≤ E053 Λ Abar t T :=
      fun μ₀ v₀ h1 h2 => by
        unfold E053
        nlinarith [neg_abs_le μ₀]
    have hpr := gauss_ineq (hXm a) (hXm a') (lawX a) (lawX a') lawD
      (hE _ _ hmu (hv _ _ hUa hC0)) (hE _ _ hmu' (hv _ _ hUa' hC0))
    rw [Real.coe_toNNReal _ hw0] at hpr
    have hF : |F| ≤ F0 * (T - t) :=
      abs_int_le htT (f := f0) (C := F0) fun u hu => hF0 u ⟨ht.trans hu.1, hu.2.trans hTH⟩
    have hexp : rexp (-F) ^ 2 ≤ rexp (2 * F0 * (T - t)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have := neg_abs_le F
      push_cast; nlinarith
    have hI0 : 0 ≤ ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂S.μ :=
      integral_nonneg fun _ => sq_nonneg _
    calc rexp (-F) ^ 2 * ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂S.μ
        ≤ rexp (2 * F0 * (T - t)) * (√6 * rexp (E053 Λ Abar t T) * (m ^ 2 + w)) :=
          mul_le_mul hexp hpr hI0 (Real.exp_pos _).le
      _ ≤ rexp (2 * F0 * (T - t)) * (√6 * rexp (E053 Λ Abar t T) * (ε ^ 2 * B053 Λ Abar t T)) := by
          gcongr
      _ = _ := by rw [Real.exp_add]; ring

theorem pointLogS : pointLogStatement := by
  intro Ω _ S k hBr r c b A Tm a a' H Λ ε Abar h f0 F0 hf0 hF0 t T htT hTH
  exact (core S k hBr h hf0 hF0 t htT hTH).1

theorem pointPriceS : pointPriceStatement := by
  intro Ω _ S k hBr r c b A Tm a a' H Λ ε Abar h f0 F0 hf0 hF0 t T htT hTH
  exact (core S k hBr h hf0 hF0 t htT hTH).2

/-! ### (d) -/

/-- `B_{t,T} ≤ C_H` and `E_{t,T} ≤ Ā²Λ²H³` for `0 ≤ t ≤ T ≤ H`. -/
lemma bounds (Λ Abar H t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    B053 Λ Abar t T ≤ C053 Λ Abar H ∧ E053 Λ Abar t T ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 := by
  have hT : 0 ≤ T := ht.trans htT
  have hTt : 0 ≤ T - t := sub_nonneg.2 htT
  have hHt : T - t ≤ H - t := by linarith
  -- `t(T − t)² ≤ t(H − t)² ≤ 4H³/27`
  have b1 : t * (T - t) ^ 2 ≤ 4 / 27 * H ^ 3 := by
    have : t * (T - t) ^ 2 ≤ t * (H - t) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hTt hHt 2) ht
    nlinarith [mul_nonneg (sq_nonneg (H - 3 * t)) (by linarith : (0:ℝ) ≤ 4 * H - 3 * t)]
  -- `t²T²(T − t)² ≤ T⁶/16 ≤ H⁶/16`
  have b2 : t ^ 2 * T ^ 2 * (T - t) ^ 2 ≤ H ^ 6 / 16 := by
    have q0 : 0 ≤ t * (T - t) := mul_nonneg ht hTt
    have q1 : t * (T - t) ≤ T ^ 2 / 4 := by nlinarith [sq_nonneg (T - 2 * t)]
    have q2 : (t * (T - t)) ^ 2 ≤ (T ^ 2 / 4) ^ 2 := pow_le_pow_left₀ q0 q1 2
    have q3 : T ^ 6 ≤ H ^ 6 := pow_le_pow_left₀ hT hTH 6
    calc t ^ 2 * T ^ 2 * (T - t) ^ 2 = T ^ 2 * (t * (T - t)) ^ 2 := by ring
      _ ≤ T ^ 2 * (T ^ 2 / 4) ^ 2 := mul_le_mul_of_nonneg_left q2 (sq_nonneg _)
      _ = T ^ 6 / 16 := by ring
      _ ≤ H ^ 6 / 16 := by linarith
  -- `tT(T − t) + 4t(T − t)² ≤ tH(H − t) + 4t(H − t)² ≤ H³`
  have b3 : t * T * (T - t) + 4 * t * (T - t) ^ 2 ≤ H ^ 3 := by
    have c1 : t * T * (T - t) ≤ t * H * (H - t) := by
      have : T * (T - t) ≤ H * (H - t) := mul_le_mul hTH hHt hTt (hT.trans hTH)
      nlinarith
    have c2 : 4 * t * (T - t) ^ 2 ≤ 4 * t * (H - t) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hTt hHt 2) (by linarith)
    have htH : t ≤ H := htT.trans hTH
    nlinarith [mul_nonneg (sq_nonneg (H - 2 * t)) (sub_nonneg.2 htH),
      mul_nonneg (ht.trans htH) (sq_nonneg t)]
  refine ⟨?_, ?_⟩
  · unfold B053 C053
    have e1 : Λ ^ 2 * t * (T - t) ^ 2 ≤ 4 / 27 * Λ ^ 2 * H ^ 3 := by
      have := mul_le_mul_of_nonneg_left b1 (sq_nonneg Λ); linarith
    have e2 : Abar ^ 2 * Λ ^ 4 * t ^ 2 * T ^ 2 * (T - t) ^ 2 ≤ 1 / 16 * Abar ^ 2 * Λ ^ 4 * H ^ 6 := by
      have := mul_le_mul_of_nonneg_left b2 (by positivity : (0:ℝ) ≤ Abar ^ 2 * Λ ^ 4); linarith
    linarith
  · unfold E053
    have := mul_le_mul_of_nonneg_left b3 (by positivity : (0:ℝ) ≤ Abar ^ 2 * Λ ^ 2)
    linarith

theorem uniformS : uniformStatement := by
  refine ⟨bounds, ?_⟩
  intro Ω _ S k hBr r c b A Tm a a' H Λ ε Abar h f0 F0 hf0 hF0 t T htT hTH
  have ht : (0:ℝ) ≤ t := t.coe_nonneg
  have hH : 0 ≤ H := ht.trans (htT.trans hTH)
  have hF00 : 0 ≤ F0 := (abs_nonneg _).trans (hF0 0 ⟨le_rfl, hH⟩)
  obtain ⟨hB, hE⟩ := bounds Λ Abar H t T ht htT hTH
  obtain ⟨hlog, hprice⟩ := core S k hBr h hf0 hF0 t htT hTH
  have hB0 : 0 ≤ B053 Λ Abar t T := by
    unfold B053
    have : 0 ≤ T - t := sub_nonneg.2 htT
    positivity
  refine ⟨hlog.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg ε)), hprice.trans ?_⟩
  have harg : 2 * F0 * (T - t) + E053 Λ Abar t T ≤ 2 * H * F0 + Abar ^ 2 * Λ ^ 2 * H ^ 3 := by
    have : F0 * (T - t) ≤ F0 * H := mul_le_mul_of_nonneg_left (by linarith) hF00
    linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 harg) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_left hB (sq_nonneg ε)) (mul_nonneg (sq_nonneg ε) hB0) (by positivity)

theorem approximationConstants : Standalone.ApproximationConstants.statement :=
  ⟨forwardS, gaussS, pointLogS, pointPriceS, uniformS⟩

end Novel.ApproximationConstantsProof

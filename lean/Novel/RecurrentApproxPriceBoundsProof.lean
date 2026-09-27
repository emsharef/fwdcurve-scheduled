import Standalone.RecurrentApproxPriceBounds
import Novel.RecurrentApproxMeanSquareProof
import Mathlib.Probability.Moments.MGFAnalytic

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentApproxEstimates
  Standalone.RecurrentApproxPriceBounds
open Novel.MaturityShapeIdentitiesProof (meas_param ii_of_bound)
open Novel.RecurrentApproxEstimatesProof
open Novel.RecurrentApproxMeanSquareProof (alpha_ii)
namespace Novel.RecurrentApproxPriceBoundsProof

/-- `α` is jointly measurable in `(s, u)`. -/
lemma alpha_meas2 (Tm : Finset ℝ) (b : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) :
    Measurable (Function.uncurry fun s u => alpha048 Tm b lam s u) := by
  have hS : Measurable fun p : ℝ × ℝ => S048 Tm b lam p.1 p.2 :=
    meas_param measurable_fst measurable_snd (K := fun p x => sig048 Tm b lam p.1 x)
      ((sig_meas Tm b hlam).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (sig_meas Tm b hlam).mul hS

/-- The inner drift integral `u ↦ ∫_0^t α(s, u) ds` is measurable. -/
lemma inner_meas (Tm : Finset ℝ) (b : ℕ → ℝ) {lam : ℝ → ℝ} (hlam : Measurable lam) (t : ℝ) :
    Measurable fun u => ∫ s in (0:ℝ)..t, alpha048 Tm b lam s u :=
  meas_param measurable_const measurable_const (K := fun u s => alpha048 Tm b lam s u)
    ((alpha_meas2 Tm b hlam).comp (measurable_snd.prodMk measurable_fst))

/-- A bound on `(a, b]` bounds the interval integral over `[a, b]`. -/
lemma abs_int_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Icc a b, |f x| ≤ C) :
    |∫ x in a..b, f x| ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := f) (C := C)
    fun x hx => by rw [uIoc_of_le hab] at hx; exact h x (Ioc_subset_Icc_self hx)
  rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this

section
variable {Tm : Finset ℝ} {a a' : ℕ → ℝ} {lam : ℝ → ℝ} {H Λ ε Abar : ℝ}
  (h : Hyp048 Tm a a' lam H Λ ε Abar)
include h

theorem boundS_aux {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hTH : T ≤ H) :
    (∀ s ∈ Set.Icc 0 t, |U048 Tm a lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a' lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a lam t T s - U048 Tm a' lam t T s| ≤ ε * Λ * (T - t)) ∧
    ∫ s in (0:ℝ)..t, U048 Tm a lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 ∧
    ∫ s in (0:ℝ)..t, U048 Tm a' lam t T s ^ 2 ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 ∧
    |mu048 Tm a lam t T| ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 / 2 ∧
    |mu048 Tm a' lam t T| ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 / 2 ∧
    |mu048 Tm a lam t T - mu048 Tm a' lam t T| ≤ ε * Abar * Λ ^ 2 * H ^ 3 / 2 ∧
    ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2 ≤ ε ^ 2 * Λ ^ 2 * H ^ 3 ∧
    (mu048 Tm a lam t T - mu048 Tm a' lam t T) ^ 2 +
        ∫ s in (0:ℝ)..t, (U048 Tm a lam t T s - U048 Tm a' lam t T s) ^ 2 ≤
      ε ^ 2 * (Λ ^ 2 * H ^ 3 + Abar ^ 2 * Λ ^ 4 * H ^ 6 / 4) := by
  have hl0 : 0 ≤ Λ := (abs_nonneg _).trans (h.2.1 0 ⟨le_rfl, ht.trans (htT.trans hTH)⟩)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).1
  have hA0 : 0 ≤ Abar := (abs_nonneg _).trans (h.2.2 0 (Nat.zero_le _)).2.1
  have hH : 0 ≤ H := ht.trans (htT.trans hTH)
  have htq : t * (T - t) ≤ H ^ 2 / 4 := by nlinarith [sq_nonneg (T - 2 * t)]
  have htq2 : t * (T - t) ^ 2 ≤ H ^ 3 := by
    have : (T - t) ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc t * (T - t) ^ 2 ≤ H * H ^ 2 := mul_le_mul (by linarith) this (sq_nonneg _) hH
      _ = H ^ 3 := by ring
  -- the integrand `U`
  have hU : ∀ s ∈ Icc 0 t, |U048 Tm a lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a' lam t T s| ≤ Abar * Λ * (T - t) ∧
      |U048 Tm a lam t T s - U048 Tm a' lam t T s| ≤ ε * Λ * (T - t) := fun s hs => by
    have hb : ∀ u ∈ Icc t T, |sig048 Tm a lam s u| ≤ Abar * Λ ∧ |sig048 Tm a' lam s u| ≤ Abar * Λ ∧
        |sig048 Tm a lam s u - sig048 Tm a' lam s u| ≤ ε * Λ := fun u hu =>
      sig_bound h (hs.2.trans hu.1) (by linarith [hs.1, hu.2])
    refine ⟨abs_int_le htT fun u hu => (hb u hu).1, abs_int_le htT fun u hu => (hb u hu).2.1, ?_⟩
    rw [U048, U048, ← intervalIntegral.integral_sub (sig_ii h a s t T htT fun u hu => (hb u hu).1)
      (sig_ii h a' s t T htT fun u hu => (hb u hu).2.1)]
    exact abs_int_le htT fun u hu => (hb u hu).2.2
  have hsq : ∀ (g : ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ s ∈ Icc 0 t, |g s| ≤ C) →
      ∫ s in (0:ℝ)..t, g s ^ 2 ≤ C ^ 2 * t := fun g C hC hg => by
    have := abs_int_le ht (f := fun s => g s ^ 2) (C := C ^ 2) fun s hs => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hg s hs) 2
    rw [sub_zero] at this
    exact (le_abs_self _).trans this
  have hUa := hsq _ _ (by nlinarith [mul_nonneg hA0 hl0]) fun s hs => (hU s hs).1
  have hUa' := hsq _ _ (by nlinarith [mul_nonneg hA0 hl0]) fun s hs => (hU s hs).2.1
  have hUd := hsq _ _ (by nlinarith [mul_nonneg hε0 hl0]) fun s hs => (hU s hs).2.2
  have c1 : (Abar * Λ * (T - t)) ^ 2 * t ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 := by
    have := mul_le_mul_of_nonneg_left htq2 (mul_nonneg (sq_nonneg Abar) (sq_nonneg Λ))
    nlinarith
  have c2 : (ε * Λ * (T - t)) ^ 2 * t ≤ ε ^ 2 * Λ ^ 2 * H ^ 3 := by
    have := mul_le_mul_of_nonneg_left htq2 (mul_nonneg (sq_nonneg ε) (sq_nonneg Λ))
    nlinarith
  -- the mean `μ`
  have hα : ∀ (b : ℕ → ℝ), (b = a ∨ b = a') → ∀ u ∈ Icc t T,
      |∫ s in (0:ℝ)..t, alpha048 Tm b lam s u| ≤ Abar ^ 2 * Λ ^ 2 * H * t := fun b hb u hu => by
    have := abs_int_le ht (f := fun s => alpha048 Tm b lam s u) (C := Abar ^ 2 * Λ ^ 2 * H)
      fun s hs => by
        have h1 := sig_bound h (hs.2.trans hu.1) (by linarith [hs.1, hu.2])
        have h2 := S_bound h hs.1 (hs.2.trans hu.1) (hu.2.trans hTH)
        have e1 : |sig048 Tm b lam s u| ≤ Abar * Λ := by
          rcases hb with rfl | rfl; exacts [h1.1, h1.2.1]
        have e2 : |S048 Tm b lam s u| ≤ Abar * Λ * (u - s) := by
          rcases hb with rfl | rfl; exacts [h2.1, h2.2.1]
        rw [alpha048, abs_mul]
        calc _ ≤ Abar * Λ * (Abar * Λ * (u - s)) :=
              mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg hA0 hl0)
          _ ≤ Abar * Λ * (Abar * Λ * H) := by
              gcongr; linarith [hs.1, hu.2]
          _ = _ := by ring
    rwa [sub_zero] at this
  have hmu : ∀ (b : ℕ → ℝ), (b = a ∨ b = a') → |mu048 Tm b lam t T| ≤ Abar ^ 2 * Λ ^ 2 * H ^ 3 / 2 :=
    fun b hb => by
      refine (abs_int_le htT (hα b hb)).trans ?_
      have : Abar ^ 2 * Λ ^ 2 * H * (t * (T - t)) ≤ Abar ^ 2 * Λ ^ 2 * H * (H ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left htq (by positivity)
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg Abar) (sq_nonneg Λ)) (pow_nonneg hH 3)]
  have hmud : |mu048 Tm a lam t T - mu048 Tm a' lam t T| ≤ ε * Abar * Λ ^ 2 * H ^ 3 / 2 := by
    have ii : ∀ (b : ℕ → ℝ), (b = a ∨ b = a') →
        IntervalIntegrable (fun u => ∫ s in (0:ℝ)..t, alpha048 Tm b lam s u) volume t T :=
      fun b hb => ii_of_bound (inner_meas Tm b h.1 t) htT (hα b hb)
    rw [mu048, mu048, ← intervalIntegral.integral_sub (ii a (Or.inl rfl)) (ii a' (Or.inr rfl))]
    refine (abs_int_le htT (C := 2 * ε * Abar * Λ ^ 2 * H * t) fun u hu => ?_).trans ?_
    · rw [← intervalIntegral.integral_sub (alpha_ii h a (Or.inl rfl) ht hu.1 (hu.2.trans hTH) hA0 hl0)
        (alpha_ii h a' (Or.inr rfl) ht hu.1 (hu.2.trans hTH) hA0 hl0)]
      have := abs_int_le ht (f := fun s => alpha048 Tm a lam s u - alpha048 Tm a' lam s u)
        (C := 2 * ε * Abar * Λ ^ 2 * H) fun s hs => by
          refine (vol_aux h hs.1 (hs.2.trans hu.1) (hu.2.trans hTH)).2.trans ?_
          exact mul_le_mul_of_nonneg_left (by linarith [hs.1, hu.2]) (by positivity)
      rwa [sub_zero] at this
    · have : 2 * ε * Abar * Λ ^ 2 * H * (t * (T - t)) ≤ 2 * ε * Abar * Λ ^ 2 * H * (H ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left htq (by positivity)
      nlinarith
  refine ⟨hU, hUa.trans c1, hUa'.trans c1, hmu a (Or.inl rfl), hmu a' (Or.inr rfl), hmud,
    hUd.trans c2, ?_⟩
  have : (mu048 Tm a lam t T - mu048 Tm a' lam t T) ^ 2 ≤ (ε * Abar * Λ ^ 2 * H ^ 3 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hmud 2
  nlinarith [hUd.trans c2]

end

lemma boundS : boundStatement := fun _ _ _ _ _ _ _ _ h _ _ ht htT hTH => boundS_aux h ht htT hTH

section
variable (m v : ℝ)

lemma hd_E (t : ℝ) : HasDerivAt (fun t => rexp (m * t + v * t ^ 2 / 2))
    ((m + v * t) * rexp (m * t + v * t ^ 2 / 2)) t := by
  have h : HasDerivAt (fun t => m * t + v * t ^ 2 / 2) (m + v * t) t := by
    have := ((hasDerivAt_id t).const_mul m).add (((hasDerivAt_pow 2 t).const_mul v).div_const 2)
    convert this using 1
    · funext x; simp
    · simp; ring
  simpa [mul_comm] using h.exp

lemma deriv_PE {P P' : ℝ → ℝ} (hP : ∀ t, HasDerivAt P (P' t) t) :
    deriv (fun t => P t * rexp (m * t + v * t ^ 2 / 2)) =
      fun t => (P' t + (m + v * t) * P t) * rexp (m * t + v * t ^ 2 / 2) := by
  funext t
  refine ((hP t).mul (hd_E m v t)).deriv.trans ?_
  ring

end

/-- The fourth moment of `N(m, v)`. -/
lemma fourth_moment (m : ℝ) (v : ℝ≥0) : ∫ x, x ^ 4 ∂gaussianReal m v = m ^ 4 + 6 * m ^ 2 * v + 3 * v ^ 2 := by
  have h0 : (0:ℝ) ∈ interior (integrableExpSet id (gaussianReal m v)) := by simp
  have := iteratedDeriv_mgf_zero h0 4
  rw [mgf_id_gaussianReal] at this
  rw [show (∫ x, x ^ 4 ∂gaussianReal m v) = (gaussianReal m v)[id ^ 4] by rfl, ← this]
  set w : ℝ := (v : ℝ)
  have e1 : iteratedDeriv 1 (fun t => rexp (m * t + w * t ^ 2 / 2)) =
      fun t => (m + w * t) * rexp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_one]; funext t; exact (hd_E m w t).deriv
  have e2 : iteratedDeriv 2 (fun t => rexp (m * t + w * t ^ 2 / 2)) =
      fun t => (w + (m + w * t) ^ 2) * rexp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e1, deriv_PE m w (P := fun t => m + w * t) (P' := fun _ => w)]
    · funext t; ring
    · intro t; simpa using ((hasDerivAt_id t).const_mul w).const_add m
  have e3 : iteratedDeriv 3 (fun t => rexp (m * t + w * t ^ 2 / 2)) =
      fun t => (3 * w * (m + w * t) + (m + w * t) ^ 3) * rexp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e2, deriv_PE m w (P := fun t => w + (m + w * t) ^ 2) (P' := fun t => 2 * (m + w * t) * w)]
    · funext t; ring
    · intro t
      have := ((((hasDerivAt_id t).const_mul w).const_add m).pow 2).const_add w
      convert this using 1 <;> (try funext x) <;> simp
  have e4 : iteratedDeriv 4 (fun t => rexp (m * t + w * t ^ 2 / 2)) =
      fun t => (3 * w ^ 2 + 6 * w * (m + w * t) ^ 2 + (m + w * t) ^ 4) *
        rexp (m * t + w * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e3, deriv_PE m w (P := fun t => 3 * w * (m + w * t) + (m + w * t) ^ 3) (P' := fun t => 3 * w * w + 3 * (m + w * t) ^ 2 * w)]
    · funext t; ring
    · intro t
      have hq := ((hasDerivAt_id t).const_mul w).const_add m
      have := (hq.const_mul (3 * w)).add (hq.pow 3)
      convert this using 1 <;> (try funext x) <;> simp
  rw [e4]; simp; ring

/-- `(e^{-x} − e^{-y})² ≤ (x − y)² (e^{-2x} + e^{-2y})`, by the mean value theorem. -/
lemma exp_diff_sq (x y : ℝ) :
    (rexp (-x) - rexp (-y)) ^ 2 ≤ (x - y) ^ 2 * (rexp (-2 * x) + rexp (-2 * y)) := by
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
  · exact (key x y h).trans (by nlinarith [Real.exp_pos (-2 * y), sq_nonneg (x - y)])
  · have := key y x h
    calc _ = (rexp (-y) - rexp (-x)) ^ 2 := by ring
      _ ≤ (y - x) ^ 2 * rexp (-2 * y) := this
      _ ≤ _ := by nlinarith [Real.exp_pos (-2 * x), sq_nonneg (x - y)]

section Price
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma int_exp {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    Integrable (fun ω => rexp (c * X ω)) P ∧ ∫ ω, rexp (c * X ω) ∂P = rexp (μ * c + v * c ^ 2 / 2) :=
  ⟨hX.integrable_comp (f := fun x => rexp (c * x)) (integrable_exp_mul_gaussianReal c),
    mgf_gaussianReal hX c⟩

lemma int_pow4 {D : Ω → ℝ} {m : ℝ} {w : ℝ≥0} (hD : HasLaw D (gaussianReal m w) P) :
    Integrable (fun ω => D ω ^ 4) P ∧ ∫ ω, D ω ^ 4 ∂P ≤ 3 * (m ^ 2 + w) ^ 2 := by
  have h0 : (0:ℝ) ∈ interior (integrableExpSet id (gaussianReal m w)) := by simp
  refine ⟨hD.integrable_comp (f := fun x => x ^ 4) (integrable_pow_of_mem_interior_integrableExpSet h0 4), ?_⟩
  rw [show (∫ ω, D ω ^ 4 ∂P) = P[(fun x : ℝ => x ^ 4) ∘ D] from rfl,
    hD.integral_comp (by fun_prop), fourth_moment]
  nlinarith [sq_nonneg m, w.2, sq_nonneg (w:ℝ)]

/-- The price comparison: for Gaussian `X`, `X'` and `X − X'`, with means at most `B/2` and
variances at most `B` in size, `E|e^{-X} − e^{-X'}|² ≤ 2√3 e^{5B} E(X − X')²`. -/
theorem price_ineq [IsProbabilityMeasure P] {X X' : Ω → ℝ} (hXm : Measurable X) (hX'm : Measurable X') {μ μ' m B : ℝ}
    {v v' w : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) (hX' : HasLaw X' (gaussianReal μ' v') P)
    (hD : HasLaw (fun ω => X ω - X' ω) (gaussianReal m w) P)
    (hμ : |μ| ≤ B / 2) (hμ' : |μ'| ≤ B / 2) (hv : (v:ℝ) ≤ B) (hv' : (v':ℝ) ≤ B) :
    ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂P ≤ 2 * √3 * rexp (5 * B) * (m ^ 2 + w) := by
  set D : Ω → ℝ := fun ω => X ω - X' ω
  set M : Ω → ℝ := fun ω => rexp (-2 * X ω) + rexp (-2 * X' ω)
  have mD : Measurable D := hXm.sub hX'm
  have mM : Measurable M := by fun_prop
  obtain ⟨i4, h4⟩ := int_pow4 hD
  obtain ⟨e1, v1⟩ := int_exp hX (-4)
  obtain ⟨e2, v2⟩ := int_exp hX' (-4)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by positivity
  -- `M² ≤ 2e^{-4X} + 2e^{-4X'}`
  have hM2 : ∀ ω, M ω ^ 2 ≤ 2 * rexp (-4 * X ω) + 2 * rexp (-4 * X' ω) := fun ω => by
    have a : rexp (-4 * X ω) = rexp (-2 * X ω) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have b : rexp (-4 * X' ω) = rexp (-2 * X' ω) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [a, b]; nlinarith [sq_nonneg (rexp (-2 * X ω) - rexp (-2 * X' ω))]
  have iM2 : Integrable (fun ω => M ω ^ 2) P :=
    ((e1.const_mul 2).add (e2.const_mul 2)).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hM2 ω)
  have LD : MemLp (fun ω => D ω ^ 2) (ENNReal.ofReal 2) P := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq (by fun_prop)]
    simpa [← pow_mul] using i4
  have LM : MemLp M (ENNReal.ofReal 2) P := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq (by fun_prop)]; exact iM2
  have iDM : Integrable (fun ω => D ω ^ 2 * M ω) P :=
    ((i4.add iM2).div_const 2).mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hM0 ω))]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (D ω ^ 2 - M ω)])
  -- pointwise, then Cauchy–Schwarz
  have step1 : ∫ ω, (rexp (-X ω) - rexp (-X' ω)) ^ 2 ∂P ≤ ∫ ω, D ω ^ 2 * M ω ∂P :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) iDM
      (Filter.Eventually.of_forall fun ω => exp_diff_sq _ _)
  have step2 := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => sq_nonneg (D ω)) (Filter.Eventually.of_forall hM0) LD LM
  have eD : ∫ ω, (D ω ^ 2) ^ (2:ℝ) ∂P = ∫ ω, D ω ^ 4 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only; rw [Real.rpow_two, ← pow_mul])
  have eM : ∫ ω, M ω ^ (2:ℝ) ∂P ≤ 4 * rexp (10 * B) := by
    simp_rw [Real.rpow_two]
    refine (integral_mono iM2 ((e1.const_mul 2).add (e2.const_mul 2)) hM2).trans ?_
    simp only [Pi.add_apply]
    rw [integral_add (e1.const_mul 2) (e2.const_mul 2), integral_const_mul, integral_const_mul, v1, v2]
    have k1 : μ * -4 + v * (-4) ^ 2 / 2 ≤ 10 * B := by
      nlinarith [neg_abs_le μ]
    have k2 : μ' * -4 + v' * (-4) ^ 2 / 2 ≤ 10 * B := by
      nlinarith [neg_abs_le μ']
    nlinarith [Real.exp_le_exp.2 k1, Real.exp_le_exp.2 k2]
  rw [eD] at step2
  have hB : 0 ≤ B := by linarith [abs_nonneg μ]
  have hmw : 0 ≤ m ^ 2 + w := by positivity
  have r1 : (∫ ω, D ω ^ 4 ∂P) ^ (1 / (2:ℝ)) ≤ √3 * (m ^ 2 + w) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq hmw, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have r2 : (∫ ω, M ω ^ (2:ℝ) ∂P) ^ (1 / (2:ℝ)) ≤ 2 * rexp (5 * B) := by
    rw [← Real.sqrt_eq_rpow]
    have : 4 * rexp (10 * B) = (2 * rexp (5 * B)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
    rw [this] at eM
    exact (Real.sqrt_le_sqrt eM).trans (Real.sqrt_sq (by positivity)).le
  have hI0 : 0 ≤ ∫ ω, D ω ^ 4 ∂P := integral_nonneg fun ω => by positivity
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ (√3 * (m ^ 2 + w)) * (2 * rexp (5 * B)) :=
        mul_le_mul r1 r2 (Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _) (by positivity)
    _ = _ := by ring

end Price

lemma fourthS : fourthMomentStatement := fourth_moment

lemma priceS : priceStatement := fun _ _ _ _ _ _ hX hX' _ _ _ _ _ _ _ hl hl' hD hμ hμ' hv hv' =>
  price_ineq hX hX' hl hl' hD hμ hμ' hv hv'

theorem recurrentApproxPriceBounds : Standalone.RecurrentApproxPriceBounds.statement := ⟨boundS, fourthS, priceS⟩

end Novel.RecurrentApproxPriceBoundsProof

import Standalone.NonnegPolySOS
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Polynomial Complex
open Standalone.NonnegPolySOS
namespace Novel.NonnegPolySOSProof

/-- `p` is a finite sum of squares. -/
def IsSOS (p : ℝ[X]) : Prop := ∃ (m : ℕ) (q : Fin m → ℝ[X]), p = ∑ i, q i ^ 2

lemma sos_sq (q : ℝ[X]) : IsSOS (q ^ 2) := ⟨1, fun _ => q, by simp⟩

lemma sos_add {p r : ℝ[X]} (hp : IsSOS p) (hr : IsSOS r) : IsSOS (p + r) := by
  obtain ⟨m, q, rfl⟩ := hp
  obtain ⟨k, s, rfl⟩ := hr
  exact ⟨m + k, Fin.append q s, by rw [Fin.sum_univ_add]; simp⟩

lemma sos_mul {p r : ℝ[X]} (hp : IsSOS p) (hr : IsSOS r) : IsSOS (p * r) := by
  obtain ⟨m, q, rfl⟩ := hp
  obtain ⟨k, s, rfl⟩ := hr
  let e := (finProdFinEquiv : Fin m × Fin k ≃ Fin (m * k))
  refine ⟨m * k, fun l => q (e.symm l).1 * s (e.symm l).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ fun ij => by simp [mul_pow]

lemma sos_C {c : ℝ} (hc : 0 ≤ c) : IsSOS (C c) :=
  ⟨1, fun _ => C (Real.sqrt c), by simp [← C_pow, Real.sq_sqrt hc]⟩

/-- A real root of a nonnegative polynomial has even multiplicity. -/
lemma root_sq (p : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x) (r : ℝ) (hr : p.eval r = 0) :
    ∃ q : ℝ[X], p = (X - C r) ^ 2 * q ∧ ∀ x, 0 ≤ q.eval x := by
  obtain ⟨q1, hq1⟩ : ∃ q1, p = (X - C r) * q1 := ⟨_, (mul_divByMonic_eq_iff_isRoot.2 hr).symm⟩
  have hq1r : q1.eval r = 0 := by
    by_contra hc
    set c := q1.eval r
    have hcont : Continuous fun y => q1.eval y * c := q1.continuous.mul continuous_const
    have hpos : 0 < q1.eval r * c := mul_self_pos.2 hc
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont.continuousAt _ hpos
    set ε := δ / (2 * (|c| + 1))
    have hε : 0 < ε := by positivity
    have hd : dist (r - ε * c) r < δ := by
      rw [Real.dist_eq, show r - ε * c - r = -(ε * c) by ring, abs_neg, abs_mul, abs_of_pos hε]
      have : ε * |c| < ε * (|c| + 1) := by nlinarith
      calc ε * |c| < ε * (|c| + 1) := this
        _ = δ / 2 := by simp only [ε]; field_simp
        _ < δ := by linarith
    have hy := hball hd
    rw [Real.dist_eq] at hy
    have hyp : 0 < q1.eval (r - ε * c) * c := by
      have := abs_sub_lt_iff.1 hy
      linarith
    have := hp (r - ε * c)
    rw [hq1, eval_mul, eval_sub, eval_X, eval_C] at this
    nlinarith
  obtain ⟨q2, hq2⟩ : ∃ q2, q1 = (X - C r) * q2 := ⟨_, (mul_divByMonic_eq_iff_isRoot.2 hq1r).symm⟩
  refine ⟨q2, by rw [hq1, hq2]; ring, fun x => ?_⟩
  have hS : {r}ᶜ ⊆ {x | 0 ≤ q2.eval x} := fun y hy => by
    have hyr : y - r ≠ 0 := sub_ne_zero.2 hy
    have := hp y
    rw [hq1, hq2, eval_mul, eval_mul, eval_sub, eval_X, eval_C] at this
    have h2 : 0 < (y - r) * (y - r) := mul_self_pos.2 hyr
    show 0 ≤ q2.eval y
    nlinarith
  have hcl : IsClosed {x | 0 ≤ q2.eval x} := isClosed_le continuous_const q2.continuous
  exact hcl.closure_subset_iff.2 hS (by rw [(dense_compl_singleton r).closure_eq]; trivial)

/-- A real polynomial of positive degree with no real root has a factor `(X − a)² + b²`, `b ≠ 0`. -/
lemma complex_factor (p : ℝ[X]) (hroot : ∀ x, p.eval x ≠ 0) (hdeg : 0 < p.natDegree) :
    ∃ (a b : ℝ) (q : ℝ[X]), b ≠ 0 ∧ p = ((X - C a) ^ 2 + (C b) ^ 2) * q := by
  set pc := p.map (algebraMap ℝ ℂ)
  have hdc : pc.degree ≠ 0 := by
    have : 0 < pc.degree := by
      rw [degree_map]; exact natDegree_pos_iff_degree_pos.1 hdeg
    exact ne_of_gt this
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root pc hdc
  have haz : aeval z p = 0 := by rw [aeval_def, eval₂_eq_eval_map]; exact hz
  have hconj : aeval (starRingEnd ℂ z) p = 0 := by
    have := aeval_algHom_apply Complex.conjAe z p
    rw [haz, map_zero] at this
    simpa using this
  have him : z.im ≠ 0 := by
    intro h0
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    have e : aeval ((z.re : ℂ)) p = ((aeval z.re p : ℝ) : ℂ) := aeval_algebraMap_apply ℂ z.re p
    rw [hzr, e, coe_aeval_eq_eval] at haz
    exact hroot z.re (by exact_mod_cast haz)
  have hne : starRingEnd ℂ z ≠ z := fun h => him (Complex.conj_eq_iff_im.1 h)
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.2 hz
  have hgc : g.IsRoot (starRingEnd ℂ z) := by
    have h1 : pc.eval (starRingEnd ℂ z) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map] at hconj; exact hconj
    rw [hg, eval_mul, eval_sub, eval_X, eval_C] at h1
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hne)
  obtain ⟨h, hh⟩ := dvd_iff_isRoot.2 hgc
  set a := z.re
  set b := z.im
  have hDmap : ((X - C a) ^ 2 + (C b) ^ 2 : ℝ[X]).map (algebraMap ℝ ℂ) =
      (X - C z) * (X - C (starRingEnd ℂ z)) := by
    have hz' : z = (a : ℂ) + (b : ℂ) * Complex.I := (Complex.re_add_im z).symm
    have hzc : starRingEnd ℂ z = (a : ℂ) - (b : ℂ) * Complex.I := by
      rw [hz']; simp [Complex.conj_ofReal]; ring
    rw [hzc, hz']
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
      Complex.coe_algebraMap, C_add, C_sub, C_mul]
    have hI : (C Complex.I : ℂ[X]) ^ 2 = -1 := by rw [← C_pow, Complex.I_sq, C_neg, C_1]
    linear_combination (C (b : ℂ)) ^ 2 * hI
  have hdvd : ((X - C a) ^ 2 + (C b) ^ 2 : ℝ[X]) ∣ p := by
    rw [← map_dvd_map' (algebraMap ℝ ℂ), hDmap]
    exact ⟨h, by show pc = _; rw [hg, hh]; ring⟩
  obtain ⟨q, hq⟩ := hdvd
  exact ⟨a, b, q, him, hq⟩

lemma sos_aux : ∀ n (p : ℝ[X]), p.natDegree = n → (∀ x, 0 ≤ p.eval x) → IsSOS p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp
  by_cases hdeg : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    have := hp 0
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C] at this
    exact sos_C this
  have hp0 : p ≠ 0 := fun h => hdeg (h ▸ natDegree_zero)
  by_cases hroot : ∃ r, p.eval r = 0
  · obtain ⟨r, hr⟩ := hroot
    obtain ⟨q, hpq, hq⟩ := root_sq p hp r hr
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hp0 hpq
    have hnd : p.natDegree = 2 + q.natDegree := by
      rw [hpq, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hq0, natDegree_pow,
        natDegree_X_sub_C]
    rw [hpq]
    exact sos_mul (sos_sq _) (ih _ (by omega) q rfl hq)
  · push Not at hroot
    obtain ⟨a, b, q, hb, hpq⟩ := complex_factor p hroot (Nat.pos_of_ne_zero hdeg)
    have hD : ∀ x, 0 < ((X - C a) ^ 2 + (C b) ^ 2 : ℝ[X]).eval x := fun x => by
      simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
      have := sq_pos_of_ne_zero hb
      nlinarith [sq_nonneg (x - a)]
    have hq : ∀ x, 0 ≤ q.eval x := fun x => by
      have := hp x
      rw [hpq, eval_mul] at this
      exact (mul_nonneg_iff_of_pos_left (hD x)).1 this
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hp0 hpq
    have hD2 : ((X - C a) ^ 2 + (C b) ^ 2 : ℝ[X]).natDegree = 2 := by
      have h1 : ((X - C a) ^ 2 : ℝ[X]).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
      have h2 : ((C b) ^ 2 : ℝ[X]).natDegree = 0 := by rw [← C_pow, natDegree_C]
      rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h1, h2]; norm_num), h1]
    have hD0 : ((X - C a) ^ 2 + (C b) ^ 2 : ℝ[X]) ≠ 0 := fun h => by
      rw [h, natDegree_zero] at hD2; exact absurd hD2 (by norm_num)
    have hnd : p.natDegree = 2 + q.natDegree := by rw [hpq, natDegree_mul hD0 hq0, hD2]
    rw [hpq]
    exact sos_mul (sos_add (sos_sq _) (sos_sq _)) (ih _ (by omega) q rfl hq)

lemma sos : sosStatement := fun p hp => sos_aux _ p rfl hp

theorem nonnegPolySOS : Standalone.NonnegPolySOS.statement := sos

end Novel.NonnegPolySOSProof

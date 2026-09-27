import Standalone.SharefFilipovicIndependence

open Set Polynomial Filter Topology
open Standalone.SharefFilipovicIndependence
namespace Novel.SharefFilipovicIndependenceProof

/-- A polynomial times `e^{−kx}` tends to `0` at `+∞` for `k > 0`. -/
lemma poly_exp_tendsto (Q : ℝ[X]) (k : ℝ) (hk : 0 < k) :
    Tendsto (fun x => Q.eval x * Real.exp (-k * x)) atTop (𝓝 0) := by
  have hm : ∀ m : ℕ, Tendsto (fun x : ℝ => x ^ m * Real.exp (-k * x)) atTop (𝓝 0) := by
    intro m
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      (tendsto_id.const_mul_atTop hk)).const_mul ((k ^ m)⁻¹)
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    simp only [Function.comp, id, mul_pow]
    have : k ^ m ≠ 0 := pow_ne_zero m hk.ne'
    field_simp
  have e : (fun x => Q.eval x * Real.exp (-k * x)) =
      fun x => ∑ m ∈ Finset.range (Q.natDegree + 1), Q.coeff m * (x ^ m * Real.exp (-k * x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  have := tendsto_finsetSum (Finset.range (Q.natDegree + 1)) fun m _ => (hm m).const_mul (Q.coeff m)
  simpa using this

/-- A polynomial tending to `0` at `+∞` is zero. -/
lemma poly_zero_of_tendsto (Q : ℝ[X]) (h : Tendsto (fun x => Q.eval x) atTop (𝓝 0)) : Q = 0 :=
  leadingCoeff_eq_zero.1 ((Polynomial.tendsto_nhds_iff Q).1 h).1

lemma zero_of_all (β : ℝ) (hβ : 0 < β) :
    ∀ (n : ℕ) (Q : Fin n → ℝ[X]),
      (∀ x, ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) = 0) → ∀ i, Q i = 0 := by
  intro n
  induction n with
  | zero => intro Q _ i; exact i.elim0
  | succ n ih =>
    intro Q h
    have hmul : ∀ x, ∑ i : Fin (n+1), (Q i).eval x * Real.exp (-(((i:ℕ):ℝ)) * β * x) = 0 := by
      intro x
      have e : Real.exp (β * x) * ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) =
          ∑ i : Fin (n+1), (Q i).eval x * Real.exp (-(((i:ℕ):ℝ)) * β * x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      rw [← e, h x, mul_zero]
    have h' : ∀ x, (Q 0).eval x + ∑ j : Fin n,
        (Q j.succ).eval x * Real.exp (-(((j:ℕ):ℝ) + 1) * β * x) = 0 := by
      intro x
      have := hmul x
      rw [Fin.sum_univ_succ] at this
      simp only [Fin.val_zero, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one,
        Fin.val_succ, Nat.cast_add, Nat.cast_one] at this
      exact this
    have hQ0 : Q 0 = 0 := by
      apply poly_zero_of_tendsto
      have hsum : Tendsto (fun x => ∑ j : Fin n,
          (Q j.succ).eval x * Real.exp (-(((j:ℕ):ℝ) + 1) * β * x)) atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
          poly_exp_tendsto (Q j.succ) ((((j:ℕ):ℝ) + 1) * β) (by positivity)
        simp only [Finset.sum_const_zero] at this
        refine this.congr fun x => Finset.sum_congr rfl fun j _ => ?_
        rw [show -((((j:ℕ):ℝ) + 1) * β) * x = -(((j:ℕ):ℝ) + 1) * β * x by ring]
      have := hsum.neg
      rw [neg_zero] at this
      refine this.congr fun x => ?_
      linarith [h' x]
    have hrest := ih (fun j => Q j.succ) (fun x => by
      have := h' x
      rw [hQ0, eval_zero, zero_add] at this
      exact this)
    intro i
    refine Fin.cases hQ0 (fun j => hrest j) i

lemma independence : independenceStatement := by
  intro β hβ n Q P c d hcd h
  set F : ℝ → ℝ := fun x => ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) - P.eval x
  have hFa : AnalyticOnNhd ℝ F univ := by
    intro x _
    have hs := Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset (Fin n))
      (f := fun i x => (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x)) (c := x) fun i _ =>
        (AnalyticOnNhd.eval_polynomial (Q i) x (mem_univ _)).mul
          ((analyticOnNhd_rexp _ (mem_univ _)).comp (by fun_prop))
    have h2 := hs.sub (AnalyticOnNhd.eval_polynomial P x (mem_univ _))
    convert h2 using 1
    funext y
    simp [F, Finset.sum_apply]
  have hmid : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hev : F =ᶠ[𝓝 ((c + d) / 2)] 0 := by
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with x hx
    simp only [F, Pi.zero_apply, h x hx, sub_self]
  have hall := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ _) hev
  have hid : ∀ x, ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) = P.eval x := fun x => by
    have := hall (mem_univ x)
    simp only [F, Pi.zero_apply] at this
    linarith
  have hP : P = 0 := by
    apply poly_zero_of_tendsto
    have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ =>
      poly_exp_tendsto (Q i) ((((i:ℕ):ℝ) + 1) * β) (by positivity)
    simp only [Finset.sum_const_zero] at this
    refine this.congr fun x => ?_
    rw [← hid x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show -((((i:ℕ):ℝ) + 1) * β) * x = -(((i:ℕ):ℝ) + 1) * β * x by ring]
  refine ⟨zero_of_all β hβ n Q fun x => ?_, hP⟩
  rw [hid x, hP, eval_zero]

theorem sharefFilipovicIndependence : Standalone.SharefFilipovicIndependence.statement := independence

end Novel.SharefFilipovicIndependenceProof

import Standalone.RecurrentLoadingStateP
import Novel.RecurrentLoadingDriftProof
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Matrix NormedSpace MeasureTheory Filter
open scoped Kronecker
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Novel.RecurrentLoadingDriftProof
namespace Novel.RecurrentLoadingStatePProof

variable {p r : ℕ}

lemma Ehat_zero (A : Matrix (Fin r) (Fin r) ℝ) : Ehat030 (p := p) A 0 = 1 := by
  simp [Ehat030]

lemma Ehat_add (A : Matrix (Fin r) (Fin r) ℝ) (a b' : ℝ) :
    Ehat030 (p := p) A (a + b') = Ehat030 A a * Ehat030 A b' := by
  rw [Ehat030, Ehat030, Ehat030, ← mul_kronecker_mul, one_mul, add_smul,
    Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _)]

/-- `e^{Âh}` acts on Kronecker vectors through the second factor. -/
lemma Ehat_mulVec_kron (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ) (y : Fin p → ℝ) (z : Fin r → ℝ) :
    Ehat030 (p := p) A h *ᵥ (fun ij => y ij.1 * z ij.2) =
      fun ij => y ij.1 * (exp (h • A) *ᵥ z) ij.2 := by
  classical
  funext ij
  obtain ⟨i, j⟩ := ij
  simp only [mulVec, dotProduct, Ehat030, kroneckerMap_apply, Fintype.sum_prod_type, one_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, one_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  · intro i' _ hi'
    simp [Ne.symm hi']
  · intro h; exact absurd (Finset.mem_univ _) h

lemma count_zero_of_none (Tm : Finset ℝ) (a b' : ℝ) (h : ∀ τ ∈ Tm, ¬ (a < τ ∧ τ ≤ b')) :
    count030 Tm a b' = 0 := by
  rw [count030, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact h

lemma propagate : propagateStatement := by
  intro p r Tm v M b A t₀ t ht hnone
  have h0 : count030 Tm t₀ t = 0 := count_zero_of_none Tm t₀ t hnone
  constructor
  · intro s hs
    have hc := (Novel.RecurrentLoadingAlgebraProof.count Tm s t₀ t 0).1 hs ht
    rw [h0, add_zero] at hc
    rw [show w030 Tm v M b A s t₀ = fun ij : Fin p × Fin r =>
        ((M ^ count030 Tm s t₀) *ᵥ v) ij.1 * (exp ((t₀ - s) • A) *ᵥ b) ij.2 from rfl,
      Ehat_mulVec_kron]
    funext ij
    simp only [w030, hc, mulVec_mulVec]
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left _ |>.smul_right _),
      ← add_smul]
    congr 4
    ring
  · intro s hs1 hs2
    have hcs : count030 Tm s t = 0 := count_zero_of_none Tm s t fun τ hτ h =>
      hnone τ hτ ⟨lt_trans hs1 h.1, h.2⟩
    rw [show beta030 v b = fun ij : Fin p × Fin r => v ij.1 * b ij.2 from rfl, Ehat_mulVec_kron]
    funext ij
    simp only [w030, hcs, pow_zero, one_mulVec]

/-- Entries of `e^{hA}` are differentiable in `h`. -/
lemma exp_entry_hasDerivAt (A : Matrix (Fin r) (Fin r) ℝ) (j j' : Fin r) (t : ℝ) :
    HasDerivAt (fun h => exp (h • A) j j') ((A * exp (t • A)) j j') t := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun h : ℝ => exp (h • A)) (A * exp (t • A)) t :=
    hasDerivAt_exp_smul_const' A t
  let L : Matrix (Fin r) (Fin r) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => X j j'
        map_add' := fun X Y => rfl
        map_smul' := fun c X => rfl }
  have h2 := HasFDerivAt.comp_hasDerivAt (x := t) L.hasFDerivAt h1
  convert h2 using 1
  all_goals first | rfl | skip

lemma Ehat_entry_hasDerivAt (A : Matrix (Fin r) (Fin r) ℝ) (c₀ t : ℝ)
    (a e : Fin p × Fin r) :
    HasDerivAt (fun u => Ehat030 (p := p) A (u - c₀) a e)
      ((Ahat030 A * Ehat030 A (t - c₀) : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) a e) t := by
  have h1 := (exp_entry_hasDerivAt A a.2 e.2 (t - c₀)).comp t ((hasDerivAt_id t).sub_const c₀)
  have e1 : (Ahat030 (p := p) A * Ehat030 A (t - c₀) : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) a e =
      (1 : Matrix (Fin p) (Fin p) ℝ) a.1 e.1 * (A * exp ((t - c₀) • A)) a.2 e.2 := by
    unfold Ahat030 Ehat030
    rw [← mul_kronecker_mul, one_mul, kroneckerMap_apply]
  rw [e1]
  simp only [Ehat030, kroneckerMap_apply, mul_one] at h1 ⊢
  exact h1.const_mul _

lemma Ehat_continuous (A : Matrix (Fin r) (Fin r) ℝ) (c₀ : ℝ) (a e : Fin p × Fin r) :
    Continuous fun s : ℝ => Ehat030 (p := p) A (c₀ - s) a e := by
  simp only [Ehat030, kroneckerMap_apply]
  exact continuous_const.mul ((continuous_apply e.2).comp ((continuous_apply a.2).comp
    ((exp_continuous A).comp (continuous_const.sub continuous_id))))

/-- Entries of a product of entrywise differentiable matrices. -/
lemma mul_entry_hasDerivAt {m : Type*} [Fintype m] (X Y : ℝ → Matrix m m ℝ) (X' Y' : Matrix m m ℝ)
    (t : ℝ) (hX : ∀ i k, HasDerivAt (fun u => X u i k) (X' i k) t)
    (hY : ∀ k j, HasDerivAt (fun u => Y u k j) (Y' k j) t) :
    ∀ i j, HasDerivAt (fun u => (X u * Y u) i j) ((X' * Y t + X t * Y') i j) t := by
  intro i j
  simp only [mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  have h := HasDerivAt.sum (u := Finset.univ) fun k _ => (hX i k).mul (hY k j)
  convert h using 1
  funext u
  simp [Finset.sum_apply]

lemma sandwich_vecMulVec {m : Type*} [Fintype m] (X : Matrix m m ℝ) (g : m → ℝ) :
    X * vecMulVec g g * Xᵀ = vecMulVec (X *ᵥ g) (X *ᵥ g) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- `w_a(s,t) w_b(s,t)` is interval integrable in `s` on every interval. -/
lemma ww_ii (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (a e : Fin p × Fin r) (x y : ℝ) :
    IntervalIntegrable (fun s => w030 Tm v M b A s t a * w030 Tm v M b A s t e) volume x y := by
  have hvb0 : 0 ≤ vecBound Tm v M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : IntervalIntegrable (fun s => ((M ^ count030 Tm s t) *ᵥ v) a.1 *
      ((M ^ count030 Tm s t) *ᵥ v) e.1) volume x y :=
    ii_bdd ((vec_measurable Tm v M t a.1).mul (vec_measurable Tm v M t e.1)).aestronglyMeasurable
      (vecBound Tm v M * vecBound Tm v M) (fun s _ => by
        rw [abs_mul]
        exact mul_le_mul (vec_le Tm v M _ (count_le_card Tm s t) a.1)
          (vec_le Tm v M _ (count_le_card Tm s t) e.1) (abs_nonneg _) hvb0)
  have h2 := h1.mul_continuousOn
    ((expv_continuous b A t a.2).mul (expv_continuous b A t e.2)).continuousOn
  have eq : (fun s => w030 Tm v M b A s t a * w030 Tm v M b A s t e) = fun s =>
      (((M ^ count030 Tm s t) *ᵥ v) a.1 * ((M ^ count030 Tm s t) *ᵥ v) e.1) *
      ((exp ((t - s) • A) *ᵥ b) a.2 * (exp ((t - s) • A) *ᵥ b) e.2) := by
    funext s; simp only [w030]; ring
  rw [eq]; exact h2

lemma ii_fsum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (h : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ S, f i x) volume a b := by
  have := IntervalIntegrable.sum S h
  convert this using 1
  funext x
  simp [Finset.sum_apply]

/-- The integrand `e^{Â(t₀−s)} β` of `P̃`. -/
noncomputable def gvec (A : Matrix (Fin r) (Fin r) ℝ) (v : Fin p → ℝ) (b : Fin r → ℝ)
    (t₀ s : ℝ) : Fin p × Fin r → ℝ :=
  Ehat030 (p := p) A (t₀ - s) *ᵥ beta030 v b

lemma gvec_continuous (A : Matrix (Fin r) (Fin r) ℝ) (v : Fin p → ℝ) (b : Fin r → ℝ)
    (t₀ : ℝ) (a : Fin p × Fin r) : Continuous fun s => gvec A v b t₀ s a := by
  simp only [gvec, mulVec, dotProduct]
  exact continuous_finset_sum _ fun e _ => (Ehat_continuous A t₀ a e).mul continuous_const

/-- `P̃(u) = P_{t₀} + ∫_{t₀}^u e^{Â(t₀−s)} β βᵀ e^{Â(t₀−s)ᵀ} ds`. -/
noncomputable def Ptil (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t₀ u : ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  fun e f => P030 Tm v M b A t₀ e f + ∫ s in t₀..u, gvec A v b t₀ s e * gvec A v b t₀ s f

lemma w_self (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (s : ℝ) : w030 Tm v M b A s s = beta030 v b := by
  have h0 : count030 Tm s s = 0 := count_zero_of_none Tm s s fun τ _ h => by linarith [h.1, h.2]
  funext ij
  simp [w030, h0, beta030]

lemma closed (Tm : Finset ℝ) (v : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (t₀ u : ℝ) (ht₀ : 0 ≤ t₀) (htu : t₀ ≤ u)
    (hnone : ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ u)) :
    P030 Tm v M b A u = Ehat030 A (u - t₀) * Ptil Tm v M b A t₀ u * (Ehat030 A (u - t₀))ᵀ := by
  classical
  obtain ⟨hp1, hp2⟩ := propagate p r Tm v M b A t₀ u htu hnone
  set X := Ehat030 (p := p) A (u - t₀)
  have hw2 : ∀ s, t₀ ≤ s → s ≤ u → w030 Tm v M b A s u = X *ᵥ gvec A v b t₀ s := by
    intro s hs1 hs2
    rcases eq_or_lt_of_le hs1 with h | h
    · subst h
      rw [hp1 _ le_rfl, w_self, gvec, sub_self, Ehat_zero, one_mulVec]
    · rw [hp2 s h hs2, gvec, mulVec_mulVec, ← Ehat_add]
      congr 2; ring
  ext ab cd
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (ww_ii Tm v M b A u ab cd 0 t₀) (ww_ii Tm v M b A u ab cd t₀ u)
  -- the part before `t₀`
  have h1 : (∫ s in (0:ℝ)..t₀, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
      ∑ e, ∑ f, X ab e * X cd f * P030 Tm v M b A t₀ e f := by
    have hc : ∀ s ∈ Set.uIcc 0 t₀, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd =
        ∑ e, ∑ f, X ab e * X cd f * (w030 Tm v M b A s t₀ e * w030 Tm v M b A s t₀ f) := by
      intro s hs
      rw [Set.uIcc_of_le ht₀] at hs
      rw [hp1 s hs.2]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (ww_ii Tm v M b A t₀ e f 0 t₀).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  -- the part after `t₀`
  have hgg : ∀ e f, IntervalIntegrable (fun s => gvec A v b t₀ s e * gvec A v b t₀ s f)
      volume t₀ u := fun e f =>
    ((gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f)).intervalIntegrable _ _
  have h2 : (∫ s in t₀..u, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) =
      ∑ e, ∑ f, X ab e * X cd f * ∫ s in t₀..u, gvec A v b t₀ s e * gvec A v b t₀ s f := by
    have hc : ∀ s ∈ Set.uIcc t₀ u, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd =
        ∑ e, ∑ f, X ab e * X cd f * (gvec A v b t₀ s e * gvec A v b t₀ s f) := by
      intro s hs
      rw [Set.uIcc_of_le htu] at hs
      rw [hw2 s hs.1 hs.2]
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_finsetSum fun e _ =>
      ii_fsum _ _ fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [intervalIntegral.integral_finsetSum fun f _ => (hgg e f).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [intervalIntegral.integral_const_mul]
  show (∫ s in (0:ℝ)..u, w030 Tm v M b A s u ab * w030 Tm v M b A s u cd) = _
  rw [← hsplit, h1, h2, ← Finset.sum_add_distrib]
  simp only [mul_apply, transpose_apply, Ptil, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by ring

lemma pEquation : pEquationStatement := by
  intro p r Tm v M b A t₀ t t₁ ht₀ htt htt₁ hnone ab cd
  classical
  have hnone' : ∀ u, u < t₁ → ∀ τ ∈ Tm, ¬ (t₀ < τ ∧ τ ≤ u) :=
    fun u hu τ hτ h => hnone τ hτ ⟨h.1, lt_of_le_of_lt h.2 hu⟩
  let X : ℝ → Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ := fun u => Ehat030 A (u - t₀)
  let Y : ℝ → Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ := fun u => Ptil Tm v M b A t₀ u
  let g := gvec A v b t₀ t
  have hX : ∀ i k, HasDerivAt (fun u => X u i k)
      ((Ahat030 A * X t : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i k) t :=
    fun i k => Ehat_entry_hasDerivAt A t₀ t i k
  have hXT : ∀ i k, HasDerivAt (fun u => (X u)ᵀ i k)
      ((Ahat030 A * X t : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ)ᵀ i k) t :=
    fun i k => by simpa only [transpose_apply] using hX k i
  have hY : ∀ e f, HasDerivAt (fun u => Y u e f) (vecMulVec g g e f) t := by
    intro e f
    have hcont : Continuous fun s => gvec A v b t₀ s e * gvec A v b t₀ s f :=
      (gvec_continuous A v b t₀ e).mul (gvec_continuous A v b t₀ f)
    have hc := hcont.integral_hasStrictDerivAt t₀ t
    simpa only [Y, Ptil, vecMulVec_apply, g] using hc.hasDerivAt.const_add (P030 Tm v M b A t₀ e f)
  have hXY := mul_entry_hasDerivAt X Y _ _ t hX hY
  have hXYZ := mul_entry_hasDerivAt (fun u => X u * Y u) (fun u => (X u)ᵀ) _ _ t hXY hXT ab cd
  have hev : (fun u => (X u * Y u * (X u)ᵀ) ab cd) =ᶠ[nhds t] fun u => P030 Tm v M b A u ab cd := by
    filter_upwards [Ioo_mem_nhds htt htt₁] with u hu
    rw [closed Tm v M b A t₀ u ht₀ hu.1.le (hnone' u hu.2)]
  have hP := hXYZ.congr_of_eventuallyEq hev.symm
  have hPt : P030 Tm v M b A t = X t * Y t * (X t)ᵀ :=
    closed Tm v M b A t₀ t ht₀ htt.le (hnone' t htt₁)
  have hβ : X t *ᵥ g = beta030 v b := by
    simp only [X, g, gvec, mulVec_mulVec, ← Ehat_add, show t - t₀ + (t₀ - t) = 0 by ring,
      Ehat_zero, one_mulVec]
  convert hP using 1
  rw [hPt, add_mul, transpose_mul, sandwich_vecMulVec, hβ]
  simp only [Matrix.mul_assoc]
  rw [add_right_comm]

theorem recurrentLoadingStateP : Standalone.RecurrentLoadingStateP.statement :=
  ⟨propagate, pEquation⟩

end Novel.RecurrentLoadingStatePProof

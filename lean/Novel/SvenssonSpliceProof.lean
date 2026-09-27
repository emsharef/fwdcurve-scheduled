import Standalone.SvenssonSplice
import Novel.SpliceAffineOverlapNSProof
import Novel.SharefFilipovicIndependenceProof
import Novel.CorrelatedFactorsAlwaysProof
import Mathlib.Topology.Order.LeftRightNhds

open Polynomial Set Filter Topology
open Standalone.SvenssonSplice
namespace Novel.SvenssonSpliceProof
open Novel.SharefFilipovicIndependenceProof

/-- Polynomials times `e^{−κ_i x}` with distinct `κ_i` summing to zero on `ℝ` all vanish. -/
lemma indep_all {ι : Type*} (κ : ι → ℝ) (Q : ι → ℝ[X]) :
    ∀ s : Finset ι, Set.InjOn κ s →
      (∀ x, ∑ i ∈ s, (Q i).eval x * Real.exp (-κ i * x) = 0) → ∀ i ∈ s, Q i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hκ h i hi
  obtain ⟨i0, hi0, hmin⟩ := s.exists_min_image κ ⟨i, hi⟩
  have hlt : ∀ j ∈ s.erase i0, κ i0 < κ j := fun j hj =>
    lt_of_le_of_ne (hmin j (Finset.mem_of_mem_erase hj))
      (fun heq => Finset.ne_of_mem_erase hj (hκ (Finset.mem_of_mem_erase hj) hi0 heq.symm))
  have hsplit : ∀ x, (Q i0).eval x * Real.exp (-κ i0 * x) +
      ∑ j ∈ s.erase i0, (Q j).eval x * Real.exp (-κ j * x) = 0 := fun x => by
    exact (Finset.add_sum_erase s (fun j => (Q j).eval x * Real.exp (-κ j * x)) hi0).trans (h x)
  have hmul : ∀ x, (Q i0).eval x +
      ∑ j ∈ s.erase i0, (Q j).eval x * Real.exp (-(κ j - κ i0) * x) = 0 := fun x => by
    have := congrArg (Real.exp (κ i0 * x) * ·) (hsplit x)
    simp only [mul_zero, mul_add, Finset.mul_sum] at this
    rw [← this]
    congr 1
    · rw [mul_left_comm, ← Real.exp_add, show κ i0 * x + -κ i0 * x = 0 by ring, Real.exp_zero,
        mul_one]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, ← Real.exp_add]
      congr 2; ring
  have hQ0 : Q i0 = 0 := by
    apply poly_zero_of_tendsto
    have := tendsto_finsetSum (s.erase i0) fun j hj =>
      poly_exp_tendsto (Q j) (κ j - κ i0) (sub_pos.2 (hlt j hj))
    simp only [Finset.sum_const_zero] at this
    have := this.neg
    rw [neg_zero] at this
    refine this.congr fun x => ?_
    linarith [hmul x]
  have hrest := ih (s.erase i0) (Finset.erase_ssubset hi0) (hκ.mono (Finset.erase_subset _ _))
    fun x => by have := hsplit x; rwa [hQ0, eval_zero, zero_mul, zero_add] at this
  by_cases hii : i = i0
  · rw [hii]; exact hQ0
  · exact hrest i (Finset.mem_erase.2 ⟨hii, hi⟩)

/-- The same on an open interval, by analytic continuation. -/
lemma indep {ι : Type*} [Fintype ι] (κ : ι → ℝ) (hκ : Function.Injective κ) (Q : ι → ℝ[X])
    (c d : ℝ) (hcd : c < d)
    (h : ∀ x ∈ Ioo c d, ∑ i, (Q i).eval x * Real.exp (-κ i * x) = 0) : ∀ i, Q i = 0 := by
  set F : ℝ → ℝ := fun x => ∑ i, (Q i).eval x * Real.exp (-κ i * x)
  have hFa : AnalyticOnNhd ℝ F univ := by
    intro x _
    have hs := Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset ι)
      (f := fun i x => (Q i).eval x * Real.exp (-κ i * x)) (c := x) fun i _ =>
        (AnalyticOnNhd.eval_polynomial (Q i) x (mem_univ _)).mul
          ((analyticOnNhd_rexp _ (mem_univ _)).comp (by fun_prop))
    convert hs using 1
    funext y
    simp [F, Finset.sum_apply]
  have hmid : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hev : F =ᶠ[𝓝 ((c + d) / 2)] 0 := by
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with x hx
    exact h x hx
  have hall := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ _) hev
  intro i
  exact indep_all κ Q Finset.univ (hκ.injOn) (fun x => hall (mem_univ x)) i (Finset.mem_univ _)

lemma I0 (β₁ β₂ x : ℝ) : ∫ η in (0:ℝ)..x, phiSv β₁ β₂ 0 η = x := by
  simp [phiSv]

lemma I1 (β₁ β₂ : ℝ) (h : β₁ ≠ 0) (x : ℝ) :
    ∫ η in (0:ℝ)..x, phiSv β₁ β₂ 1 η = 1 / β₁ - 1 / β₁ * Real.exp (-β₁ * x) :=
  Novel.SpliceAffineOverlapNSProof.hI1 β₁ h x

lemma I2 (β₁ β₂ : ℝ) (h : β₁ ≠ 0) (x : ℝ) :
    ∫ η in (0:ℝ)..x, phiSv β₁ β₂ 2 η = 1 / β₁ ^ 2 - (x / β₁ + 1 / β₁ ^ 2) * Real.exp (-β₁ * x) :=
  Novel.SpliceAffineOverlapNSProof.hI2 β₁ h x

lemma I3 (β₁ β₂ : ℝ) (h : β₂ ≠ 0) (x : ℝ) :
    ∫ η in (0:ℝ)..x, phiSv β₁ β₂ 3 η = 1 / β₂ ^ 2 - (x / β₂ + 1 / β₂ ^ 2) * Real.exp (-β₂ * x) :=
  Novel.SpliceAffineOverlapNSProof.hI2 β₂ h x

lemma hd (β₁ β₂ : ℝ) (z : Fin 4 → ℝ) (x : ℝ) :
    deriv (FSv β₁ β₂ z) x = (z 2 - β₁ * z 1 - β₁ * z 2 * x) * Real.exp (-β₁ * x) +
      (z 3 - β₂ * z 3 * x) * Real.exp (-β₂ * x) := by
  have h := ((Novel.SharefFilipovicResidualProof.hd_pe (C (z 1) + C (z 2) * X) β₁ x).add
    (Novel.SharefFilipovicResidualProof.hd_pe (C (z 3) * X) β₂ x)).const_add (z 0)
  have e : FSv β₁ β₂ z = fun x => z 0 + ((C (z 1) + C (z 2) * X).eval x * Real.exp (-β₁ * x) +
      (C (z 3) * X).eval x * Real.exp (-β₂ * x)) := by
    funext x
    simp [FSv, phiSv, Fin.sum_univ_four]
    ring
  rw [e]
  refine h.deriv.trans ?_
  simp
  ring

/-- The residual's closed form: an affine part plus `e^{−β₁x}`, `e^{−β₂x}`, `e^{−2β₁x}`,
`e^{−(β₁+β₂)x}` and `e^{−2β₂x}` times quadratics. -/
lemma closed (β₁ β₂ : ℝ) (h₁ : β₁ ≠ 0) (h₂ : β₂ ≠ 0) (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ)
    (x : ℝ) :
    residualSv β₁ β₂ z b a x =
      ((b 0 - a 0 1 / β₁ - a 0 2 / β₁ ^ 2 - a 0 3 / β₂ ^ 2) + (-a 0 0) * x) +
      ((b 1 + a 0 1 / β₁ + a 0 2 / β₁ ^ 2 - a 1 1 / β₁ - a 1 2 / β₁ ^ 2 - a 1 3 / β₂ ^ 2 - z 2 +
          β₁ * z 1) +
        (b 2 + a 0 2 / β₁ - a 1 0 - a 2 1 / β₁ - a 2 2 / β₁ ^ 2 - a 2 3 / β₂ ^ 2 + β₁ * z 2) * x +
        (-a 2 0) * x ^ 2) * Real.exp (-β₁ * x) +
      ((a 0 3 / β₂ ^ 2 - z 3) +
        (b 3 + a 0 3 / β₂ - a 3 1 / β₁ - a 3 2 / β₁ ^ 2 - a 3 3 / β₂ ^ 2 + β₂ * z 3) * x +
        (-a 3 0) * x ^ 2) * Real.exp (-β₂ * x) +
      ((a 1 1 / β₁ + a 1 2 / β₁ ^ 2) + (a 1 2 / β₁ + a 2 1 / β₁ + a 2 2 / β₁ ^ 2) * x +
        (a 2 2 / β₁) * x ^ 2) * (Real.exp (-β₁ * x) * Real.exp (-β₁ * x)) +
      ((a 1 3 / β₂ ^ 2) + (a 1 3 / β₂ + a 2 3 / β₂ ^ 2 + a 3 1 / β₁ + a 3 2 / β₁ ^ 2) * x +
        (a 2 3 / β₂ + a 3 2 / β₁) * x ^ 2) * (Real.exp (-β₁ * x) * Real.exp (-β₂ * x)) +
      ((a 3 3 / β₂ ^ 2) * x + (a 3 3 / β₂) * x ^ 2) *
        (Real.exp (-β₂ * x) * Real.exp (-β₂ * x)) := by
  unfold residualSv
  simp only [Fin.sum_univ_four]
  rw [I0, I1 β₁ β₂ h₁, I2 β₁ β₂ h₁, I3 β₁ β₂ h₂, hd]
  simp only [phiSv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- `p + q X + r X²`. -/
noncomputable def qd (p q r : ℝ) : ℝ[X] := C p + C q * X + C r * X ^ 2

lemma qd_eval (p q r x : ℝ) : (qd p q r).eval x = p + q * x + r * x ^ 2 := by
  simp [qd]

lemma qd_zero {p q r : ℝ} (h : qd p q r = 0) : p = 0 ∧ q = 0 ∧ r = 0 := by
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  have h2 := congrArg (coeff · 2) h
  simp [qd, coeff_X, coeff_C] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

lemma qd_add (p q r p' q' r' : ℝ) : qd p q r + qd p' q' r' = qd (p + p') (q + q') (r + r') := by
  simp only [qd, C_add]; ring

section coeffs
variable (β₁ β₂ : ℝ) (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ)

/-- The exponent-zero part minus the affine target `c₀ + c₁ x`. -/
noncomputable def Q0 (c₀ c₁ : ℝ) : ℝ[X] :=
  qd (b 0 - a 0 1 / β₁ - a 0 2 / β₁ ^ 2 - a 0 3 / β₂ ^ 2 - c₀) (-a 0 0 - c₁) 0
noncomputable def Q1 : ℝ[X] :=
  qd (b 1 + a 0 1 / β₁ + a 0 2 / β₁ ^ 2 - a 1 1 / β₁ - a 1 2 / β₁ ^ 2 - a 1 3 / β₂ ^ 2 - z 2 +
      β₁ * z 1)
    (b 2 + a 0 2 / β₁ - a 1 0 - a 2 1 / β₁ - a 2 2 / β₁ ^ 2 - a 2 3 / β₂ ^ 2 + β₁ * z 2) (-a 2 0)
noncomputable def Q2 : ℝ[X] :=
  qd (a 0 3 / β₂ ^ 2 - z 3)
    (b 3 + a 0 3 / β₂ - a 3 1 / β₁ - a 3 2 / β₁ ^ 2 - a 3 3 / β₂ ^ 2 + β₂ * z 3) (-a 3 0)
noncomputable def Q11 : ℝ[X] :=
  qd (a 1 1 / β₁ + a 1 2 / β₁ ^ 2) (a 1 2 / β₁ + a 2 1 / β₁ + a 2 2 / β₁ ^ 2) (a 2 2 / β₁)
noncomputable def Q12 : ℝ[X] :=
  qd (a 1 3 / β₂ ^ 2) (a 1 3 / β₂ + a 2 3 / β₂ ^ 2 + a 3 1 / β₁ + a 3 2 / β₁ ^ 2)
    (a 2 3 / β₂ + a 3 2 / β₁)
noncomputable def Q22 : ℝ[X] := qd 0 (a 3 3 / β₂ ^ 2) (a 3 3 / β₂)

end coeffs

lemma closedQ (β₁ β₂ : ℝ) (h₁ : β₁ ≠ 0) (h₂ : β₂ ≠ 0) (z b : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → ℝ)
    (c₀ c₁ x : ℝ) :
    residualSv β₁ β₂ z b a x - (c₀ + c₁ * x) =
      (Q0 β₁ β₂ b a c₀ c₁).eval x + (Q1 β₁ β₂ z b a).eval x * Real.exp (-β₁ * x) +
      (Q2 β₁ β₂ z b a).eval x * Real.exp (-β₂ * x) +
      (Q11 β₁ a).eval x * (Real.exp (-β₁ * x) * Real.exp (-β₁ * x)) +
      (Q12 β₁ β₂ a).eval x * (Real.exp (-β₁ * x) * Real.exp (-β₂ * x)) +
      (Q22 β₂ a).eval x * (Real.exp (-β₂ * x) * Real.exp (-β₂ * x)) := by
  rw [closed β₁ β₂ h₁ h₂]
  simp only [Q0, Q1, Q2, Q11, Q12, Q22, qd_eval]
  ring

lemma exp_mul_self (k x : ℝ) : Real.exp (-k * x) * Real.exp (-k * x) = Real.exp (-(2 * k) * x) := by
  rw [← Real.exp_add]; ring_nf

lemma exp_mul_exp (k l x : ℝ) :
    Real.exp (-k * x) * Real.exp (-l * x) = Real.exp (-(k + l) * x) := by
  rw [← Real.exp_add]; ring_nf

/-- Symmetry of a nonnegative definite real matrix. -/
lemma psd_symm {a : Matrix (Fin 4) (Fin 4) ℝ} (ha : a.PosSemidef) (i j : Fin 4) : a j i = a i j := by
  have := congrFun (congrFun ha.1.eq i) j
  simpa [Matrix.conjTranspose_apply] using this

lemma nonresonant : nonresonantStatement := by
  intro β₁ β₂ h₁ h₂ h12 h21 z b a hz3 ha ⟨c₀, c₁, h⟩
  have h₁0 := h₁.ne'
  have h₂0 := h₂.ne'
  have hz : ∀ x ∈ Ioo (0:ℝ) 1, residualSv β₁ β₂ z b a x - (c₀ + c₁ * x) = 0 := fun x hx => by
    rw [h x hx.1.le, sub_self]
  -- `a_{44} = 0` and the `e^{−β₂x}` group vanishes, then `z_4 = 0`
  suffices key : a 3 3 = 0 ∧ Q2 β₁ β₂ z b a = 0 by
    obtain ⟨h33, hQ2⟩ := key
    obtain ⟨hc, -, -⟩ := qd_zero hQ2
    have h03 := (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 3 0 h33).2
    rw [h03, zero_div, zero_sub, neg_eq_zero] at hc
    exact hz3 hc
  by_cases h3 : β₁ = 2 * β₂
  · -- `β₁ = 2β₂`: the exponents are `0, β₂, 2β₂, 3β₂, 4β₂`
    have hind := indep ![0, β₂, 2 * β₂, 3 * β₂, 4 * β₂]
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith)
      ![Q0 β₁ β₂ b a c₀ c₁, Q2 β₁ β₂ z b a, Q1 β₁ β₂ z b a + Q22 β₂ a, Q12 β₁ β₂ a, Q11 β₁ a]
      0 1 one_pos fun x hx => by
        have e := (closedQ β₁ β₂ h₁0 h₂0 z b a c₀ c₁ x).symm.trans (hz x hx)
        rw [Fin.sum_univ_five]
        change (Q0 β₁ β₂ b a c₀ c₁).eval x * Real.exp (-(0:ℝ) * x) +
          (Q2 β₁ β₂ z b a).eval x * Real.exp (-β₂ * x) +
          (Q1 β₁ β₂ z b a + Q22 β₂ a).eval x * Real.exp (-(2 * β₂) * x) +
          (Q12 β₁ β₂ a).eval x * Real.exp (-(3 * β₂) * x) +
          (Q11 β₁ a).eval x * Real.exp (-(4 * β₂) * x) = 0
        rw [eval_add]
        have E1 : Real.exp (-β₁ * x) = Real.exp (-(2 * β₂) * x) := by rw [h3]
        have E2 : Real.exp (-(3 * β₂) * x) = Real.exp (-β₁ * x) * Real.exp (-β₂ * x) := by
          rw [exp_mul_exp, h3]; ring_nf
        have E3 : Real.exp (-(4 * β₂) * x) = Real.exp (-β₁ * x) * Real.exp (-β₁ * x) := by
          rw [exp_mul_self, h3]; ring_nf
        rw [E2, E3, ← exp_mul_self, E1, ← exp_mul_self]
        rw [E1, ← exp_mul_self] at e
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at e ⊢
        linear_combination e
    have h11 : Q11 β₁ a = 0 := hind 4
    have h1p22 : Q1 β₁ β₂ z b a + Q22 β₂ a = 0 := hind 2
    obtain ⟨-, -, h22⟩ := qd_zero h11
    have ha22 : a 2 2 = 0 := by
      rcases div_eq_zero_iff.1 h22 with h | h
      · exact h
      · exact absurd h h₁0
    have h20 := (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 2 0 ha22).1
    simp only [Q1, Q22, qd_add] at h1p22
    obtain ⟨-, -, hx2⟩ := qd_zero h1p22
    rw [h20, neg_zero, zero_add] at hx2
    refine ⟨?_, (hind 1 : Q2 β₁ β₂ z b a = 0)⟩
    rcases div_eq_zero_iff.1 hx2 with h | h
    · exact h
    · exact absurd h h₂0
  · -- generic: the six exponents are distinct
    have hind := indep ![0, β₁, β₂, 2 * β₁, β₁ + β₂, 2 * β₂]
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
          first | linarith | exact h12 (by linarith) | exact h21 (by linarith) |
            exact h3 (by linarith))
      ![Q0 β₁ β₂ b a c₀ c₁, Q1 β₁ β₂ z b a, Q2 β₁ β₂ z b a, Q11 β₁ a, Q12 β₁ β₂ a, Q22 β₂ a]
      0 1 one_pos fun x hx => by
        have e := (closedQ β₁ β₂ h₁0 h₂0 z b a c₀ c₁ x).symm.trans (hz x hx)
        rw [Fin.sum_univ_six]
        change (Q0 β₁ β₂ b a c₀ c₁).eval x * Real.exp (-(0:ℝ) * x) +
          (Q1 β₁ β₂ z b a).eval x * Real.exp (-β₁ * x) +
          (Q2 β₁ β₂ z b a).eval x * Real.exp (-β₂ * x) +
          (Q11 β₁ a).eval x * Real.exp (-(2 * β₁) * x) +
          (Q12 β₁ β₂ a).eval x * Real.exp (-(β₁ + β₂) * x) +
          (Q22 β₂ a).eval x * Real.exp (-(2 * β₂) * x) = 0
        rw [← exp_mul_self, ← exp_mul_self, ← exp_mul_exp]
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at e ⊢
        linear_combination e
    have h22 : Q22 β₂ a = 0 := hind 5
    obtain ⟨-, -, h33⟩ := qd_zero h22
    refine ⟨?_, (hind 2 : Q2 β₁ β₂ z b a = 0)⟩
    rcases div_eq_zero_iff.1 h33 with h | h
    · exact h
    · exact absurd h h₂0

lemma path : pathStatement := by
  intro β₁ β₂ h₁ h₂ h12 h21 Z a b t₀ δ hδ hcont hne hae
  obtain ⟨u, hu, hsub⟩ :=
    mem_nhdsGE_iff_exists_Ico_subset.1 (hcont (compl_singleton_mem_nhds hne))
  have hη : t₀ < min (t₀ + δ) u := lt_min (by linarith) hu
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae
  have hzero : MeasureTheory.volume (Ioo t₀ (min (t₀ + δ) u)) = 0 := by
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with t ht htI
    obtain ⟨ha, hR⟩ := ht ⟨htI.1, htI.2.trans_le (min_le_left _ _)⟩
    exact nonresonant β₁ β₂ h₁ h₂ h12 h21 (Z t) (b t) (a t)
      (hsub ⟨htI.1.le, htI.2.trans_le (min_le_right _ _)⟩) ha hR
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  linarith

lemma residual : residualStatement := by
  intro β hβ z b a hsym ⟨hz, h11, hb1, hb2, hb3⟩ x
  have hβ0 := hβ.ne'
  have z_ : ∀ i j : Fin 4, (2 ≤ i ∨ 2 ≤ j) → a i j = 0 := hz
  rw [closed β (2 * β) hβ0 (by positivity) z b a x, hsym, h11, hb1, hb2, hb3,
    z_ 0 2 (by decide), z_ 0 3 (by decide), z_ 1 2 (by decide), z_ 1 3 (by decide),
    z_ 2 0 (by decide), z_ 2 1 (by decide), z_ 2 2 (by decide), z_ 2 3 (by decide),
    z_ 3 0 (by decide), z_ 3 1 (by decide), z_ 3 2 (by decide), z_ 3 3 (by decide),
    ← exp_mul_self β x]
  field_simp
  ring

lemma resonant : resonantStatement := by
  intro β hβ z b a ha
  have hβ0 := hβ.ne'
  have h2β : (2 * β) ≠ 0 := by positivity
  constructor
  · rintro ⟨c₀, c₁, h⟩
    have hind := indep ![0, β, 2 * β, 3 * β, 4 * β]
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith)
      ![Q0 β (2 * β) b a c₀ c₁, Q1 β (2 * β) z b a, Q2 β (2 * β) z b a + Q11 β a,
        Q12 β (2 * β) a, Q22 (2 * β) a]
      0 1 one_pos fun x hx => by
        have e := (closedQ β (2 * β) hβ0 h2β z b a c₀ c₁ x).symm.trans
          (by rw [h x hx.1.le, sub_self])
        rw [Fin.sum_univ_five]
        change (Q0 β (2 * β) b a c₀ c₁).eval x * Real.exp (-(0:ℝ) * x) +
          (Q1 β (2 * β) z b a).eval x * Real.exp (-β * x) +
          (Q2 β (2 * β) z b a + Q11 β a).eval x * Real.exp (-(2 * β) * x) +
          (Q12 β (2 * β) a).eval x * Real.exp (-(3 * β) * x) +
          (Q22 (2 * β) a).eval x * Real.exp (-(4 * β) * x) = 0
        have E3 : Real.exp (-(3 * β) * x) = Real.exp (-β * x) * Real.exp (-(2 * β) * x) := by
          rw [exp_mul_exp]; ring_nf
        have E4 : Real.exp (-(4 * β) * x) =
            Real.exp (-(2 * β) * x) * Real.exp (-(2 * β) * x) := by
          rw [exp_mul_self]; ring_nf
        rw [eval_add, E3, E4, ← exp_mul_self β x]
        rw [← exp_mul_self β x] at e
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at e ⊢
        linear_combination e
    have hQ1 : Q1 β (2 * β) z b a = 0 := hind 1
    have hQ211 : Q2 β (2 * β) z b a + Q11 β a = 0 := hind 2
    have hQ22 : Q22 (2 * β) a = 0 := hind 4
    simp only [Q2, Q11, qd_add] at hQ211
    obtain ⟨hc0, hc1, hc2⟩ := qd_zero hQ211
    obtain ⟨hb0, hb1, -⟩ := qd_zero hQ1
    obtain ⟨-, -, h33⟩ := qd_zero hQ22
    have psd0 := Novel.SharefFilipovicMaxFactorsProof.psd_zero ha
    have ha33 : a 3 3 = 0 := by
      rcases div_eq_zero_iff.1 h33 with h | h
      · exact h
      · exact absurd h h2β
    have r3 : ∀ j, a 3 j = 0 ∧ a j 3 = 0 := fun j => psd0 3 j ha33
    have ha22 : a 2 2 = 0 := by
      rw [(r3 0).1, neg_zero, zero_add] at hc2
      rcases div_eq_zero_iff.1 hc2 with h | h
      · exact h
      · exact absurd h hβ0
    have r2 : ∀ j, a 2 j = 0 ∧ a j 2 = 0 := fun j => psd0 2 j ha22
    have hzero : ∀ i j : Fin 4, (2 ≤ i ∨ 2 ≤ j) → a i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij <;>
        first | exact (r2 _).1 | exact (r2 _).2 | exact (r3 _).1 | exact (r3 _).2
    have hs := psd_symm ha 0 1
    have z2 : ∀ j, a 2 j = 0 := fun j => (r2 j).1
    have z2' : ∀ j, a j 2 = 0 := fun j => (r2 j).2
    have z3 : ∀ j, a 3 j = 0 := fun j => (r3 j).1
    have z3' : ∀ j, a j 3 = 0 := fun j => (r3 j).2
    simp only [z2, z2', z3, z3', hs, zero_div, add_zero, sub_zero, zero_sub] at hc0 hc1 hb0 hb1
    have h11 : a 1 1 = β * z 3 := by
      field_simp at hc0; linarith
    refine ⟨hzero, h11, ?_, ?_, ?_⟩
    · rw [h11] at hb0
      field_simp at hb0 ⊢
      linarith
    · field_simp at hb1 ⊢
      linarith
    · field_simp at hc1
      linarith
  · intro hc
    exact ⟨b 0 - a 0 1 / β, -a 0 0, fun x _ => by
      rw [residual β hβ z b a (psd_symm ha 0 1) hc x]; ring⟩

lemma alone : aloneStatement := by
  intro β hβ z b a ha
  constructor
  · intro h
    have hc := (resonant β hβ z b a ha).1 ⟨0, 0, fun x hx => by rw [h x hx]; ring⟩
    have hr := residual β hβ z b a (psd_symm ha 0 1) hc
    have e0 := hr 0
    have e1 := hr 1
    rw [h 0 le_rfl] at e0
    rw [h 1 zero_le_one] at e1
    have h00 : a 0 0 = 0 := by linarith
    have h01 := (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha 0 1 h00).1
    refine ⟨hc, h00, h01, ?_⟩
    rw [h01, h00, zero_div, zero_mul, sub_zero, sub_zero] at e0
    linarith
  · rintro ⟨hc, h00, h01, hb0⟩ x _
    rw [residual β hβ z b a (psd_symm ha 0 1) hc x, h00, h01, hb0]
    ring

lemma level : levelStatement := by
  rintro β hβ z b a ha ⟨-, h11, -⟩
  have hd := ha.diag_nonneg (i := 1)
  have hm := Novel.CorrelatedFactorsAlwaysProof.minor2 a ha 0 1
  rw [psd_symm ha 0 1, h11] at hm
  rw [h11] at hd
  exact ⟨nonneg_of_mul_nonneg_right (by linarith) hβ, by nlinarith⟩

lemma correlated : correlatedStatement := by
  intro β hβ z hz3
  set s := Real.sqrt (β * z 3)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hss : s * s = β * z 3 := Real.mul_self_sqrt (by positivity)
  set v : Fin 4 → ℝ := ![1, s, 0, 0]
  set a : Matrix (Fin 4) (Fin 4) ℝ := Matrix.vecMulVec v v
  have ha : a.PosSemidef := by
    have := Matrix.posSemidef_vecMulVec_self_star v
    simpa [star_trivial] using this
  have hc : ResonantConditions β z
      ![0, z 2 + z 3 - β * z 1 - a 0 1 / β, a 0 1 - β * z 2, -2 * β * z 3] a := by
    refine ⟨fun i j hij => ?_, by simp [a, v, hss], rfl, rfl, rfl⟩
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp [a, v]
  refine ⟨a, ![0, z 2 + z 3 - β * z 1 - a 0 1 / β, a 0 1 - β * z 2, -2 * β * z 3], ha,
    by simp [a, v, hs.ne'], ?_⟩
  exact (resonant β hβ z _ a ha).2 hc

theorem svenssonSplice : Standalone.SvenssonSplice.statement :=
  ⟨nonresonant, path, resonant, residual, alone, level, correlated⟩

end Novel.SvenssonSpliceProof

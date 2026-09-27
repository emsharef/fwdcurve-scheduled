import Standalone.SpliceVaryingExponents
import Novel.SvenssonSpliceProof
import Novel.CorrelatedFactorsReductionProof

open Polynomial Set Filter
open Standalone.SpliceVaryingExponents
namespace Novel.SpliceVaryingExponentsProof

/-- `f` is a finite sum of polynomials times `e^{−κx}`, every `κ > 0`. -/
def ExpPos (f : ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (κ : ι → ℝ) (Q : ι → ℝ[X]), (∀ i, 0 < κ i) ∧
    ∀ x, f x = ∑ i, (Q i).eval x * Real.exp (-κ i * x)

namespace ExpPos

lemma zero : ExpPos fun _ => 0 :=
  ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun x => by simp⟩

lemma single (Q : ℝ[X]) {κ : ℝ} (hκ : 0 < κ) : ExpPos fun x => Q.eval x * Real.exp (-κ * x) :=
  ⟨Unit, inferInstance, fun _ => κ, fun _ => Q, fun _ => hκ, fun x => by simp⟩

lemma congr {f g : ℝ → ℝ} (hf : ExpPos f) (h : ∀ x, g x = f x) : ExpPos g := by
  obtain ⟨ι, _, κ, Q, hκ, hf⟩ := hf
  exact ⟨ι, inferInstance, κ, Q, hκ, fun x => (h x).trans (hf x)⟩

lemma add {f g : ℝ → ℝ} (hf : ExpPos f) (hg : ExpPos g) : ExpPos fun x => f x + g x := by
  obtain ⟨ι, _, κ, Q, hκ, hf⟩ := hf
  obtain ⟨ι', _, κ', Q', hκ', hg⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim κ κ', Sum.elim Q Q', fun i => ?_, fun x => ?_⟩
  · cases i with
    | inl i => exact hκ i
    | inr i => exact hκ' i
  · beta_reduce
    rw [Fintype.sum_sum_type, hf, hg]
    rfl

lemma polymul (p : ℝ[X]) {f : ℝ → ℝ} (hf : ExpPos f) : ExpPos fun x => p.eval x * f x := by
  obtain ⟨ι, _, κ, Q, hκ, hf⟩ := hf
  refine ⟨ι, inferInstance, κ, fun i => p * Q i, hκ, fun x => ?_⟩
  beta_reduce
  rw [hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [eval_mul]; ring

lemma const_mul (c : ℝ) {f : ℝ → ℝ} (hf : ExpPos f) : ExpPos fun x => c * f x :=
  (polymul (C c) hf).congr fun x => by rw [eval_C]

lemma sub {f g : ℝ → ℝ} (hf : ExpPos f) (hg : ExpPos g) : ExpPos fun x => f x - g x :=
  (add hf (const_mul (-1) hg)).congr fun x => by ring

lemma mul {f g : ℝ → ℝ} (hf : ExpPos f) (hg : ExpPos g) : ExpPos fun x => f x * g x := by
  obtain ⟨ι, _, κ, Q, hκ, hf⟩ := hf
  obtain ⟨ι', _, κ', Q', hκ', hg⟩ := hg
  refine ⟨ι × ι', inferInstance, fun p => κ p.1 + κ' p.2, fun p => Q p.1 * Q' p.2,
    fun p => add_pos (hκ p.1) (hκ' p.2), fun x => ?_⟩
  beta_reduce
  rw [hf, hg, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, show -(κ i + κ' j) * x = -κ i * x + -κ' j * x by ring, Real.exp_add]
  ring

lemma sum {ι : Type} [Fintype ι] {f : ι → ℝ → ℝ} (h : ∀ i, ExpPos (f i)) :
    ExpPos fun x => ∑ i, f i x := by
  classical
  have key : ∀ s : Finset ι, ExpPos fun x => ∑ i ∈ s, f i x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using zero
    | insert i s hi ih =>
      exact (add (h i) ih).congr fun x => by rw [Finset.sum_insert hi]
  exact key Finset.univ

/-- A function of the class that equals a polynomial on an open interval is zero, and so is
the polynomial. -/
lemma eq_poly {f : ℝ → ℝ} (hf : ExpPos f) (P : ℝ[X]) (c d : ℝ) (hcd : c < d)
    (h : ∀ x ∈ Ioo c d, f x = P.eval x) : P = 0 ∧ ∀ x, f x = 0 := by
  classical
  obtain ⟨ι, _, κ, Q, hκ, hf⟩ := hf
  set S := Finset.univ.image κ
  let T := {v // v ∈ S} ⊕ Unit
  let κ' : T → ℝ := Sum.elim (fun v => v.1) fun _ => 0
  let Q' : T → ℝ[X] := Sum.elim (fun v => ∑ i ∈ Finset.univ.filter (fun i => κ i = v.1), Q i)
    fun _ => -P
  have hSpos : ∀ v ∈ S, 0 < v := fun v hv => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact hκ i
  have hinj : Function.Injective κ' := by
    intro t t' htt
    cases t with
    | inl v =>
      cases t' with
      | inl w => exact congrArg Sum.inl (Subtype.ext htt)
      | inr _ => exact absurd htt (hSpos v.1 v.2).ne'
    | inr u =>
      cases t' with
      | inl w => exact absurd htt.symm (hSpos w.1 w.2).ne'
      | inr u' => rfl
  have hgroup : ∀ x, ∑ v : {v // v ∈ S}, (Q' (Sum.inl v)).eval x * Real.exp (-v.1 * x) = f x := by
    intro x
    show ∑ v : {v // v ∈ S}, (∑ i ∈ Finset.univ.filter (fun i => κ i = v.1), Q i).eval x *
      Real.exp (-v.1 * x) = _
    rw [hf x, Finset.sum_coe_sort S (fun v => (∑ i ∈ Finset.univ.filter (fun i => κ i = v), Q i).eval x *
      Real.exp (-v * x)), ← Finset.sum_fiberwise_of_maps_to (g := κ) (t := S)
      (fun i _ => Finset.mem_image_of_mem κ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hzero := Novel.SvenssonSpliceProof.indep κ' hinj Q' c d hcd fun x hx => by
    rw [Fintype.sum_sum_type]
    have := hgroup x
    simp only [κ', Q', Sum.elim_inl, Sum.elim_inr] at this ⊢
    rw [this, h x hx]
    simp
  refine ⟨neg_eq_zero.1 (hzero (Sum.inr ())), fun x => ?_⟩
  rw [← hgroup x]
  exact Finset.sum_eq_zero fun v _ => by rw [hzero (Sum.inl v), eval_zero, zero_mul]

end ExpPos

variable {K : ℕ} {n : Fin K → ℕ}

/-- `p_i` as a polynomial. -/
noncomputable def polyP (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) : ℝ[X] :=
  ∑ μ : Fin (n i + 1), C (z ⟨i, μ.castSucc⟩) * X ^ (μ : ℕ)

lemma polyP_eval (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (i : Fin K) (x : ℝ) :
    (polyP z i).eval x = poly z i x := by
  simp [polyP, poly, eval_finsetSum]

/-- Each first parameter derivative is a polynomial times `e^{−β x}`. -/
lemma dF_form (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (I : Σ i : Fin K, Fin (n i + 2)) :
    ∃ Q : ℝ[X], ∀ x, dF z I x = Q.eval x * Real.exp (-expo z I.1 * x) := by
  unfold dF
  by_cases h : (I.2 : ℕ) < n I.1 + 1
  · exact ⟨X ^ (I.2 : ℕ), fun x => by simp [h]⟩
  · exact ⟨-(X * polyP z I.1), fun x => by simp [h, polyP_eval]⟩

lemma dF_exp (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (hz : ∀ i, 0 < expo z i)
    (I : Σ i : Fin K, Fin (n i + 2)) : ExpPos (dF z I) := by
  obtain ⟨Q, hQ⟩ := dF_form z I
  exact (ExpPos.single Q (hz I.1)).congr hQ

lemma d2F_exp (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (hz : ∀ i, 0 < expo z i)
    (I J : Σ i : Fin K, Fin (n i + 2)) : ExpPos (d2F z I J) := by
  unfold d2F
  split_ifs
  · exact ExpPos.zero
  · exact (ExpPos.single (-(X ^ ((I.2 : ℕ) + 1))) (hz I.1)).congr fun x => by simp
  · exact (ExpPos.single (-(X ^ ((J.2 : ℕ) + 1))) (hz I.1)).congr fun x => by simp
  · exact (ExpPos.single (X ^ 2 * polyP z I.1) (hz I.1)).congr fun x => by
      simp [polyP_eval]
  · exact ExpPos.zero

/-- `∫_0^x Q(η) e^{−βη} dη` is a constant plus a function of the class. -/
lemma int_exp (Q : ℝ[X]) {β : ℝ} (hβ : 0 < β) :
    ∃ c₀ : ℝ, ∃ g : ℝ → ℝ, ExpPos g ∧
      ∀ x, ∫ η in (0:ℝ)..x, Q.eval η * Real.exp (-β * η) = c₀ + g x := by
  set q : ℝ[X] := ∑ ν ∈ Finset.range (Q.natDegree + 1),
    C (Q.coeff ν) * Standalone.CorrelatedFactorsReduction.Pnu β ν
  have hq : C β * q - derivative q = Q := by
    conv_rhs => rw [Q.as_sum_range_C_mul_X_pow]
    simp only [q, Finset.mul_sum, derivative_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [derivative_C_mul, ← Novel.CorrelatedFactorsReductionProof.Pnu_anti β hβ.ne' ν]
    ring
  refine ⟨q.eval 0, fun x => (-q).eval x * Real.exp (-β * x), ExpPos.single (-q) hβ, fun x => ?_⟩
  rw [Novel.SharefFilipovicMaxFactorsProof.int_of_anti Q q β hq x]
  simp only [eval_neg]
  ring

/-- `∂_x F` is in the class. -/
lemma deriv_exp (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (hz : ∀ i, 0 < expo z i) :
    ExpPos (deriv (FBEP z)) := by
  have hd : ∀ x, HasDerivAt (FBEP z)
      (∑ i, (derivative (polyP z i) - C (expo z i) * polyP z i).eval x *
        Real.exp (-expo z i * x)) x := fun x => by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      Novel.SharefFilipovicResidualProof.hd_pe (polyP z i) (expo z i) x
    convert h using 1
    funext y
    simp [FBEP, polyP_eval, Finset.sum_apply]
  refine (ExpPos.sum fun i => ExpPos.single (derivative (polyP z i) - C (expo z i) * polyP z i)
    (hz i)).congr fun x => (hd x).deriv

/-- The residual (3) is in the class. -/
lemma residual_exp (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (hz : ∀ i, 0 < expo z i)
    (a : (Σ i : Fin K, Fin (n i + 2)) → (Σ i : Fin K, Fin (n i + 2)) → ℝ)
    (b : (Σ i : Fin K, Fin (n i + 2)) → ℝ) : ExpPos (residualBEP z a b) := by
  have hint : ∀ J : Σ i : Fin K, Fin (n i + 2), ∃ c₀ : ℝ, ∃ g : ℝ → ℝ, ExpPos g ∧
      ∀ x, ∫ η in (0:ℝ)..x, dF z J η = c₀ + g x := fun J => by
    obtain ⟨Q, hQ⟩ := dF_form z J
    obtain ⟨c₀, g, hg, he⟩ := int_exp Q (hz J.1)
    exact ⟨c₀, g, hg, fun x => by rw [← he]; exact intervalIntegral.integral_congr fun η _ => hQ η⟩
  choose c₀ g hg he using hint
  have h1 : ExpPos fun x => ∑ I, b I * dF z I x :=
    ExpPos.sum fun I => ExpPos.const_mul (b I) (dF_exp z hz I)
  have h2 : ExpPos fun x => (1 / 2) * ∑ I, ∑ J, a I J * d2F z I J x :=
    ExpPos.const_mul _ (ExpPos.sum fun I => ExpPos.sum fun J =>
      ExpPos.const_mul (a I J) (d2F_exp z hz I J))
  have h3 : ExpPos fun x => ∑ I, ∑ J, a I J * dF z I x * (∫ η in (0:ℝ)..x, dF z J η) :=
    ExpPos.sum fun I => ExpPos.sum fun J =>
      ((ExpPos.const_mul (a I J * c₀ J) (dF_exp z hz I)).add
        (ExpPos.const_mul (a I J) ((dF_exp z hz I).mul (hg J)))).congr fun x => by
        rw [he J x]; ring
  exact ((h1.add h2).sub h3).sub (deriv_exp z hz) |>.congr fun x => rfl

lemma reduction : Standalone.SpliceVaryingExponents.reductionStatement := by
  intro K n z a b hz P c d hcd h
  exact (residual_exp z hz a b).eq_poly P c d hcd h

section Deriv
variable (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (I : Σ i : Fin K, Fin (n i + 2)) (x : ℝ)

lemma upd_deriv (J : Σ i : Fin K, Fin (n i + 2)) :
    HasDerivAt (fun w => Function.update z I w J) (if J = I then 1 else 0) (z I) := by
  by_cases h : J = I
  · subst h
    have e : (fun w => Function.update z J w J) = fun w => w :=
      funext fun w => Function.update_self J w z
    rw [e, ite_eq_left rfl]
    exact hasDerivAt_id' _
  · have e : (fun w => Function.update z I w J) = fun _ => z J :=
      funext fun w => Function.update_of_ne h w z
    rw [e, ite_eq_right h]
    exact hasDerivAt_const _ _

lemma poly_deriv (j : Fin K) :
    HasDerivAt (fun w => poly (Function.update z I w) j x)
      (∑ ν : Fin (n j + 1), (if (⟨j, ν.castSucc⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0) *
        x ^ (ν : ℕ)) (z I) := by
  have h := HasDerivAt.sum (u := Finset.univ)
    (A := fun (ν : Fin (n j + 1)) w => Function.update z I w ⟨j, ν.castSucc⟩ * x ^ (ν : ℕ))
    fun ν _ => (upd_deriv z I _).mul_const _
  convert h using 1
  funext w
  simp [poly, Finset.sum_apply]

lemma term_deriv (j : Fin K) :
    HasDerivAt (fun w => poly (Function.update z I w) j x *
        Real.exp (-expo (Function.update z I w) j * x))
      ((∑ ν : Fin (n j + 1),
          (if (⟨j, ν.castSucc⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0) * x ^ (ν : ℕ)) *
          Real.exp (-expo z j * x) +
        poly z j x * (Real.exp (-expo z j * x) *
          (-x * (if (⟨j, Fin.last (n j + 1)⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0))))
      (z I) := by
  have hlin : HasDerivAt (fun w => -expo (Function.update z I w) j * x)
      (-x * (if (⟨j, Fin.last (n j + 1)⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0))
      (z I) := by
    have := (upd_deriv z I ⟨j, Fin.last (n j + 1)⟩).const_mul (-x)
    convert this using 1
    funext w
    simp only [expo]
    ring
  have he := hlin.exp
  have h := (poly_deriv z I x j).mul he
  simp only [Function.update_eq_self] at h
  exact h

lemma first_deriv : HasDerivAt (fun w => FBEP (Function.update z I w) x) (dF z I x) (z I) := by
  classical
  have h := HasDerivAt.sum (u := Finset.univ)
    (A := fun j w => poly (Function.update z I w) j x *
      Real.exp (-expo (Function.update z I w) j * x)) fun j _ => term_deriv z I x j
  have hF : (fun w => FBEP (Function.update z I w) x) = ∑ j ∈ Finset.univ, fun w =>
      poly (Function.update z I w) j x * Real.exp (-expo (Function.update z I w) j * x) := by
    funext w; simp [FBEP, Finset.sum_apply]
  rw [hF]
  convert h using 1
  obtain ⟨i₀, μ₀⟩ := I
  have hne : ∀ j ≠ i₀, ∀ ν : Fin (n j + 2),
      (⟨j, ν⟩ : Σ i : Fin K, Fin (n i + 2)) ≠ ⟨i₀, μ₀⟩ := fun j hj ν h => hj (congrArg Sigma.fst h)
  rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hne j hj]) (by simp)]
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  induction μ₀ using Fin.lastCases with
  | last =>
    simp only [Fin.castSucc_ne_last, ite_false, zero_mul, Finset.sum_const_zero, ite_true, dF,
      Fin.val_last, lt_irrefl]
    ring
  | cast m =>
    simp only [(Fin.castSucc_ne_last m).symm, ite_false, Fin.castSucc_inj, dF, Fin.val_castSucc,
      m.isLt, ite_true]
    rw [Finset.sum_eq_single m (fun ν _ hν => by simp [hν]) (by simp)]
    simp

lemma exp_deriv (j : Fin K) :
    HasDerivAt (fun w => Real.exp (-expo (Function.update z I w) j * x))
      (Real.exp (-expo z j * x) *
        (-x * (if (⟨j, Fin.last (n j + 1)⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0)))
      (z I) := by
  have hlin : HasDerivAt (fun w => -expo (Function.update z I w) j * x)
      (-x * (if (⟨j, Fin.last (n j + 1)⟩ : Σ i : Fin K, Fin (n i + 2)) = I then 1 else 0))
      (z I) := by
    have := (upd_deriv z I ⟨j, Fin.last (n j + 1)⟩).const_mul (-x)
    convert this using 1
    funext w
    simp only [expo]
    ring
  have he := hlin.exp
  simp only [Function.update_eq_self] at he
  exact he

lemma second_deriv (J : Σ i : Fin K, Fin (n i + 2)) :
    HasDerivAt (fun w => dF (Function.update z J w) I x) (d2F z I J x) (z J) := by
  classical
  obtain ⟨i, μ⟩ := I
  obtain ⟨j, ν⟩ := J
  induction μ using Fin.lastCases with
  | last =>
    have h := (term_deriv z ⟨j, ν⟩ x i).const_mul (-x)
    have hf : (fun w => dF (Function.update z ⟨j, ν⟩ w) ⟨i, Fin.last (n i + 1)⟩ x) =
        fun w => -x * (poly (Function.update z ⟨j, ν⟩ w) i x *
          Real.exp (-expo (Function.update z ⟨j, ν⟩ w) i * x)) := by
      funext w; simp [dF]; ring
    rw [hf]
    convert h using 1
    by_cases hij : i = j
    · subst hij
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      induction ν using Fin.lastCases with
      | last =>
        simp only [Fin.castSucc_ne_last, ite_false, zero_mul, Finset.sum_const_zero, ite_true, d2F,
          Fin.val_last, lt_irrefl]
        ring
      | cast m =>
        simp only [(Fin.castSucc_ne_last m).symm, ite_false, Fin.castSucc_inj, d2F,
          Fin.val_castSucc, m.isLt, ite_true, Fin.val_last, lt_irrefl]
        rw [Finset.sum_eq_single m (fun ν _ hν => by simp [hν]) (by simp)]
        simp only [ite_true, one_mul]
        ring
    · have hne : ∀ ρ : Fin (n i + 2),
          (⟨i, ρ⟩ : Σ i : Fin K, Fin (n i + 2)) ≠ ⟨j, ν⟩ := fun ρ h => hij (congrArg Sigma.fst h)
      simp [hne, d2F, hij]
  | cast m =>
    have h := (exp_deriv z ⟨j, ν⟩ x i).const_mul (x ^ (m : ℕ))
    have hf : (fun w => dF (Function.update z ⟨j, ν⟩ w) ⟨i, m.castSucc⟩ x) =
        fun w => x ^ (m : ℕ) * Real.exp (-expo (Function.update z ⟨j, ν⟩ w) i * x) := by
      funext w; simp [dF, Fin.val_castSucc, m.isLt]
    rw [hf]
    convert h using 1
    by_cases hij : i = j
    · subst hij
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      induction ν using Fin.lastCases with
      | last =>
        simp only [ite_true, d2F, Fin.val_castSucc, m.isLt, Fin.val_last, lt_irrefl, ite_false]
        ring
      | cast m' =>
        simp only [(Fin.castSucc_ne_last m').symm, ite_false, d2F, Fin.val_castSucc, m.isLt,
          m'.isLt, ite_true]
        ring
    · have hne : (⟨i, Fin.last (n i + 1)⟩ : Σ i : Fin K, Fin (n i + 2)) ≠ ⟨j, ν⟩ :=
        fun h => hij (congrArg Sigma.fst h)
      simp [hne, d2F, hij]

end Deriv

lemma deriv' : Standalone.SpliceVaryingExponents.derivStatement := fun _ _ z I x =>
  ⟨first_deriv z I x, fun J => second_deriv z I x J⟩

lemma transfer : Standalone.SpliceVaryingExponents.transferStatement := by
  intro K n X _ ν Z a b hP hAX
  filter_upwards [hP, hAX] with p hp ⟨P, c, d, hcd, h⟩
  exact (reduction K n (Z p) (a p) (b p) hp P c d hcd h).2

theorem spliceVaryingExponents : Standalone.SpliceVaryingExponents.statement :=
  ⟨deriv', reduction, transfer⟩

end Novel.SpliceVaryingExponentsProof

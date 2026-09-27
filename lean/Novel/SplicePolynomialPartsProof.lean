import Standalone.SplicePolynomialParts
import Novel.SpliceVaryingExponentsProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Polynomial Set Filter
open Standalone.SpliceVaryingExponents Standalone.SplicePolynomialParts
namespace Novel.SplicePolynomialPartsProof
open Novel.SpliceVaryingExponentsProof

variable {d K : ℕ} {n : Fin K → ℕ}

/-- `p_0` as a polynomial. -/
noncomputable def p0 (z : Idx d K n → ℝ) : ℝ[X] := ∑ μ : Fin (d + 1), C (z (Sum.inl μ)) * X ^ (μ : ℕ)

lemma p0_eval (z : Idx d K n → ℝ) (x : ℝ) :
    (p0 z).eval x = ∑ μ : Fin (d + 1), z (Sum.inl μ) * x ^ (μ : ℕ) := by
  simp [p0, eval_finsetSum]

lemma F43_deriv (z : Idx d K n → ℝ) (x : ℝ) :
    deriv (F43 z) x = (derivative (p0 z)).eval x + deriv (FBEP fun I => z (Sum.inr I)) x := by
  have hB : DifferentiableAt ℝ (FBEP fun I => z (Sum.inr I)) x := by
    have hd : ∀ x, HasDerivAt (FBEP fun I => z (Sum.inr I))
        (∑ i, (derivative (polyP (fun I => z (Sum.inr I)) i) - C (expo (fun I => z (Sum.inr I)) i) *
          polyP (fun I => z (Sum.inr I)) i).eval x *
          Real.exp (-expo (fun I => z (Sum.inr I)) i * x)) x := fun x => by
      have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        Novel.SharefFilipovicResidualProof.hd_pe (polyP (fun I => z (Sum.inr I)) i)
          (expo (fun I => z (Sum.inr I)) i) x
      convert h using 1
      funext y
      simp [FBEP, polyP_eval, Finset.sum_apply]
    exact (hd x).differentiableAt
  have hP := (p0 z).hasDerivAt x
  have e : F43 z = fun x => (p0 z).eval x + FBEP (fun I => z (Sum.inr I)) x := by
    funext x; rw [p0_eval]; rfl
  rw [e]
  exact (hP.add hB.hasDerivAt).deriv

/-- `∫_0^x ∂_J F` for an exponential parameter is a constant plus a member of the class. -/
lemma int_dF (z : (Σ i : Fin K, Fin (n i + 2)) → ℝ) (hz : ∀ i, 0 < expo z i)
    (J : Σ i : Fin K, Fin (n i + 2)) :
    ∃ c₀ : ℝ, ∃ g : ℝ → ℝ, ExpPos g ∧ ∀ x, ∫ η in (0:ℝ)..x, dF z J η = c₀ + g x := by
  obtain ⟨Q, hQ⟩ := dF_form z J
  obtain ⟨c₀, g, hg, he⟩ := int_exp Q (hz J.1)
  exact ⟨c₀, g, hg, fun x => by rw [← he]; exact intervalIntegral.integral_congr fun η _ => hQ η⟩

lemma int_pow (ν : ℕ) (x : ℝ) : ∫ η in (0:ℝ)..x, η ^ ν = x ^ (ν + 1) / (ν + 1) := by
  rw [integral_pow]; simp

/-- The residual is a polynomial of degree at most `d`, minus the double sum of (43.2), plus a
member of the positive-exponent class. -/
lemma decomp43 (z : Idx d K n → ℝ) (hz : ∀ i, 0 < expo (fun I => z (Sum.inr I)) i)
    (a : Idx d K n → Idx d K n → ℝ) (b : Idx d K n → ℝ) :
    ∃ Plow : ℝ[X], Plow.natDegree ≤ d ∧ ∃ G : ℝ → ℝ, ExpPos G ∧ ∀ x,
      residual43 z a b x = Plow.eval x -
        (∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
          a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1))) + G x := by
  set zb : (Σ i : Fin K, Fin (n i + 2)) → ℝ := fun I => z (Sum.inr I)
  choose c g hg hcg using int_dF zb hz
  let Plow : ℝ[X] := ∑ μ : Fin (d + 1), C (b (Sum.inl μ)) * X ^ (μ : ℕ) -
    ∑ μ : Fin (d + 1), C (∑ J, a (Sum.inl μ) (Sum.inr J) * c J) * X ^ (μ : ℕ) - derivative (p0 z)
  have hdeg : Plow.natDegree ≤ d := by
    have h1 : ∀ (f : Fin (d + 1) → ℝ), (∑ μ : Fin (d + 1), C (f μ) * X ^ (μ : ℕ)).natDegree ≤ d :=
      fun f => natDegree_sum_le_of_forall_le _ _ fun μ _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 μ.isLt)
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
      (max_le (h1 _) (h1 _))) ((natDegree_derivative_le _).trans ?_))
    exact (Nat.sub_le _ 1).trans (h1 _)
  let G : ℝ → ℝ := fun x => (∑ J, b (Sum.inr J) * dF zb J x) +
    (1 / 2) * (∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * d2F zb J J' x) -
    ((∑ μ : Fin (d + 1), ∑ J, a (Sum.inl μ) (Sum.inr J) * x ^ (μ : ℕ) * g J x) +
      (∑ J, ∑ ν : Fin (d + 1), a (Sum.inr J) (Sum.inl ν) * dF zb J x *
        (x ^ ((ν : ℕ) + 1) / ((ν : ℕ) + 1))) +
      (∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * dF zb J x * (c J' + g J' x))) -
    deriv (FBEP zb) x
  have hG : ExpPos G := by
    have g1 : ExpPos fun x => ∑ J, b (Sum.inr J) * dF zb J x :=
      ExpPos.sum fun J => ExpPos.const_mul _ (dF_exp zb hz J)
    have g2 : ExpPos fun x => (1 / 2) * (∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * d2F zb J J' x) :=
      ExpPos.const_mul _ (ExpPos.sum fun J => ExpPos.sum fun J' =>
        ExpPos.const_mul _ (d2F_exp zb hz J J'))
    have g3 : ExpPos fun x => ∑ μ : Fin (d + 1), ∑ J,
        a (Sum.inl μ) (Sum.inr J) * x ^ (μ : ℕ) * g J x :=
      ExpPos.sum fun μ => ExpPos.sum fun J =>
        (ExpPos.polymul (C (a (Sum.inl μ) (Sum.inr J)) * X ^ (μ : ℕ)) (hg J)).congr fun x => by
          simp only [eval_mul, eval_C, eval_pow, eval_X]
    have g4 : ExpPos fun x => ∑ J, ∑ ν : Fin (d + 1), a (Sum.inr J) (Sum.inl ν) * dF zb J x *
        (x ^ ((ν : ℕ) + 1) / ((ν : ℕ) + 1)) :=
      ExpPos.sum fun J => ExpPos.sum fun ν =>
        (ExpPos.polymul (C (a (Sum.inr J) (Sum.inl ν) / ((ν : ℕ) + 1)) * X ^ ((ν : ℕ) + 1))
          (dF_exp zb hz J)).congr fun x => by
          simp only [eval_mul, eval_C, eval_pow, eval_X]; ring
    have g5 : ExpPos fun x => ∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * dF zb J x *
        (c J' + g J' x) :=
      ExpPos.sum fun J => ExpPos.sum fun J' =>
        ((ExpPos.const_mul (a (Sum.inr J) (Sum.inr J') * c J') (dF_exp zb hz J)).add
          (ExpPos.const_mul (a (Sum.inr J) (Sum.inr J')) ((dF_exp zb hz J).mul (hg J')))).congr
          fun x => by ring
    exact (((g1.add g2).sub ((g3.add g4).add g5)).sub (deriv_exp zb hz)).congr fun x => rfl
  refine ⟨Plow, hdeg, G, hG, fun x => ?_⟩
  have eA : ∑ I, b I * dF43 z I x = (∑ μ : Fin (d + 1), b (Sum.inl μ) * x ^ (μ : ℕ)) +
      ∑ J, b (Sum.inr J) * dF zb J x := by
    rw [Fintype.sum_sum_type]; rfl
  have eB : ∑ I, ∑ J, a I J * d2F43 z I J x =
      ∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * d2F zb J J' x := by
    simp [Fintype.sum_sum_type, d2F43, zb]
  have eC : ∑ I, ∑ J, a I J * dF43 z I x * (∫ η in (0:ℝ)..x, dF43 z J η) =
      (∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
        a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1))) +
      (∑ μ : Fin (d + 1), ∑ J, a (Sum.inl μ) (Sum.inr J) * c J * x ^ (μ : ℕ)) +
      ((∑ μ : Fin (d + 1), ∑ J, a (Sum.inl μ) (Sum.inr J) * x ^ (μ : ℕ) * g J x) +
        (∑ J, ∑ ν : Fin (d + 1), a (Sum.inr J) (Sum.inl ν) * dF zb J x *
          (x ^ ((ν : ℕ) + 1) / ((ν : ℕ) + 1))) +
        (∑ J, ∑ J', a (Sum.inr J) (Sum.inr J') * dF zb J x * (c J' + g J' x))) := by
    have hcg' : ∀ J x, ∫ η in (0:ℝ)..x, dF (fun L => z (Sum.inr L)) J η = c J + g J x := hcg
    simp only [Fintype.sum_sum_type, dF43, Sum.elim_inl, Sum.elim_inr, int_pow, hcg']
    have e1 : ∀ μ : Fin (d + 1), ∑ ν : Fin (d + 1), a (Sum.inl μ) (Sum.inl ν) * x ^ (μ : ℕ) *
        (x ^ ((ν : ℕ) + 1) / ((ν : ℕ) + 1)) = ∑ ν : Fin (d + 1),
        a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1)) := fun μ =>
      Finset.sum_congr rfl fun ν _ => by rw [add_assoc, pow_add]; ring
    have e2 : ∀ μ : Fin (d + 1), ∑ J, a (Sum.inl μ) (Sum.inr J) * x ^ (μ : ℕ) * (c J + g J x) =
        (∑ J, a (Sum.inl μ) (Sum.inr J) * c J * x ^ (μ : ℕ)) +
          ∑ J, a (Sum.inl μ) (Sum.inr J) * x ^ (μ : ℕ) * g J x := fun μ => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun J _ => by ring
    simp only [e1, e2, Finset.sum_add_distrib]
    ring
  have ePlow : Plow.eval x = (∑ μ : Fin (d + 1), b (Sum.inl μ) * x ^ (μ : ℕ)) -
      (∑ μ : Fin (d + 1), ∑ J, a (Sum.inl μ) (Sum.inr J) * c J * x ^ (μ : ℕ)) -
      (derivative (p0 z)).eval x := by
    simp only [Plow, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
  rw [residual43, eA, eB, eC, F43_deriv, ePlow]
  simp only [G]
  ring

/-- The coefficients of (43.2) above degree `d` vanish when `R` is affine (above degree 1 too). -/
lemma coeff_hi (z : Idx d K n → ℝ) (hz : ∀ i, 0 < expo (fun I => z (Sum.inr I)) i)
    (a : Idx d K n → Idx d K n → ℝ) (b : Idx d K n → ℝ) (c₀ c₁ : ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → residual43 z a b x = c₀ + c₁ * x) (k : ℕ) (hk : d < k)
    (hk1 : 1 < k ∨ c₁ = 0) :
    ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      (if (μ : ℕ) + (ν : ℕ) + 1 = k then a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1) else 0) = 0 := by
  obtain ⟨Plow, hdeg, G, hG, hR⟩ := decomp43 z hz a b
  let HiP : ℝ[X] := ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
    C (a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1)) * X ^ ((μ : ℕ) + (ν : ℕ) + 1)
  have hHi : ∀ x, HiP.eval x = ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1)) := fun x => by
    simp only [HiP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  let Q : ℝ[X] := C c₀ + C c₁ * X - Plow + HiP
  have hQ := (hG.eq_poly Q 0 1 one_pos fun x hx => by
    have := hR x
    rw [h x hx.1.le, ← hHi] at this
    simp only [Q, eval_add, eval_sub, eval_mul, eval_C, eval_X]
    linarith).1
  have hc := congrArg (coeff · k) hQ
  simp only [Q, coeff_add, coeff_sub, coeff_C, coeff_C_mul_X, Polynomial.coeff_zero] at hc
  rw [ite_eq_right (by omega), coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hk)] at hc
  have hHk : HiP.coeff k = ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      (if (μ : ℕ) + (ν : ℕ) + 1 = k then a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1) else 0) := by
    simp only [HiP, finsetSum_coeff, coeff_C_mul_X_pow]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
      split_ifs <;> first | rfl | (exfalso; omega)
  rw [← hHk]
  rcases hk1 with hk1 | hk1
  · rw [ite_eq_right (by omega)] at hc; linarith
  · rw [hk1] at hc; split_ifs at hc <;> linarith

lemma rows : Standalone.SplicePolynomialParts.rowsStatement := by
  intro d K n hd z hz a b ha ⟨c₀, c₁, h⟩ μ ν hμν
  classical
  set m := (d - 1) / 2
  -- every diagonal entry beyond `m` vanishes
  have hdiag : ∀ ρ : Fin (d + 1), m < (ρ : ℕ) → a (Sum.inl ρ) (Sum.inl ρ) = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨ρ₀, hρ₀m, hρ₀⟩ := hne
    have hS : (Finset.univ.filter fun ρ : Fin (d + 1) => a (Sum.inl ρ) (Sum.inl ρ) ≠ 0).Nonempty :=
      ⟨ρ₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hρ₀⟩⟩
    obtain ⟨ρs, hρs, hmax⟩ := Finset.exists_max_image _ (fun ρ : Fin (d + 1) => (ρ : ℕ)) hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρs hmax
    have hge : (ρ₀ : ℕ) ≤ ρs := hmax ρ₀ hρ₀
    have hbig : ∀ ρ : Fin (d + 1), (ρs : ℕ) < ρ → ∀ σ,
        a (Sum.inl ρ) σ = 0 ∧ a σ (Sum.inl ρ) = 0 := fun ρ hρ σ => by
      have : a (Sum.inl ρ) (Sum.inl ρ) = 0 := by
        by_contra h'; exact absurd (hmax ρ h') (not_le.2 hρ)
      exact Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ σ this
    have hc := coeff_hi z hz a b c₀ c₁ h (2 * ρs + 1) (by omega) (Or.inl (by omega))
    rw [Finset.sum_eq_single ρs] at hc
    · rw [Finset.sum_eq_single ρs] at hc
      · rw [ite_eq_left (by ring)] at hc
        have hpos : (0:ℝ) < (ρs : ℕ) + 1 := by positivity
        exact hρs (by field_simp at hc; linarith)
      · intro ν _ hν
        rw [ite_eq_right (fun h => hν (Fin.ext (by omega)))]
      · simp
    · intro μ' _ hμ'
      refine Finset.sum_eq_zero fun ν' _ => ?_
      split_ifs with hs
      · rcases lt_or_gt_of_ne (fun h => hμ' (Fin.ext h)) with hlt | hlt
        · rw [(hbig ν' (by omega) (Sum.inl μ')).2, zero_div]
        · rw [(hbig μ' hlt (Sum.inl ν')).1, zero_div]
      · rfl
    · simp
  rcases hμν with hμ | hν
  · exact (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ (Sum.inl ν) (hdiag μ hμ)).1
  · exact (Novel.SharefFilipovicMaxFactorsProof.psd_zero ha _ (Sum.inl μ) (hdiag ν hν)).2

/-- `R` depends on `b` only through `∑_I b_I ∂_I F`. -/
lemma residual_sub (z : Idx d K n → ℝ) (a : Idx d K n → Idx d K n → ℝ) (b b' : Idx d K n → ℝ)
    (x : ℝ) : residual43 z a b x - residual43 z a b' x = ∑ I, (b I - b' I) * dF43 z I x := by
  simp only [residual43, sub_mul, Finset.sum_sub_distrib]
  ring

lemma same : Standalone.SplicePolynomialParts.sameStatement := by
  intro d K n hd z a b
  classical
  set i0 : Idx d K n := Sum.inl 0
  set i1 : Idx d K n := Sum.inl ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by
    have := Fin.ext_iff.1 (Sum.inl_injective h); simp at this
  have hdF0 : ∀ x, dF43 z i0 x = 1 := fun x => by simp [i0, dF43]
  have hdF1 : ∀ x, dF43 z i1 x = x := fun x => by simp [i1, dF43]
  have hdiff : ∀ b' : Idx d K n → ℝ, (∀ I, I ≠ i0 → I ≠ i1 → b' I = b I) → ∀ x,
      residual43 z a b x - residual43 z a b' x = (b i0 - b' i0) + (b i1 - b' i1) * x :=
    fun b' hb' x => by
      rw [residual_sub, Finset.sum_eq_add i0 i1 h01 (fun I _ hI => by
        rw [hb' I hI.1 hI.2, sub_self, zero_mul]) (by simp) (by simp), hdF0, hdF1, mul_one]
  constructor
  · rintro ⟨c₀, c₁, h⟩
    let b' := Function.update (Function.update b i0 (b i0 - c₀)) i1 (b i1 - c₁)
    have hb' : ∀ I, I ≠ i0 → I ≠ i1 → b' I = b I := fun I h0 h1 => by
      simp [b', Function.update_of_ne h0, Function.update_of_ne h1]
    refine ⟨b', hb', fun x hx => ?_⟩
    have e := hdiff b' hb' x
    have e0 : b' i0 = b i0 - c₀ := by simp [b', Function.update_of_ne h01]
    have e1 : b' i1 = b i1 - c₁ := by simp [b']
    rw [e0, e1, h x hx] at e
    linarith
  · rintro ⟨b', hb', h⟩
    refine ⟨b i0 - b' i0, b i1 - b' i1, fun x hx => ?_⟩
    have e := hdiff b' hb' x
    rw [h x hx] at e
    linarith

/-- For a polynomial block, `R = ∑_k b_{0,k} x^k − ∑ a x^{μ+ν+1}/(ν+1) − p_0'(x)`. -/
lemma residual_K0 (n : Fin 0 → ℕ) (z : Idx d 0 n → ℝ) (a : Idx d 0 n → Idx d 0 n → ℝ)
    (b : Idx d 0 n → ℝ) (x : ℝ) :
    residual43 z a b x = (∑ μ : Fin (d + 1), b (Sum.inl μ) * x ^ (μ : ℕ)) -
      (∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
        a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1))) -
      (derivative (p0 z)).eval x := by
  have hF : FBEP (fun I => z (Sum.inr I)) = fun _ => 0 := funext fun y => by simp [FBEP]
  simp only [residual43, Fintype.sum_sum_type, F43_deriv, hF, deriv_const, dF43, Sum.elim_inl,
    int_pow, Finset.univ_eq_empty, Finset.sum_empty, add_zero, d2F43, mul_zero,
    Finset.sum_const_zero]
  have e : ∀ μ : Fin (d + 1), ∑ ν : Fin (d + 1), a (Sum.inl μ) (Sum.inl ν) * x ^ (μ : ℕ) *
      (x ^ ((ν : ℕ) + 1) / ((ν : ℕ) + 1)) = ∑ ν : Fin (d + 1),
      a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1)) := fun μ =>
    Finset.sum_congr rfl fun ν _ => by rw [add_assoc, pow_add]; ring
  simp only [e]

lemma attained : Standalone.SplicePolynomialParts.attainedStatement := by
  intro d n hd z a ha
  classical
  set m := (d - 1) / 2
  let HiP : ℝ[X] := ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
    C (a (Sum.inl μ) (Sum.inl ν) / ((ν : ℕ) + 1)) * X ^ ((μ : ℕ) + (ν : ℕ) + 1)
  have hHdeg : HiP.natDegree ≤ d := by
    refine natDegree_sum_le_of_forall_le _ _ fun μ _ =>
      natDegree_sum_le_of_forall_le _ _ fun ν _ => ?_
    by_cases hμν : (μ : ℕ) ≤ m ∧ (ν : ℕ) ≤ m
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · have : a (Sum.inl μ) (Sum.inl ν) = 0 := ha μ ν (by omega)
      simp [this]
  set Q : ℝ[X] := derivative (p0 z) + HiP
  have hQdeg : Q.natDegree ≤ d := by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_derivative_le _).trans ?_) hHdeg)
    refine (Nat.sub_le _ 1).trans (natDegree_sum_le_of_forall_le _ _ fun μ _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 μ.isLt))
  refine ⟨Sum.elim (fun μ => Q.coeff μ) fun _ => 0, fun x => ?_⟩
  rw [residual_K0]
  have hsum : ∑ μ : Fin (d + 1), (Sum.elim (fun μ : Fin (d + 1) => Q.coeff μ) fun _ => 0 :
      Idx d 0 n → ℝ) (Sum.inl μ) * x ^ (μ : ℕ) = Q.eval x := by
    rw [eval_eq_sum_range' (n := d + 1) (by omega), ← Fin.sum_univ_eq_sum_range]
    rfl
  have hHi : HiP.eval x = ∑ μ : Fin (d + 1), ∑ ν : Fin (d + 1),
      a (Sum.inl μ) (Sum.inl ν) * (x ^ ((μ : ℕ) + (ν : ℕ) + 1) / ((ν : ℕ) + 1)) := by
    simp only [HiP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  rw [hsum, ← hHi]
  simp only [Q, eval_add]
  ring

lemma level : Standalone.SplicePolynomialParts.levelStatement := by
  refine ⟨fun K n z hz a b h => ?_, fun n z a b => ?_⟩
  · have hc := coeff_hi z hz a b 0 0 (fun x hx => by rw [h x hx]; ring) 1 (by omega) (Or.inr rfl)
    simpa using hc
  · refine ⟨b (Sum.inl 0), -a (Sum.inl 0) (Sum.inl 0), fun x => ?_⟩
    rw [residual_K0]
    have hd : derivative (p0 z) = 0 := by simp [p0]
    simp [hd]
    ring

lemma updG {ι : Type*} [DecidableEq ι] (z : ι → ℝ) (I J : ι) :
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

/-- Updating a polynomial coordinate leaves the exponential parameters unchanged. -/
lemma upd_inl (z : Idx d K n → ℝ) (μ : Fin (d + 1)) (w : ℝ) :
    (fun L => Function.update z (Sum.inl μ) w (Sum.inr L)) = fun L => z (Sum.inr L) :=
  funext fun L => by simp

/-- Updating an exponential coordinate is updating the BEP parameters. -/
lemma upd_inr (z : Idx d K n → ℝ) (J : Σ i : Fin K, Fin (n i + 2)) (w : ℝ) :
    (fun L => Function.update z (Sum.inr J) w (Sum.inr L)) =
      Function.update (fun L => z (Sum.inr L)) J w := by
  classical
  funext L
  by_cases h : L = J
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (Sum.inr_injective e)), Function.update_of_ne h]

lemma deriv43 : Standalone.SplicePolynomialParts.derivStatement := by
  intro d K n z I x
  classical
  set zb : (Σ i : Fin K, Fin (n i + 2)) → ℝ := fun L => z (Sum.inr L)
  refine ⟨?_, fun J => ?_⟩
  · cases I with
    | inl μ =>
      have hpoly : HasDerivAt (fun w => ∑ ν : Fin (d + 1),
          Function.update z (Sum.inl μ) w (Sum.inl ν) * x ^ (ν : ℕ)) (x ^ (μ : ℕ)) (z (Sum.inl μ)) := by
        have h := HasDerivAt.sum (u := Finset.univ)
          (A := fun (ν : Fin (d + 1)) w => Function.update z (Sum.inl μ) w (Sum.inl ν) * x ^ (ν : ℕ))
          (A' := fun ν => (if (Sum.inl ν : Idx d K n) = Sum.inl μ then 1 else 0) * x ^ (ν : ℕ))
          (x := z (Sum.inl μ)) fun ν _ => (updG z (Sum.inl μ) (Sum.inl ν)).mul_const _
        convert h using 1
        · funext w; simp [Finset.sum_apply]
        · rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [hν]) (by simp)]
          simp
      have hF : (fun w => F43 (Function.update z (Sum.inl μ) w) x) = fun w =>
          (∑ ν : Fin (d + 1), Function.update z (Sum.inl μ) w (Sum.inl ν) * x ^ (ν : ℕ)) +
            FBEP zb x := funext fun w => by
        simp only [F43]; rw [upd_inl]
      rw [hF]
      simpa [dF43] using hpoly.add_const (FBEP zb x)
    | inr J =>
      have hF : (fun w => F43 (Function.update z (Sum.inr J) w) x) = fun w =>
          (∑ ν : Fin (d + 1), z (Sum.inl ν) * x ^ (ν : ℕ)) +
            FBEP (Function.update zb J w) x := funext fun w => by
        simp only [F43]
        rw [upd_inr]
        congr 1
      rw [hF]
      exact (Novel.SpliceVaryingExponentsProof.first_deriv zb J x).const_add _
  · cases I with
    | inl μ =>
      have e : (fun w => dF43 (Function.update z J w) (Sum.inl μ) x) = fun _ => x ^ (μ : ℕ) := rfl
      rw [e]
      cases J <;> exact hasDerivAt_const _ _
    | inr I' =>
      cases J with
      | inl ν =>
        have e : (fun w => dF43 (Function.update z (Sum.inl ν) w) (Sum.inr I') x) =
            fun _ => dF zb I' x := funext fun w => by
          simp only [dF43, Sum.elim_inr]; rw [upd_inl]
        rw [e]
        exact hasDerivAt_const _ _
      | inr J' =>
        have e : (fun w => dF43 (Function.update z (Sum.inr J') w) (Sum.inr I') x) =
            fun w => dF (Function.update zb J' w) I' x := funext fun w => by
          simp only [dF43, Sum.elim_inr]; rw [upd_inr]
        rw [e]
        exact Novel.SpliceVaryingExponentsProof.second_deriv zb I' x J'

theorem splicePolynomialParts : Standalone.SplicePolynomialParts.statement :=
  ⟨deriv43, same, rows, attained, level⟩

end Novel.SplicePolynomialPartsProof

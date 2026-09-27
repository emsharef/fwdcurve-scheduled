import Standalone.SharefFilipovicResidual
import Novel.SharefFilipovicIndependenceProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

open Set Polynomial Filter
open Standalone.SharefFilipovicResidual
namespace Novel.SharefFilipovicResidualProof

variable (β : ℝ)

/-- Exponential polynomials with the exponents `−β, −2β, −3β, −4β` and no exponent zero. -/
def IsEP (f : ℝ → ℝ) : Prop :=
  ∃ Q : Fin 4 → ℝ[X], ∀ x, f x = ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x)

lemma ep_zero : IsEP β (fun _ => 0) := ⟨0, fun x => by simp⟩

lemma ep_add {f g : ℝ → ℝ} (hf : IsEP β f) (hg : IsEP β g) : IsEP β (fun x => f x + g x) := by
  obtain ⟨Q, hQ⟩ := hf
  obtain ⟨R, hR⟩ := hg
  exact ⟨Q + R, fun x => by show f x + g x = _; rw [hQ, hR, ← Finset.sum_add_distrib]; simp [add_mul]⟩

lemma ep_smul (c : ℝ) {f : ℝ → ℝ} (hf : IsEP β f) : IsEP β (fun x => c * f x) := by
  obtain ⟨Q, hQ⟩ := hf
  exact ⟨fun i => C c * Q i, fun x => by show c * f x = _; rw [hQ, Finset.mul_sum]; simp [mul_assoc]⟩

lemma ep_neg {f : ℝ → ℝ} (hf : IsEP β f) : IsEP β (fun x => -f x) := by
  simpa using ep_smul β (-1) hf

lemma ep_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (h : ∀ i ∈ s, IsEP β (f i)) :
    IsEP β (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ep_zero β
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ep_add β (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma ep_mono (m : ℕ) (hm : m < 4) (p : ℝ[X]) :
    IsEP β (fun x => p.eval x * Real.exp (-((m:ℝ) + 1) * β * x)) := by
  classical
  refine ⟨Pi.single ⟨m, hm⟩ p, fun x => ?_⟩
  rw [Finset.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- For `λ ≠ 0` every polynomial `p` is `λ q − q'` for a polynomial `q`. -/
lemma anti (l : ℝ) (hl : l ≠ 0) : ∀ n (p : ℝ[X]), p.natDegree ≤ n →
    ∃ q : ℝ[X], C l * q - derivative q = p := by
  have hinv : ∀ p : ℝ[X], C l * (C l⁻¹ * p) = p := fun p => by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hl, C_1, one_mul]
  intro n
  induction n with
  | zero =>
    intro p hp
    have hd : derivative p = 0 := derivative_of_natDegree_zero (Nat.le_zero.1 hp)
    refine ⟨C l⁻¹ * p, ?_⟩
    rw [derivative_mul, derivative_C, zero_mul, zero_add, hd, mul_zero, sub_zero, hinv]
  | succ n ih =>
    intro p hp
    have hdeg : (C l⁻¹ * derivative p).natDegree ≤ n :=
      (natDegree_C_mul_le _ _).trans ((natDegree_derivative_le p).trans (by omega))
    obtain ⟨q2, hq2⟩ := ih _ hdeg
    refine ⟨C l⁻¹ * p + q2, ?_⟩
    rw [mul_add, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination hinv p + hq2

/-- The derivative of `p(x) e^{−λx}`. -/
lemma hd_pe (p : ℝ[X]) (l x : ℝ) :
    HasDerivAt (fun x => p.eval x * Real.exp (-l * x))
      ((derivative p - C l * p).eval x * Real.exp (-l * x)) x := by
  have h1 : HasDerivAt (fun x => Real.exp (-l * x)) (Real.exp (-l * x) * (-l)) x := by
    have := ((hasDerivAt_id x).const_mul (-l)).exp
    convert this using 1 <;> simp
  convert (p.hasDerivAt x).mul h1 using 1
  simp only [eval_sub, eval_mul, eval_C]
  ring

/-- `∫_0^x p(η) e^{−λη} dη = c − q(x) e^{−λx}`. -/
lemma int_pe (p : ℝ[X]) (l : ℝ) (hl : l ≠ 0) :
    ∃ (q : ℝ[X]) (c : ℝ), ∀ x, ∫ η in (0:ℝ)..x, p.eval η * Real.exp (-l * η) =
      c - q.eval x * Real.exp (-l * x) := by
  obtain ⟨q, hq⟩ := anti l hl p.natDegree p le_rfl
  refine ⟨q, q.eval 0, fun x => ?_⟩
  have hH : ∀ y, HasDerivAt (fun y => -(q.eval y * Real.exp (-l * y)))
      (p.eval y * Real.exp (-l * y)) y := fun y => by
    have := (hd_pe q l y).neg
    convert this using 1
    rw [← hq]
    simp only [eval_sub, eval_mul, eval_C]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hH y)
    ((p.continuous.mul (by fun_prop)).intervalIntegrable _ _)]
  simp
  ring

section Basis
variable {n₁ n₂ : ℕ}

/-- The exponent index of a basis function: `0` for `e^{−βx}`, `1` for `e^{−2βx}`. -/
def kIdx : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The polynomial factor of a basis function. -/
noncomputable def pIdx : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ[X] :=
  Sum.elim (fun μ => X ^ (μ : ℕ)) (fun μ => X ^ (μ : ℕ))

lemma kIdx_le (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) : kIdx i ≤ 1 := by
  cases i <;> simp [kIdx]

lemma phi_eq (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (x : ℝ) :
    phi034 β n₁ n₂ i x = (pIdx i).eval x * Real.exp (-(((kIdx i : ℕ) : ℝ) + 1) * β * x) := by
  cases i <;> simp only [phi034, pIdx, kIdx, Sum.elim_inl, Sum.elim_inr, eval_pow, eval_X] <;>
    congr 2 <;> push_cast <;> ring

lemma ep_phi (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) : IsEP β (phi034 β n₁ n₂ i) := by
  have := ep_mono β (kIdx i) (by have := kIdx_le i; omega) (pIdx i)
  simpa only [← phi_eq] using this

lemma ep_dphi (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) :
    ∃ g : ℝ → ℝ, IsEP β g ∧ ∀ x, HasDerivAt (phi034 β n₁ n₂ i) (g x) x := by
  set l := ((kIdx i : ℕ) : ℝ) + 1
  refine ⟨fun x => (derivative (pIdx i) - C (l * β) * pIdx i).eval x *
    Real.exp (-(l * β) * x), ?_, fun x => ?_⟩
  · have := ep_mono β (kIdx i) (by have := kIdx_le i; omega)
      (derivative (pIdx i) - C (l * β) * pIdx i)
    refine (by simpa only [l, neg_mul, mul_assoc] using this)
  · have h := hd_pe (pIdx i) (l * β) x
    have e : phi034 β n₁ n₂ i = fun x => (pIdx i).eval x * Real.exp (-(l * β) * x) := by
      funext y; rw [phi_eq]; congr 2; simp only [l]; ring
    rw [e]
    exact h

lemma ep_prodint (i j : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) (hβ : 0 < β) :
    IsEP β (fun x => phi034 β n₁ n₂ i x * ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η) := by
  set lj := ((kIdx j : ℕ) : ℝ) + 1
  have hl : lj * β ≠ 0 := by positivity
  obtain ⟨q, c, hqc⟩ := int_pe (pIdx j) (lj * β) hl
  have hint : ∀ x, (∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η) = c - q.eval x * Real.exp (-(lj * β) * x) := by
    intro x
    rw [← hqc]
    refine intervalIntegral.integral_congr fun η _ => ?_
    rw [phi_eq]; congr 2; simp only [lj]; ring
  have hki := kIdx_le i
  have hkj := kIdx_le j
  have h1 := ep_smul β c (ep_phi β i)
  have h2 := ep_mono β (kIdx i + kIdx j + 1) (by omega) (pIdx i * q)
  have := ep_add β h1 (ep_neg β h2)
  refine (show IsEP β _ from this).elim fun Q hQ => ⟨Q, fun x => ?_⟩
  rw [← hQ x]
  beta_reduce
  rw [hint, phi_eq]
  simp only [eval_mul]
  have e : Real.exp (-(((kIdx i : ℕ) : ℝ) + 1) * β * x) * Real.exp (-(lj * β) * x) =
      Real.exp (-((((kIdx i + kIdx j + 1 : ℕ)) : ℝ) + 1) * β * x) := by
    rw [← Real.exp_add]; congr 1; simp only [lj]; push_cast; ring
  rw [mul_sub, ← e]
  ring

end Basis

lemma residual : residualStatement := by
  intro β hβ n₁ n₂ z b a P c d hcd h
  classical
  -- the derivative of `F`
  choose g hg hgd using fun i => ep_dphi β (n₁ := n₁) (n₂ := n₂) i
  have hF : ∀ x, deriv (F034 β n₁ n₂ z) x = ∑ i, z i * g i x := fun x => by
    have := HasDerivAt.sum (u := Finset.univ) fun i _ => (hgd i x).const_mul (z i)
    rw [show F034 β n₁ n₂ z = ∑ i ∈ Finset.univ, fun y => z i * phi034 β n₁ n₂ i y from by
      funext y; simp [F034, Finset.sum_apply]]
    exact this.deriv
  have hEP : IsEP β (residual034 β n₁ n₂ z b a) := by
    have e1 := ep_neg β (ep_sum β Finset.univ (fun i x => z i * g i x)
      fun i _ => ep_smul β (z i) (hg i))
    have e2 := ep_sum β Finset.univ (fun i x => b i * phi034 β n₁ n₂ i x)
      fun i _ => ep_smul β (b i) (ep_phi β i)
    have e3 := ep_neg β (ep_sum β Finset.univ (fun i x => ∑ j, a i j * phi034 β n₁ n₂ i x *
      ∫ η in (0:ℝ)..x, phi034 β n₁ n₂ j η) fun i _ => ep_sum β Finset.univ _ fun j _ => by
        simpa only [mul_assoc] using ep_smul β (a i j) (ep_prodint β i j hβ))
    obtain ⟨Q, hQ⟩ := ep_add β (ep_add β e1 e2) e3
    refine ⟨Q, fun x => ?_⟩
    rw [← hQ x, residual034, hF]
    ring
  obtain ⟨Q, hQ⟩ := hEP
  have hind := Novel.SharefFilipovicIndependenceProof.independence β hβ 4 Q P c d hcd
    (fun x hx => by rw [← hQ x]; exact h x hx)
  intro x
  rw [hQ x]
  simp [hind.1]

theorem sharefFilipovicResidual : Standalone.SharefFilipovicResidual.statement := residual

end Novel.SharefFilipovicResidualProof

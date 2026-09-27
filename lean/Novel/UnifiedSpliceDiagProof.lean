import Standalone.UnifiedSpliceDiag
import Novel.UnifiedSpliceDiagLemmas
import Novel.UnifiedSpliceNecessityProof

open Matrix NormedSpace Polynomial
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceDiag
open Novel.UnifiedSpliceDiagLemmas
namespace Novel.UnifiedSpliceDiagProof

variable {k r : ℕ}

/-! ### The residual in real terms -/

section Real
variable (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)

/-- `Φ_v(x) = c e^{xA} v`. -/
noncomputable def Φ (x : ℝ) (v : Fin r → ℝ) : ℝ := c ⬝ᵥ (exp (x • A) *ᵥ v)

lemma ephi_dot (x : ℝ) (v : Fin r → ℝ) : ephi c A x ⬝ᵥ v = Φ c A x v := by
  rw [ephi, ← dotProduct_mulVec]; rfl

lemma ePhi_dot (hA : IsUnit A.det) (x : ℝ) (v : Fin r → ℝ) :
    ePhi c A x ⬝ᵥ v = Φ c A x (A⁻¹ *ᵥ v) - c ⬝ᵥ (A⁻¹ *ᵥ v) := by
  rw [ePhi, ← dotProduct_mulVec, mul_sub, mul_one,
    Novel.UnifiedSpliceNecessityProof.inv_comm_exp A hA, sub_mulVec, dotProduct_sub,
    ← mulVec_mulVec]
  rfl

/-- `σ^B·Σ^B`, by the powers of the level rows and the exponential part. -/
lemma sig_split (x : ℝ) :
    sigB Hp Hz c A d x ⬝ᵥ SigB Hp Hz c A d x =
      (∑ μ ∈ Finset.range (d + 1), x ^ μ * ((∑ ν ∈ Finset.range (d + 1),
        x ^ (ν + 1) / (ν + 1) * (Hp ν ⬝ᵥ Hp μ)) + ePhi c A x ⬝ᵥ (Hz *ᵥ Hp μ))) +
      ((∑ ν ∈ Finset.range (d + 1), x ^ (ν + 1) / (ν + 1) * (ephi c A x ⬝ᵥ (Hz *ᵥ Hp ν))) +
        (ePhi c A x ᵥ* Hz) ⬝ᵥ (ephi c A x ᵥ* Hz)) := by
  have hW : ∀ W, W ⬝ᵥ SigB Hp Hz c A d x = _ := fun W =>
    Novel.UnifiedSpliceAlgebraProof.dot_SigB Hp Hz c A d x W
  have e1 : sigB Hp Hz c A d x ⬝ᵥ SigB Hp Hz c A d x =
      (∑ μ ∈ Finset.range (d + 1), x ^ μ * (Hp μ ⬝ᵥ SigB Hp Hz c A d x)) +
        (ephi c A x ᵥ* Hz) ⬝ᵥ SigB Hp Hz c A d x := by
    simp only [sigB, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [e1, hW (ephi c A x ᵥ* Hz)]
  congr 1
  · exact Finset.sum_congr rfl fun μ _ => by rw [hW]
  · congr 1
    · exact Finset.sum_congr rfl fun ν _ => by rw [dotProduct_comm, ← dotProduct_mulVec]
    · rw [dotProduct_mulVec]

/-- The polynomial–exponential part `N(x) = Σ_μ x^μ Φ_{A⁻¹w_μ} + Σ_ν x^{ν+1}/(ν+1) Φ_{w_ν}`,
`w_μ = H^ζ H^{0,μ⊤}`. -/
noncomputable def Nf (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range (d + 1), x ^ μ * Φ c A x (A⁻¹ *ᵥ (Hz *ᵥ Hp μ))) +
    ∑ ν ∈ Finset.range (d + 1), x ^ (ν + 1) / (ν + 1) * Φ c A x (Hz *ᵥ Hp ν)

/-- The rest of the residual. -/
noncomputable def Jf (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (x : ℝ) : ℝ :=
  (∑ μ ∈ Finset.range (d + 1), bP μ * x ^ μ) + Φ c A x bZ -
    ((∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * zP μ * x ^ (μ - 1)) + Φ c A x (A *ᵥ z)) -
    (∑ μ ∈ Finset.range (d + 1), x ^ μ * ((∑ ν ∈ Finset.range (d + 1),
      x ^ (ν + 1) / (ν + 1) * (Hp ν ⬝ᵥ Hp μ)) - c ⬝ᵥ (A⁻¹ *ᵥ (Hz *ᵥ Hp μ)))) -
    ∑ l, (Φ c A x (A⁻¹ *ᵥ fun a => Hz a l) - c ⬝ᵥ (A⁻¹ *ᵥ fun a => Hz a l)) *
      Φ c A x (fun a => Hz a l)

lemma resid_split (hA : IsUnit A.det) (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (x : ℝ) :
    resid Hp Hz c A d bP zP bZ z x = Jf Hp Hz c A d bP zP bZ z x - Nf Hp Hz c A d x := by
  have hEE : (ePhi c A x ᵥ* Hz) ⬝ᵥ (ephi c A x ᵥ* Hz) =
      ∑ l, (Φ c A x (A⁻¹ *ᵥ fun a => Hz a l) - c ⬝ᵥ (A⁻¹ *ᵥ fun a => Hz a l)) *
        Φ c A x (fun a => Hz a l) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 := ePhi_dot c A hA x (fun a => Hz a l)
    have h2 := ephi_dot c A x (fun a => Hz a l)
    simp only [dotProduct] at h1 h2
    rw [← h1, ← h2]; rfl
  have hμ : ∑ μ ∈ Finset.range (d + 1), x ^ μ * ((∑ ν ∈ Finset.range (d + 1),
      x ^ (ν + 1) / (ν + 1) * (Hp ν ⬝ᵥ Hp μ)) + ePhi c A x ⬝ᵥ (Hz *ᵥ Hp μ)) =
      (∑ μ ∈ Finset.range (d + 1), x ^ μ * ((∑ ν ∈ Finset.range (d + 1),
        x ^ (ν + 1) / (ν + 1) * (Hp ν ⬝ᵥ Hp μ)) - c ⬝ᵥ (A⁻¹ *ᵥ (Hz *ᵥ Hp μ)))) +
      ∑ μ ∈ Finset.range (d + 1), x ^ μ * Φ c A x (A⁻¹ *ᵥ (Hz *ᵥ Hp μ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by rw [ePhi_dot c A hA]; ring
  have hν : ∑ ν ∈ Finset.range (d + 1), x ^ (ν + 1) / (ν + 1) * (ephi c A x ⬝ᵥ (Hz *ᵥ Hp ν)) =
      ∑ ν ∈ Finset.range (d + 1), x ^ (ν + 1) / (ν + 1) * Φ c A x (Hz *ᵥ Hp ν) :=
    Finset.sum_congr rfl fun ν _ => by rw [ephi_dot]
  rw [resid, sig_split, hμ, hν, hEE, ephi_dot, ephi_dot, Jf, Nf]
  ring

end Real

/-! ### The part without powers of `x` on the exponentials -/

section Junk
variable (lam : Fin r → ℂ)

/-- A polynomial plus constants times `e^{λ_i x}` and `e^{(λ_i + λ_j) x}`. -/
def Junk (f : ℝ → ℂ) : Prop := ∃ (Q : ℂ[X]) (a : Fin r → ℂ) (κ : Fin r → Fin r → ℂ), ∀ x : ℝ,
  f x = Q.eval (x : ℂ) + ∑ i, a i * Complex.exp (x * lam i) +
    ∑ i, ∑ j, κ i j * Complex.exp (x * (lam i + lam j))

variable {lam}

lemma junk_add {f g : ℝ → ℂ} (hf : Junk lam f) (hg : Junk lam g) : Junk lam (f + g) := by
  obtain ⟨Q, a, κ, h⟩ := hf
  obtain ⟨Q', a', κ', h'⟩ := hg
  refine ⟨Q + Q', a + a', κ + κ', fun x => ?_⟩
  simp only [Pi.add_apply, h, h', eval_add, add_mul, Finset.sum_add_distrib]
  ring

lemma junk_smul (b : ℂ) {f : ℝ → ℂ} (hf : Junk lam f) : Junk lam (fun x => b * f x) := by
  obtain ⟨Q, a, κ, h⟩ := hf
  refine ⟨C b * Q, b • a, b • κ, fun x => ?_⟩
  simp only [h, eval_mul, eval_C, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

lemma junk_sub {f g : ℝ → ℂ} (hf : Junk lam f) (hg : Junk lam g) : Junk lam (f - g) := by
  have := junk_add hf (junk_smul (-1) hg)
  convert this using 1
  funext x; simp [sub_eq_add_neg]

lemma junk_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, Junk lam (f i)) :
    Junk lam (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, fun x => by simp⟩
  | insert i s hi ih =>
    have := junk_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert this using 1
    funext x; simp [Finset.sum_insert hi]

lemma junk_mono (b : ℂ) (n : ℕ) : Junk lam (fun x => b * (x : ℂ) ^ n) :=
  ⟨C b * X ^ n, 0, 0, fun x => by simp⟩

variable {A : Matrix (Fin r) (Fin r) ℝ} {P : Matrix (Fin r) (Fin r) ℂ}
  (hP : IsUnit P.det) (hAP : A.map Complex.ofReal * P = P * diagonal lam)
include hP hAP

lemma junk_Φ (c : Fin r → ℝ) (v : Fin r → ℝ) : Junk lam (fun x => (Φ c A x v : ℂ)) := by
  refine ⟨0, fun i => ((fun i => (c i : ℂ)) ᵥ* P) i * (P⁻¹ *ᵥ fun j => (v j : ℂ)) i, 0,
    fun x => ?_⟩
  simp only [Φ]
  rw [phi_eig hP hAP]
  simp only [eval_zero, zero_add, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma junk_ΦΦ (c : Fin r → ℝ) (v w : Fin r → ℝ) :
    Junk lam (fun x => (Φ c A x v : ℂ) * (Φ c A x w : ℂ)) := by
  set c' := (fun i => (c i : ℂ)) ᵥ* P
  set y := P⁻¹ *ᵥ fun j => (v j : ℂ)
  set y' := P⁻¹ *ᵥ fun j => (w j : ℂ)
  refine ⟨0, 0, fun i j => c' i * y i * (c' j * y' j), fun x => ?_⟩
  simp only [Φ]
  rw [phi_eig hP hAP, phi_eig hP hAP, Finset.sum_mul_sum]
  simp only [eval_zero, zero_add, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Complex.exp_add]
  ring

/-- The part `J` of the residual is junk. -/
lemma junk_J (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (d : ℕ)
    (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) :
    Junk lam (fun x => (Jf Hp Hz c A d bP zP bZ z x : ℂ)) := by
  have hS1 := junk_sum (lam := lam) (Finset.range (d + 1))
    (fun μ x => (bP μ : ℂ) * (x : ℂ) ^ μ) fun μ _ => junk_mono _ _
  have hS2 := junk_sum (lam := lam) (Finset.range (d + 1))
    (fun μ x => (((μ : ℝ) * zP μ : ℝ) : ℂ) * (x : ℂ) ^ (μ - 1)) fun μ _ => junk_mono _ _
  have hS3 := junk_sum (lam := lam) (Finset.range (d + 1))
    (fun μ x => (∑ ν ∈ Finset.range (d + 1), ((Hp ν ⬝ᵥ Hp μ / (ν + 1) : ℝ) : ℂ) *
      (x : ℂ) ^ (μ + ν + 1)) - ((c ⬝ᵥ (A⁻¹ *ᵥ (Hz *ᵥ Hp μ)) : ℝ) : ℂ) * (x : ℂ) ^ μ)
    fun μ _ => junk_sub (junk_sum _ _ fun ν _ => junk_mono _ _) (junk_mono _ _)
  have hS4 := junk_sum (lam := lam) Finset.univ
    (fun (l : Fin k) x => (Φ c A x (A⁻¹ *ᵥ fun a => Hz a l) : ℂ) * (Φ c A x (fun a => Hz a l) : ℂ) -
      ((c ⬝ᵥ (A⁻¹ *ᵥ fun a => Hz a l) : ℝ) : ℂ) * (Φ c A x (fun a => Hz a l) : ℂ))
    fun l _ => junk_sub (junk_ΦΦ hP hAP c _ _) (junk_smul _ (junk_Φ hP hAP c _))
  have hall := junk_sub (junk_sub (junk_sub (junk_add hS1 (junk_Φ hP hAP c bZ))
    (junk_add hS2 (junk_Φ hP hAP c (A *ᵥ z)))) hS3) hS4
  convert hall using 1
  funext x
  simp only [Jf, Pi.add_apply, Pi.sub_apply]
  push_cast
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun ν _ => by ring
    · ring
  · refine Finset.sum_congr rfl fun l _ => by ring

end Junk

/-! ### The polynomial–exponential part in the eigenbasis -/

/-- `Np_i(X) = Σ_μ (ω_μ/λ X^μ + ω_μ/(μ+1) X^{μ+1})`. -/
noncomputable def NP (ω : ℕ → ℂ) (l : ℂ) (d : ℕ) : ℂ[X] :=
  ∑ μ ∈ Finset.range (d + 1), (C (ω μ / l) * X ^ μ + C (ω μ / ((μ : ℂ) + 1)) * X ^ (μ + 1))

lemma NP_coeff (ω : ℕ → ℂ) (l : ℂ) (d n : ℕ) :
    (NP ω l d).coeff (n + 1) = (if n + 1 ≤ d then ω (n + 1) / l else 0) +
      (if n ≤ d then ω n / ((n : ℂ) + 1) else 0) := by
  simp only [NP, finsetSum_coeff, coeff_add, coeff_C_mul, coeff_X_pow, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_ite_eq]; simp only [Finset.mem_range]
    split_ifs <;> first | rfl | omega
  · have : ∀ μ ∈ Finset.range (d + 1), (if n + 1 = μ + 1 then ω μ / ((μ : ℂ) + 1) else 0) =
        if n = μ then ω n / ((n : ℂ) + 1) else 0 := fun μ _ => by
      split_ifs with h1 h2 h2
      · subst h2; rfl
      · omega
      · omega
      · rfl
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]; simp only [Finset.mem_range]
    split_ifs <;> first | rfl | omega

lemma NP_descent (ω : ℕ → ℂ) (l : ℂ) (d : ℕ) (h : ∀ n, (NP ω l d).coeff (n + 1) = 0) :
    ∀ μ ≤ d, ω μ = 0 := by
  suffices ∀ j μ, μ + j = d → ω μ = 0 from fun μ hμ => this (d - μ) μ (by omega)
  intro j
  induction j with
  | zero =>
    intro μ hμ
    have := h μ
    rw [NP_coeff] at this
    simp only [show ¬ (μ + 1 ≤ d) by omega, show μ ≤ d by omega, ite_true, ite_false,
      zero_add] at this
    have hne : ((μ : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero μ
    exact (div_eq_zero_iff.1 this).resolve_right hne
  | succ j ih =>
    intro μ hμ
    have hnext := ih (μ + 1) (by omega)
    have := h μ
    rw [NP_coeff] at this
    simp only [show μ + 1 ≤ d by omega, show μ ≤ d by omega, ite_true, hnext, zero_div,
      zero_add] at this
    have hne : ((μ : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero μ
    exact (div_eq_zero_iff.1 this).resolve_right hne

/-- `N(x) = Σ_i (cP)_i e^{λ_i x} Np_i(x)`, with `ω_{μ,i} = (P⁻¹ H^ζ H^{0,μ⊤})_i`. -/
lemma N_eig {A : Matrix (Fin r) (Fin r) ℝ} {P : Matrix (Fin r) (Fin r) ℂ} {lam : Fin r → ℂ}
    (hP : IsUnit P.det) (hAP : A.map Complex.ofReal * P = P * diagonal lam) (hA : IsUnit A.det)
    (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ) (d : ℕ) (x : ℝ) :
    (Nf Hp Hz c A d x : ℂ) = ∑ i, ((fun i => (c i : ℂ)) ᵥ* P) i * Complex.exp (x * lam i) *
      (NP (fun μ => (P⁻¹ *ᵥ fun j => ((Hz *ᵥ Hp μ) j : ℂ)) i) (lam i) d).eval (x : ℂ) := by
  set c' := (fun i => (c i : ℂ)) ᵥ* P
  set ω : ℕ → Fin r → ℂ := fun μ i => (P⁻¹ *ᵥ fun j => ((Hz *ᵥ Hp μ) j : ℂ)) i
  have hΦ : ∀ v, ((Φ c A x v : ℝ) : ℂ) = ∑ i, c' i * Complex.exp (x * lam i) *
      (P⁻¹ *ᵥ fun j => (v j : ℂ)) i := fun v => phi_eig hP hAP c x v
  simp only [Nf, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one, hΦ, inv_eig hP hAP hA]
  simp only [NP, eval_finsetSum, eval_add, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (d + 1)) (t := Finset.univ),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-! ### (b2) -/

theorem diagS : diagStatement := by
  classical
  intro k r d Hp Hz c A hA hobs ⟨P, lam, hP, hAP⟩ bP zP bZ z ⟨α, β, hR⟩
  set c' := (fun i => (c i : ℂ)) ᵥ* P
  set ω : ℕ → Fin r → ℂ := fun μ i => (P⁻¹ *ᵥ fun j => ((Hz *ᵥ Hp μ) j : ℂ)) i
  obtain ⟨Q, a, κ, hJ⟩ := junk_J hP hAP Hp Hz c d bP zP bZ z
  -- the residual as an exponential polynomial
  let ι := Fin r ⊕ (Fin r × Fin r) ⊕ Unit
  let φ : ι → ℂ := Sum.elim lam (Sum.elim (fun ij => lam ij.1 + lam ij.2) fun _ => 0)
  let q : ι → ℂ[X] := Sum.elim (fun i => C (a i) - C (c' i) * NP (fun μ => ω μ i) (lam i) d)
    (Sum.elim (fun ij => C (κ ij.1 ij.2)) fun _ => Q - C (α : ℂ) - C (β : ℂ) * X)
  have hzero : ∀ x : ℝ, ∑ j, (q j).eval (x : ℂ) * Complex.exp (φ j * x) = 0 := fun x => by
    have h1 := hR x
    rw [resid_split Hp Hz c A d hA] at h1
    have h2 : ((Jf Hp Hz c A d bP zP bZ z x : ℝ) : ℂ) - (Nf Hp Hz c A d x : ℂ) = α + β * x := by
      exact_mod_cast h1
    have hJx := hJ x
    simp only at hJx
    rw [hJx, N_eig hP hAP hA] at h2
    simp only [ι, φ, q, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, zero_mul, Complex.exp_zero, mul_one, eval_sub,
      eval_mul, eval_C, eval_X]
    have e1 : ∀ i, Complex.exp (lam i * x) = Complex.exp (x * lam i) := fun i => by rw [mul_comm]
    have e2 : ∀ i j, Complex.exp ((lam i + lam j) * x) = Complex.exp (x * (lam i + lam j)) :=
      fun i j => by rw [mul_comm]
    simp only [e1, e2, sub_mul, Finset.sum_sub_distrib]
    have e3 : ∑ i, c' i * (NP (fun μ => ω μ i) (lam i) d).eval (x : ℂ) * Complex.exp (x * lam i) =
        ∑ i, ((fun i => (c i : ℂ)) ᵥ* P) i * Complex.exp (x * lam i) *
          (NP (fun μ => (P⁻¹ *ᵥ fun j => ((Hz *ᵥ Hp μ) j : ℂ)) i) (lam i) d).eval (x : ℂ) :=
      Finset.sum_congr rfl fun i _ => by simp only [c', ω]; ring
    linear_combination h2 - e3
  -- the fiber of `λ_i`, and its coefficients of `x^{n+1}`
  have hcoef : ∀ i n, (NP (fun μ => ω μ i) (lam i) d).coeff (n + 1) = 0 := fun i n => by
    have hf := Novel.UnifiedSpliceDiagLemmas.fiber_indep φ q hzero (lam i)
    have hinj := lam_inj hP hAP c hobs
    have hc := congrArg (fun p : ℂ[X] => p.coeff (n + 1)) hf
    simp only [finsetSum_coeff, coeff_zero] at hc
    have hterm : ∀ j : ι, (if φ j = lam i then q j else 0).coeff (n + 1) =
        if j = Sum.inl i then -(c' i * (NP (fun μ => ω μ i) (lam i) d).coeff (n + 1)) else 0 := by
      rintro (j | ij | u)
      · split_ifs with h1 h2 h2
        · cases Sum.inl_injective h2
          simp only [q, Sum.elim_inl, coeff_sub, coeff_C_mul, coeff_C, Nat.succ_ne_zero,
            ite_false, zero_sub]
        · exact absurd (congrArg Sum.inl (hinj h1)) h2
        · cases Sum.inl_injective h2; exact absurd rfl h1
        · rfl
      · split_ifs with h1 h2 h2
        · cases h2
        · simp [q]
        · cases h2
        · rfl
      · split_ifs with h1 h2 h2
        · cases h2
        · exact absurd h1.symm (lam_ne hP hAP hA i)
        · cases h2
        · rfl
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq'] at hc
    simp only [Finset.mem_univ, ite_true, neg_eq_zero] at hc
    exact (mul_eq_zero.1 hc).resolve_left (cP_ne hP hAP c hobs i)
  intro μ hμ
  have hω : ∀ i, ω μ i = 0 := fun i => NP_descent _ _ d (hcoef i) μ hμ
  have hw : (fun j => ((Hz *ᵥ Hp μ) j : ℂ)) = 0 := by
    have h0 : P⁻¹ *ᵥ (fun j => ((Hz *ᵥ Hp μ) j : ℂ)) = 0 := funext hω
    have := congrArg (P *ᵥ ·) h0
    simp only [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec, mulVec_zero] at this
    exact this
  funext j
  have := congrFun hw j
  simpa using this

lemma effectiveS : effectiveStatement := by
  intro k r d Hp Hz c A hA hobs hdiag bP zP bZ z V hR
  have h := diagS k r d (sharp Hp V) Hz c A hA hobs hdiag bP zP bZ z hR
  refine ⟨fun μ h1 h2 => ?_, ?_⟩
  · have := h μ h2
    rwa [sharp, Function.update_of_ne (by omega)] at this
  · have := h 0 (Nat.zero_le _)
    rwa [sharp, Function.update_self] at this

theorem unifiedSpliceDiag : Standalone.UnifiedSpliceDiag.statement := ⟨diagS, effectiveS⟩

end Novel.UnifiedSpliceDiagProof

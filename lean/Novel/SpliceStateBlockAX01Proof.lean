import Standalone.SpliceStateBlockAX01
import Novel.SpliceStateBlockCrossProof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceStateBlockCross Standalone.SpliceStateBlockAX01
namespace Novel.SpliceStateBlockAX01Proof

variable {r k : ℕ}

/-- `v ↦ c e^{A(v−u)} x` is continuous. -/
lemma cexp_cont (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (u : ℝ) (x : Fin r → ℝ) :
    Continuous fun v : ℝ => c ⬝ᵥ (exp ((v - u) • A) *ᵥ x) :=
  (Novel.SpliceQuasiExponentialConsistencyProof.cont_of_analytic
    (Novel.SpliceQuasiExponentialKeyProof.analytic_g A c x)).comp
    (continuous_id.sub continuous_const)

/-- `∫_u^T c e^{A(v−u)} x dv = c A^{−1}(e^{A(T−u)} − I) x`. -/
lemma int_cexp (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (c : Fin r → ℝ)
    (u T : ℝ) (x : Fin r → ℝ) :
    ∫ v in u..T, c ⬝ᵥ (exp ((v - u) • A) *ᵥ x) =
      c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ x) := by
  have hF : ∀ v, HasDerivAt (fun v => (c ᵥ* A⁻¹) ⬝ᵥ ((A ^ 0 * exp ((v - u) • A)) *ᵥ x))
      (c ⬝ᵥ (exp ((v - u) • A) *ᵥ x)) v := fun v => by
    have h := (Novel.RecurrenceNecessityReductionProof.deriv_g A (c ᵥ* A⁻¹) x 0 (v - u)).comp_sub_const
      v u
    convert h using 1
    rw [zero_add, pow_one, ← dotProduct_mulVec, ← mulVec_mulVec]
    rw [show A⁻¹ *ᵥ (A *ᵥ (exp ((v - u) • A) *ᵥ x)) = exp ((v - u) • A) *ᵥ x by
      rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hF v)
    ((cexp_cont c A u x).intervalIntegrable _ _)]
  simp only [pow_zero, one_mul, sub_self, zero_smul, NormedSpace.exp_zero, one_mulVec]
  rw [← dotProduct_mulVec, ← dotProduct_mulVec, ← dotProduct_sub, ← mulVec_sub,
    ← mulVec_mulVec, sub_mulVec, one_mulVec]

/-- `∫_u^T σ_l(u, v) dv = S^S(u, T) H^S_l(u) + c A^{−1}(e^{A(T−u)} − I) H^Z_{·l}(u)`. -/
lemma sigma_int (s : ℕ → ℝ → ℝ) (hs : ∀ j, Measurable (s j)) (C : ℝ) (hsC : ∀ j u, |s j u| ≤ C)
    (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (u T : ℝ) (l : Fin k) :
    ∫ v in u..T, sigma040 s HS HZ Tm c A u v l =
      SS033 s Tm u T * HS u l + c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ fun i => HZ u i l) := by
  have hm : Measurable fun v => sigS033 s Tm u v :=
    (Novel.SpliceCrossTermDriftProof.sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)
  have i1 : IntervalIntegrable (fun v => sigS033 s Tm u v * HS u l) volume u T :=
    (Novel.SpliceCrossTermDriftProof.ii_bdd hm C (fun v => hsC _ _) u T).mul_const _
  have i2 : IntervalIntegrable (fun v => c ⬝ᵥ (exp ((v - u) • A) *ᵥ fun i => HZ u i l)) volume u T :=
    (cexp_cont c A u _).intervalIntegrable _ _
  unfold sigma040
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const, int_cexp A hA]
  rfl

lemma dot_w (c : Fin r → ℝ) (M : Matrix (Fin r) (Fin r) ℝ) (HS : ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (u : ℝ) :
    c ⬝ᵥ (M *ᵥ w040 HS HZ u) = ∑ l, HS u l * c ⬝ᵥ (M *ᵥ fun i => HZ u i l) := by
  have hw : w040 HS HZ u = ∑ l, HS u l • (fun i => HZ u i l) := by
    funext i
    simp only [w040, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hw, mulVec_sum, dotProduct_sum]
  simp only [mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma alg (h β B : Fin k → ℝ) (a S : ℝ) :
    ∑ l, (a * h l + β l) * (S * h l + B l) =
      (∑ l, h l ^ 2) * (a * S) + ∑ l, β l * B l + (a * ∑ l, h l * B l + (∑ l, h l * β l) * S) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `σ·∫σ = σ^S ∫σ^S + σ^B·∫σ^B + cross`. -/
lemma expand (s : ℕ → ℝ → ℝ) (hs : ∀ j, Measurable (s j)) (C : ℝ) (hsC : ∀ j u, |s j u| ≤ C)
    (HS : ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (u T : ℝ) :
    (sigma040 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma040 s HS HZ Tm c A u v l) =
      stepPart s HS Tm u T +
      (∑ l, c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l)) *
        c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l))) +
      cross040 s Tm c A (w040 HS HZ) u T := by
  have e : (sigma040 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma040 s HS HZ Tm c A u v l) =
      ∑ l, (sigS033 s Tm u T * HS u l + c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l))) *
        (SS033 s Tm u T * HS u l +
          c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l))) := by
    simp only [sigma_int s hs C hsC HS HZ Tm c A hA u T]
    rfl
  rw [e, alg]
  unfold stepPart cross040
  rw [dot_w, dot_w]

/-- `c e^{A(T−u)} x = ∑_i (c e^{AT})_i (e^{−Au} x)_i`. -/
lemma fac1 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T u : ℝ) (x : Fin r → ℝ) :
    c ⬝ᵥ (exp ((T - u) • A) *ᵥ x) = ∑ i, (c ᵥ* exp (T • A)) i * (exp (u • (-A)) *ᵥ x) i := by
  have e : exp ((T - u) • A) = exp (T • A) * exp (u • (-A)) := by
    rw [smul_neg, ← neg_smul, ← Novel.SpliceQuasiExponentialBlockProof.exp_add'', sub_eq_add_neg]
  rw [e, ← mulVec_mulVec, dotProduct_mulVec]
  rfl

/-- `c A^{−1}(e^{A(T−u)} − I) x = ∑_i (c A^{−1} e^{AT})_i (e^{−Au} x)_i − c A^{−1} x`. -/
lemma fac2 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T u : ℝ) (x : Fin r → ℝ) :
    c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ x) =
      ∑ i, ((c ᵥ* A⁻¹) ᵥ* exp (T • A)) i * (exp (u • (-A)) *ᵥ x) i - c ⬝ᵥ (A⁻¹ *ᵥ x) := by
  rw [mul_sub, mul_one, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec c A⁻¹,
    fac1]

/-- The entries of `c e^{AT}` are analytic in `T`. -/
lemma row_analytic (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) :
    AnalyticOnNhd ℝ (fun T : ℝ => (c ᵥ* exp (T • A)) i) univ := by
  have e : (fun T : ℝ => (c ᵥ* exp (T • A)) i) =
      fun T => c ⬝ᵥ (exp (T • A) *ᵥ Pi.single i 1) := by
    funext T
    rw [mulVec_single_one]
    rfl
  rw [e]
  exact Novel.SpliceQuasiExponentialKeyProof.analytic_g A c _

/-- Bounded measurable times continuous is interval integrable. -/
lemma ii_bc {f g : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ u, |f u| ≤ B) (hg : Continuous g)
    (a b : ℝ) : IntervalIntegrable (fun u => f u * g u) volume a b :=
  (Novel.SpliceCrossTermDriftProof.ii_bdd hf B hB a b).mul_continuousOn hg.continuousOn

/-- `(e^{−Au} y(u))_i = ∑_j y_j(u) (e^{−Au} e_j)_i`. -/
lemma pexp (A : Matrix (Fin r) (Fin r) ℝ) (y : ℝ → Fin r → ℝ) (u : ℝ) (i : Fin r) :
    (exp (u • (-A)) *ᵥ y u) i = ∑ j, y u j * (exp (u • (-A)) *ᵥ Pi.single j 1) i :=
  Novel.SpliceStateBlockCrossProof.mv_sum _ _ _

lemma econt (A : Matrix (Fin r) (Fin r) ℝ) (i j : Fin r) :
    Continuous fun u : ℝ => (exp (u • (-A)) *ᵥ Pi.single j 1) i :=
  Novel.RecurrenceNecessityReductionProof.phi_cont (-A) _ i

/-- `(e^{−Au} y(u))_i` is interval integrable for integrable `y`. -/
lemma ii_p (A : Matrix (Fin r) (Fin r) ℝ) (y : ℝ → Fin r → ℝ) (a b : ℝ)
    (hy : ∀ j, IntervalIntegrable (fun u => y u j) volume a b) (i : Fin r) :
    IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ y u) i) volume a b := by
  have h := IntervalIntegrable.sum Finset.univ fun j _ =>
    (hy j).mul_continuousOn (econt A i j).continuousOn
  convert h using 1
  funext u
  rw [pexp A y, Finset.sum_apply]

/-- `(e^{−Au} h(u))_i (e^{−Au} h(u))_j` is interval integrable for bounded measurable `h`. -/
lemma ii_pp (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → Fin r → ℝ) (hm : ∀ j, Measurable fun u => h u j)
    (B : ℝ) (hB : ∀ u j, |h u j| ≤ B) (a b : ℝ) (i i' : Fin r) (g : ℝ → ℝ) (hg : Continuous g) :
    IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ h u) i * (exp (u • (-A)) *ᵥ h u) i' * g u)
      volume a b := by
  have e : (fun u => (exp (u • (-A)) *ᵥ h u) i * (exp (u • (-A)) *ᵥ h u) i' * g u) =
      ∑ j, ∑ j', fun u => (h u j * h u j') * ((exp (u • (-A)) *ᵥ Pi.single j 1) i *
        (exp (u • (-A)) *ᵥ Pi.single j' 1) i' * g u) := by
    funext u
    rw [pexp A h u i, pexp A h u i', Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j' _ => by ring
  rw [e]
  refine IntervalIntegrable.sum Finset.univ fun j _ => IntervalIntegrable.sum Finset.univ
    fun j' _ => ?_
  refine ii_bc ((hm j).mul (hm j')) (B * B) (fun u => ?_)
    (((econt A i j).mul (econt A i' j')).mul hg) a b
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hB u j) (hB u j') (abs_nonneg _) ((abs_nonneg _).trans (hB u j))

/-- `(e^{−Au} h(u))_i κ(u)` is interval integrable for bounded measurable `h`, `κ`. -/
lemma ii_pk (A : Matrix (Fin r) (Fin r) ℝ) (h : ℝ → Fin r → ℝ) (hm : ∀ j, Measurable fun u => h u j)
    (B : ℝ) (hB : ∀ u j, |h u j| ≤ B) (κ : ℝ → ℝ) (hκ : Measurable κ) (K : ℝ) (hK : ∀ u, |κ u| ≤ K)
    (a b : ℝ) (i : Fin r) :
    IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ h u) i * κ u) volume a b := by
  have e : (fun u => (exp (u • (-A)) *ᵥ h u) i * κ u) =
      ∑ j, fun u => (h u j * κ u) * (exp (u • (-A)) *ᵥ Pi.single j 1) i := by
    funext u
    rw [pexp A h u i, Finset.sum_mul, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine IntervalIntegrable.sum Finset.univ fun j _ => ?_
  refine ii_bc ((hm j).mul hκ) (B * K) (fun u => ?_) (econt A i j) a b
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hB u j) (hK u) (abs_nonneg _) ((abs_nonneg _).trans (hB u j))

lemma ii_sum {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i, f i u) volume a b := by
  have := IntervalIntegrable.sum Finset.univ fun i _ => h i
  convert this using 1
  funext u
  simp [Finset.sum_apply]

/-- `∫ ∑_i α_i f_i = ∑_i α_i ∫ f_i`. -/
lemma int_sum_const {ι : Type*} [Fintype ι] (α : ι → ℝ) (f : ι → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    ∫ u in a..b, ∑ i, α i * f i u = ∑ i, α i * ∫ u in a..b, f i u := by
  rw [intervalIntegral.integral_finsetSum fun i _ => (hf i).const_mul (α i)]
  exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

section Block
variable (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
  (bZ z : ℝ → Fin r → ℝ)

/-- `σ^B·∫σ^B` for one driver `l`, in factored form. -/
lemma bb_fac (l : Fin k) (u T : ℝ) :
    c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l)) *
        c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l)) =
      ∑ i, ∑ j, ((c ᵥ* exp (T • A)) i * ((c ᵥ* A⁻¹) ᵥ* exp (T • A)) j) *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j) -
        ∑ i, (c ᵥ* exp (T • A)) i *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l))) := by
  rw [fac1, fac2]
  simp only [mul_sub, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- `σ^B·∫σ^B` summed over the drivers. -/
noncomputable def bbS (u T : ℝ) : ℝ :=
  ∑ l, c ⬝ᵥ (exp ((T - u) • A) *ᵥ (fun i => HZ u i l)) *
    c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ (fun i => HZ u i l))

variable {c A HZ bZ z}

/-- The integrability facts about the block, on `[0, t]`. -/
lemma block_ii (hHZ : ∀ i l, Measurable fun u => HZ u i l) (hz : ∀ i, Measurable fun u => z u i)
    (B : ℝ) (hHZB : ∀ u i l, |HZ u i l| ≤ B) (hzB : ∀ u i, |z u i| ≤ B) (t : ℝ)
    (hbZ : ∀ i, IntervalIntegrable (fun u => bZ u i) volume 0 t) :
    (∀ i, IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ (bZ u - A *ᵥ z u)) i) volume 0 t) ∧
    (∀ l i j, IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
      (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j) volume 0 t) ∧
    (∀ l i, IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
      c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l))) volume 0 t) := by
  refine ⟨fun i => ii_p A _ 0 t (fun j => ?_) i, fun l i j => ?_, fun l i => ?_⟩
  · refine (hbZ j).sub (Novel.SpliceCrossTermDriftProof.ii_bdd (f := fun u => (A *ᵥ z u) j)
      ?_ (∑ m, |A j m| * B) (fun u => ?_) 0 t)
    · simp only [mulVec, dotProduct]
      exact Finset.measurable_sum _ fun m _ => measurable_const.mul (hz m)
    · simp only [mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hzB u m) (abs_nonneg _)
  · have h := ii_pp A (fun u i => HZ u i l) (fun j => hHZ j l) B (fun u j => hHZB u j l) 0 t i j
      (fun _ => 1) continuous_const
    simpa using h
  · refine ii_pk A (fun u i => HZ u i l) (fun j => hHZ j l) B (fun u j => hHZB u j l)
      (fun u => c ⬝ᵥ (A⁻¹ *ᵥ fun i => HZ u i l)) ?_ (∑ m, |(c ᵥ* A⁻¹) m| * B) (fun u => ?_) 0 t i
    · have e : (fun u => c ⬝ᵥ (A⁻¹ *ᵥ fun i => HZ u i l)) =
          fun u => ∑ m, (c ᵥ* A⁻¹) m * HZ u m l := funext fun u => by
        rw [dotProduct_mulVec]; rfl
      rw [e]
      exact Finset.measurable_sum _ fun m _ => measurable_const.mul (hHZ m l)
    · rw [dotProduct_mulVec]
      simp only [dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hHZB u m l) (abs_nonneg _)

/-- The integrated block part `∫_0^t (D^B − σ^B·∫σ^B)` is analytic in `T`, and both integrands are
interval integrable. -/
lemma block_analytic (hHZ : ∀ i l, Measurable fun u => HZ u i l)
    (hz : ∀ i, Measurable fun u => z u i) (B : ℝ) (hHZB : ∀ u i l, |HZ u i l| ≤ B)
    (hzB : ∀ u i, |z u i| ≤ B) (t : ℝ)
    (hbZ : ∀ i, IntervalIntegrable (fun u => bZ u i) volume 0 t) :
    (∀ T, IntervalIntegrable (fun u => driftB c A bZ z u T) volume 0 t) ∧
    (∀ T, IntervalIntegrable (fun u => bbS c A HZ u T) volume 0 t) ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) univ := by
  obtain ⟨hq, hpp, hpk⟩ := block_ii (c := c) (A := A) hHZ hz B hHZB hzB t hbZ
  have hD : ∀ T : ℝ, (fun u => driftB c A bZ z u T) =
      fun u => ∑ i, (c ᵥ* exp (T • A)) i * (exp (u • (-A)) *ᵥ (bZ u - A *ᵥ z u)) i :=
    fun T => funext fun u => fac1 c A T u _
  have hbb : ∀ T : ℝ, (fun u => bbS c A HZ u T) = fun u => ∑ l,
      (∑ i, ∑ j, ((c ᵥ* exp (T • A)) i * ((c ᵥ* A⁻¹) ᵥ* exp (T • A)) j) *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j) -
        ∑ i, (c ᵥ* exp (T • A)) i *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l)))) :=
    fun T => funext fun u => Finset.sum_congr rfl fun l _ => bb_fac c A HZ l u T
  have iD : ∀ T : ℝ, IntervalIntegrable (fun u => driftB c A bZ z u T) volume 0 t := fun T => by
    rw [hD T]
    exact ii_sum fun i => (hq i).const_mul _
  have iL : ∀ (T : ℝ) (l : Fin k), IntervalIntegrable (fun u =>
      ∑ i, ∑ j, ((c ᵥ* exp (T • A)) i * ((c ᵥ* A⁻¹) ᵥ* exp (T • A)) j) *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j) -
        ∑ i, (c ᵥ* exp (T • A)) i *
          ((exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i * c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l))))
      volume 0 t := fun T l =>
    (ii_sum fun i => ii_sum
      fun j => (hpp l i j).const_mul _).sub
      (ii_sum fun i => (hpk l i).const_mul _)
  have iB : ∀ T : ℝ, IntervalIntegrable (fun u => bbS c A HZ u T) volume 0 t := fun T => by
    rw [hbb T]
    exact ii_sum fun l => iL T l
  refine ⟨iD, iB, ?_⟩
  -- the integral as a finite sum of analytic functions times constants
  have e : (fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) = fun T =>
      ∑ i, (c ᵥ* exp (T • A)) i * (∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (bZ u - A *ᵥ z u)) i) -
      ∑ l, (∑ i, ∑ j, ((c ᵥ* exp (T • A)) i * ((c ᵥ* A⁻¹) ᵥ* exp (T • A)) j) *
          (∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
            (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j) -
        ∑ i, (c ᵥ* exp (T • A)) i * (∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
            c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l)))) := by
    funext T
    rw [intervalIntegral.integral_sub (iD T) (iB T), hD T, hbb T, int_sum_const _ _ _ _ hq,
      intervalIntegral.integral_finsetSum fun l _ => iL T l]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_sub (ii_sum fun i =>
        ii_sum fun j => (hpp l i j).const_mul _)
      (ii_sum fun i => (hpk l i).const_mul _),
      int_sum_const _ _ _ _ (hpk l)]
    congr 1
    rw [intervalIntegral.integral_finsetSum fun i _ => ii_sum
      fun j => (hpp l i j).const_mul _]
    exact Finset.sum_congr rfl fun i _ => int_sum_const _ _ _ _ (hpp l i)
  rw [e]
  intro T _
  have ha := fun i => row_analytic c A i T (mem_univ _)
  have ha' := fun j => row_analytic (c ᵥ* A⁻¹) A j T (mem_univ _)
  have hq' := fun i => (ha i).mul
    (analyticAt_const (v := ∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (bZ u - A *ᵥ z u)) i))
  have h := (Finset.analyticAt_sum Finset.univ fun i _ => hq' i).sub
    (Finset.analyticAt_sum Finset.univ fun l _ => (Finset.analyticAt_sum Finset.univ fun i _ =>
      Finset.analyticAt_sum Finset.univ fun j _ => ((ha i).mul (ha' j)).mul
        (analyticAt_const (v := ∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
            (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) j))).sub
      (Finset.analyticAt_sum Finset.univ fun i _ => (ha i).mul
        (analyticAt_const (v := ∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ (fun i => HZ u i l)) i *
            c ⬝ᵥ (A⁻¹ *ᵥ (fun i => HZ u i l))))))
  convert h using 1
  funext T'
  simp [Finset.sum_apply]

end Block

/-- The step scales weighted by `|H^S(u)|`. -/
noncomputable def sn (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) : ℕ → ℝ → ℝ :=
  fun j u => Real.sqrt (∑ l, HS u l ^ 2) * s j u

lemma step_sn (s : ℕ → ℝ → ℝ) (HS : ℝ → Fin k → ℝ) (Tm : Finset ℝ) (u T : ℝ) :
    stepPart s HS Tm u T = sigS033 (sn s HS) Tm u T * SS033 (sn s HS) Tm u T := by
  have hSS : SS033 (sn s HS) Tm u T = Real.sqrt (∑ l, HS u l ^ 2) * SS033 s Tm u T := by
    unfold SS033
    rw [← intervalIntegral.integral_const_mul]
    rfl
  rw [hSS, stepPart]
  show _ = Real.sqrt (∑ l, HS u l ^ 2) * sigS033 s Tm u T * _
  have := Real.mul_self_sqrt (Finset.sum_nonneg (s := Finset.univ) fun l _ => sq_nonneg (HS u l))
  linear_combination (-(sigS033 s Tm u T * SS033 s Tm u T)) * this

/-- The path data give measurable bounded weighted scales and covariation density. -/
lemma data_sn {s : ℕ → ℝ → ℝ} {HS : ℝ → Fin k → ℝ} {HZ : ℝ → Fin r → Fin k → ℝ}
    {dL dC : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ} {H : ℝ} (h : PathData040 s HS HZ dL dC bZ z H) :
    ((∀ j, Measurable (sn s HS j)) ∧ ∃ C : ℝ, ∀ j u, |sn s HS j u| ≤ C) ∧
      PathData s (w040 HS HZ) := by
  obtain ⟨hs, hHS, hHZ, -, ⟨C, hsC, hHSC, hHZC, -⟩, -⟩ := h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hsC 0 0)
  have hn : ∀ u, Real.sqrt (∑ l, HS u l ^ 2) ≤ Real.sqrt (∑ l : Fin k, C ^ 2) := fun u =>
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun l _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hHSC u l) 2)
  have hW0 : 0 ≤ ∑ l : Fin k, C * C := Finset.sum_nonneg fun _ _ => mul_nonneg hC0 hC0
  refine ⟨⟨fun j => ((Finset.measurable_sum _ fun l _ => (hHS l).pow_const 2).sqrt).mul (hs j),
    Real.sqrt (∑ l : Fin k, C ^ 2) * C, fun j u => ?_⟩, fun j => hs j, fun i => ?_,
    C + ∑ l : Fin k, C * C, fun j u => (hsC j u).trans (le_add_of_nonneg_right hW0),
    fun u i => ?_⟩
  · rw [sn, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hn u) (hsC j u) (abs_nonneg _) (Real.sqrt_nonneg _)
  · exact Finset.measurable_sum _ fun l _ => (hHZ i l).mul (hHS l)
  · refine le_trans ?_ (le_add_of_nonneg_left hC0)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hHZC u i l) (hHSC u l) (abs_nonneg _) hC0

section Main
variable {s : ℕ → ℝ → ℝ} {HS : ℝ → Fin k → ℝ} {HZ : ℝ → Fin r → Fin k → ℝ} {dL dC : ℕ → ℝ → ℝ}
  {bZ z : ℝ → Fin r → ℝ} {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ}

/-- The integrands of AX-01 are interval integrable on `[0, t]`, `0 ≤ t ≤ T`, `t ≤ H`. -/
lemma parts_ii (h : PathData040 s HS HZ dL dC bZ z H) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (htH : t ≤ H) :
    IntervalIntegrable (fun u => driftS dL dC Tm u T) volume 0 t ∧
    IntervalIntegrable (fun u => driftB c A bZ z u T) volume 0 t ∧
    IntervalIntegrable (fun u => stepPart s HS Tm u T) volume 0 t ∧
    IntervalIntegrable (fun u => bbS c A HZ u T) volume 0 t ∧
    IntervalIntegrable (fun u => cross040 s Tm c A (w040 HS HZ) u T) volume 0 t ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) univ := by
  have h' := h
  obtain ⟨⟨hsn, Cn, hCn⟩, hPD⟩ := data_sn h'
  obtain ⟨hs, -, hHZ, hz, ⟨C, hsC, -, hHZC, hzC⟩, hdL, hdC, hbZ⟩ := h
  have hsub : uIcc 0 t ⊆ uIcc 0 H := by
    rw [uIcc_of_le ht, uIcc_of_le (ht.trans htH)]
    exact Icc_subset_Icc le_rfl htH
  obtain ⟨iD, iB, hG⟩ := block_analytic (c := c) (A := A) hHZ hz C hHZC hzC t
    fun i => (hbZ i).mono_set hsub
  refine ⟨((hdL _).mono_set hsub).add (((hdC _).mono_set hsub).mul_const T), iD T, ?_, iB T, ?_,
    hG⟩
  · refine ((Novel.SpliceRandomScalesNecessityProof.ii_parts Tm (sn s HS) hsn Cn hCn c A
      (fun _ => 0) 0 t T ht htT).1).congr fun u _ => ?_
    exact (step_sn s HS Tm u T).symm
  · have hc := fun i => Novel.SpliceStateBlockCrossProof.sw_data hPD i
    refine (ii_sum fun i => (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm
      (Novel.SpliceStateBlockCrossProof.sw s (w040 HS HZ) i) (hc i).1 (hc i).2.choose
      (hc i).2.choose_spec c A (Pi.single i 1) 1 t T ht htT).2).congr fun u _ => ?_
    exact (Novel.SpliceStateBlockCrossProof.cross_sum s Tm c A _ u T).symm

/-- Integrating AX-01 over `[0, t]`: the cross term is the front end's part plus the block's. -/
lemma decomp (h : PathData040 s HS HZ dL dC bZ z H) (hA : IsUnit A.det)
    (hAX : AX01Path s HS HZ dL dC bZ z Tm c A H) (t : ℝ) (ht : 0 ≤ t) (htH : t ≤ H) :
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross040 s Tm c A (w040 HS HZ) u T =
      ((∫ u in (0:ℝ)..t, driftS dL dC Tm u T) - ∫ u in (0:ℝ)..t, stepPart s HS Tm u T) +
        ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T) := by
  intro T hT
  have hs := h.1
  obtain ⟨C, hsC, -⟩ := h.2.2.2.2.1
  obtain ⟨iS, iD, iP, iB, iX, -⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h t T ht hT.1.le htH
  have hae : ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB c A bZ z u T) =
      ∫ u in (0:ℝ)..t, (stepPart s HS Tm u T + bbS c A HZ u T +
        cross040 s Tm c A (w040 HS HZ) u T) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hAX] with u hu hu'
    rw [uIoc_of_le ht] at hu'
    rw [hu ⟨hu'.1.le, hu'.2.trans htH⟩ T ⟨hu'.2.trans hT.1.le, hT.2.le⟩,
      expand s hs C hsC HS HZ Tm c A hA u T]
    rfl
  rw [intervalIntegral.integral_add iS iD, intervalIntegral.integral_add (iP.add iB) iX,
    intervalIntegral.integral_add iP iB] at hae
  rw [intervalIntegral.integral_sub iD iB]
  linarith

/-- The front end's part `∫ D^S − ∫ σ^S ∫σ^S` is affine on each maturity interval. -/
lemma front_affine (h : PathData040 s HS HZ dL dC bZ z H) (t : ℝ) (ht : 0 ≤ t) (htH : t ≤ H)
    (j : ℕ) : ∃ k₀ k₁ : ℝ, ∀ T, idx033 Tm T = j → t ≤ T →
      (∫ u in (0:ℝ)..t, driftS dL dC Tm u T) - (∫ u in (0:ℝ)..t, stepPart s HS Tm u T) =
        k₀ + k₁ * T := by
  obtain ⟨⟨hsn, Cn, hCn⟩, -⟩ := data_sn h
  obtain ⟨-, -, -, -, -, hdL, hdC, -⟩ := h
  have hsub : uIcc 0 t ⊆ uIcc 0 H := by
    rw [uIcc_of_le ht, uIcc_of_le (ht.trans htH)]
    exact Icc_subset_Icc le_rfl htH
  obtain ⟨c₀, c₁, hc⟩ := Novel.SpliceCrossTermCurveProof.step Tm (sn s HS) hsn Cn hCn j t ht
  refine ⟨(∫ u in (0:ℝ)..t, dL j u) - c₀, (∫ u in (0:ℝ)..t, dC j u) - c₁, fun T hT htT => ?_⟩
  have e1 : ∫ u in (0:ℝ)..t, driftS dL dC Tm u T =
      (∫ u in (0:ℝ)..t, dL j u) + (∫ u in (0:ℝ)..t, dC j u) * T := by
    simp only [driftS, hT]
    rw [intervalIntegral.integral_add ((hdL j).mono_set hsub)
      (((hdC j).mono_set hsub).mul_const T), intervalIntegral.integral_mul_const]
  have e2 : ∫ u in (0:ℝ)..t, stepPart s HS Tm u T = c₀ + c₁ * T := by
    rw [← hc T hT htT]
    exact intervalIntegral.integral_congr fun u _ => step_sn s HS Tm u T
  rw [e1, e2]
  ring

end Main

lemma necessity : Standalone.SpliceStateBlockAX01.necessityStatement := by
  intro r k A hA c hobs s HS HZ dL dC bZ z Tm H h hAX τ hτ hτH
  obtain ⟨-, hPD⟩ := data_sn h
  refine Novel.SpliceStateBlockCrossProof.core r A hA c hobs s (w040 HS HZ) hPD Tm τ H hτ hτH
    fun t ht => ?_
  have htH : t ≤ H := ht.2.le.trans hτH.le
  obtain ⟨-, -, -, -, -, hG⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h t t ht.1 le_rfl htH
  refine ⟨fun T => (∫ u in (0:ℝ)..t, driftS dL dC Tm u T) - ∫ u in (0:ℝ)..t, stepPart s HS Tm u T,
    fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T), hG, fun j => ?_,
    decomp h hA hAX t ht.1 htH⟩
  obtain ⟨k₀, k₁, hk⟩ := front_affine (Tm := Tm) h t ht.1 htH j
  exact ⟨k₀, k₁, fun T hT hTj => hk T hTj hT.1.le⟩

lemma jumpFree : Standalone.SpliceStateBlockAX01.jumpFreeStatement := by
  intro r k A hA c s HS HZ dL dC bZ z Tm H h hjump t ht
  obtain ⟨-, hPD⟩ := data_sn h
  have hcase : ∀ i : Fin r, (1:ℝ) = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 t → ∀ v, t ≤ v →
      Novel.SpliceStateBlockCrossProof.sw s (w040 HS HZ) i (idx033 Tm v) u =
        Novel.SpliceStateBlockCrossProof.sw s (w040 HS HZ) i (idx033 Tm t) u := fun i => by
    right
    filter_upwards [(eventually_all_finset Tm).2 hjump] with u hu hu0
    exact Novel.SpliceCrossTermSufficiencyProof.chain Tm _ u t hu0.2 fun τ hτ huτ => by
      have := congrFun (hu τ hτ ⟨hu0.1, huτ⟩) i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Novel.SpliceStateBlockCrossProof.sw] at this ⊢
      linear_combination this
  have hX := fun i => Novel.SpliceQuasiExponentialCrossProof.uncorrelated Tm
    (Novel.SpliceStateBlockCrossProof.sw s (w040 HS HZ) i)
    (Novel.SpliceStateBlockCrossProof.sw_data hPD i).1
    (Novel.SpliceStateBlockCrossProof.sw_data hPD i).2.choose
    (Novel.SpliceStateBlockCrossProof.sw_data hPD i).2.choose_spec r A hA (Pi.single i 1) c 1 t ht
    (hcase i)
  choose K y z' hX using hX
  refine ⟨∑ i, K i, ∑ i, y i, ∑ i, z' i, fun T hT => ?_⟩
  rw [Novel.SpliceStateBlockCrossProof.int_sum hPD Tm c A t T ht hT,
    Finset.sum_congr rfl fun i _ => hX i T hT, Finset.sum_add_distrib,
    Novel.SpliceStateBlockCrossProof.cexp_sum]

lemma affine : Standalone.SpliceStateBlockAX01.affineStatement := by
  intro r k A hA c s HS HZ dL dC bZ z Tm H h hAX hjump t ht htH
  obtain ⟨K, y, z', hX⟩ := jumpFree r k A hA c s HS HZ dL dC bZ z Tm H h hjump t ht
  obtain ⟨-, -, -, -, -, hG⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h t t ht le_rfl htH.le
  -- the block's part as an analytic function
  let Φ : ℝ → ℝ := fun T => (∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) -
    (K + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z')))
  have hΦa : AnalyticOnNhd ℝ Φ univ := fun T _ =>
    (hG T (mem_univ _)).sub (analyticAt_const.add
      (Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A y z' T (mem_univ _)))
  have hΦ : ∀ T ∈ Ioo t H, blockPart s HS HZ bZ z Tm c A t T = Φ T := by
    intro T hT
    obtain ⟨-, iD, -, iB, iX, -⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h t T ht hT.1.le htH.le
    show ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T -
      cross040 s Tm c A (w040 HS HZ) u T) = Φ T
    rw [intervalIntegral.integral_sub (iD.sub iB) iX, hX T hT.1.le]
  -- on a piece of one maturity interval it is affine
  set T₁ := (t + H) / 2
  have hT₁ : T₁ ∈ Ioo t H := ⟨by simp only [T₁]; linarith, by simp only [T₁]; linarith⟩
  obtain ⟨ε, hε, hidx⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm T₁
  obtain ⟨k₀, k₁, hk⟩ := front_affine (Tm := Tm) h t ht htH.le (idx033 Tm T₁)
  set T₂ := min (T₁ + ε) H
  have hT₂ : T₁ < T₂ := lt_min (by linarith) hT₁.2
  have hI : ∀ T ∈ Ioo T₁ T₂, Φ T = -(k₀ + k₁ * T) := by
    intro T hT
    have hTI : T ∈ Ioo t H := ⟨hT₁.1.trans hT.1, lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
    have hTj : idx033 Tm T = idx033 Tm T₁ := hidx T ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
    have hd := decomp h hA hAX t ht htH.le T hTI
    have := hk T hTj hTI.1.le
    rw [hX T hTI.1.le] at hd
    simp only [Φ]
    linarith
  -- so it is that affine function everywhere
  have hall : ∀ T, Φ T = -(k₀ + k₁ * T) := by
    have hF : AnalyticOnNhd ℝ (fun T => Φ T + (k₀ + k₁ * T)) univ := fun T hT =>
      (hΦa T hT).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    have hmid : (T₁ + T₂) / 2 ∈ Ioo T₁ T₂ := ⟨by linarith, by linarith⟩
    intro T
    have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [hI x hx]) (mem_univ T)
    simp only [Pi.zero_apply] at this
    linarith
  exact ⟨-k₀, -k₁, fun T hT => by rw [hΦ T hT, hall T]; ring⟩

lemma converse : Standalone.SpliceStateBlockAX01.converseStatement := by
  intro r k A hA c s HS HZ dL dC bZ z Tm H h t T ht htT hTH hdrift
  have hs := h.1
  obtain ⟨C, hsC, -⟩ := h.2.2.2.2.1
  obtain ⟨iS, iD, iP, iB, iX, -⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h t T ht htT
    (htT.trans hTH)
  have e : ∫ u in (0:ℝ)..t, sigma040 s HS HZ Tm c A u T ⬝ᵥ
      (fun l => ∫ v in u..T, sigma040 s HS HZ Tm c A u v l) =
      ∫ u in (0:ℝ)..t, (stepPart s HS Tm u T + bbS c A HZ u T +
        cross040 s Tm c A (w040 HS HZ) u T) :=
    intervalIntegral.integral_congr fun u _ => expand s hs C hsC HS HZ Tm c A hA u T
  rw [e, intervalIntegral.integral_add iS iD, intervalIntegral.integral_add (iP.add iB) iX,
    intervalIntegral.integral_add iP iB]
  have hb : blockPart s HS HZ bZ z Tm c A t T =
      (∫ u in (0:ℝ)..t, driftB c A bZ z u T) - (∫ u in (0:ℝ)..t, bbS c A HZ u T) -
        ∫ u in (0:ℝ)..t, cross040 s Tm c A (w040 HS HZ) u T := by
    show ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T -
      cross040 s Tm c A (w040 HS HZ) u T) = _
    rw [intervalIntegral.integral_sub (iD.sub iB) iX, intervalIntegral.integral_sub iD iB]
  rw [hb] at hdrift
  linarith

lemma noThirdWay : Standalone.SpliceStateBlockAX01.noThirdWayStatement := by
  intro r k A hA c hobs s HS HZ bZ z Tm H τ hτ hτH hne dL dC h hAX
  exact hne (necessity r k A hA c hobs s HS HZ dL dC bZ z Tm H h hAX τ hτ hτH)

theorem spliceStateBlockAX01 : Standalone.SpliceStateBlockAX01.statement :=
  ⟨necessity, jumpFree, affine, converse, noThirdWay⟩

end Novel.SpliceStateBlockAX01Proof

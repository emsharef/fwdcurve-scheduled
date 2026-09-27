import Standalone.SpliceExponentZeroAX01
import Novel.SpliceExponentZeroCrossProof
import Novel.SpliceStateBlockAX01Proof

open Matrix NormedSpace MeasureTheory Set Filter Polynomial
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceStateBlockCross Standalone.SpliceStateBlockAX01
open Standalone.SpliceExponentZeroCross Standalone.SpliceExponentZeroAX01
namespace Novel.SpliceExponentZeroAX01Proof
open Novel.SpliceStateBlockAX01Proof

variable {r k : ℕ}

/-! ### Separable integrands

`F(u, T) = ∑_i α_i(T) β_i(u)`, finitely many terms, with every `α_i` analytic. Then
`T ↦ ∫_0^t F(u, T) du` is analytic. -/

/-- Separable, with `β_i` integrable on `[0, t]`. -/
def Sep (t : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (α β : ι → ℝ → ℝ), (∀ i, AnalyticOnNhd ℝ (α i) univ) ∧
    (∀ i, IntervalIntegrable (β i) volume 0 t) ∧ ∀ u T, F u T = ∑ i, α i T * β i u

/-- Separable, with `β_i` measurable and bounded on `[0, t]`. -/
def SepB (t : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (α β : ι → ℝ → ℝ), (∀ i, AnalyticOnNhd ℝ (α i) univ) ∧
    (∀ i, Measurable (β i)) ∧ (∃ B, ∀ i, ∀ u ∈ uIcc 0 t, |β i u| ≤ B) ∧
    ∀ u T, F u T = ∑ i, α i T * β i u

variable {t : ℝ}

lemma sep_int {F : ℝ → ℝ → ℝ} (h : Sep t F) :
    (∀ T, IntervalIntegrable (fun u => F u T) volume 0 t) ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t, F u T) univ := by
  obtain ⟨ι, _, α, β, hα, hβ, hF⟩ := h
  have e : ∀ T, (fun u => F u T) = fun u => ∑ i, α i T * β i u := fun T => funext fun u => hF u T
  refine ⟨fun T => by rw [e T]; exact ii_sum fun i => (hβ i).const_mul _, ?_⟩
  have e' : (fun T => ∫ u in (0:ℝ)..t, F u T) =
      fun T => ∑ i, α i T * ∫ u in (0:ℝ)..t, β i u := by
    funext T
    rw [e T]
    exact int_sum_const _ _ _ _ hβ
  rw [e']
  intro T _
  have := Finset.analyticAt_sum Finset.univ fun i _ =>
    (hα i T (mem_univ _)).mul (analyticAt_const (v := ∫ u in (0:ℝ)..t, β i u))
  convert this using 1
  funext T'
  simp [Finset.sum_apply]

lemma sep_congr {F G : ℝ → ℝ → ℝ} (h : ∀ u T, F u T = G u T) (hG : Sep t G) : Sep t F := by
  obtain ⟨ι, hι, α, β, hα, hβ, hF⟩ := hG
  exact ⟨ι, hι, α, β, hα, hβ, fun u T => (h u T).trans (hF u T)⟩

lemma sepB_congr {F G : ℝ → ℝ → ℝ} (h : ∀ u T, F u T = G u T) (hG : SepB t G) : SepB t F := by
  obtain ⟨ι, hι, α, β, hα, hβ, hB, hF⟩ := hG
  exact ⟨ι, hι, α, β, hα, hβ, hB, fun u T => (h u T).trans (hF u T)⟩

lemma sepB_sep {F : ℝ → ℝ → ℝ} (h : SepB t F) : Sep t F := by
  obtain ⟨ι, hι, α, β, hα, hβ, ⟨B, hB⟩, hF⟩ := h
  exact ⟨ι, hι, α, β, hα, fun i => Novel.SpliceCrossTermCurveProof.ii_on (hβ i) B (hB i), hF⟩

lemma sep_zero : Sep t fun _ _ => 0 :=
  ⟨Empty, inferInstance, fun _ _ => 0, fun _ _ => 0, fun i => i.elim, fun i => i.elim,
    fun _ _ => by simp⟩

lemma sepB_zero : SepB t fun _ _ => 0 :=
  ⟨Empty, inferInstance, fun _ _ => 0, fun _ _ => 0, fun i => i.elim, fun i => i.elim,
    ⟨0, fun i => i.elim⟩, fun _ _ => by simp⟩

lemma sep_add {F G : ℝ → ℝ → ℝ} (hF : Sep t F) (hG : Sep t G) :
    Sep t fun u T => F u T + G u T := by
  obtain ⟨ι, _, α, β, hα, hβ, hF⟩ := hF
  obtain ⟨ι', _, α', β', hα', hβ', hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim α α', Sum.elim β β', fun i => ?_, fun i => ?_,
    fun u T => ?_⟩
  · cases i <;> simp [hα, hα']
  · cases i <;> simp [hβ, hβ']
  · beta_reduce
    rw [Fintype.sum_sum_type, hF, hG]
    rfl

lemma sepB_add {F G : ℝ → ℝ → ℝ} (hF : SepB t F) (hG : SepB t G) :
    SepB t fun u T => F u T + G u T := by
  obtain ⟨ι, _, α, β, hα, hβ, ⟨B, hB⟩, hF⟩ := hF
  obtain ⟨ι', _, α', β', hα', hβ', ⟨B', hB'⟩, hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim α α', Sum.elim β β', fun i => ?_, fun i => ?_,
    ⟨max B B', fun i u hu => ?_⟩, fun u T => ?_⟩
  · cases i <;> simp [hα, hα']
  · cases i <;> simp [hβ, hβ']
  · cases i with
    | inl i => exact (hB i u hu).trans (le_max_left _ _)
    | inr i => exact (hB' i u hu).trans (le_max_right _ _)
  · beta_reduce
    rw [Fintype.sum_sum_type, hF, hG]
    rfl

lemma sep_smul (a : ℝ) {F : ℝ → ℝ → ℝ} (hF : Sep t F) : Sep t fun u T => a * F u T := by
  obtain ⟨ι, hι, α, β, hα, hβ, hF⟩ := hF
  refine ⟨ι, hι, fun i T => a * α i T, β, fun i => analyticOnNhd_const.mul (hα i), hβ,
    fun u T => ?_⟩
  beta_reduce
  rw [hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sepB_smul (a : ℝ) {F : ℝ → ℝ → ℝ} (hF : SepB t F) : SepB t fun u T => a * F u T := by
  obtain ⟨ι, hι, α, β, hα, hβ, hB, hF⟩ := hF
  refine ⟨ι, hι, fun i T => a * α i T, β, fun i => analyticOnNhd_const.mul (hα i), hβ, hB,
    fun u T => ?_⟩
  beta_reduce
  rw [hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sep_sub {F G : ℝ → ℝ → ℝ} (hF : Sep t F) (hG : Sep t G) :
    Sep t fun u T => F u T - G u T :=
  sep_congr (fun u T => by ring) (sep_add hF (sep_smul (-1) hG))

lemma sepB_sub {F G : ℝ → ℝ → ℝ} (hF : SepB t F) (hG : SepB t G) :
    SepB t fun u T => F u T - G u T :=
  sepB_congr (fun u T => by ring) (sepB_add hF (sepB_smul (-1) hG))

lemma sep_sum {κ : Type*} (s : Finset κ) {F : κ → ℝ → ℝ → ℝ} (h : ∀ l ∈ s, Sep t (F l)) :
    Sep t fun u T => ∑ l ∈ s, F l u T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact sep_congr (fun u T => by simp) sep_zero
  | insert a s ha ih =>
    exact sep_congr (fun u T => by rw [Finset.sum_insert ha])
      (sep_add (h a (Finset.mem_insert_self a s)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl)))

lemma sepB_sum {κ : Type*} (s : Finset κ) {F : κ → ℝ → ℝ → ℝ} (h : ∀ l ∈ s, SepB t (F l)) :
    SepB t fun u T => ∑ l ∈ s, F l u T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact sepB_congr (fun u T => by simp) sepB_zero
  | insert a s ha ih =>
    exact sepB_congr (fun u T => by rw [Finset.sum_insert ha])
      (sepB_add (h a (Finset.mem_insert_self a s)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl)))

lemma sepB_mul {F G : ℝ → ℝ → ℝ} (hF : SepB t F) (hG : SepB t G) :
    SepB t fun u T => F u T * G u T := by
  obtain ⟨ι, _, α, β, hα, hβ, ⟨B, hB⟩, hF⟩ := hF
  obtain ⟨ι', _, α', β', hα', hβ', ⟨B', hB'⟩, hG⟩ := hG
  refine ⟨ι × ι', inferInstance, fun p T => α p.1 T * α' p.2 T, fun p u => β p.1 u * β' p.2 u,
    fun p => (hα p.1).mul (hα' p.2), fun p => (hβ p.1).mul (hβ' p.2),
    ⟨|B| * |B'|, fun p u hu => ?_⟩, fun u T => ?_⟩
  · rw [abs_mul]
    exact mul_le_mul ((hB p.1 u hu).trans (le_abs_self B)) ((hB' p.2 u hu).trans (le_abs_self B'))
      (abs_nonneg _) (abs_nonneg B)
  · beta_reduce
    rw [hF, hG, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `α(T) g(u)`, `g` integrable. -/
lemma sep_one {α g : ℝ → ℝ} (hα : AnalyticOnNhd ℝ α univ)
    (hg : IntervalIntegrable g volume 0 t) : Sep t fun u T => α T * g u :=
  ⟨Unit, inferInstance, fun _ => α, fun _ => g, fun _ => hα, fun _ => hg, fun u T => by simp⟩

/-- `α(T) g(u)`, `g` measurable and bounded on `[0, t]`. -/
lemma sepB_one {α g : ℝ → ℝ} (hα : AnalyticOnNhd ℝ α univ) (hg : Measurable g) (B : ℝ)
    (hB : ∀ u ∈ uIcc 0 t, |g u| ≤ B) : SepB t fun u T => α T * g u :=
  ⟨Unit, inferInstance, fun _ => α, fun _ => g, fun _ => hα, fun _ => hg, ⟨B, fun _ => hB⟩,
    fun u T => by simp⟩

/-- `g(u)`, `g` measurable and bounded on `[0, t]`. -/
lemma sepB_u {g : ℝ → ℝ} (hg : Measurable g) (B : ℝ) (hB : ∀ u ∈ uIcc 0 t, |g u| ≤ B) :
    SepB t fun u _ => g u :=
  sepB_congr (fun u T => by simp) (sepB_one (α := fun _ => 1) analyticOnNhd_const hg B hB)

/-- `g(u)`, `g` continuous. -/
lemma sepB_cont {g : ℝ → ℝ} (hg : Continuous g) : SepB t fun u _ => g u := by
  obtain ⟨B, hB⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
    hg.continuousOn
  exact sepB_u hg.measurable B fun u hu => by simpa [Real.norm_eq_abs] using hB u hu

/-- `(T − u)^n`. -/
lemma sepB_pow (n : ℕ) : SepB t fun u T => (T - u) ^ n := by
  refine sepB_congr (fun u T => ?_) (sepB_sum (Finset.range (n + 1)) fun i _ =>
    sepB_mul (sepB_one (α := fun T => (n.choose i : ℝ) * T ^ i) (g := fun _ => 1)
      (analyticOnNhd_const.mul (analyticOnNhd_id.pow i)) measurable_const 1 (fun _ _ => by simp))
      (sepB_cont (g := fun u => (-u) ^ (n - i)) (by fun_prop)))
  rw [sub_eq_add_neg, add_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `(T − u)^n b(u)`, `b` integrable. -/
lemma sep_pow_mul (n : ℕ) {b : ℝ → ℝ} (hb : IntervalIntegrable b volume 0 t) :
    Sep t fun u T => (T - u) ^ n * b u := by
  refine sep_congr (fun u T => ?_) (sep_sum (Finset.range (n + 1)) fun i _ =>
    sep_one (α := fun T => (n.choose i : ℝ) * T ^ i) (g := fun u => (-u) ^ (n - i) * b u)
      (analyticOnNhd_const.mul (analyticOnNhd_id.pow i))
      (hb.continuousOn_mul (by fun_prop)))
  rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring


/-- `(T − u)^n`-free vector pieces: `v · x(u)`. -/
lemma sepB_dot (v : Fin r → ℝ) {x : ℝ → Fin r → ℝ} (hx : ∀ i, Measurable fun u => x u i) (B : ℝ)
    (hB : ∀ u i, |x u i| ≤ B) : SepB t fun u _ => v ⬝ᵥ x u :=
  sepB_congr (fun _ _ => rfl) (sepB_sum Finset.univ fun i _ =>
    sepB_smul (v i) (sepB_u (hx i) B fun u _ => hB u i))

/-- `c e^{A(T−u)} x(u)`, `x` measurable and bounded. -/
lemma sepB_cexp (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) {x : ℝ → Fin r → ℝ}
    (hx : ∀ i, Measurable fun u => x u i) (B : ℝ) (hB : ∀ u i, |x u i| ≤ B) :
    SepB t fun u T => c ⬝ᵥ (exp ((T - u) • A) *ᵥ x u) := by
  refine sepB_congr (fun u T => ?_) (sepB_sum Finset.univ fun i _ =>
    sepB_mul (sepB_one (α := fun T => (c ᵥ* exp (T • A)) i) (g := fun _ => 1)
      (row_analytic c A i) measurable_const 1 (fun _ _ => by simp))
    (sepB_sum Finset.univ fun j _ =>
      sepB_mul (sepB_u (hx j) B fun u _ => hB u j) (sepB_cont (econt A i j))))
  rw [fac1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pexp A x u i, mul_one]

/-- `c e^{A(T−u)} y(u)`, `y` integrable. -/
lemma sep_cexp (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) {y : ℝ → Fin r → ℝ}
    (hy : ∀ i, IntervalIntegrable (fun u => (exp (u • (-A)) *ᵥ y u) i) volume 0 t) :
    Sep t fun u T => c ⬝ᵥ (exp ((T - u) • A) *ᵥ y u) :=
  sep_congr (fun u T => fac1 c A T u _) (sep_sum Finset.univ fun i _ =>
    sep_one (α := fun T => (c ᵥ* exp (T • A)) i) (row_analytic c A i) (hy i))

/-! ### Closed forms and the expansion of `σ·∫σ` -/

lemma int_pow_shift (μ : ℕ) (u T : ℝ) :
    ∫ v in u..T, (v - u) ^ μ = (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ μ) u, integral_pow]
  simp

/-- `∫_u^T σ^B_l(u, v) dv`, in closed form. -/
noncomputable def IB (HP : ℕ → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (u T : ℝ) (l : Fin k) : ℝ :=
  ∑ μ ∈ Finset.range (d + 1), (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) * HP μ u l +
    c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ fun i => HZ u i l)

lemma sigmaB_cont (HP : ℕ → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (u : ℝ) (l : Fin k) :
    Continuous fun v => sigmaB044 HP HZ c A d u v l :=
  (continuous_finsetSum _ fun μ _ => by fun_prop).add (cexp_cont c A u _)

lemma sigmaB_int (HP : ℕ → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (d : ℕ) (u T : ℝ) (l : Fin k) :
    ∫ v in u..T, sigmaB044 HP HZ c A d u v l = IB HP HZ c A d u T l := by
  have i1 : IntervalIntegrable (fun v => ∑ μ ∈ Finset.range (d + 1), (v - u) ^ μ * HP μ u l)
      volume u T :=
    (continuous_finsetSum _ fun μ _ => by fun_prop).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun v => c ⬝ᵥ (exp ((v - u) • A) *ᵥ fun i => HZ u i l)) volume u T :=
    (cexp_cont c A u _).intervalIntegrable _ _
  unfold sigmaB044
  rw [intervalIntegral.integral_add i1 i2, int_cexp A hA,
    intervalIntegral.integral_finsetSum fun μ _ =>
      (by fun_prop : Continuous fun v : ℝ => (v - u) ^ μ * HP μ u l).intervalIntegrable _ _]
  simp only [intervalIntegral.integral_mul_const, int_pow_shift]
  rfl

lemma sigma_int044 (s : ℕ → ℝ → ℝ) (hs : ∀ j, Measurable (s j)) (C : ℝ)
    (hsC : ∀ j u, |s j u| ≤ C) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : IsUnit A.det) (d : ℕ) (u T : ℝ) (l : Fin k) :
    ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l =
      SS033 s Tm u T * HS u l + IB HP HZ c A d u T l := by
  have hm : Measurable fun v => sigS033 s Tm u v :=
    (Novel.SpliceCrossTermDriftProof.sigS_meas2 s hs Tm).comp (measurable_const.prodMk measurable_id)
  have i1 : IntervalIntegrable (fun v => sigS033 s Tm u v * HS u l) volume u T :=
    (Novel.SpliceCrossTermDriftProof.ii_bdd hm C (fun v => hsC _ _) u T).mul_const _
  have i2 : IntervalIntegrable (fun v => sigmaB044 HP HZ c A d u v l) volume u T :=
    (sigmaB_cont HP HZ c A d u l).intervalIntegrable _ _
  unfold sigma044
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
    sigmaB_int HP HZ c A hA]
  rfl

/-- `σ·∫σ = σ^S ∫σ^S + σ^B·∫σ^B + cross`. -/
lemma expand044 (s : ℕ → ℝ → ℝ) (hs : ∀ j, Measurable (s j)) (C : ℝ)
    (hsC : ∀ j u, |s j u| ≤ C) (HS : ℝ → Fin k → ℝ) (HP : ℕ → ℝ → Fin k → ℝ)
    (HZ : ℝ → Fin r → Fin k → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : IsUnit A.det) (d : ℕ) (u T : ℝ) :
    (sigma044 s HS HP HZ Tm c A d u T ⬝ᵥ fun l => ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l) =
      stepPart s HS Tm u T + bb044 HP HZ c A d u T +
        cross044 s Tm c A (w040 HS HZ) d (wP044 HS HP) u T := by
  have e : (sigma044 s HS HP HZ Tm c A d u T ⬝ᵥ
      fun l => ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l) =
      ∑ l, (sigS033 s Tm u T * HS u l + sigmaB044 HP HZ c A d u T l) *
        (SS033 s Tm u T * HS u l + IB HP HZ c A d u T l) := by
    simp only [sigma_int044 s hs C hsC HS HP HZ Tm c A hA d u T]
    rfl
  rw [e, alg (HS u) (sigmaB044 HP HZ c A d u T) (fun l => IB HP HZ c A d u T l)]
  have hbb : ∑ l, sigmaB044 HP HZ c A d u T l * IB HP HZ c A d u T l = bb044 HP HZ c A d u T := by
    unfold bb044
    simp only [sigmaB_int HP HZ c A hA d u]
  have hB : ∑ l, HS u l * IB HP HZ c A d u T l =
      ∑ μ ∈ Finset.range (d + 1), (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) * wP044 HS HP μ u +
        c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ w040 HS HZ u) := by
    rw [dot_w]
    simp only [IB, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [wP044, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hβ : ∑ l, HS u l * sigmaB044 HP HZ c A d u T l =
      ∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * wP044 HS HP μ u +
        c ⬝ᵥ (exp ((T - u) • A) *ᵥ w040 HS HZ u) := by
    rw [dot_w]
    simp only [sigmaB044, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [wP044, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hbb, hB, hβ]
  unfold stepPart cross044 cross040 crossPoly044
  have hsum : ∑ μ ∈ Finset.range (d + 1), wP044 HS HP μ u *
      (sigS033 s Tm u T * (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) + (T - u) ^ μ * SS033 s Tm u T) =
      sigS033 s Tm u T * ∑ μ ∈ Finset.range (d + 1), (T - u) ^ (μ + 1) / ((μ : ℝ) + 1) *
        wP044 HS HP μ u + (∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * wP044 HS HP μ u) *
          SS033 s Tm u T := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [hsum]
  ring

/-! ### The block's part is analytic -/

section Block
variable {HP : ℕ → ℝ → Fin k → ℝ} {HZ : ℝ → Fin r → Fin k → ℝ} {c : Fin r → ℝ}
  {A : Matrix (Fin r) (Fin r) ℝ} {d : ℕ} {bP zP : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ}

lemma sepB_sigmaB (hHP : ∀ μ l, Measurable fun u => HP μ u l)
    (hHZ : ∀ i l, Measurable fun u => HZ u i l) (B : ℝ) (hHPB : ∀ μ u l, |HP μ u l| ≤ B)
    (hHZB : ∀ u i l, |HZ u i l| ≤ B) (l : Fin k) :
    SepB t fun u T => sigmaB044 HP HZ c A d u T l :=
  sepB_congr (fun _ _ => rfl) (sepB_add (sepB_sum (Finset.range (d + 1)) fun μ _ =>
      sepB_mul (sepB_pow μ) (sepB_u (hHP μ l) B fun u _ => hHPB μ u l))
    (sepB_cexp c A (fun i => hHZ i l) B fun u i => hHZB u i l))

lemma sepB_IB (hHP : ∀ μ l, Measurable fun u => HP μ u l)
    (hHZ : ∀ i l, Measurable fun u => HZ u i l) (B : ℝ) (hHPB : ∀ μ u l, |HP μ u l| ≤ B)
    (hHZB : ∀ u i l, |HZ u i l| ≤ B) (l : Fin k) :
    SepB t fun u T => IB HP HZ c A d u T l := by
  refine sepB_congr (fun u T => ?_) (sepB_add (sepB_sum (Finset.range (d + 1)) fun μ _ =>
      sepB_mul (sepB_smul (1 / ((μ : ℝ) + 1)) (sepB_pow (μ + 1)))
        (sepB_u (hHP μ l) B fun u _ => hHPB μ u l))
    (sepB_sub (sepB_cexp (c ᵥ* A⁻¹) A (fun i => hHZ i l) B fun u i => hHZB u i l)
      (sepB_dot (c ᵥ* A⁻¹) (fun i => hHZ i l) B fun u i => hHZB u i l)))
  unfold IB
  congr 1
  · exact Finset.sum_congr rfl fun μ _ => by ring
  · rw [mul_sub, mul_one, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec c A⁻¹,
      dotProduct_mulVec c A⁻¹]

/-- The block's integrands are integrable on `[0, t]` and `∫_0^t (D^B − σ^B·∫σ^B)` is analytic. -/
lemma block_sep (hA : IsUnit A.det) (hHP : ∀ μ l, Measurable fun u => HP μ u l)
    (hHZ : ∀ i l, Measurable fun u => HZ u i l) (hzP : ∀ μ, Measurable (zP μ))
    (hz : ∀ i, Measurable fun u => z u i) (B : ℝ) (hHPB : ∀ μ u l, |HP μ u l| ≤ B)
    (hHZB : ∀ u i l, |HZ u i l| ≤ B) (hzPB : ∀ μ u, |zP μ u| ≤ B) (hzB : ∀ u i, |z u i| ≤ B)
    (hbP : ∀ μ, IntervalIntegrable (bP μ) volume 0 t)
    (hbZ : ∀ i, IntervalIntegrable (fun u => bZ u i) volume 0 t) :
    (∀ T, IntervalIntegrable (fun u => driftB044 c A d bP zP bZ z u T) volume 0 t) ∧
    (∀ T, IntervalIntegrable (fun u => bb044 HP HZ c A d u T) volume 0 t) ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t,
      (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T)) univ := by
  obtain ⟨hq, -, -⟩ := block_ii (c := c) (A := A) (bZ := bZ) hHZ hz B hHZB hzB t hbZ
  have hD : Sep t fun u T => driftB044 c A d bP zP bZ z u T :=
    sep_congr (fun u T => rfl) (sep_add (sep_sum (Finset.range (d + 1)) fun μ _ =>
      sep_sub (sep_pow_mul μ (hbP μ)) (sepB_sep (sepB_congr (fun u T => by ring)
        (sepB_smul (μ : ℝ) (sepB_mul (sepB_pow (μ - 1)) (sepB_u (hzP μ) B fun u _ => hzPB μ u))))))
      (sep_cexp c A hq))
  have hbb : SepB t fun u T => bb044 HP HZ c A d u T :=
    sepB_congr (fun u T => by simp only [bb044, sigmaB_int HP HZ c A hA d u]; rfl)
      (sepB_sum Finset.univ fun l _ =>
        sepB_mul (sepB_sigmaB hHP hHZ B hHPB hHZB l) (sepB_IB hHP hHZ B hHPB hHZB l))
  exact ⟨(sep_int hD).1, (sep_int (sepB_sep hbb)).1, (sep_int (sep_sub hD (sepB_sep hbb))).2⟩

end Block

/-! ### The path data -/

lemma ii_fsum {κ : Type*} (S : Finset κ) {f : κ → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i ∈ S, f i u) volume a b := by
  have := IntervalIntegrable.sum S h
  convert this using 1
  funext u
  simp [Finset.sum_apply]

section Data
variable {s : ℕ → ℝ → ℝ} {HS : ℝ → Fin k → ℝ} {HP : ℕ → ℝ → Fin k → ℝ}
  {HZ : ℝ → Fin r → Fin k → ℝ} {dL dC : ℕ → ℝ → ℝ} {bP zP : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ}
  {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} {d : ℕ}

/-- The covariation densities are measurable and bounded. -/
lemma pd044 (h : DriverData044 s HS HP HZ dL dC bP zP bZ z H) :
    Standalone.SpliceExponentZeroCross.PathData044 s (w040 HS HZ) (wP044 HS HP) := by
  obtain ⟨h0, hHP, -, ⟨C', hHPC, -⟩, -⟩ := h
  obtain ⟨-, hPD⟩ := data_sn h0
  obtain ⟨-, hHS, -, -, ⟨C, -, hHSC, -, -⟩, -⟩ := h0
  refine ⟨hPD, fun μ => Finset.measurable_sum _ fun l _ => (hHP μ l).mul (hHS l),
    ∑ _l : Fin k, |C'| * |C|, fun μ u => ?_⟩
  simp only [wP044]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  exact mul_le_mul ((hHPC μ u l).trans (le_abs_self _)) ((hHSC u l).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

lemma blk (h : DriverData044 s HS HP HZ dL dC bP zP bZ z H) (hA : IsUnit A.det) (t : ℝ)
    (ht : 0 ≤ t) (htH : t ≤ H) :
    (∀ T, IntervalIntegrable (fun u => driftB044 c A d bP zP bZ z u T) volume 0 t) ∧
    (∀ T, IntervalIntegrable (fun u => bb044 HP HZ c A d u T) volume 0 t) ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t,
      (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T)) univ := by
  obtain ⟨⟨-, -, hHZ, hz, ⟨C, -, -, hHZC, hzC⟩, -, -, hbZ⟩, hHP, hzP, ⟨C', hHPC, hzPC⟩, hbP⟩ := h
  have hsub : uIcc 0 t ⊆ uIcc 0 H := by
    rw [uIcc_of_le ht, uIcc_of_le (ht.trans htH)]
    exact Icc_subset_Icc le_rfl htH
  have b1 : ∀ x, x ≤ C → x ≤ |C| + |C'| := fun x hx =>
    hx.trans ((le_abs_self C).trans (le_add_of_nonneg_right (abs_nonneg _)))
  have b2 : ∀ x, x ≤ C' → x ≤ |C| + |C'| := fun x hx =>
    hx.trans ((le_abs_self C').trans (le_add_of_nonneg_left (abs_nonneg _)))
  exact block_sep hA hHP hHZ hzP hz _ (fun μ u l => b2 _ (hHPC μ u l)) (fun u i l => b1 _ (hHZC u i l))
    (fun μ u => b2 _ (hzPC μ u)) (fun u i => b1 _ (hzC u i)) (fun μ => (hbP μ).mono_set hsub)
    (fun i => (hbZ i).mono_set hsub)

end Data

/-- The cross term of `z_{0,μ}` is integrable on `[0, t]`, `0 ≤ t ≤ T`. -/
lemma crossPoly_ii {s : ℕ → ℝ → ℝ} {w : ℝ → ℝ} (hs : ∀ j, Measurable (s j)) (hw : Measurable w)
    {Cs Cw : ℝ} (hsC : ∀ j u, |s j u| ≤ Cs) (hwC : ∀ u, |w u| ≤ Cw) (Tm : Finset ℝ) (μ : ℕ)
    (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun u => crossPoly044 s Tm μ w u T) volume 0 t := by
  obtain ⟨G, hGm, hG⟩ := Novel.SpliceCrossTermDriftProof.SS_measurable s hs Tm T
  have hGb : ∀ u ∈ uIcc 0 t, |G u| ≤ Cs * T := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    rw [← hG u (hu.2.trans htT), SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T) (C := Cs)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by rw [Real.norm_eq_abs]; exact hsC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ T - u)] at hb
    nlinarith [hu.1, (abs_nonneg _).trans (hsC 0 0)]
  have hc : ∀ n, ContinuousOn (fun u : ℝ => (T - u) ^ n) (uIcc 0 t) := fun n => by fun_prop
  have i1 := ((Novel.SpliceExponentZeroCrossProof.ws_ii hs hw hsC hwC (idx033 Tm T) t).mul_continuousOn
    (hc (μ + 1))).const_mul (1 / ((μ : ℝ) + 1))
  have i2 := (Novel.SpliceCrossTermCurveProof.ii_on (hw.mul hGm) (Cw * (Cs * T)) fun u hu => by
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hwC u) (hGb u hu) (abs_nonneg _) ((abs_nonneg _).trans (hwC u))).mul_continuousOn
    (hc μ)
  refine (i1.add i2).congr fun u hu => ?_
  rw [uIoc_of_le ht] at hu
  simp only [Pi.mul_apply, crossPoly044, sigS033, ← hG u (hu.2.trans htT)]
  ring

lemma cross044_ii {s : ℕ → ℝ → ℝ} {wζ : ℝ → Fin r → ℝ} {wP : ℕ → ℝ → ℝ}
    (h : Standalone.SpliceExponentZeroCross.PathData044 s wζ wP) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun u => cross044 s Tm c A wζ d wP u T) volume 0 t ∧
    ∀ μ, IntervalIntegrable (fun u => crossPoly044 s Tm μ (wP μ) u T) volume 0 t := by
  obtain ⟨hPD, hwm, Cw, hwC⟩ := h
  obtain ⟨hs, -, Cs, hsC, -⟩ := id hPD
  have hP := fun μ => crossPoly_ii hs (hwm μ) hsC (hwC μ) Tm μ t T ht htT
  exact ⟨(Novel.SpliceExponentZeroCrossProof.cross040_ii hPD Tm c A t T ht htT).add
    (ii_fsum _ fun μ _ => hP μ), hP⟩

section Main
variable {s : ℕ → ℝ → ℝ} {HS : ℝ → Fin k → ℝ} {HP : ℕ → ℝ → Fin k → ℝ}
  {HZ : ℝ → Fin r → Fin k → ℝ} {dL dC : ℕ → ℝ → ℝ} {bP zP : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ}
  {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} {d : ℕ}

/-- Integrating AX-01 over `[0, t]`: the cross term is the front end's part plus the block's. -/
lemma decomp044 (h : DriverData044 s HS HP HZ dL dC bP zP bZ z H) (hA : IsUnit A.det)
    (hAX : AX01Path044 s HS HP HZ dL dC bP zP bZ z Tm c A d H) (t : ℝ) (ht : 0 ≤ t)
    (htH : t ≤ H) :
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross044 s Tm c A (w040 HS HZ) d (wP044 HS HP) u T =
      ((∫ u in (0:ℝ)..t, driftS dL dC Tm u T) - ∫ u in (0:ℝ)..t, stepPart s HS Tm u T) +
        ∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T) := by
  intro T hT
  have hs := h.1.1
  obtain ⟨C, hsC, -⟩ := h.1.2.2.2.2.1
  obtain ⟨iS, -, iP, -, -, -⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h.1 t T ht hT.1.le htH
  obtain ⟨iD, iB, -⟩ := blk (c := c) (A := A) (d := d) h hA t ht htH
  have iX := (cross044_ii (pd044 h) Tm c A d t T ht hT.1.le).1
  have hae : ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB044 c A d bP zP bZ z u T) =
      ∫ u in (0:ℝ)..t, (stepPart s HS Tm u T + bb044 HP HZ c A d u T +
        cross044 s Tm c A (w040 HS HZ) d (wP044 HS HP) u T) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hAX] with u hu hu'
    rw [uIoc_of_le ht] at hu'
    rw [hu ⟨hu'.1.le, hu'.2.trans htH⟩ T ⟨hu'.2.trans hT.1.le, hT.2.le⟩,
      expand044 s hs C hsC HS HP HZ Tm c A hA d u T]
  rw [intervalIntegral.integral_add iS (iD T), intervalIntegral.integral_add (iP.add (iB T)) iX,
    intervalIntegral.integral_add iP (iB T)] at hae
  rw [intervalIntegral.integral_sub (iD T) (iB T)]
  linarith

end Main

lemma necessity : Standalone.SpliceExponentZeroAX01.necessityStatement := by
  intro r k A hA c hobs d s HS HP HZ dL dC bP zP bZ z Tm H h hAX τ hτ hτH
  refine Novel.SpliceExponentZeroCrossProof.core r A hA c hobs s (w040 HS HZ) d (wP044 HS HP)
    (pd044 h) Tm τ H hτ hτH fun t ht => ?_
  have htH : t ≤ H := ht.2.le.trans hτH.le
  obtain ⟨-, -, hG⟩ := blk (c := c) (A := A) (d := d) h hA t ht.1 htH
  refine ⟨fun T => (∫ u in (0:ℝ)..t, driftS dL dC Tm u T) - ∫ u in (0:ℝ)..t, stepPart s HS Tm u T,
    fun T => ∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T), hG,
    fun j => ?_, decomp044 h hA hAX t ht.1 htH⟩
  obtain ⟨k₀, k₁, hk⟩ := front_affine (Tm := Tm) h.1 t ht.1 htH j
  exact ⟨k₀, k₁, fun T hT hTj => hk T hTj hT.1.le⟩

/-! ### (b) -/

lemma PJ_hi (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (w : ℝ → ℝ) (μ j : ℕ) (T0 t : ℝ) (i : ℕ)
    (hi : μ + 1 < i) : (Novel.SpliceExponentZeroCrossProof.PJ s Tm w μ j T0 t).coeff i = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp only [Novel.SpliceExponentZeroCrossProof.PJ, coeff_add, coeff_C_mul, coeff_X_mul,
    Novel.SpliceExponentZeroCrossProof.mom_hi _ (μ + 1) t (m + 1) hi,
    Novel.SpliceExponentZeroCrossProof.mom_hi _ μ t m (by omega),
    Novel.SpliceExponentZeroCrossProof.mom_hi _ μ t (m + 1) (by omega)]
  ring

lemma level : Standalone.SpliceExponentZeroAX01.levelStatement := by
  intro s w hs hw ⟨C, hsC, hwC⟩ Tm t ht j
  by_cases hne : ∃ T0, idx033 Tm T0 = j ∧ t ≤ T0
  swap
  · push Not at hne
    exact ⟨0, 0, fun T hT htT => absurd htT (not_le.2 (hne T hT))⟩
  obtain ⟨T0, hT0, htT0⟩ := hne
  set P := Novel.SpliceExponentZeroCrossProof.PJ s Tm w 0 j T0 t
  refine ⟨P.coeff 0, P.coeff 1, fun T hT htT => ?_⟩
  have hseg : ∀ v ∈ Ioo (min T0 T) (max T0 T), idx033 Tm v = j := fun v hv => by
    have h1 := Novel.SpliceCrossTermDriftProof.idx_mono Tm hv.1.le
    have h2 := Novel.SpliceCrossTermDriftProof.idx_mono Tm hv.2.le
    rcases le_total T0 T with h | h
    · rw [min_eq_left h] at h1
      rw [max_eq_right h] at h2
      omega
    · rw [min_eq_right h] at h1
      rw [max_eq_left h] at h2
      omega
  rw [(Novel.SpliceExponentZeroCrossProof.int_PJ hs hw hsC hwC Tm 0 j T0 t T ht htT0 hT hseg).2]
  have hdeg : P.natDegree < 2 := Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 fun i hi =>
    PJ_hi s Tm w 0 j T0 t i (by exact_mod_cast hi))
  rw [eval_eq_sum_range' hdeg]
  simp [Finset.sum_range_succ]

lemma jumpFree : Standalone.SpliceExponentZeroAX01.jumpFreeStatement := by
  intro r k A hA c d s HS HP HZ dL dC bP zP bZ z Tm H h hcond t ht
  obtain ⟨c₀, y, z', hX⟩ := Novel.SpliceStateBlockAX01Proof.jumpFree r k A hA c s HS HZ dL dC bZ z
    Tm H h.1 (fun τ hτ => (hcond τ hτ).1) t ht
  obtain ⟨hPD, hwm, Cw, hwC⟩ := pd044 h
  obtain ⟨hs, -, Cs, hsC, -⟩ := id hPD
  set j0 := idx033 Tm t
  have hpoly : ∀ μ, 1 ≤ μ → μ ≤ d → ∀ T, t ≤ T →
      ∫ u in (0:ℝ)..t, crossPoly044 s Tm μ (wP044 HS HP μ) u T =
        (Novel.SpliceExponentZeroCrossProof.PJ s Tm (wP044 HS HP μ) μ j0 t t).eval T := by
    intro μ hμ1 hμd T htT
    set w := wP044 HS HP μ
    have hgood : ∀ᵐ u ∂volume, u ∈ Icc 0 t → ∀ v, t ≤ v →
        w u * s (idx033 Tm v) u = w u * s j0 u := by
      filter_upwards [(eventually_all_finset Tm).2 fun τ hτ => (hcond τ hτ).2 μ hμ1 hμd]
        with u hu hu0
      exact Novel.SpliceCrossTermSufficiencyProof.chain Tm (fun j u => w u * s j u) u t hu0.2
        fun τ hτ huτ => by
          have := hu τ hτ ⟨hu0.1, huτ⟩
          linear_combination this
    rw [← (Novel.SpliceExponentZeroCrossProof.int_rhs hs (hwm μ) hsC (hwC μ) Tm μ j0 t t T ht
      le_rfl).2]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hgood] with u hu hmem
    rw [uIoc_of_le ht] at hmem
    have hu' := hu ⟨hmem.1.le, hmem.2⟩
    have hsig : w u * s (idx033 Tm T) u = w u * s j0 u := hu' T htT
    have hSS : w u * SS033 s Tm u T = w u * (SS033 s Tm u t + s j0 u * (T - t)) := by
      by_cases hw0 : w u = 0
      · simp [hw0]
      · rw [Novel.SpliceQuasiExponentialCrossProof.SS_after Tm s hs Cs hsC u t T htT
          fun v hv => mul_left_cancel₀ hw0 (hu' v hv)]
    simp only [crossPoly044, sigS033, kappa033]
    linear_combination ((T - u) ^ (μ + 1) / ((μ : ℝ) + 1)) * hsig + (T - u) ^ μ * hSS
  refine ⟨c₀, y, z', ∑ μ ∈ Finset.range d,
    Novel.SpliceExponentZeroCrossProof.PJ s Tm (wP044 HS HP (μ + 1)) (μ + 1) j0 t t,
    fun T htT => ?_⟩
  have iX := Novel.SpliceExponentZeroCrossProof.cross040_ii hPD Tm c A t T ht htT
  have iP := fun μ => crossPoly_ii hs (hwm μ) hsC (hwC μ) Tm μ t T ht htT
  unfold restCross044
  rw [intervalIntegral.integral_add iX (ii_fsum _ fun μ _ => iP (μ + 1)),
    intervalIntegral.integral_finsetSum fun μ _ => iP (μ + 1), hX T htT, eval_finsetSum,
    Finset.sum_congr rfl fun μ hμ => hpoly (μ + 1) (by omega)
      (by simp only [Finset.mem_range] at hμ; omega) T htT]

section Split
variable {s : ℕ → ℝ → ℝ} {HS : ℝ → Fin k → ℝ} {HP : ℕ → ℝ → Fin k → ℝ}
  {HZ : ℝ → Fin r → Fin k → ℝ} {dL dC : ℕ → ℝ → ℝ} {bP zP : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ}
  {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} {d : ℕ}

/-- The cross term is the level's plus the rest. -/
lemma split044 (h : DriverData044 s HS HP HZ dL dC bP zP bZ z H) (t T : ℝ) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    IntervalIntegrable (fun u => restCross044 s HS HP HZ Tm c A d u T) volume 0 t ∧
    ∫ u in (0:ℝ)..t, cross044 s Tm c A (w040 HS HZ) d (wP044 HS HP) u T =
      (∫ u in (0:ℝ)..t, crossPoly044 s Tm 0 (wP044 HS HP 0) u T) +
        ∫ u in (0:ℝ)..t, restCross044 s HS HP HZ Tm c A d u T := by
  obtain ⟨-, iP⟩ := cross044_ii (pd044 h) Tm c A d t T ht htT
  have iR : IntervalIntegrable (fun u => restCross044 s HS HP HZ Tm c A d u T) volume 0 t :=
    (Novel.SpliceExponentZeroCrossProof.cross040_ii (pd044 h).1 Tm c A t T ht htT).add
      (ii_fsum _ fun μ _ => iP (μ + 1))
  refine ⟨iR, ?_⟩
  rw [← intervalIntegral.integral_add (iP 0) iR]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [cross044, restCross044, Finset.sum_range_succ']
  ring

end Split

lemma affine : Standalone.SpliceExponentZeroAX01.affineStatement := by
  intro r k A hA c d s HS HP HZ dL dC bP zP bZ z Tm H h hAX hcond t ht htH
  obtain ⟨K, y, z', P, hX⟩ := jumpFree r k A hA c d s HS HP HZ dL dC bP zP bZ z Tm H h hcond t ht
  obtain ⟨-, -, hG⟩ := blk (c := c) (A := A) (d := d) h hA t ht htH.le
  obtain ⟨hPD, hwm, Cw, hwC⟩ := pd044 h
  obtain ⟨hs, -, Cs, hsC, -⟩ := id hPD
  -- the block's part as an analytic function
  let Φ : ℝ → ℝ := fun T =>
    (∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T)) -
      (K + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z')) + P.eval T)
  have hΦa : AnalyticOnNhd ℝ Φ univ := fun T _ =>
    (hG T (mem_univ _)).sub ((analyticAt_const.add
      (Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A y z' T (mem_univ _))).add
      (AnalyticOnNhd.eval_polynomial P T (mem_univ _)))
  have hΦ : ∀ T ∈ Ioo t H, blockPart044 s HS HP HZ bP zP bZ z Tm c A d t T = Φ T := by
    intro T hT
    obtain ⟨iD, iB, -⟩ := blk (c := c) (A := A) (d := d) h hA t ht htH.le
    obtain ⟨iR, -⟩ := split044 (Tm := Tm) (c := c) (A := A) (d := d) h t T ht hT.1.le
    show ∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T -
      restCross044 s HS HP HZ Tm c A d u T) = Φ T
    rw [intervalIntegral.integral_sub ((iD T).sub (iB T)) iR, hX T hT.1.le]
  -- on a piece of one maturity interval it is affine
  set T₁ := (t + H) / 2
  have hT₁ : T₁ ∈ Ioo t H := ⟨by simp only [T₁]; linarith, by simp only [T₁]; linarith⟩
  obtain ⟨ε, hε, hidx⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm T₁
  obtain ⟨k₀, k₁, hk⟩ := front_affine (Tm := Tm) h.1 t ht htH.le (idx033 Tm T₁)
  obtain ⟨l₀, l₁, hl⟩ := level s (wP044 HS HP 0) hs (hwm 0)
    ⟨|Cs| + |Cw|, fun j u => (hsC j u).trans ((le_abs_self _).trans (le_add_of_nonneg_right
      (abs_nonneg _))), fun u => (hwC 0 u).trans ((le_abs_self _).trans (le_add_of_nonneg_left
      (abs_nonneg _)))⟩ Tm t ht (idx033 Tm T₁)
  set T₂ := min (T₁ + ε) H
  have hT₂ : T₁ < T₂ := lt_min (by linarith) hT₁.2
  have hI : ∀ T ∈ Ioo T₁ T₂, Φ T = (l₀ + l₁ * T) - (k₀ + k₁ * T) := by
    intro T hT
    have hTI : T ∈ Ioo t H := ⟨hT₁.1.trans hT.1, lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
    have hTj : idx033 Tm T = idx033 Tm T₁ :=
      hidx T ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
    have hd := decomp044 h hA hAX t ht htH.le T hTI
    rw [(split044 (Tm := Tm) (c := c) (A := A) (d := d) h t T ht hTI.1.le).2, hX T hTI.1.le,
      hl T hTj hTI.1.le, hk T hTj hTI.1.le] at hd
    simp only [Φ]
    linarith
  -- so it is that affine function everywhere
  have hall : ∀ T, Φ T = (l₀ + l₁ * T) - (k₀ + k₁ * T) := by
    have hF : AnalyticOnNhd ℝ (fun T => Φ T - ((l₀ + l₁ * T) - (k₀ + k₁ * T))) univ := fun T hT =>
      (hΦa T hT).sub ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).sub
        (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))
    have hmid : (T₁ + T₂) / 2 ∈ Ioo T₁ T₂ := ⟨by linarith, by linarith⟩
    intro T
    have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [hI x hx]) (mem_univ T)
    simp only [Pi.zero_apply] at this
    linarith
  exact ⟨l₀ - k₀, l₁ - k₁, fun T hT => by rw [hΦ T hT, hall T]; ring⟩

lemma converse : Standalone.SpliceExponentZeroAX01.converseStatement := by
  intro r k A hA c d s HS HP HZ dL dC bP zP bZ z Tm H h t T ht htT hTH hdrift
  have hs := h.1.1
  obtain ⟨C, hsC, -⟩ := h.1.2.2.2.2.1
  obtain ⟨iS, -, iP, -, -, -⟩ := parts_ii (c := c) (A := A) (Tm := Tm) h.1 t T ht htT
    (htT.trans hTH)
  obtain ⟨iD, iB, -⟩ := blk (c := c) (A := A) (d := d) h hA t ht (htT.trans hTH)
  obtain ⟨iX, -⟩ := cross044_ii (pd044 h) Tm c A d t T ht htT
  obtain ⟨iR, hc⟩ := split044 (Tm := Tm) (c := c) (A := A) (d := d) h t T ht htT
  have e : ∫ u in (0:ℝ)..t, sigma044 s HS HP HZ Tm c A d u T ⬝ᵥ
      (fun l => ∫ v in u..T, sigma044 s HS HP HZ Tm c A d u v l) =
      ∫ u in (0:ℝ)..t, (stepPart s HS Tm u T + bb044 HP HZ c A d u T +
        cross044 s Tm c A (w040 HS HZ) d (wP044 HS HP) u T) :=
    intervalIntegral.integral_congr fun u _ => expand044 s hs C hsC HS HP HZ Tm c A hA d u T
  rw [e, intervalIntegral.integral_add iS (iD T), intervalIntegral.integral_add (iP.add (iB T)) iX,
    intervalIntegral.integral_add iP (iB T), hc]
  have hb : blockPart044 s HS HP HZ bP zP bZ z Tm c A d t T =
      (∫ u in (0:ℝ)..t, driftB044 c A d bP zP bZ z u T) - (∫ u in (0:ℝ)..t, bb044 HP HZ c A d u T) -
        ∫ u in (0:ℝ)..t, restCross044 s HS HP HZ Tm c A d u T := by
    show ∫ u in (0:ℝ)..t, (driftB044 c A d bP zP bZ z u T - bb044 HP HZ c A d u T -
      restCross044 s HS HP HZ Tm c A d u T) = _
    rw [intervalIntegral.integral_sub ((iD T).sub (iB T)) iR, intervalIntegral.integral_sub (iD T) (iB T)]
  rw [hb] at hdrift
  linarith

lemma noThirdWay : Standalone.SpliceExponentZeroAX01.noThirdWayStatement := by
  intro r k A hA c hobs d s HS HP HZ bP zP bZ z Tm H τ hτ hτH hne dL dC h hAX
  exact hne (necessity r k A hA c hobs d s HS HP HZ dL dC bP zP bZ z Tm H h hAX τ hτ hτH)

theorem spliceExponentZeroAX01 : Standalone.SpliceExponentZeroAX01.statement :=
  ⟨necessity, level, jumpFree, affine, converse, noThirdWay⟩

end Novel.SpliceExponentZeroAX01Proof

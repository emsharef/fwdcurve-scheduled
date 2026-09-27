import Standalone.MaturityShapeIdentities
import Novel.DiffusionMeetingIdentitiesProof
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open Standalone.MaturityShapeIdentities
namespace Novel.MaturityShapeIdentitiesProof

/-- Fubini on the triangle `a < s ≤ x ≤ b`, for a kernel bounded on the box. -/
lemma tri {a b : ℝ} (hab : a ≤ b) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k)) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, ∀ s ∈ Icc a b, |k x s| ≤ M) :
    ∫ x in a..b, (∫ s in a..x, k x s) = ∫ s in a..b, ∫ x in s..b, k x s := by
  classical
  set F : ℝ → ℝ → ℝ := fun x s => if s ≤ x then k x s else 0
  set A := Ioc a b
  have hA : ∀ x ∈ A, ∫ s in a..x, k x s = ∫ s in A, F x s := fun x hx => by
    rw [intervalIntegral.integral_of_le hx.1.le]
    have : (fun s => F x s) = (Iic x).indicator fun s => k x s := by
      funext s; simp [F, indicator, mem_Iic]
    have e : A ∩ Iic x = Ioc a x := by
      ext s; simp only [A, mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hx.2⟩, h2⟩
    rw [this, setIntegral_indicator measurableSet_Iic, e]
  have hB : ∀ s ∈ A, ∫ x in s..b, k x s = ∫ x in A, F x s := fun s hs => by
    rw [intervalIntegral.integral_of_le hs.2]
    have : (fun x => F x s) = (Ici s).indicator fun x => k x s := by
      funext x; simp [F, indicator, mem_Ici]
    rw [this, setIntegral_indicator measurableSet_Ici]
    have e : A ∩ Ici s = Icc s b := by
      ext x; simp only [A, mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans_le h1, h2⟩, h1⟩
    rw [e, integral_Icc_eq_integral_Ioc]
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) hk measurable_const
  have : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hae : ∀ᵐ p ∂((volume.restrict A).prod (volume.restrict A)), p ∈ A ×ˢ A := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hFi : Integrable (Function.uncurry F) ((volume.restrict A).prod (volume.restrict A)) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable |M| (hae.mono fun p hp => ?_)
    simp only [Function.uncurry, F]
    split_ifs
    · rw [Real.norm_eq_abs]
      exact (hM _ (Ioc_subset_Icc_self hp.1) _ (Ioc_subset_Icc_self hp.2)).trans (le_abs_self M)
    · simp
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_congr_fun measurableSet_Ioc hB]
  exact integral_integral_swap hFi

section
variable {ψ : ℝ → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
include hψ hC

lemma ii (a b : ℝ) : IntervalIntegrable ψ volume a b :=
  Novel.SpliceCrossTermDriftProof.ii_bdd hψ C hC a b

lemma prim_cont (c : ℝ) : Continuous fun x => ∫ y in c..x, ψ y :=
  intervalIntegral.continuous_primitive (fun a b => ii hψ hC a b) c

lemma ii_prod (c a b : ℝ) : IntervalIntegrable (fun x => ψ x * ∫ y in c..x, ψ y) volume a b :=
  (ii hψ hC a b).mul_continuousOn (prim_cont hψ hC c).continuousOn

lemma prim_cont' (b : ℝ) : Continuous fun s => ∫ x in s..b, ψ x := by
  have := (prim_cont hψ hC b).neg
  convert this using 1
  funext s
  exact intervalIntegral.integral_symm b s

/-- `∫_a^b ψ(x) ∫_a^x ψ = (∫_a^b ψ)²/2`, for `a ≤ b`. -/
lemma half_sq {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, ψ x * ∫ y in a..x, ψ y = (∫ y in a..b, ψ y) ^ 2 / 2 := by
  have hJ' : (∫ x in a..b, ψ x * ∫ y in a..x, ψ y) = ∫ s in a..b, ψ s * ∫ x in s..b, ψ x := by
    have h := tri hab (k := fun x s => ψ x * ψ s)
      ((hψ.comp measurable_fst).mul (hψ.comp measurable_snd)) (M := C * C) fun x _ s _ => by
        rw [abs_mul]
        exact mul_le_mul (hC x) (hC s) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
    rw [intervalIntegral.integral_congr (g := fun x => ∫ s in a..x, ψ x * ψ s)
      (fun x _ => (intervalIntegral.integral_const_mul _ _).symm), h]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [intervalIntegral.integral_mul_const, mul_comm]
  have hsum : (∫ x in a..b, ψ x * ∫ y in a..x, ψ y) + (∫ s in a..b, ψ s * ∫ x in s..b, ψ x) =
      (∫ y in a..b, ψ y) ^ 2 := by
    rw [← intervalIntegral.integral_add (ii_prod hψ hC a a b)
      ((ii hψ hC a b).mul_continuousOn (prim_cont' hψ hC b).continuousOn),
      intervalIntegral.integral_congr (g := fun x => ψ x * ∫ y in a..b, ψ y) fun x _ => by
        simp only
        rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals (ii hψ hC a x)
          (ii hψ hC x b)],
      intervalIntegral.integral_mul_const]
    ring
  linarith

lemma squareS_aux (c a b : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, ψ x * ∫ y in c..x, ψ y =
      ((∫ y in c..b, ψ y) ^ 2 - (∫ y in c..a, ψ y) ^ 2) / 2 := by
  have e : ∀ x, ∫ y in c..x, ψ y = (∫ y in c..a, ψ y) + ∫ y in a..x, ψ y := fun x =>
    (intervalIntegral.integral_add_adjacent_intervals (ii hψ hC c a) (ii hψ hC a x)).symm
  rw [intervalIntegral.integral_congr (g := fun x => ψ x * (∫ y in c..a, ψ y) +
      ψ x * ∫ y in a..x, ψ y) fun x _ => by simp only; rw [e x, mul_add],
    intervalIntegral.integral_add ((ii hψ hC a b).mul_const _) (ii_prod hψ hC a a b),
    intervalIntegral.integral_mul_const, half_sq hψ hC hab, e b]
  ring
end

lemma squareS : squareStatement := by
  intro ψ hψ ⟨C, hC⟩ c a b
  rcases le_total a b with hab | hba
  · exact squareS_aux hψ hC c a b hab
  · rw [intervalIntegral.integral_symm, squareS_aux hψ hC c b a hba]
    ring

lemma a21S : assumption21Statement := by
  intro φ hφ ⟨C, hC⟩ g hg t T
  have h := squareS (φ t) (hφ t) ⟨C, hC t⟩ t t T
  rw [intervalIntegral.integral_same] at h
  norm_num at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul, Phi]
  rw [h, mul_pow, Real.sq_sqrt (hg t)]
  ring

/-! ### Measurability and bounds of the parametric integrals -/

lemma meas_param {α : Type*} [MeasurableSpace α] {lo hi : α → ℝ} (hlo : Measurable lo)
    (hhi : Measurable hi) {K : α → ℝ → ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable fun p => ∫ x in lo p..hi p, K p x := by
  classical
  have h1 : ∀ (l h : α → ℝ), Measurable l → Measurable h →
      Measurable fun p => ∫ x in Ioc (l p) (h p), K p x := fun l h hl hh => by
    have e : (fun p => ∫ x in Ioc (l p) (h p), K p x) =
        fun p => ∫ x, (fun q : α × ℝ => if l q.1 < q.2 ∧ q.2 ≤ h q.1 then K q.1 q.2 else 0) (p, x) := by
      funext p
      rw [← integral_indicator measurableSet_Ioc]
      congr 1; funext x; simp [indicator, mem_Ioc]
    rw [e]
    refine (StronglyMeasurable.integral_prod_right' (f := fun q : α × ℝ =>
      if l q.1 < q.2 ∧ q.2 ≤ h q.1 then K q.1 q.2 else 0) ?_).measurable
    refine (Measurable.ite ?_ hK measurable_const).stronglyMeasurable
    exact (measurableSet_lt (hl.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hh.comp measurable_fst))
  have e : (fun p => ∫ x in lo p..hi p, K p x) =
      fun p => (∫ x in Ioc (lo p) (hi p), K p x) - ∫ x in Ioc (hi p) (lo p), K p x := by
    funext p; rfl
  rw [e]
  exact (h1 lo hi hlo hhi).sub (h1 hi lo hhi hlo)

lemma Phi_meas {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) :
    Measurable (Function.uncurry (Phi φ)) :=
  meas_param measurable_fst measurable_snd (K := fun p x => φ p.1 x)
    (hφ.comp (measurable_fst.fst.prodMk measurable_snd))

lemma Phi_bound {φ : ℝ → ℝ → ℝ} {C : ℝ} (hC : ∀ s T, |φ s T| ≤ C) (s T : ℝ) :
    |Phi φ s T| ≤ C * |T - s| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := T) (f := φ s)
    (C := C) fun x _ => by rw [Real.norm_eq_abs]; exact hC s x
  simpa [Phi, Real.norm_eq_abs] using this

/-- On `(a, b]`, pointwise equality suffices. -/
lemma congr_Ioc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Ioc a b, f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_fun measurableSet_Ioc h

/-- A measurable function bounded on `[a, b]` is integrable there. -/
lemma ii_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b M : ℝ} (hab : a ≤ b)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable (M := M) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]; exact hM x (Ioc_subset_Icc_self hx)

/-! ### The drift and the bracket -/

section
variable {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {C : ℝ} (hC : ∀ s T, |φ s T| ≤ C)
  {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ s, |g s| ≤ B)
include hφ hC hg hB

omit hC hB in
/-- The kernel `k(u, s) = σ(s)² φ(s, u) Φ(s, u)`. -/
lemma k_meas : Measurable (Function.uncurry fun u s => g s * φ s u * Phi φ s u) :=
  ((hg.comp measurable_snd).mul (hφ.comp measurable_swap)).mul ((Phi_meas hφ).comp measurable_swap)

omit hφ hg in
lemma k_bound {S : ℝ} : ∀ u ∈ Icc 0 S, ∀ s ∈ Icc 0 S,
    |g s * φ s u * Phi φ s u| ≤ B * C * (C * S) := fun u hu s hs => by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [abs_mul, abs_mul]
  have h3 : |Phi φ s u| ≤ C * S := (Phi_bound hC s u).trans
    (mul_le_mul_of_nonneg_left (abs_sub_le_iff.2 ⟨by linarith [hu.2, hs.1], by linarith [hu.1, hs.2]⟩) hC0)
  exact mul_le_mul (mul_le_mul (hB s) (hC s u) (abs_nonneg _) hB0) h3 (abs_nonneg _)
    (mul_nonneg hB0 hC0)

omit hg hB in
/-- `∫_m^b σ(s)² φ(s, u) Φ(s, u) du = σ(s)² (Φ(s, b)² − Φ(s, m)²)/2`. -/
lemma inner_sq (s m b : ℝ) :
    ∫ u in m..b, g s * φ s u * Phi φ s u = g s * ((Phi φ s b ^ 2 - Phi φ s m ^ 2) / 2) := by
  have h := squareS (φ s) (hφ.comp (measurable_const.prodMk measurable_id)) ⟨C, hC s⟩ s m b
  simp only [mul_assoc, intervalIntegral.integral_const_mul, Phi]
  rw [h]

lemma driftS_aux {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, ∫ s in (0:ℝ)..u, g s * φ s u * Phi φ s u =
      ∫ s in (0:ℝ)..b, g s * dtil φ a b s := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  set k0 : ℝ → ℝ → ℝ := fun u s => g s * φ s u * Phi φ s u
  have hk0 := k_meas hφ hg
  have hk : Measurable (Function.uncurry fun u s => (if a < u then (1:ℝ) else 0) * k0 u s) :=
    (measurable_const.ite (measurableSet_lt measurable_const measurable_fst) measurable_const).mul hk0
  have h := tri hb (k := fun u s => (if a < u then (1:ℝ) else 0) * k0 u s) hk
    (M := B * C * (C * b)) fun u hu s hs => by
      have hbd := k_bound hC hB u hu s hs
      have h0 : 0 ≤ B * C * (C * b) := le_trans (abs_nonneg _) hbd
      by_cases hau : a < u
      · simpa [hau, k0] using hbd
      · simpa [hau] using h0
  -- the outer integral
  have hG : Measurable fun u => ∫ s in (0:ℝ)..u, k0 u s :=
    meas_param measurable_const measurable_id (K := k0) hk0
  have hGb : ∀ u ∈ Icc 0 b, |∫ s in (0:ℝ)..u, k0 u s| ≤ B * C * (C * b) * b := fun u hu => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u) (f := k0 u)
      (C := B * C * (C * b)) fun s hs => by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hu.1] at hs
        exact k_bound hC hB u hu s ⟨hs.1.le, hs.2.trans hu.2⟩
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hu.1] at this
    exact this.trans (mul_le_mul_of_nonneg_left hu.2 ((abs_nonneg _).trans
      (k_bound hC hB 0 ⟨le_rfl, hb⟩ 0 ⟨le_rfl, hb⟩)))
  have lhs : ∫ u in (0:ℝ)..b, ∫ s in (0:ℝ)..u, (if a < u then (1:ℝ) else 0) * k0 u s =
      ∫ u in a..b, ∫ s in (0:ℝ)..u, k0 u s := by
    simp only [intervalIntegral.integral_const_mul]
    have i0 : IntervalIntegrable (fun u => (if a < u then (1:ℝ) else 0) * ∫ s in (0:ℝ)..u, k0 u s)
        volume 0 b := by
      refine ii_of_bound ((measurable_const.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const).mul hG) hb (M := B * C * (C * b) * b) fun u hu => ?_
      simp only [Pi.mul_apply, id]
      split_ifs
      · rw [one_mul]; exact hGb u hu
      · rw [zero_mul, abs_zero]; exact (abs_nonneg _).trans (hGb u hu)
    rw [← intervalIntegral.integral_add_adjacent_intervals (i0.mono_set (by
        rw [uIcc_of_le ha, uIcc_of_le hb]; exact Icc_subset_Icc le_rfl hab))
      (i0.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hb]; exact Icc_subset_Icc ha le_rfl)),
      congr_Ioc ha (g := fun _ => 0) fun u hu => by simp [not_lt.2 hu.2],
      congr_Ioc hab (g := fun u => ∫ s in (0:ℝ)..u, k0 u s) fun u hu => by simp [hu.1]]
    simp
  have rhs : ∀ s ∈ uIcc 0 b, ∫ u in s..b, (if a < u then (1:ℝ) else 0) * k0 u s =
      g s * dtil φ a b s := fun s hs => by
    rw [uIcc_of_le hb] at hs
    have hm1 : s ≤ max a s := le_max_right _ _
    have hm2 : max a s ≤ b := max_le hab hs.2
    have hcont : Continuous fun u => Phi φ s u :=
      prim_cont (hφ.comp (measurable_const.prodMk measurable_id)) (hC s) s
    have iu : ∀ x y, IntervalIntegrable (fun u => (if a < u then (1:ℝ) else 0) * k0 u s) volume x y :=
      fun x y => by
        have : (fun u => (if a < u then (1:ℝ) else 0) * k0 u s) =
            fun u => ((if a < u then (1:ℝ) else 0) * (g s * φ s u)) * Phi φ s u := by
          funext u; simp only [k0]; ring
        rw [this]
        refine (Novel.SpliceCrossTermDriftProof.ii_bdd ((measurable_const.ite
          (measurableSet_lt measurable_const measurable_id) measurable_const).mul
          (measurable_const.mul (hφ.comp (measurable_const.prodMk measurable_id)))) (|B| * C)
          (fun u => ?_) x y).mul_continuousOn hcont.continuousOn
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
        simp only [Pi.mul_apply, id, Function.comp, Function.uncurry]
        split_ifs
        · rw [one_mul, abs_mul]
          exact mul_le_mul ((hB s).trans (le_abs_self B)) (hC s u) (abs_nonneg _) (abs_nonneg _)
        · simp; positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (iu s (max a s)) (iu (max a s) b),
      congr_Ioc hm1 (g := fun _ => 0) fun u hu => by
        have : ¬ a < u := fun h => by
          rcases le_total a s with has | hsa
          · rw [max_eq_right has] at hu; exact absurd (hu.1.trans_le hu.2) (lt_irrefl _)
          · rw [max_eq_left hsa] at hu; linarith [hu.2]
        simp [this],
      congr_Ioc hm2 (g := fun u => k0 u s) fun u hu => by
        simp [(le_max_left a s).trans_lt hu.1],
      intervalIntegral.integral_zero, zero_add]
    exact inner_sq hφ hC s (max a s) b
  rw [← lhs, h, intervalIntegral.integral_congr rhs]
end

lemma driftS : driftStatement := by
  intro φ hφ ⟨C, hC⟩ g hg ⟨B, hB⟩ a b ha hab
  exact driftS_aux hφ hC hg hB ha hab

section
variable {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {C : ℝ} (hC : ∀ s T, |φ s T| ≤ C)
  {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ s, |g s| ≤ B)
include hφ hC hg hB

lemma bracketS_aux {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ u in (0:ℝ)..t, ∫ s in (0:ℝ)..u, g s * φ s u * Phi φ s u) +
      (∫ x in t..T, ∫ s in (0:ℝ)..t, g s * φ s x * Phi φ s x) =
      ∫ s in (0:ℝ)..t, g s * Phi φ s T ^ 2 / 2 := by
  classical
  have hT : 0 ≤ T := ht.trans htT
  set k0 : ℝ → ℝ → ℝ := fun u s => g s * φ s u * Phi φ s u
  have hk0 := k_meas hφ hg
  set M := B * C * (C * T)
  have hbd := k_bound (S := T) hC hB
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hbd 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩)
  set kk : ℝ → ℝ → ℝ := fun u s => (if s ≤ t then (1:ℝ) else 0) * k0 u s
  have hkk : Measurable (Function.uncurry kk) :=
    (measurable_const.ite (measurableSet_le measurable_snd measurable_const) measurable_const).mul hk0
  have hkkb : ∀ u ∈ Icc 0 T, ∀ s ∈ Icc 0 T, |kk u s| ≤ M := fun u hu s hs => by
    by_cases hst : s ≤ t
    · simp only [kk, hst, ite_true, one_mul]; exact hbd u hu s hs
    · simp only [kk, hst, ite_false, zero_mul, abs_zero]; exact hM0
  have h := tri hT hkk hkkb
  have hks : ∀ u, Measurable fun s => kk u s := fun u =>
    hkk.comp (measurable_const.prodMk measurable_id)
  have iin : ∀ u ∈ Icc 0 T, ∀ x y, 0 ≤ x → x ≤ y → y ≤ T →
      IntervalIntegrable (fun s => kk u s) volume x y := fun u hu x y hx hxy hy =>
    ii_of_bound (hks u) hxy (M := M) fun s hs => hkkb u hu s ⟨hx.trans hs.1, hs.2.trans hy⟩
  have hin1 : ∀ u ∈ Ioc 0 t, ∫ s in (0:ℝ)..u, kk u s = ∫ s in (0:ℝ)..u, k0 u s := fun u hu =>
    congr_Ioc hu.1.le fun s hs => by simp [kk, hs.2.trans hu.2]
  have hin2 : ∀ u ∈ Ioc t T, ∫ s in (0:ℝ)..u, kk u s = ∫ s in (0:ℝ)..t, k0 u s := fun u hu => by
    have hu' : u ∈ Icc 0 T := ⟨ht.trans hu.1.le, hu.2⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (iin u hu' 0 t le_rfl ht htT)
        (iin u hu' t u ht hu.1.le hu.2),
      congr_Ioc ht (g := fun s => k0 u s) fun s hs => by simp [kk, hs.2],
      congr_Ioc hu.1.le (g := fun _ => 0) fun s hs => by simp [kk, not_le.2 hs.1]]
    simp
  -- the outer integral on the left
  have hU : Measurable fun u => ∫ s in (0:ℝ)..u, kk u s :=
    meas_param measurable_const measurable_id (K := kk) hkk
  have iU : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T →
      IntervalIntegrable (fun u => ∫ s in (0:ℝ)..u, kk u s) volume x y := fun x y hx hxy hy =>
    ii_of_bound hU hxy (M := M * T) fun u hu => by
      have hu' : u ∈ Icc 0 T := ⟨hx.trans hu.1, hu.2.trans hy⟩
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u)
        (f := fun s => kk u s) (C := M) fun s hs => by
          rw [Real.norm_eq_abs]
          rw [uIoc_of_le hu'.1] at hs
          exact hkkb u hu' s ⟨hs.1.le, hs.2.trans hu'.2⟩
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hu'.1] at this
      exact this.trans (mul_le_mul_of_nonneg_left hu'.2 hM0)
  have lhs : ∫ u in (0:ℝ)..T, ∫ s in (0:ℝ)..u, kk u s =
      (∫ u in (0:ℝ)..t, ∫ s in (0:ℝ)..u, k0 u s) + ∫ x in t..T, ∫ s in (0:ℝ)..t, k0 x s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (iU 0 t le_rfl ht htT)
      (iU t T ht htT le_rfl), congr_Ioc ht hin1, congr_Ioc htT hin2]
  -- the outer integral on the right
  have hw : Measurable fun s => g s * Phi φ s T ^ 2 / 2 :=
    ((hg.mul (((Phi_meas hφ).comp (measurable_id.prodMk measurable_const)).pow_const 2)).div_const 2)
  have rhs_in : ∀ s, ∫ u in s..T, kk u s = (if s ≤ t then (1:ℝ) else 0) * (g s * Phi φ s T ^ 2 / 2) :=
    fun s => by
      simp only [kk, intervalIntegral.integral_const_mul]
      rw [inner_sq hφ hC s s T]
      simp only [Phi, intervalIntegral.integral_same]
      ring
  have iw : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T →
      IntervalIntegrable (fun s => (if s ≤ t then (1:ℝ) else 0) * (g s * Phi φ s T ^ 2 / 2)) volume x y :=
    fun x y hx hxy hy =>
      ii_of_bound ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).mul hw) hxy (M := B * (C * T) ^ 2 / 2 + |B * (C * T) ^ 2 / 2|)
        fun s hs => by
          have hs' : s ∈ Icc 0 T := ⟨hx.trans hs.1, hs.2.trans hy⟩
          have hP : |Phi φ s T| ≤ C * T := (Phi_bound hC s T).trans (mul_le_mul_of_nonneg_left
            (by rw [abs_of_nonneg (by linarith [hs'.2])]; linarith [hs'.1])
            ((abs_nonneg _).trans (hC 0 0)))
          have hP2 : Phi φ s T ^ 2 ≤ (C * T) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hP 2
          have hgs : |g s| ≤ B := hB s
          simp only [Pi.mul_apply, id]
          split_ifs
          · rw [one_mul, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (Phi φ s T)), abs_two]
            have : |g s| * Phi φ s T ^ 2 ≤ B * (C * T) ^ 2 :=
              mul_le_mul hgs hP2 (sq_nonneg _) ((abs_nonneg _).trans hgs)
            linarith [abs_nonneg (B * (C * T) ^ 2 / 2)]
          · simp only [zero_mul, abs_zero]
            linarith [neg_abs_le (B * (C * T) ^ 2 / 2)]
  have rhs : ∫ s in (0:ℝ)..T, ∫ u in s..T, kk u s = ∫ s in (0:ℝ)..t, g s * Phi φ s T ^ 2 / 2 := by
    simp only [rhs_in]
    rw [← intervalIntegral.integral_add_adjacent_intervals (iw 0 t le_rfl ht htT)
      (iw t T ht htT le_rfl), congr_Ioc ht (g := fun s => g s * Phi φ s T ^ 2 / 2)
        fun s hs => by simp [hs.2],
      congr_Ioc htT (g := fun _ => 0) fun s hs => by simp [not_le.2 hs.1]]
    simp
  rw [← lhs, h, rhs]
end

lemma bracketS : bracketStatement := by
  intro φ hφ ⟨C, hC⟩ g hg ⟨B, hB⟩ t T ht htT
  exact bracketS_aux hφ hC hg hB ht htT

theorem maturityShapeIdentities : Standalone.MaturityShapeIdentities.statement :=
  ⟨squareS, a21S, driftS, bracketS⟩

end Novel.MaturityShapeIdentitiesProof

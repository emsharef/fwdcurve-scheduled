import Standalone.DiffusionMeetingIdentities
import Novel.SpliceCrossTermDriftProof
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Set

namespace Novel.DiffusionMeetingIdentitiesProof

/-- Fubini on the triangle `0 < s ≤ x ≤ S`. -/
lemma tri {S : ℝ} (hS : 0 ≤ S) {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ s, |g s| ≤ B)
    {h : ℝ → ℝ → ℝ} (hh : Continuous (Function.uncurry h)) :
    ∫ x in (0:ℝ)..S, (∫ s in (0:ℝ)..x, g s * h x s) =
      ∫ s in (0:ℝ)..S, g s * ∫ x in s..S, h x s := by
  classical
  set F : ℝ → ℝ → ℝ := fun x s => if s ≤ x then g s * h x s else 0
  set A := Ioc (0:ℝ) S
  -- the inner integrals as integrals over `A`
  have hA : ∀ x ∈ A, ∫ s in (0:ℝ)..x, g s * h x s = ∫ s in A, F x s := fun x hx => by
    rw [intervalIntegral.integral_of_le hx.1.le]
    have : (fun s => F x s) = (Iic x).indicator fun s => g s * h x s := by
      funext s; simp [F, indicator, mem_Iic]
    have e : A ∩ Iic x = Ioc 0 x := by
      ext s; simp only [A, mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hx.2⟩, h2⟩
    rw [this, setIntegral_indicator measurableSet_Iic, e]
  have hB : ∀ s ∈ A, g s * ∫ x in s..S, h x s = ∫ x in A, F x s := fun s hs => by
    rw [intervalIntegral.integral_of_le hs.2, ← integral_const_mul]
    have : (fun x => F x s) = (Ici s).indicator fun x => g s * h x s := by
      funext x; simp [F, indicator, mem_Ici]
    rw [this, setIntegral_indicator measurableSet_Ici]
    have e : A ∩ Ici s = Icc s S := by
      ext x; simp only [A, mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans_le h1, h2⟩, h1⟩
    rw [e, integral_Icc_eq_integral_Ioc]
  -- integrability of `F` on `A × A`
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0:ℝ) S ×ˢ Icc (0:ℝ) S) hh.continuousOn
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((hg.comp measurable_snd).mul hh.measurable) measurable_const
  have : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hae : ∀ᵐ p ∂((volume.restrict A).prod (volume.restrict A)), p ∈ A ×ˢ A := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hFi : Integrable (Function.uncurry F) ((volume.restrict A).prod (volume.restrict A)) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (|B| * |M|) (hae.mono fun p hp => ?_)
    have hp' : p ∈ Icc (0:ℝ) S ×ˢ Icc (0:ℝ) S :=
      ⟨Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩
    simp only [Function.uncurry, F]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul]
      have := hM (p.1, p.2) hp'
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul ((hgB _).trans (le_abs_self B)) (this.trans (le_abs_self M)) (abs_nonneg _)
        (abs_nonneg B)
    · simp only [norm_zero]; positivity
  rw [intervalIntegral.integral_of_le hS, intervalIntegral.integral_of_le hS,
    setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_congr_fun measurableSet_Ioc hB]
  exact integral_integral_swap hFi

open Standalone.DiffusionMeetingIdentities

section
variable {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ s, |g s| ≤ B)
include hg hB

lemma ii (φ : ℝ → ℝ) (hφ : Continuous φ) (a b : ℝ) :
    IntervalIntegrable (fun v => g v * φ v) volume a b :=
  (Novel.SpliceCrossTermDriftProof.ii_bdd hg B hB a b).mul_continuousOn hφ.continuousOn

/-- `∫_0^t ∫_0^s g(v) h(s − v) dv ds` for `h(y) = y`: `∫_0^t g(v)(t − v)²/2 dv`. -/
lemma tri_lin {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, ∫ v in (0:ℝ)..s, g v * (s - v) = ∫ v in (0:ℝ)..t, g v * ((t - v) ^ 2 / 2) := by
  rw [tri ht hg hB (h := fun x s => x - s) (by fun_prop)]
  refine intervalIntegral.integral_congr fun v _ => ?_
  congr 1
  rw [intervalIntegral.integral_comp_sub_right (fun x => x) v, sub_self, integral_id]
  ring

end

lemma bracketS : Standalone.DiffusionMeetingIdentities.bracketStatement := by
  rintro g hg ⟨B, hB⟩ t T ht htT
  set G := ∫ v in (0:ℝ)..t, g v
  set H := ∫ v in (0:ℝ)..t, g v * v
  have hG := ii hg hB (fun _ => 1) continuous_const 0 t
  have hH := ii hg hB id continuous_id 0 t
  simp only [mul_one, id] at hG hH
  have rect : ∀ u, ∫ v in (0:ℝ)..t, g v * (u - v) = u * G - H := fun u => by
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub (hG.mul_const u) hH, intervalIntegral.integral_mul_const]
    ring
  simp only [rect]
  rw [intervalIntegral.integral_sub (f := fun u => u * G) (g := fun _ => H)
    ((continuous_id.mul continuous_const).intervalIntegrable t T)
    intervalIntegrable_const,
    intervalIntegral.integral_mul_const, integral_id, intervalIntegral.integral_const, smul_eq_mul,
    tri_lin hg hB ht]
  have e : ∀ v, g v * (T - v) ^ 2 / 2 =
      ((T ^ 2 - t ^ 2) / 2) * g v - (T - t) * (g v * v) + g v * ((t - v) ^ 2 / 2) := fun v => by
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((hG.const_mul _).sub (hH.const_mul _))
      (ii hg hB _ (by fun_prop) 0 t),
    intervalIntegral.integral_sub (hG.const_mul _) (hH.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

lemma accumulatedS : Standalone.DiffusionMeetingIdentities.accumulatedStatement := by
  rintro g hg ⟨B, hB⟩ S hS
  have := tri hS hg hB (h := fun _ _ => 1) continuous_const
  simp only [mul_one] at this
  rw [this]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp

lemma driftS : Standalone.DiffusionMeetingIdentities.driftStatement := by
  rintro g hg ⟨B, hB⟩ a b ha hab
  have hb : 0 ≤ b := ha.trans hab
  -- `K(u) = ∫_0^u g(s)(u − s) ds` is continuous
  have hK : ∀ u, ∫ s in (0:ℝ)..u, g s * (u - s) =
      u * (∫ s in (0:ℝ)..u, g s) - ∫ s in (0:ℝ)..u, g s * s := fun u => by
    have h1 : IntervalIntegrable (fun s => g s * u) volume 0 u := ii hg hB (fun _ => u) continuous_const 0 u
    have h2 : IntervalIntegrable (fun s => g s * s) volume 0 u := ii hg hB id continuous_id 0 u
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_mul_const]
    ring
  have hcont : Continuous fun u => ∫ s in (0:ℝ)..u, g s * (u - s) := by
    simp only [hK]
    have h1 := intervalIntegral.continuous_primitive (fun a b => ii hg hB (fun _ => 1) continuous_const a b) 0
    have h2 := intervalIntegral.continuous_primitive (fun a b => ii hg hB id continuous_id a b) 0
    simp only [mul_one, id] at h1 h2
    exact (continuous_id.mul h1).sub h2
  rw [← intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 b)
    (hcont.intervalIntegrable 0 a), tri_lin hg hB hb, tri_lin hg hB ha]
  -- the right side on `[0, a]` and `[a, b]`
  have e1 : ∀ s ∈ Set.uIcc (0:ℝ) b, g s * dfun a b s =
      g s * ((b - s) ^ 2 / 2) - g s * (max (a - s) 0 ^ 2 / 2) := fun s hs => by
    rw [Set.uIcc_of_le hb] at hs
    rw [dfun, max_eq_left (by linarith [hs.2])]
    ring
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_sub
    (ii hg hB _ (by fun_prop) 0 b) (ii hg hB _ (by fun_prop) 0 b)]
  have e2 : ∫ s in (0:ℝ)..b, g s * (max (a - s) 0 ^ 2 / 2) =
      ∫ s in (0:ℝ)..a, g s * ((a - s) ^ 2 / 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (ii hg hB _ (by fun_prop) 0 a)
      (ii hg hB _ (by fun_prop) a b)]
    have z : ∫ s in a..b, g s * (max (a - s) 0 ^ 2 / 2) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun s hs => by
        rw [Set.uIcc_of_le hab] at hs
        rw [max_eq_right (by linarith [hs.1])]
        ring]
      simp
    rw [z, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ha] at hs
    rw [max_eq_left (by linarith [hs.2])]
  rw [e2]

theorem diffusionMeetingIdentities : Standalone.DiffusionMeetingIdentities.statement :=
  ⟨bracketS, driftS, accumulatedS⟩

end Novel.DiffusionMeetingIdentitiesProof

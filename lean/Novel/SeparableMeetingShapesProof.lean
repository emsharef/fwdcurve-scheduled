import Standalone.SeparableMeetingShapes
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped BigOperators
open Standalone.SeparableMeetingShapes
namespace Novel.SeparableMeetingShapesProof

lemma drift : driftStatement := by
  intro g t T hg
  let F := fun u => ∫ v in t..u, g v
  have hF : AbsolutelyContinuousOnInterval F t T :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have h := hF.integral_deriv_mul_eq_sub hF
  have he : (∫ u in t..T, deriv F u * F u + F u * deriv F u) =
      2 * (∫ u in t..T, g u * F u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with u hu huI
    have hd : deriv F u = g u := (hu (uIoc_subset_uIcc huI) t (by simp)).deriv
    rw [hd]; ring
  rw [he] at h
  have h0 : F t = 0 := by simp [F]
  rw [h0] at h
  dsimp [F] at h ⊢
  nlinarith

lemma hjm : hjmStatement := by
  intro d g chi t T hg
  have hF j : ContinuousOn (fun u => ∫ v in t..u, g j v) (uIcc t T) :=
    ((hg j).absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
  have hi j : IntervalIntegrable (fun u => g j u * (∫ v in t..u, g j v)) volume t T :=
    (hg j).mul_continuousOn (hF j)
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    simpa only [mul_assoc] using (hi j).const_mul (chi j ^ 2)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc (chi j ^ 2), intervalIntegral.integral_const_mul,
    drift (g j) t T (hg j)]
  ring

lemma primitive : primitiveStatement := by
  intro g phi a b T hg0 hg hshape
  have h := intervalIntegral.integral_add_adjacent_intervals hg0 hg
  have hi : (∫ u in b..T, g u) = a * (∫ u in b..T, phi u) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hshape
  dsimp [G026]
  rw [← h, hi]

lemma shape : shapeStatement := by
  intro d n a B M A phi Phi f0
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [C026, V026, mul_add, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma coefficient : coefficientStatement := by
  intro n a B J q G t hq hqG
  have hi k : IntervalIntegrable (fun s => a k * q k s * (B k - G k s)) volume 0 t := by
    have h := ((hq k).mul_const (B k)).sub (hqG k)
    convert h.const_mul (a k) using 1
    ext s
    ring
  constructor
  · rw [intervalIntegral.integral_finsetSum (fun k _ => hi k), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [M026, A026]
    have he : (fun s => a k * q k s * (B k - G k s)) =
        (fun s => a k * (q k s * B k - q k s * G k s)) := by funext s; ring
    rw [he, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((hq k).mul_const _) (hqG k),
      intervalIntegral.integral_mul_const]
    ring
  · rw [intervalIntegral.integral_finsetSum (fun k _ => (hq k).const_mul (a k ^ 2))]
    simp only [V026, A026, intervalIntegral.integral_const_mul]

lemma variance : varianceStatement := by
  intro n a q H hH hq hpos
  dsimp only
  let v := fun s => ∑ k, a k ^ 2 * q k s
  let V := fun t => V026 a (fun k => A026 (q k) t)
  have hv : IntervalIntegrable v volume 0 H := by
    convert IntervalIntegrable.sum Finset.univ (fun k _ => (hq k).const_mul (a k ^ 2)) using 1
    ext s
    simp [v, Finset.sum_apply]
  have hvpos s : 0 ≤ v s := Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hpos k s))
  have he t (ht : t ∈ Icc 0 H) : V t = ∫ s in (0:ℝ)..t, v s := by
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      ((hq k).mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hH]; exact Icc_subset_Icc le_rfl ht.2)).const_mul (a k ^ 2))]
    simp only [V, V026, A026, intervalIntegral.integral_const_mul]
  have hac := hv.absolutelyContinuousOnInterval_intervalIntegral (by simp : (0:ℝ) ∈ uIcc 0 H)
  have hVac : AbsolutelyContinuousOnInterval V 0 H := by
    apply hac.congr
    intro t ht
    exact (he t (by simpa [uIcc_of_le hH] using ht)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [V026, A026]
  · intro t ht
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _)
      (intervalIntegral.integral_nonneg_of_forall ht (hpos k)))
  · intro x hx y hy hxy
    change V x ≤ V y
    rw [he x hx, he y hy]
    have hxint := hv.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hH]; exact Icc_subset_Icc le_rfl hx.2)
    have hxyint := hv.mono_set (by rw [uIcc_of_le hxy, uIcc_of_le hH]; exact Icc_subset_Icc hx.1 hy.2)
    have had := intervalIntegral.integral_add_adjacent_intervals hxint hxyint
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hxy hvpos
    linarith
  · simpa [uIcc_of_le hH] using hVac.continuousOn
  · simpa [uIcc_of_le hH] using hVac.boundedVariationOn
  · -- Derive each accumulated integral before taking the finite sum; no
    -- pointwise continuity of the predictable scale is assumed.
    have hd : ∀ᵐ t ∂volume, ∀ k, t ∈ uIcc 0 H →
        HasDerivAt (A026 (q k)) (q k t) t := by
      rw [ae_all_iff]
      intro k
      filter_upwards [(hq k).ae_hasDerivAt_integral] with t ht htI
      exact ht htI 0 (by simp)
    filter_upwards [hd] with t ht htI
    convert HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      (ht k (by simpa [uIcc_of_le hH] using htI)).const_mul (a k ^ 2)) using 1
    ext s
    simp [V026, Finset.sum_apply]

lemma step : stepStatement := by
  intro d C V level slope b T
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem separableMeetingShapes : Standalone.SeparableMeetingShapes.statement :=
  ⟨drift, hjm, primitive, shape, coefficient, variance, step⟩

end Novel.SeparableMeetingShapesProof

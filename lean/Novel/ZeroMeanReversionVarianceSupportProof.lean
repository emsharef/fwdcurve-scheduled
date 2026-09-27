import Standalone.ZeroMeanReversionVarianceSupport
import Novel.StochasticMeetingVarianceProof
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory ProbabilityTheory Matrix Set Filter MeasurableSpace
open scoped Topology
open Standalone.ZeroMeanReversionVarianceSupport
namespace Novel.ZeroMeanReversionVarianceSupportProof

variable {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)

lemma closed_cone (hA : ∀ i j, 0 ≤ A i j) : IsClosed (cone0154 A 0) := by
  apply IsSeqClosed.isClosed
  intro y z hy hz
  choose x hx hxy using hy
  have hxy' (n) : y n = A.mulVec (x n) := by simpa using hxy n
  let a : Fin d → ℝ := fun j => ∑ i, A i j
  have ha (j) : 0 ≤ a j := Finset.sum_nonneg fun i _ => hA i j
  have haz (j) (hj : a j = 0) (i) : A i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hA i j)).1 hj i (Finset.mem_univ _)
  have hsum (n) : ∑ i, y n i = ∑ j, a j * x n j := by
    simp_rw [hxy' n, mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [a, Finset.sum_mul]
  obtain ⟨B, hB⟩ := (show Tendsto (fun n => ∑ i, y n i) atTop (𝓝 (∑ i, z i)) from
    (continuous_finsetSum _ (fun i _ => continuous_apply i)).tendsto z |>.comp hz).bddAbove_range
  have hbound (n j) : a j * x n j ≤ B := by
    calc
      a j * x n j ≤ ∑ k, a k * x n k :=
        Finset.single_le_sum (fun k _ => mul_nonneg (ha k) (hx n k)) (Finset.mem_univ _)
      _ = ∑ i, y n i := (hsum n).symm
      _ ≤ B := hB (mem_range_self n)
  let x' : ℕ → Fin d → ℝ := fun n j => if a j = 0 then 0 else x n j
  let U : Fin d → ℝ := fun j => max 0 (B / a j)
  have hx' (n) : x' n ∈ Icc 0 U := by
    constructor
    · intro j; dsimp [x']; split_ifs <;> simp_all
    · intro j
      dsimp [x', U]
      split_ifs with hj
      · exact le_max_left _ _
      · exact (le_div_iff₀ (lt_of_le_of_ne (ha j) (Ne.symm hj))).2
          (by simpa [mul_comm] using hbound n j) |>.trans (le_max_right _ _)
  obtain ⟨v, hv, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx'
  have hsame (n) : A.mulVec (x' n) = y n := by
    rw [hxy' n]
    ext i
    change (∑ j, A i j * x' n j) = ∑ j, A i j * x n j
    apply Finset.sum_congr rfl
    intro j _
    dsimp [x']
    split_ifs with hj
    · simp [haz j hj i]
    · rfl
  have hc : Continuous A.mulVec := A.mulVecLin.continuous_of_finiteDimensional
  have heq : A.mulVec v = z := tendsto_nhds_unique
    (hc.tendsto v |>.comp hlim) (by simpa only [Function.comp_def, hsame] using hz.comp hφ.tendsto_atTop)
  exact ⟨v, hv.1, by simpa using heq.symm⟩

lemma closed_translate (b : Fin m → ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    IsClosed (cone0154 A b) := by
  have heq : cone0154 A b = (fun y => y - b) ⁻¹' cone0154 A 0 := by
    ext y
    simp only [cone0154, mem_ofPred_eq, mem_preimage, zero_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, add_sub_cancel_left _ _⟩
    · rintro ⟨x, hx, heq⟩; exact ⟨x, hx, by rw [← heq]; abel⟩
  rw [heq]
  exact (closed_cone A hA).preimage (by fun_prop)


lemma support_image (b : Fin m → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (μ : Measure (Fin d → ℝ)) (hμ : μ.support = {x | ∀ j, 0 ≤ x j}) :
    (μ.map (fun x => b + A.mulVec x)).support = cone0154 A b := by
  let f : (Fin d → ℝ) → (Fin m → ℝ) := fun x => b + A.mulVec x
  have hf : Continuous f := continuous_const.add A.mulVecLin.continuous_of_finiteDimensional
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed (closed_translate A b hA)
    apply (ae_map_iff hf.measurable.aemeasurable (closed_translate A b hA).measurableSet).2
    filter_upwards [μ.support_mem_ae] with x hx
    exact ⟨x, by simpa [hμ] using hx, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    apply (Measure.mem_support_iff_forall x).1 (by simpa [hμ] using hx)
    exact hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)

lemma dot_mulVec (w : Fin m → ℝ) (x : Fin d → ℝ) :
    dotProduct w (A.mulVec x) = dotProduct (A.transpose.mulVec w) x := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma affine_equalities (b : Fin m → ℝ) (μ : Measure (Fin m → ℝ))
    (hμ : μ.support = cone0154 A b) (w : Fin m → ℝ) :
    (∀ᵐ y ∂μ, dotProduct w (y - b) = 0) ↔ A.transpose.mulVec w = 0 := by
  constructor
  · intro hw
    have hc : IsClosed {y : Fin m → ℝ | dotProduct w (y - b) = 0} :=
      isClosed_eq (by unfold dotProduct; fun_prop) continuous_const
    have hs := Measure.support_subset_of_isClosed hc hw
    funext j
    have he := hs (show b + A.mulVec (Pi.single j 1) ∈ μ.support from by
      rw [hμ]
      exact ⟨Pi.single j 1, fun k => by by_cases hk : k = j <;> simp [hk], rfl⟩)
    change dotProduct w (b + A.mulVec (Pi.single j 1) - b) = 0 at he
    rw [add_sub_cancel_left, dot_mulVec] at he
    simpa using he
  · intro hw
    filter_upwards [μ.support_mem_ae] with y hy
    rw [hμ] at hy
    obtain ⟨x, _, rfl⟩ := hy
    simp [dot_mulVec, hw]

lemma zero_image (hA : ∀ i j, 0 ≤ A i j) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) :
    b + A.mulVec x = b ↔ ∀ j, (∃ i, A i j ≠ 0) → x j = 0 := by
  rw [add_eq_left]
  constructor
  · intro h j hj
    obtain ⟨i, hi⟩ := hj
    have he : ∑ k, A i k * x k = 0 := congrFun h i
    have hj0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hA i k) (hx k))).1
      he j (Finset.mem_univ _)
    exact (mul_eq_zero.1 hj0).resolve_left hi
  · intro h
    ext i
    change (∑ j, A i j * x j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : A i j = 0
    · simp [hij]
    · simp [h j ⟨i, hij⟩]

lemma quadratic_form (q : Fin d → ℝ) (w : Fin m → ℝ) :
    dotProduct w ((cov0157 A q).mulVec w) =
      ∑ j, q j * (A.transpose.mulVec w j) ^ 2 := by
  rw [cov0157, ← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec]
  simp only [mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma covariance_kernel (q : Fin d → ℝ) (hq : ∀ j, 0 < q j) :
    LinearMap.ker (cov0157 A q).mulVecLin = LinearMap.ker A.transpose.mulVecLin := by
  ext w
  simp only [LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro hw
    have hs : ∑ j, q j * (A.transpose.mulVec w j) ^ 2 = 0 := by
      rw [← quadratic_form, hw, dotProduct_zero]
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hq k).le (sq_nonneg _))).1 hs j (Finset.mem_univ _)
    exact (sq_eq_zero_iff).1 ((mul_eq_zero.1 hj).resolve_left (ne_of_gt (hq j)))
  · intro hw
    simp [cov0157, ← mulVec_mulVec, hw]

lemma covariance_rank (q : Fin d → ℝ) (hq : ∀ j, 0 < q j) :
    (cov0157 A q).rank = A.rank := by
  have h₁ := (cov0157 A q).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [covariance_kernel A q hq] at h₁
  change (cov0157 A q).rank + _ = _ at h₁
  change A.transpose.rank + _ = _ at h₂
  rw [rank_transpose] at h₂
  omega

lemma affine_hull_zero :
    (affineSpan ℝ (cone0154 A 0) : Set (Fin m → ℝ)) = LinearMap.range A.mulVecLin := by
  have hz : (0 : Fin m → ℝ) ∈ cone0154 A 0 := ⟨0, fun _ => le_rfl, by simp⟩
  rw [← insert_eq_of_mem hz, affineSpan_insert_zero]
  apply congrArg (fun S : Submodule ℝ (Fin m → ℝ) => (S : Set (Fin m → ℝ)))
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro y ⟨x, _, rfl⟩
    exact ⟨x, by simp⟩
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro y ⟨j, rfl⟩
    exact ⟨Pi.single j 1, fun k => by by_cases hk : k = j <;> simp [hk], by simp⟩

lemma affine_hull (b : Fin m → ℝ) :
    (affineSpan ℝ (cone0154 A b) : Set (Fin m → ℝ)) =
      (fun x => b + x) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) := by
  let f := (AffineEquiv.constVAdd ℝ (Fin m → ℝ) b).toAffineMap
  have himg : cone0154 A b = f '' cone0154 A 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A.mulVec x, ⟨x, hx, by simp⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [f]⟩
  rw [himg, ← AffineSubspace.map_span, AffineSubspace.coe_map, affine_hull_zero]
  rfl

lemma nullity : m - d ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin) := by
  have h := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := A.rank_le_width
  change A.transpose.rank + _ = _ at h
  rw [Module.finrank_pi, rank_transpose] at h
  simp only [Fintype.card_fin] at h hr
  omega

lemma product_support (μ : Fin d → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, (μ j).support = Ici 0) :
    (Measure.pi μ).support = {x | ∀ j, 0 ≤ x j} := by
  have hae : ∀ᵐ x ∂Measure.pi μ, ∀ j, 0 ≤ x j := by
    rw [ae_all_iff]
    intro j
    apply Measure.tendsto_eval_ae_ae.eventually
    have hj := (μ j).support_mem_ae
    rw [hμ j] at hj
    exact hj
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed _ hae
    have heq : {x : Fin d → ℝ | ∀ j, 0 ≤ x j} = Ici 0 := rfl
    rw [heq]
    exact isClosed_Ici
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.1 hU x hxU
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.2
    apply Finset.prod_ne_zero_iff.2
    intro j _
    apply ne_of_gt
    apply (Measure.mem_support_iff_forall (x j)).1 (by simpa [hμ j] using hx j)
    exact (hu j).1.mem_nhds (hu j).2

lemma product_atom (b : Fin m → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (μ : Fin d → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, (μ j).support = Ici 0) :
    ((Measure.pi μ).map (fun x => b + A.mulVec x)) {b} =
      ∏ j, if (∃ i, A i j ≠ 0) then μ j {0} else 1 := by
  classical
  let s : Fin d → Set ℝ := fun j => if (∃ i, A i j ≠ 0) then {0} else univ
  have hae : ∀ᵐ x ∂Measure.pi μ, ∀ j, 0 ≤ x j := by
    have h := (Measure.pi μ).support_mem_ae
    rw [product_support μ hμ] at h
    exact h
  have heq : (fun x => b + A.mulVec x) ⁻¹' {b} =ᵐ[Measure.pi μ] univ.pi s := by
    filter_upwards [hae] with x hx
    apply propext
    simp only [mem_preimage, mem_singleton_iff, Set.mem_pi, mem_univ, forall_const]
    rw [zero_image A hA b x hx]
    apply forall_congr'
    intro j
    by_cases hj : ∃ i, A i j ≠ 0 <;> simp [s, hj]
  have hf : Measurable (fun x => b + A.mulVec x) :=
    (continuous_const.add A.mulVecLin.continuous_of_finiteDimensional).measurable
  rw [Measure.map_apply hf (measurableSet_singleton _), measure_congr heq, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : ∃ i, A i j ≠ 0 <;> simp [s, hj]

lemma covariance_image {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : Fin m → ℝ) (X : Fin d → Ω → ℝ) (q : Fin d → ℝ)
    (hX : ∀ j, MemLp (X j) 2 μ) (hind : iIndepFun X μ) (hq : ∀ j, Var[X j; μ] = q j)
    (i k : Fin m) :
    cov[fun ω => b i + ∑ j, A i j * X j ω,
      fun ω => b k + ∑ j, A k j * X j ω; μ] = cov0157 A q i k := by
  have hsum (i : Fin m) : MemLp (fun ω => ∑ j, A i j * X j ω) 2 μ :=
    memLp_finsetSum _ (fun j _ => (hX j).const_mul (A i j))
  rw [covariance_const_add_left ((hsum i).integrable (by norm_num)),
    covariance_const_add_right ((hsum k).integrable (by norm_num)),
    covariance_fun_sum_fun_sum (fun j => (hX j).const_mul (A i j))
      (fun j => (hX j).const_mul (A k j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  have hcross (j l : Fin d) : cov[X j, X l; μ] = if j = l then q j else 0 := by
    by_cases hjl : j = l
    · subst l
      simp only [ite_true]
      exact (covariance_self (hX j).aestronglyMeasurable.aemeasurable).trans (hq j)
    · simp [hjl, (hind.indepFun hjl).covariance_eq_zero (hX j) (hX l)]
  simp_rw [hcross]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ j, A k j * (A i j * q j)) = ∑ j, (A * diagonal q) i j * A k j
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal]
  ring

lemma exponential_atom (b : Fin m → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (μ : Fin d → Measure ℝ) (r : Fin d → ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, (μ j).support = Ici 0)
    (hr : ∀ j, μ j {0} = ENNReal.ofReal (Real.exp (-r j))) :
    ((Measure.pi μ).map (fun x => b + A.mulVec x)) {b} =
      ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, A i j ≠ 0) then r j else 0))) := by
  classical
  rw [product_atom A b hA μ hμ, ← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : ∃ i, A i j ≠ 0 <;> simp [hj, hr]

section Laplace
open BoundedContinuousFunction

/-- The bounded exponential test function in (15.2). -/
noncomputable def e0152 (l : Fin d → NNReal) : (Fin d → NNReal) →ᵇ ℝ :=
  .ofNormedAddCommGroup (fun x => Real.exp (-(∑ j, (l j : ℝ) * x j)))
    (by fun_prop) 1 (by
      intro x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun j _ => by positivity)))

lemma e0152_zero : e0152 (0 : Fin d → NNReal) = 1 := by ext x; simp [e0152]
lemma e0152_mul (l η : Fin d → NNReal) : e0152 l * e0152 η = e0152 (l + η) := by
  ext x
  change Real.exp _ * Real.exp _ = Real.exp _
  rw [← Real.exp_add]
  congr 1
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_comm]

noncomputable def S0152 (d : ℕ) : StarSubalgebra ℝ ((Fin d → NNReal) →ᵇ ℝ) where
  carrier := Submodule.span ℝ (range (e0152 (d := d)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' r := by
    have h := (Submodule.span ℝ (range (e0152 (d := d)))).smul_mem r
      (Submodule.subset_span (mem_range_self (0 : Fin d → NNReal)))
    simpa [e0152_zero, Algebra.algebraMap_eq_smul_one] using h
  mul_mem' {f g} hf hg := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨l, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨η, rfl⟩ := hg
        rw [e0152_mul]
        exact Submodule.subset_span (mem_range_self _)
      | zero => simp
      | add f g hf hg ihf ihg => rw [mul_add]; exact Submodule.add_mem _ ihf ihg
      | smul r f hf ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
    | zero => simp
    | add f g hf hg ihf ihg => rw [add_mul]; exact Submodule.add_mem _ ihf ihg
    | smul r f hf ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih
  star_mem' {f} hf := by
    have he : star f = f := by ext x; simp [BoundedContinuousFunction.star_apply]
    rwa [he]

lemma laplace_unique_nnreal (μ ν : Measure (Fin d → NNReal))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ l : Fin d → NNReal,
      (∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂μ) =
      ∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (A := S0152 d)
  · intro x y hxy
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hxy
    refine ⟨(e0152 (Pi.single j 1)).toContinuousMap, ?_, ?_⟩
    · exact ⟨_, ⟨e0152 (Pi.single j 1), Submodule.subset_span (mem_range_self _), rfl⟩, rfl⟩
    · change Real.exp _ ≠ Real.exp _
      simpa [e0152, Pi.single_apply, apply_ite, Finset.sum_ite_eq'] using hj
  · intro f hf
    change f ∈ Submodule.span ℝ (range (e0152 (d := d))) at hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨l, rfl⟩ := hf; exact h l
    | zero => simp
    | add f g hf hg ihf ihg =>
      simp only [coe_add, Pi.add_apply, integral_add (f.integrable _) (g.integrable _),
        ihf, ihg]
    | smul r f hf ih => simp only [coe_smul, smul_eq_mul,
        integral_const_mul, ih]
lemma laplace_unique (μ ν : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, ∀ j, 0 ≤ x j) (hν : ∀ᵐ x ∂ν, ∀ j, 0 ≤ x j)
    (h : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ x, Real.exp (-(∑ j, l j * x j)) ∂μ) =
      ∫ x, Real.exp (-(∑ j, l j * x j)) ∂ν) : μ = ν := by
  let f : (Fin d → ℝ) → (Fin d → NNReal) := fun x j => (x j).toNNReal
  let g : (Fin d → NNReal) → (Fin d → ℝ) := fun x j => x j
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hi (l : Fin d → NNReal) (P : Measure (Fin d → ℝ))
      (hP : ∀ᵐ x ∂P, ∀ j, 0 ≤ x j) :
      (∫ x, e0152 l x ∂P.map f) = ∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂P := by
    rw [integral_map hf.aemeasurable (e0152 l).continuous.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hP] with x hx
    dsimp [e0152, f]
    simp only [max_eq_left (hx _)]
  have he : μ.map f = ν.map f := laplace_unique_nnreal _ _ (fun l => by
    change (∫ x, e0152 l x ∂μ.map f) = ∫ x, e0152 l x ∂ν.map f
    rw [hi l μ hμ, hi l ν hν]
    exact h (fun j => l j) (fun j => (l j).coe_nonneg))
  have hb (P : Measure (Fin d → ℝ)) (hP : ∀ᵐ x ∂P, ∀ j, 0 ≤ x j) :
      (P.map f).map g = P := by
    rw [Measure.map_map hg hf]
    calc
      P.map (g ∘ f) = P.map id := Measure.map_congr (by
        filter_upwards [hP] with x hx
        ext j
        exact Real.coe_toNNReal _ (hx j))
      _ = P := Measure.map_id
  rw [← hb μ hμ, he, hb ν hν]

lemma independence_of_laplace (μ : Measure (Fin d → NNReal)) [IsProbabilityMeasure μ]
    (v c : Fin d → ℝ)
    (h : ∀ l : Fin d → NNReal,
      (∫ x, Real.exp (-(∑ j, (l j : ℝ) * x j)) ∂μ) =
        Real.exp (-(∑ j, v j * l j / (1 + c j * l j)))) :
    iIndepFun (fun j (x : Fin d → NNReal) => x j) μ := by
  let μj : Fin d → Measure NNReal := fun j => μ.map (fun x => x j)
  have : ∀ j, IsProbabilityMeasure (μj j) := fun j =>
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply j).aemeasurable).2 inferInstance
  have hm (j : Fin d) (l : NNReal) :
      (∫ x, Real.exp (-(l : ℝ) * x) ∂μj j) = Real.exp (-(v j * l / (1 + c j * l))) := by
    rw [integral_map (measurable_pi_apply j).aemeasurable (by fun_prop)]
    have hs (x : Fin d → NNReal) :
        (∑ k, ((Pi.single j l : Fin d → NNReal) k : ℝ) * x k) = (l : ℝ) * x j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj; simp [Pi.single_eq_of_ne hkj]
      · simp
    have hv : (∑ k, v k * ((Pi.single j l : Fin d → NNReal) k : ℝ) /
        (1 + c k * ((Pi.single j l : Fin d → NNReal) k : ℝ))) = v j * l / (1 + c j * l) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj; simp [Pi.single_eq_of_ne hkj]
      · simp
    simpa only [hs, hv, neg_mul] using h (Pi.single j l)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_pi_apply j).aemeasurable)]
  change μ.map id = Measure.pi μj
  rw [Measure.map_id]
  apply laplace_unique_nnreal
  intro l
  rw [h]
  have he (x : Fin d → NNReal) : Real.exp (-(∑ j, (l j : ℝ) * x j)) =
      ∏ j, Real.exp (-(l j : ℝ) * x j) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [neg_mul]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun j (x : NNReal) => Real.exp (-(l j : ℝ) * x))]
  simp_rw [hm, ← Real.exp_sum, Finset.sum_neg_distrib]

lemma conditional_laplace_unique {Ω : Type*} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hG : G ≤ mΩ)
    (X : Ω → Fin d → NNReal) (hX : Measurable X)
    (κ : Kernel Ω (Fin d → NNReal)) [IsMarkovKernel κ]
    (h : ∀ l : Fin d → NNReal,
      μ[fun ω => Real.exp (-(∑ j, (l j : ℝ) * X ω j)) | G] =ᵐ[μ]
        fun ω => ∫ y, Real.exp (-(∑ j, (l j : ℝ) * y j)) ∂κ ω)
    (D : Set Ω) (hD : MeasurableSet[G] D) :
    (μ.restrict D).map X = κ ∘ₘ μ.restrict D := by
  apply laplace_unique_nnreal
  intro l
  change (∫ x, e0152 l x ∂(μ.restrict D).map X) = ∫ x, e0152 l x ∂κ ∘ₘ μ.restrict D
  rw [integral_map hX.aemeasurable (e0152 l).continuous.aestronglyMeasurable]
  have hi := (e0152 l).integrable (κ ∘ₘ μ.restrict D)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ ω in D, e0152 l (X ω) ∂μ) = ∫ ω in D, ∫ y, e0152 l y ∂κ ω ∂μ
  have hxi : Integrable (fun ω => e0152 l (X ω)) μ :=
    (e0152 l).integrable (μ.map X) |>.comp_measurable hX
  rw [← setIntegral_condExp hG hxi hD]
  exact integral_congr_ae (ae_restrict_of_ae (h l))

lemma poisson_power_integral (r : NNReal) (z : ℝ) :
    (∫ n, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1)) := by
  rw [integral_poissonMeasure]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).tsum_eq
  rw [← Real.exp_eq_exp_ℝ] at hs
  calc
    (∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) • z ^ n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ) * z) ^ n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      ext n
      simp only [smul_eq_mul, mul_pow]
      ring
    _ = Real.exp ((r : ℝ) * (z - 1)) := by rw [hs, ← Real.exp_add]; congr 1; ring

lemma poisson_transform (c x l : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (hl : 0 ≤ l) :
    (∫ n, ((1 + c * l)⁻¹) ^ n ∂poissonMeasure (x / c).toNNReal) =
      Real.exp (-x * l / (1 + c * l)) := by
  rw [poisson_power_integral, Real.coe_toNNReal _ (div_nonneg hx hc.le)]
  congr 1
  have hd : 1 + c * l ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end Laplace

lemma exponential_nonneg (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  change ∀ᵐ x ∂volume.withDensity (exponentialPDF r), 0 ≤ x
  rw [ae_iff]
  simp only [not_le]
  change (volume.withDensity (exponentialPDF r)) (Iio 0) = 0
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

lemma exponential_zero (r : ℝ) : expMeasure r {0} = 0 := by
  change (volume.withDensity (exponentialPDF r)) {0} = 0
  exact measure_singleton 0

lemma exponential_support (r : ℝ) (hr : 0 < r) : (expMeasure r).support = Ici 0 := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (exponential_nonneg r)
  · have h : Ioi (0 : ℝ) ⊆ (expMeasure r).support := by
      intro x hx
      rw [Measure.support_eq_forall_isOpen]
      intro U hxU hU
      change 0 < (volume.withDensity (exponentialPDF r)) U
      rw [withDensity_apply _ hU.measurableSet, setLIntegral_pos_iff (by
        unfold exponentialPDF; fun_prop)]
      have he : Function.support (exponentialPDF r) = Ici 0 := by
        ext y
        simp only [Function.mem_support, mem_Ici]
        by_cases hy : 0 ≤ y
        · simp [exponentialPDF_of_nonneg hy, hr, Real.exp_pos, hy]
        · simp [exponentialPDF_of_neg (lt_of_not_ge hy), hy]
      rw [he]
      have hp : 0 < volume (Ioi (0 : ℝ) ∩ U) :=
        (isOpen_Ioi.inter hU).measure_pos volume ⟨x, hx, hxU⟩
      exact hp.trans_le (measure_mono (inter_subset_inter_left _ Ioi_subset_Ici_self))
    have hh := closure_minimal h (expMeasure r).isClosed_support
    simpa only [closure_Ioi] using hh

lemma exponential_laplace (r l : ℝ) (hr : 0 < r) (hl : 0 ≤ l) :
    (∫ x, Real.exp (-l * x) ∂expMeasure r) = r / (r + l) := by
  change (∫ x, Real.exp (-l * x) ∂volume.withDensity (exponentialPDF r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r) (by unfold exponentialPDF; fun_prop)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have he (x : ℝ) : (exponentialPDF r x).toReal • Real.exp (-l * x) =
      (Ici 0).indicator (fun x => r * Real.exp (-(r + l) * x)) x := by
    by_cases hx : 0 ≤ x
    · simp only [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le),
        smul_eq_mul, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp [exponentialPDF_of_neg (lt_of_not_ge hx), indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos (add_pos_of_pos_of_nonneg hr hl))]
  simp only [mul_zero, Real.exp_zero, div_eq_mul_inv, inv_neg, neg_mul_neg, one_mul]

lemma sum_markov (c : ℝ) (hc : 0 < c) : IsMarkovKernel (S0153 c) := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  constructor
  intro n
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

lemma sum_nonneg (c : ℝ) (hc : 0 < c) (n : ℕ) : ∀ᵐ x ∂S0153 c n, 0 ≤ x := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  change ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map (fun x => ∑ j, x j), 0 ≤ x
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).2
  have h : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => expMeasure c⁻¹), ∀ j, 0 ≤ x j := by
    rw [ae_all_iff]
    intro j
    exact Measure.tendsto_eval_ae_ae.eventually (exponential_nonneg c⁻¹)
  filter_upwards [h] with x hx
  exact Finset.sum_nonneg fun j _ => hx j

lemma sum_laplace (c l : ℝ) (hc : 0 < c) (hl : 0 ≤ l) (n : ℕ) :
    (∫ x, Real.exp (-l * x) ∂S0153 c n) = ((1 + c * l)⁻¹) ^ n := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  change (∫ x, Real.exp (-l * x) ∂(Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map
    (fun x => ∑ j, x j)) = _
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ x => Real.exp (-l * x))]
  simp_rw [exponential_laplace _ l (inv_pos.2 hc) hl]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have hd : c⁻¹ + l ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (inv_pos.2 hc) hl)
  have he : 1 + c * l ≠ 0 := ne_of_gt (by positivity)
  field_simp

lemma sum_one (c : ℝ) (hc : 0 < c) : S0153 c 1 = expMeasure c⁻¹ := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  change (Measure.pi (fun _ : Fin 1 => expMeasure c⁻¹)).map (fun x => ∑ j, x j) = _
  simpa only [Fin.sum_univ_one] using
    (measurePreserving_eval (fun _ : Fin 1 => expMeasure c⁻¹) (0 : Fin 1)).map_eq

lemma sum_atom (c : ℝ) (hc : 0 < c) (n : ℕ) : S0153 c n {0} = (0 : ENNReal) ^ n := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  change ((Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map (fun x => ∑ j, x j)) {0} = _
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have h : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => expMeasure c⁻¹), ∀ j, 0 ≤ x j := by
    rw [ae_all_iff]
    intro j
    exact Measure.tendsto_eval_ae_ae.eventually (exponential_nonneg c⁻¹)
  have he : (fun x : Fin n → ℝ => ∑ j, x j) ⁻¹' {0} =ᵐ[Measure.pi (fun _ : Fin n => expMeasure c⁻¹)]
      univ.pi (fun _ => {0}) := by
    filter_upwards [h] with x hx
    simp only [mem_preimage, mem_singleton_iff, Set.mem_pi, mem_univ, forall_const]
    exact propext (by simpa using Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun j _ => hx j))
  rw [measure_congr he, Measure.pi_pi]
  simp [exponential_zero]

lemma poisson_sum_probability (c : ℝ) (hc : 0 < c) (r : NNReal) :
    IsProbabilityMeasure (P0153 c r) := by
  have := sum_markov c hc
  unfold P0153
  infer_instance

lemma poisson_sum_nonneg (c : ℝ) (hc : 0 < c) (r : NNReal) : ∀ᵐ x ∂P0153 c r, 0 ≤ x :=
  Measure.ae_comp_of_ae_ae measurableSet_Ici (ae_of_all _ (sum_nonneg c hc))

lemma poisson_sum_atom (c : ℝ) (hc : 0 < c) (r : NNReal) :
    P0153 c r {0} = ENNReal.ofReal (Real.exp (-(r : ℝ))) := by
  rw [P0153, Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton 0)]
  simp only [Measure.smul_apply, smul_eq_mul, sum_atom c hc]
  rw [tsum_eq_single 0]
  · simp [poissonMeasure_singleton]
  · intro n hn
    simp [zero_pow hn]

lemma poisson_sum_support (c : ℝ) (hc : 0 < c) (r : NNReal) (hr : 0 < r) :
    (P0153 c r).support = Ici 0 := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (poisson_sum_nonneg c hc r)
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    have hs : 0 < S0153 c 1 U := by
      apply (Measure.mem_support_iff_forall x).1 ?_ U (hU.mem_nhds hxU)
      rw [sum_one c hc, exponential_support _ (inv_pos.2 hc)]
      exact hx
    have hw : 0 < poissonMeasure r {1} := by
      rw [poissonMeasure_singleton, ENNReal.ofReal_pos]
      positivity
    have hle : poissonMeasure r {1} • S0153 c 1 ≤ P0153 c r := by
      rw [P0153, Measure.comp_eq_sum_of_countable]
      exact Measure.le_sum (fun n : ℕ => poissonMeasure r {n} • S0153 c n) 1
    have hp : 0 < poissonMeasure r {1} * S0153 c 1 U := by positivity
    exact hp.trans_le (hle U)

lemma poisson_sum_laplace (c : ℝ) (hc : 0 < c) (r : NNReal) (l : ℝ) (hl : 0 ≤ l) :
    (∫ x, Real.exp (-l * x) ∂P0153 c r) =
      Real.exp ((r : ℝ) * ((1 + c * l)⁻¹ - 1)) := by
  have := sum_markov c hc
  have := poisson_sum_probability c hc r
  have hi : Integrable (fun x => Real.exp (-l * x)) (P0153 c r) :=
    (integrable_const 1).mono' (by fun_prop) (by
      filter_upwards [poisson_sum_nonneg c hc r] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) hx))
  unfold P0153 at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ n, ∫ x, Real.exp (-l * x) ∂S0153 c n ∂poissonMeasure r) = _
  simp_rw [sum_laplace c l hc hl]
  exact poisson_power_integral r _

noncomputable def L01513 : Kernel NNReal ℕ where
  toFun := poissonMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
    simp only [poissonMeasure, Measure.sum_apply _ hB, Measure.smul_apply, smul_eq_mul]
    apply Measurable.tsum
    intro n
    fun_prop

noncomputable def K0153 (c : ℝ) : Kernel NNReal ℝ := S0153 c ∘ₖ L01513

lemma poisson_kernel_apply (c : ℝ) (r : NNReal) : K0153 c r = P0153 c r := rfl

lemma poisson_kernel_markov (c : ℝ) (hc : 0 < c) : IsMarkovKernel (K0153 c) :=
  ⟨poisson_sum_probability c hc⟩

lemma scalar_laplace_unique (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ l : ℝ, 0 ≤ l → (∫ x, Real.exp (-l * x) ∂μ) = ∫ x, Real.exp (-l * x) ∂ν) :
    μ = ν := by
  let f : ℝ → Fin 1 → ℝ := fun x _ => x
  have hf : Measurable f := by fun_prop
  have he : μ.map f = ν.map f := laplace_unique _ _
    ((ae_map_iff hf.aemeasurable (by exact isClosed_Ici.measurableSet)).2 (by simpa [f] using hμ))
    ((ae_map_iff hf.aemeasurable (by exact isClosed_Ici.measurableSet)).2 (by simpa [f] using hν))
    (fun l hl => by
      have hm : Continuous (fun x : Fin 1 → ℝ => Real.exp (-(∑ j, l j * x j))) := by fun_prop
      rw [integral_map hf.aemeasurable hm.aestronglyMeasurable,
        integral_map hf.aemeasurable hm.aestronglyMeasurable]
      simpa [f, Fin.sum_univ_one, neg_mul] using h (l 0) (hl 0))
  have hm (P : Measure ℝ) : (P.map f).map (fun x => x 0) = P := by
    rw [Measure.map_map (by fun_prop) hf]
    exact Measure.map_id
  rw [← hm μ, he, hm ν]

lemma poisson_sum_zero (c : ℝ) (hc : 0 < c) : P0153 c 0 = Measure.dirac 0 := by
  have := poisson_sum_probability c hc 0
  apply scalar_laplace_unique _ _ (poisson_sum_nonneg c hc 0) (by simp)
  intro l hl
  rw [poisson_sum_laplace c hc 0 l hl]
  simp

/-- The measurable scalar family, bundled as a probability kernel below. -/
noncomputable def κ01513 (c : ℝ) : Kernel NNReal ℝ where
  toFun := K01513 c
  measurable' := (K0153 c).measurable.comp (by fun_prop)

lemma transition_apply (c : ℝ) (x : NNReal) :
    K01513 c x = P0153 c ((x : ℝ) / c).toNNReal := rfl

lemma transition_markov (c : ℝ) (hc : 0 < c) : IsMarkovKernel (κ01513 c) :=
  ⟨fun _ => poisson_sum_probability c hc _⟩

lemma transition_laplace (c : ℝ) (hc : 0 < c) (x : NNReal) (l : ℝ) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-l * y) ∂K01513 c x) = Real.exp (-(x : ℝ) * l / (1 + c * l)) := by
  rw [transition_apply, poisson_sum_laplace c hc _ l hl,
    Real.coe_toNNReal _ (div_nonneg x.coe_nonneg hc.le)]
  congr 1
  have hd : 1 + c * l ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma transition_atom (c : ℝ) (hc : 0 < c) (x : NNReal) :
    K01513 c x {0} = ENNReal.ofReal (Real.exp (-(x : ℝ) / c)) := by
  rw [transition_apply, poisson_sum_atom c hc,
    Real.coe_toNNReal _ (div_nonneg x.coe_nonneg hc.le), neg_div]

lemma transition_zero (c : ℝ) (hc : 0 < c) : K01513 c 0 = Measure.dirac 0 := by
  simpa [transition_apply] using poisson_sum_zero c hc

lemma transition_support (c : ℝ) (hc : 0 < c) (x : NNReal) (hx : 0 < x) :
    (K01513 c x).support = Ici 0 := by
  rw [transition_apply]
  apply poisson_sum_support c hc
  exact Real.toNNReal_pos.2 (div_pos (by exact hx) hc)

lemma law_of_scalar_transform (c : ℝ) (hc : 0 < c) (x : NNReal) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    (h : ∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-l * y) ∂μ) =
      Real.exp (-(x : ℝ) * l / (1 + c * l))) : μ = K01513 c x := by
  have : IsProbabilityMeasure (K01513 c x) :=
    poisson_sum_probability c hc ((x : ℝ) / c).toNNReal
  exact scalar_laplace_unique μ _ hμ (poisson_sum_nonneg c hc _) (fun l hl =>
    (h l hl).trans (transition_laplace c hc x l hl).symm)

lemma conditional_scalar_law {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hG : G ≤ mΩ)
    (c : ℝ) (hc : 0 < c) (S : Ω → NNReal) (hS : Measurable[G] S)
    (X : Ω → ℝ) (hX : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (h : ∀ l : ℝ, 0 ≤ l → μ[fun ω => Real.exp (-l * X ω) | G] =ᵐ[μ]
      fun ω => Real.exp (-(S ω : ℝ) * l / (1 + c * l))) :
    (∀ B, MeasurableSet B → Measurable[G] (fun ω => K01513 c (S ω) B)) ∧
      ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
        (μ.restrict D).map X B = ∫⁻ ω in D, K01513 c (S ω) B ∂μ := by
  have := transition_markov c hc
  constructor
  · intro B hB
    exact (κ01513 c).measurable_coe hB |>.comp hS
  · intro D hD
    let κ : Kernel Ω ℝ := ⟨fun ω => K01513 c (S ω),
      (κ01513 c).measurable.comp (hS.mono hG le_rfl)⟩
    have : IsMarkovKernel κ := ⟨fun ω => poisson_sum_probability c hc _⟩
    have hkn (ω) : ∀ᵐ y ∂κ ω, 0 ≤ y := poisson_sum_nonneg c hc _
    have he : (μ.restrict D).map X = κ ∘ₘ μ.restrict D := by
      apply scalar_laplace_unique
      · exact (ae_map_iff hX.aemeasurable measurableSet_Ici).2 (ae_restrict_of_ae hXpos)
      · exact Measure.ae_comp_of_ae_ae measurableSet_Ici (ae_of_all _ hkn)
      · intro l hl
        have hi : Integrable (fun y => Real.exp (-l * y)) (κ ∘ₘ μ.restrict D) :=
          (integrable_const 1).mono' (by fun_prop) (by
            filter_upwards [Measure.ae_comp_of_ae_ae measurableSet_Ici (ae_of_all _ hkn)] with y hy
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) hy))
        have hxi : Integrable (fun ω => Real.exp (-l * X ω)) μ :=
          (integrable_const 1).mono' (by fun_prop) (by
            filter_upwards [hXpos] with ω hω
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) hω))
        rw [integral_map hX.aemeasurable (by fun_prop)]
        rw [Measure.comp_eq_comp_const_apply] at hi ⊢
        rw [Kernel.integral_comp hi]
        change (∫ ω in D, Real.exp (-l * X ω) ∂μ) =
          ∫ ω in D, ∫ y, Real.exp (-l * y) ∂K01513 c (S ω) ∂μ
        simp_rw [transition_laplace c hc _ l hl]
        rw [← setIntegral_condExp hG hxi hD]
        exact integral_congr_ae (ae_restrict_of_ae (h l hl))
    intro B hB
    rw [he, Measure.bind_apply hB κ.aemeasurable]
    rfl


lemma exponential_pow_density (r : ℝ) (hr : 0 < r) (k : ℕ) (x : ℝ) :
    (exponentialPDF r x).toReal • x ^ k =
      (Ici 0).indicator (fun x => r * (x ^ k * Real.exp (-r * x))) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le),
      indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    simp only [smul_eq_mul, neg_mul]
    ring
  · simp [exponentialPDF_of_neg (lt_of_not_ge hx),
      indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]

lemma exponential_pow_integrable (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (expMeasure r) := by
  change Integrable _ (volume.withDensity (exponentialPDF r))
  rw [integrable_withDensity_iff_integrable_smul' (f := exponentialPDF r) (by unfold exponentialPDF; fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [exponential_pow_density r hr k]
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  apply Integrable.const_mul
  simpa only [Real.rpow_natCast, Real.rpow_one, pow_one, IntegrableOn] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) zero_lt_one hr)

lemma exponential_pow_integral (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂expMeasure r) = k.factorial / r ^ k := by
  change (∫ x : ℝ, x ^ k ∂volume.withDensity (exponentialPDF r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r)
    (by unfold exponentialPDF; fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [exponential_pow_density r hr k]
  rw [integral_indicator measurableSet_Ici, integral_const_mul, integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  simp_rw [neg_mul]
  rw [h, Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast]
  rw [div_pow, one_pow, pow_succ]
  field_simp

lemma exponential_memLp_two (r : ℝ) (hr : 0 < r) : MemLp (fun x : ℝ => x) 2 (expMeasure r) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact exponential_pow_integrable r hr 2

lemma exponential_moments (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ, x ∂expMeasure c⁻¹) = c ∧ Var[fun x : ℝ => x; expMeasure c⁻¹] = c ^ 2 := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  have h1 := exponential_pow_integral c⁻¹ (inv_pos.2 hc) 1
  have h2 := exponential_pow_integral c⁻¹ (inv_pos.2 hc) 2
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_div, inv_inv] at h1
  constructor
  · exact h1
  · rw [variance_eq_sub (exponential_memLp_two c⁻¹ (inv_pos.2 hc)), h1]
    simp only [Pi.pow_apply]
    rw [h2]
    norm_num
    ring

lemma poisson_first_hasSum (r : NNReal) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * n) (r : ℝ) := by
  have he (n : ℕ) :
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) * (n + 1 : ℕ) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) * (n + 1 : ℕ)) r := by
    simpa only [he, mul_one] using hs
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero] using
    (hasSum_nat_add_iff (f := fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * n) 1).1 ht

lemma poisson_second_hasSum (r : NNReal) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * (n : ℝ) ^ 2)
      ((r : ℝ) ^ 2 + r) := by
  have he (n : ℕ) :
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) * ((n + 1 : ℕ) : ℝ) ^ 2 =
      (r : ℝ) * ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * n +
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hs := ((poisson_first_hasSum r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have ht : HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) * ((n + 1 : ℕ) : ℝ) ^ 2)
      ((r : ℝ) * (r + 1)) := by simpa only [he] using hs
  have hh := (hasSum_nat_add_iff (f := fun n : ℕ =>
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * (n : ℝ) ^ 2) 1).1 ht
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hh
  convert hh using 1
  ring

lemma poisson_moments (r : NNReal) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) ∧
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) ∧
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r ∧
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integrable_poissonMeasure_iff]
    simpa only [Real.norm_natCast] using (poisson_first_hasSum r).summable
  · rw [integrable_poissonMeasure_iff]
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)] using (poisson_second_hasSum r).summable
  · rw [integral_poissonMeasure]
    exact (poisson_first_hasSum r).tsum_eq
  · rw [integral_poissonMeasure]
    exact (poisson_second_hasSum r).tsum_eq

lemma sum_memLp_two (c : ℝ) (hc : 0 < c) (n : ℕ) :
    MemLp (fun x : ℝ => x) 2 (S0153 c n) := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  change MemLp (fun x : ℝ => x) 2 ((Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map
    (fun x => ∑ j, x j))
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (exponential_memLp_two c⁻¹ (inv_pos.2 hc)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => expMeasure c⁻¹) j))

lemma sum_moments (c : ℝ) (hc : 0 < c) (n : ℕ) :
    (∫ x : ℝ, x ∂S0153 c n) = n * c ∧
    (∫ x : ℝ, x ^ 2 ∂S0153 c n) = n * c ^ 2 + (n * c) ^ 2 := by
  have : IsProbabilityMeasure (expMeasure c⁻¹) := isProbabilityMeasure_expMeasure (inv_pos.2 hc)
  have := sum_markov c hc
  have hx (j : Fin n) : MemLp (fun x : Fin n → ℝ => x j) 2
      (Measure.pi (fun _ : Fin n => expMeasure c⁻¹)) :=
    (exponential_memLp_two c⁻¹ (inv_pos.2 hc)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => expMeasure c⁻¹) j)
  have hm : (∫ x : ℝ, x ∂S0153 c n) = n * c := by
    change (∫ x : ℝ, x ∂(Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map
      (fun x => ∑ j, x j)) = _
    rw [integral_map (by fun_prop) (by fun_prop), integral_finsetSum _ (fun j _ => (hx j).integrable (by norm_num))]
    have hj (j : Fin n) : (∫ x : Fin n → ℝ, x j ∂Measure.pi (fun _ : Fin n => expMeasure c⁻¹)) = c := by
      rw [← integral_map (μ := Measure.pi (fun _ : Fin n => expMeasure c⁻¹))
        (φ := fun x : Fin n → ℝ => x j) (measurable_pi_apply j).aemeasurable
        (f := fun x : ℝ => x) (by fun_prop),
        (measurePreserving_eval (fun _ : Fin n => expMeasure c⁻¹) j).map_eq]
      exact (exponential_moments c hc).1
    simp_rw [hj]
    simp
  have hv : Var[fun x : ℝ => x; S0153 c n] = n * c ^ 2 := by
    change Var[fun x : ℝ => x; (Measure.pi (fun _ : Fin n => expMeasure c⁻¹)).map
      (fun x => ∑ j, x j)] = _
    rw [variance_map (by fun_prop) (by fun_prop)]
    have h := variance_sum_pi (fun _ : Fin n => exponential_memLp_two c⁻¹ (inv_pos.2 hc))
    simp only [(exponential_moments c hc).2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    have he : (∑ i : Fin n, fun ω : Fin n → ℝ => ω i) = fun ω => ∑ i, ω i := by
      ext ω
      simp
    rw [he] at h
    exact h
  refine ⟨hm, ?_⟩
  rw [variance_eq_sub (sum_memLp_two c hc n), hm] at hv
  simp only [Pi.pow_apply] at hv
  linarith

lemma poisson_sum_integrable (c : ℝ) (hc : 0 < c) (r : NNReal) :
    Integrable (fun x : ℝ => x) (P0153 c r) ∧ Integrable (fun x : ℝ => x ^ 2) (P0153 c r) := by
  have := sum_markov c hc
  have hm (n : ℕ) : (∫ x : ℝ, ‖x‖ ∂S0153 c n) = n * c := by
    rw [← (sum_moments c hc n).1]
    apply integral_congr_ae
    filter_upwards [sum_nonneg c hc n] with x hx
    exact Real.norm_of_nonneg hx
  have hq (n : ℕ) : (∫ x : ℝ, ‖x ^ 2‖ ∂S0153 c n) = n * c ^ 2 + (n * c) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using (sum_moments c hc n).2
  constructor
  · unfold P0153
    rw [Measure.integrable_comp_iff (by fun_prop)]
    constructor
    · exact ae_of_all _ fun n => (sum_memLp_two c hc n).integrable (by norm_num)
    · simp_rw [hm]
      exact (poisson_moments r).1.mul_const c
  · unfold P0153
    rw [Measure.integrable_comp_iff (by fun_prop)]
    constructor
    · exact ae_of_all _ fun n => (memLp_two_iff_integrable_sq (by fun_prop)).1 (sum_memLp_two c hc n)
    · simp_rw [hq, mul_pow]
      exact ((poisson_moments r).1.mul_const (c ^ 2)).add ((poisson_moments r).2.1.mul_const (c ^ 2))

lemma poisson_sum_moments (c : ℝ) (hc : 0 < c) (r : NNReal) :
    MemLp (fun x : ℝ => x) 2 (P0153 c r) ∧
    (∫ x : ℝ, x ∂P0153 c r) = r * c ∧ Var[fun x : ℝ => x; P0153 c r] = 2 * r * c ^ 2 := by
  have := sum_markov c hc
  have := poisson_sum_probability c hc r
  have hi := poisson_sum_integrable c hc r
  have hLp := (memLp_two_iff_integrable_sq (by fun_prop)).2 hi.2
  have h1 : (∫ x : ℝ, x ∂P0153 c r) = r * c := by
    have hh := hi.1
    unfold P0153 at hh ⊢
    rw [Measure.comp_eq_comp_const_apply] at hh ⊢
    rw [Kernel.integral_comp hh]
    change (∫ n, ∫ x : ℝ, x ∂S0153 c n ∂poissonMeasure r) = _
    simp_rw [(sum_moments c hc _).1]
    rw [integral_mul_const, (poisson_moments r).2.2.1]
  have h2 : (∫ x : ℝ, x ^ 2 ∂P0153 c r) = (r : ℝ) * c ^ 2 + ((r : ℝ) ^ 2 + r) * c ^ 2 := by
    have hh := hi.2
    unfold P0153 at hh ⊢
    rw [Measure.comp_eq_comp_const_apply] at hh ⊢
    rw [Kernel.integral_comp hh]
    change (∫ n, ∫ x : ℝ, x ^ 2 ∂S0153 c n ∂poissonMeasure r) = _
    simp_rw [(sum_moments c hc _).2, mul_pow]
    rw [integral_add ((poisson_moments r).1.mul_const _) ((poisson_moments r).2.1.mul_const _),
      integral_mul_const, integral_mul_const, (poisson_moments r).2.2.1, (poisson_moments r).2.2.2]
  refine ⟨hLp, h1, ?_⟩
  rw [variance_eq_sub hLp, h1]
  simp only [Pi.pow_apply]
  rw [h2]
  ring

lemma transition_moments (c : ℝ) (hc : 0 < c) (x : NNReal) :
    MemLp (fun y : ℝ => y) 2 (K01513 c x) ∧
    (∫ y : ℝ, y ∂K01513 c x) = x ∧ Var[fun y : ℝ => y; K01513 c x] = 2 * c * x := by
  obtain ⟨hLp, hm, hv⟩ := poisson_sum_moments c hc ((x : ℝ) / c).toNNReal
  rw [Real.coe_toNNReal _ (div_nonneg x.coe_nonneg hc.le)] at hm hv
  refine ⟨hLp, ?_, ?_⟩
  · change (∫ y : ℝ, y ∂P0153 c ((x : ℝ) / c).toNNReal) = _
    rw [hm, div_mul_cancel₀ _ hc.ne']
  · change Var[fun y : ℝ => y; P0153 c ((x : ℝ) / c).toNNReal] = _
    rw [hv]
    field_simp


lemma scalar_probability (c : ℝ) (hc : 0 ≤ c) (x : NNReal) :
    IsProbabilityMeasure (T01513 c x) := by
  by_cases h : c = 0
  · simp [T01513, h]; infer_instance
  · simpa [T01513, h, K01513] using poisson_sum_probability c (lt_of_le_of_ne hc (Ne.symm h))
      ((x : ℝ) / c).toNNReal
lemma scalar_measurable (c : ℝ) : Measurable (T01513 c) := by
  unfold T01513
  by_cases h : c = 0
  · simpa [h] using (show Measurable (fun x : NNReal => Measure.dirac (x : ℝ)) by fun_prop)
  · simp only [h, ite_false]
    exact (K0153 c).measurable.comp (by fun_prop)
lemma scalar_nonneg (c : ℝ) (hc : 0 ≤ c) (x : NNReal) :
    ∀ᵐ y ∂T01513 c x, 0 ≤ y := by
  by_cases h : c = 0
  · simp [T01513, h, x.coe_nonneg]
  · simpa [T01513, h, K01513] using poisson_sum_nonneg c (lt_of_le_of_ne hc (Ne.symm h))
      ((x : ℝ) / c).toNNReal
lemma scalar_transform (c : ℝ) (hc : 0 ≤ c) (x : NNReal) (l : ℝ) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-l * y) ∂T01513 c x) = Real.exp (-(x : ℝ) * l / (1 + c * l)) := by
  by_cases h : c = 0
  · simp [T01513, h, mul_comm]
  · simpa [T01513, h] using transition_laplace c (lt_of_le_of_ne hc (Ne.symm h)) x l hl
lemma vector_probability {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    IsProbabilityMeasure (Q01513 c x) := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  unfold Q01513
  infer_instance
lemma vector_measurable {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) :
    Measurable (Q01513 c) := by
  have : ∀ x, IsProbabilityMeasure (Q01513 c x) := vector_probability c hc
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (generateFrom_eq_pi (fun _ => generateFrom_measurableSet)
      (fun _ => isCountablySpanning_measurableSet)).symm
    (IsPiSystem.pi (fun _ => isPiSystem_measurableSet))
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_univ_pi] at hs
  have : ∀ (x : Fin d → NNReal) j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun x j => scalar_probability _ (hc j) _
  simp_rw [Q01513, Measure.pi_pi]
  apply Finset.measurable_prod
  intro j _
  exact (Measure.measurable_coe (show MeasurableSet (s j) from hs j)).comp ((scalar_measurable (c j)).comp (measurable_pi_apply j))
lemma vector_nonneg {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    ∀ᵐ y ∂Q01513 c x, ∀ j, 0 ≤ y j := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  rw [ae_all_iff]
  intro j
  exact Measure.tendsto_eval_ae_ae.eventually (scalar_nonneg _ (hc j) _)
lemma vector_transform {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (x : Fin d → NNReal) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    (∫ y, Real.exp (-(∑ j, l j * y j)) ∂Q01513 c x) =
      Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j))) := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  have he (y : Fin d → ℝ) : Real.exp (-(∑ j, l j * y j)) = ∏ j, Real.exp (-l j * y j) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [neg_mul]
  simp_rw [he, Q01513]
  rw [integral_fintype_prod_eq_prod (fun j (y : ℝ) => Real.exp (-l j * y))]
  simp_rw [scalar_transform _ (hc _) _ _ (hl _), ← Real.exp_sum,
    neg_mul, neg_div, Finset.sum_neg_distrib]

lemma law_of_vector_transform {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (x : Fin d → NNReal) (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ∀ j, 0 ≤ y j)
    (h : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ y, Real.exp (-(∑ j, l j * y j)) ∂μ) =
        Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j)))) : μ = Q01513 c x := by
  have := vector_probability c hc x
  exact laplace_unique μ _ hμ (vector_nonneg c hc x) (fun l hl =>
    (h l hl).trans (vector_transform c hc x l hl).symm)

lemma conditional_vector_law {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hG : G ≤ mΩ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (S : Ω → Fin d → NNReal) (hS : Measurable[G] S)
    (X : Ω → Fin d → ℝ) (hX : Measurable X) (hXpos : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ X ω j)
    (h : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * X ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (S ω j : ℝ) * l j / (1 + c j * l j)))) :
    (∀ B, MeasurableSet B → Measurable[G] (fun ω => Q01513 c (S ω) B)) ∧
      ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
        (μ.restrict D).map X B = ∫⁻ ω in D, Q01513 c (S ω) B ∂μ := by
  have hmeas := (vector_measurable c hc).comp (hS.mono hG le_rfl)
  let κ : Kernel Ω (Fin d → ℝ) := ⟨fun ω => Q01513 c (S ω), hmeas⟩
  have : IsMarkovKernel κ := ⟨fun ω => vector_probability c hc _⟩
  have hkn (ω) : ∀ᵐ y ∂κ ω, ∀ j, 0 ≤ y j := vector_nonneg c hc _
  have hpos : MeasurableSet {y : Fin d → ℝ | ∀ j, 0 ≤ y j} :=
    measurableSet_setOfPred.mpr (by fun_prop)
  constructor
  · intro B hB
    exact (Measure.measurable_coe hB).comp ((vector_measurable c hc).comp hS)
  · intro D hD
    have he : (μ.restrict D).map X = κ ∘ₘ μ.restrict D := by
      apply laplace_unique
      · exact (ae_map_iff hX.aemeasurable hpos).2 (ae_restrict_of_ae hXpos)
      · exact Measure.ae_comp_of_ae_ae hpos (ae_of_all _ hkn)
      · intro l hl
        have hb (y : Fin d → ℝ) (hy : ∀ j, 0 ≤ y j) :
            ‖Real.exp (-(∑ j, l j * y j))‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun j _ => mul_nonneg (hl j) (hy j)))
        have hf : Continuous (fun y : Fin d → ℝ => Real.exp (-(∑ j, l j * y j))) := by fun_prop
        have hi : Integrable (fun y => Real.exp (-(∑ j, l j * y j))) (κ ∘ₘ μ.restrict D) :=
          (integrable_const 1).mono' hf.aestronglyMeasurable (by
            filter_upwards [Measure.ae_comp_of_ae_ae hpos (ae_of_all _ hkn)] with y hy
            exact hb y hy)
        have hxi : Integrable (fun ω => Real.exp (-(∑ j, l j * X ω j))) μ :=
          (integrable_const 1).mono' (by fun_prop) (by
            filter_upwards [hXpos] with ω hω
            exact hb _ hω)
        rw [integral_map hX.aemeasurable hf.aestronglyMeasurable]
        rw [Measure.comp_eq_comp_const_apply] at hi ⊢
        rw [Kernel.integral_comp hi]
        change (∫ ω in D, Real.exp (-(∑ j, l j * X ω j)) ∂μ) =
          ∫ ω in D, ∫ y, Real.exp (-(∑ j, l j * y j)) ∂Q01513 c (S ω) ∂μ
        simp_rw [vector_transform c hc _ l hl]
        rw [← setIntegral_condExp hG hxi hD]
        exact integral_congr_ae (ae_restrict_of_ae (h l hl))
    intro B hB
    rw [he, Measure.bind_apply hB κ.aemeasurable]
    rfl

lemma dirac_support015 (x : ℝ) : (Measure.dirac x).support = {x} := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_singleton (by simp)
  · rintro y rfl
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    simp [Measure.dirac_apply' _ hU.measurableSet, hxU]

lemma scalar_support (c : ℝ) (hc : 0 ≤ c) (x : NNReal) :
    (T01513 c x).support = if c = 0 ∨ x = 0 then {(x : ℝ)} else Ici 0 := by
  by_cases h : c = 0
  · simp [T01513, h, dirac_support015]
  have hp := lt_of_le_of_ne hc (Ne.symm h)
  by_cases hx : x = 0
  · simp [T01513, h, hx, transition_zero c hp, dirac_support015]
  · simp [T01513, h, hx, transition_support c hp x (pos_iff_ne_zero.2 hx)]

lemma product_support015 {d : ℕ} (μ : Fin d → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)] :
    (Measure.pi μ).support = {y | ∀ j, y j ∈ (μ j).support} := by
  have hae : ∀ᵐ y ∂Measure.pi μ, ∀ j, y j ∈ (μ j).support := by
    rw [ae_all_iff]
    exact fun j => Measure.tendsto_eval_ae_ae.eventually (μ j).support_mem_ae
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed _ hae
    simpa only [ofPred_forall, preimage] using isClosed_iInter (fun j => (μ j).isClosed_support.preimage (continuous_apply j))
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.1 hU x hxU
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.2
    apply Finset.prod_ne_zero_iff.2
    intro j _
    exact ne_of_gt ((Measure.mem_support_iff_forall (x j)).1 (hx j) _ ((hu j).1.mem_nhds (hu j).2))

lemma vector_support {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    (Q01513 c x).support =
      {y | ∀ j, if c j = 0 ∨ x j = 0 then y j = (x j : ℝ) else 0 ≤ y j} := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  rw [Q01513, product_support015]
  ext y
  simp only [mem_ofPred_eq, scalar_support _ (hc _)]
  apply forall_congr'
  intro j
  split_ifs <;> rfl

lemma scalar_moments (c : ℝ) (hc : 0 ≤ c) (x : NNReal) :
    MemLp (fun y : ℝ => y) 2 (T01513 c x) ∧
      (∫ y : ℝ, y ∂T01513 c x) = x ∧ Var[fun y : ℝ => y; T01513 c x] = 2 * c * x := by
  by_cases h : c = 0
  · simp only [T01513, h, ite_true, mul_zero, zero_mul, integral_dirac, variance_dirac, and_true]
    apply (memLp_const (x : ℝ) (μ := Measure.dirac (x : ℝ)) (p := 2)).ae_eq
    exact (ae_eq_dirac (fun y : ℝ => y)).symm
  · simpa [T01513, h] using transition_moments c (lt_of_le_of_ne hc (Ne.symm h)) x

lemma vector_independence {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    iIndepFun (fun j (y : Fin d → ℝ) => y j) (Q01513 c x) := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma vector_moments {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal)
    (j : Fin d) : MemLp (fun y => y j) 2 (Q01513 c x) ∧
      (∫ y, y j ∂Q01513 c x) = x j ∧ Var[fun y => y j; Q01513 c x] = 2 * c j * x j := by
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  have hm := measurePreserving_eval (fun j => T01513 (c j) (x j)) j
  obtain ⟨hLp, hmean, hvar⟩ := scalar_moments _ (hc j) (x j)
  refine ⟨hLp.comp_measurePreserving hm, ?_, ?_⟩
  · rw [← hmean, ← hm.map_eq, integral_map hm.measurable.aemeasurable (f := fun y : ℝ => y) (by fun_prop)]
    rfl
  · rw [← hvar, ← hm.map_eq, variance_map (X := fun y : ℝ => y) (by fun_prop) hm.measurable.aemeasurable]
    rfl

lemma image_eq01514 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (c : Fin d → ℝ) (x : Fin d → NNReal) (z : Fin d → ℝ) :
    b01514 A b c x + (A01514 A c x).mulVec z =
      b + A.mulVec (fun j => if c j = 0 ∨ x j = 0 then (x j : ℝ) else z j) := by
  classical
  ext i
  simp only [b01514, A01514, Pi.add_apply, mulVec, dotProduct]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma image_support01514 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    ((Q01513 c x).map (fun y => b + A.mulVec y)).support =
      cone0154 (A01514 A c x) (b01514 A b c x) := by
  classical
  let f : (Fin d → ℝ) → (Fin m → ℝ) := fun y => b + A.mulVec y
  have hf : Continuous f := continuous_const.add A.mulVecLin.continuous_of_finiteDimensional
  have hB : ∀ i j, 0 ≤ A01514 A c x i j := by
    intro i j
    dsimp [A01514]
    split_ifs <;> simp_all
  have hclosed := closed_translate (A01514 A c x) (b01514 A b c x) hB
  have he : f '' (Q01513 c x).support = cone0154 (A01514 A c x) (b01514 A b c x) := by
    rw [vector_support c hc x]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(fun j => if c j = 0 ∨ x j = 0 then 0 else z j), ?_, ?_⟩
      · intro j
        specialize hz j
        simp only
        split_ifs with h <;> simp_all
      · rw [image_eq01514]
        congr 2
        ext j
        specialize hz j
        split_ifs with h <;> simp_all
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(fun j => if c j = 0 ∨ x j = 0 then (x j : ℝ) else z j), ?_, ?_⟩
      · intro j
        split_ifs <;> simp_all
      · exact (image_eq01514 A b c x z).symm
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed hclosed
    apply (ae_map_iff hf.measurable.aemeasurable hclosed.measurableSet).2
    filter_upwards [(Q01513 c x).support_mem_ae] with y hy
    have hh : f y ∈ cone0154 (A01514 A c x) (b01514 A b c x) := by
      rw [← he]
      exact mem_image_of_mem f hy
    exact hh
  · rw [← he]
    rintro y ⟨z, hz, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hzU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact (Measure.mem_support_iff_forall z).1 hz _
      (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hzU))

lemma vector_image_moments {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    (∀ i, (∫ y, b i + ∑ j, A i j * y j ∂Q01513 c x) = b i + ∑ j, A i j * x j) ∧
    (∀ i k, cov[fun y => b i + ∑ j, A i j * y j,
      fun y => b k + ∑ j, A k j * y j; Q01513 c x] = cov0157 A (fun j => 2 * c j * x j) i k) := by
  have := vector_probability c hc x
  constructor
  · intro i
    have hLp (j) := (vector_moments c hc x j).1
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun j _ =>
      ((hLp j).integrable (by norm_num)).const_mul _)), integral_const,
      integral_finsetSum _ (fun j _ => ((hLp j).integrable (by norm_num)).const_mul _)]
    simp_rw [integral_const_mul, (vector_moments c hc x _).2.1]
    simp
  · exact covariance_image A (Q01513 c x) b (fun j (y : Fin d → ℝ) => y j) (fun j => 2 * c j * x j) (fun j => (vector_moments c hc x j).1)
      (vector_independence c hc x) (fun j => (vector_moments c hc x j).2.2)

lemma vector_image_atom {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    ((Q01513 c x).map (fun y => b + A.mulVec y)) {b01514 A b c x} =
      ENNReal.ofReal (Real.exp (-(∑ j, if (∃ i, A01514 A c x i j ≠ 0)
        then (x j : ℝ) / c j else 0))) := by
  classical
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) := fun j => scalar_probability _ (hc j) _
  let B := A01514 A c x
  let b' := b01514 A b c x
  let s : Fin d → Set ℝ := fun j => if (∃ i, B i j ≠ 0) then {0} else univ
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    dsimp [B, A01514]
    split_ifs <;> simp_all
  have hae : ∀ᵐ y ∂Q01513 c x, ∀ j, if c j = 0 ∨ x j = 0 then y j = (x j : ℝ) else 0 ≤ y j := by
    have hh := (Q01513 c x).support_mem_ae
    rw [vector_support c hc x] at hh
    exact hh
  have heq : (fun y => b + A.mulVec y) ⁻¹' {b'} =ᵐ[Q01513 c x] univ.pi s := by
    filter_upwards [hae, vector_nonneg c hc x] with y hy hpos
    have he : b + A.mulVec y = b' + B.mulVec y := by
      rw [image_eq01514]
      congr 2
      ext j
      specialize hy j
      split_ifs <;> simp_all
    apply propext
    simp only [mem_preimage, mem_singleton_iff, Set.mem_pi, mem_univ, forall_const]
    rw [he, zero_image B hB b' y hpos]
    apply forall_congr'
    intro j
    by_cases hj : ∃ i, B i j ≠ 0 <;> simp [s, hj]
  have hf : Measurable (fun y => b + A.mulVec y) :=
    (continuous_const.add A.mulVecLin.continuous_of_finiteDimensional).measurable
  change ((Q01513 c x).map (fun y => b + A.mulVec y)) {b'} = _
  rw [Measure.map_apply hf (measurableSet_singleton _), measure_congr heq]
  change (Measure.pi (fun j => T01513 (c j) (x j))) (univ.pi s) = _
  rw [Measure.pi_pi, ← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : ∃ i, B i j ≠ 0
  · have hcz : c j ≠ 0 := by
      intro hz
      obtain ⟨i, hi⟩ := hj
      simp [B, A01514, hz] at hi
    have hpos := lt_of_le_of_ne (hc j) (Ne.symm hcz)
    simp only [s, hj, ite_true, T01513, hcz, ite_false, transition_atom _ hpos,
      neg_div, B]
  · simp [s, hj, B] at *

lemma vector_covariance_rank {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal) :
    LinearMap.ker (cov0157 A (fun j => 2 * c j * x j)).mulVecLin =
      LinearMap.ker (A01514 A c x).transpose.mulVecLin ∧
    (cov0157 A (fun j => 2 * c j * x j)).rank = (A01514 A c x).rank := by
  classical
  let q : Fin d → ℝ := fun j => if c j = 0 ∨ x j = 0 then 1 else 2 * c j * x j
  have hq (j) : 0 < q j := by
    dsimp [q]
    split_ifs with h
    · norm_num
    · have hcj : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm (not_or.mp h).1)
      have hxj : (0 : ℝ) < x j := by exact_mod_cast (pos_iff_ne_zero.2 (not_or.mp h).2 : 0 < x j)
      positivity
  have he : cov0157 A (fun j => 2 * c j * x j) = cov0157 (A01514 A c x) q := by
    ext i k
    simp only [cov0157]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : c j = 0 ∨ x j = 0
    · rcases h with hz | hz <;> simp [q, A01514, hz]
    · simp [q, A01514, h]
  rw [he]
  exact ⟨covariance_kernel _ q hq, covariance_rank _ q hq⟩

lemma vector_rank_bound {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (c : Fin d → ℝ) (x : Fin d → NNReal) :
    (A01514 A c x).rank ≤ (Finset.univ.filter (fun j => c j ≠ 0 ∧ x j ≠ 0)).card := by
  classical
  rw [← rank_transpose]
  apply rank_le_card_of_support_subset
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra h
  have hz : c j = 0 ∨ x j = 0 := by tauto
  apply hj
  ext i
  simp [Matrix.row, A01514, hz]

lemma conditional_vector_image_law {d m : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (hG : G ≤ mΩ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (S : Ω → Fin d → NNReal) (hS : Measurable[G] S)
    (X : Ω → Fin d → ℝ) (hX : Measurable X) (hXpos : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ X ω j)
    (h : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * X ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (S ω j : ℝ) * l j / (1 + c j * l j))))
    (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ) :
    (∀ B, MeasurableSet B → Measurable[G]
      (fun ω => ((Q01513 c (S ω)).map (fun y => b + A.mulVec y)) B)) ∧
    ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
      (μ.restrict D).map (fun ω => b + A.mulVec (X ω)) B =
        ∫⁻ ω in D, ((Q01513 c (S ω)).map (fun y => b + A.mulVec y)) B ∂μ := by
  have hv := conditional_vector_law G μ hG c hc S hS X hX hXpos h
  have hf : Measurable (fun y => b + A.mulVec y) :=
    (continuous_const.add A.mulVecLin.continuous_of_finiteDimensional).measurable
  constructor
  · intro B hB
    simp_rw [Measure.map_apply hf hB]
    exact hv.1 _ (hf hB)
  · intro D hD B hB
    have he := hv.2 D hD _ (hf hB)
    simp_rw [Measure.map_apply hf hB]
    rw [Measure.map_apply hX (hf hB)] at he
    rw [Measure.map_apply (show Measurable (fun ω => b + A.mulVec (X ω)) from hf.comp hX) hB]
    exact he

lemma table_scale (t : ℝ) (ht : 0 < t) :
    0 < c0159 t 0 ∧ 0 < c0159 t 1 ∧ c0159 t 2 = 0 := by
  dsimp [c0159, α0159]
  constructor
  · positivity
  constructor
  · positivity
  · ring
lemma table_scale_nonneg (t : ℝ) (ht : 0 ≤ t) : ∀ j, 0 ≤ c0159 t j := by
  intro j
  exact div_nonneg (mul_nonneg (sq_nonneg _) ht) (by norm_num)

lemma table_translation {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ)
    (t : ℝ) (ht : 0 < t) (x : Fin 3 → NNReal) (hx : x 2 = 1) :
    b01514 A 0 (c0159 t) x = fun i => A i 2 := by
  have hc := table_scale t ht
  ext i
  simp only [b01514, Pi.zero_apply, Pi.add_apply, zero_add, mulVec, dotProduct,
    Fin.sum_univ_succ]
  simp [hc.1.ne', hc.2.1.ne', hc.2.2, hx]
  split_ifs <;> simp_all

lemma table_columns {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) (t : ℝ) (ht : 0 < t)
    (y : Fin 3 → ℝ) :
    (A01514 A (c0159 t) 1).mulVec y = (A0159 A).mulVec ![y 0, y 1] := by
  have hc := table_scale t ht
  ext i
  simp [A01514, A0159, mulVec, dotProduct, Fin.sum_univ_succ,
    hc.1.ne', hc.2.1.ne', hc.2.2]

lemma table_cone {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) (t : ℝ) (ht : 0 < t) :
    cone0154 (A01514 A (c0159 t) 1) (b01514 A 0 (c0159 t) 1) =
      cone0154 (A0159 A) (fun i => A i 2) := by
  rw [table_translation A t ht 1 rfl]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨![z 0, z 1], ?_, ?_⟩
    · intro j; fin_cases j <;> simpa using hz _
    · rw [table_columns A t ht z]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨![z 0, z 1, 0], ?_, ?_⟩
    · intro j; fin_cases j <;> simp [hz]
    · rw [table_columns A t ht]
      congr 2
      ext j
      fin_cases j <;> rfl

lemma table_support {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (t : ℝ) (ht : 0 < t) :
    ((Q01513 (c0159 t) 1).map A.mulVec).support = cone0154 (A0159 A) (fun i => A i 2) := by
  simpa only [zero_add, table_cone A t ht] using
    image_support01514 A 0 hA (c0159 t) (table_scale_nonneg t ht.le) 1

lemma table_conditional_rank {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ)
    (t : ℝ) (x : Fin 3 → NNReal) : (A01514 A (c0159 t) x).rank ≤ 2 := by
  apply (vector_rank_bound A (c0159 t) x).trans
  calc
    (Finset.univ.filter (fun j => c0159 t j ≠ 0 ∧ x j ≠ 0)).card ≤
        (Finset.univ.filter (fun j : Fin 3 => j ≠ 2)).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro he
      subst j
      exact hj.1 (by simp [c0159, α0159])
    _ = 2 := by decide

lemma nullity_of_rank_le {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (hk : A.rank ≤ k) :
    m - k ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin) := by
  have h := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  change A.transpose.rank + _ = _ at h
  rw [Module.finrank_pi, rank_transpose] at h
  simp only [Fintype.card_fin] at h
  omega

lemma vector_zero_scale {d : ℕ} (x : Fin d → NNReal) :
    Q01513 0 x = Measure.dirac (fun j => (x j : ℝ)) := by
  symm
  apply law_of_vector_transform 0 (fun _ => le_rfl)
  · simp only [ae_dirac_eq, Filter.eventually_pure]
    exact fun j => (x j).coe_nonneg
  · intro l hl
    simp [integral_dirac, mul_comm]

lemma vector_zero_start {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) :
    Q01513 c 0 = Measure.dirac 0 := by
  symm
  apply law_of_vector_transform c hc
  · simp
  · intro l hl
    simp

lemma conditional_point_law {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (hG : G ≤ mΩ) (Y : Ω → Fin d → ℝ) (hY : Measurable[G] Y) :
    (∀ B, MeasurableSet B → Measurable[G] (fun ω => Measure.dirac (Y ω) B)) ∧
      ∀ D, MeasurableSet[G] D → ∀ B, MeasurableSet B →
        (μ.restrict D).map Y B = ∫⁻ ω in D, Measure.dirac (Y ω) B ∂μ := by
  constructor
  · intro B hB
    exact (Measure.measurable_coe hB).comp (Measure.measurable_dirac.comp hY)
  · intro D _ B hB
    rw [← Measure.bind_dirac_eq_map _ (hY.mono hG le_rfl)]
    exact Measure.bind_apply hB
      (show Measurable (fun ω => Measure.dirac (Y ω)) from
        Measure.measurable_dirac.comp (hY.mono hG le_rfl)).aemeasurable

lemma initial_image_law {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin d → ℝ)
    (hX : ∀ᵐ ω ∂μ, X ω = 1) (A : Matrix (Fin m) (Fin d) ℝ) :
    μ.map (fun ω => A.mulVec (X ω)) = Measure.dirac (fun i => ∑ j, A i j) := by
  have he : (fun ω => A.mulVec (X ω)) =ᵐ[μ] (fun _ => A.mulVec 1) := hX.mono (fun _ h => congrArg A.mulVec h)
  rw [Measure.map_congr he, Measure.map_const]
  simp only [measure_univ, one_smul]
  congr 1
  ext i
  simp [mulVec, dotProduct]

lemma table_image {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) (y : Fin 3 → ℝ) (hy : y 2 = 1) :
    A.mulVec y = fun i => A i 2 + A i 0 * y 0 + A i 1 * y 1 := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ]
  simp [hy]
  ring

lemma table_conditional_support {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (t : ℝ) (ht : 0 < t) (x : Fin 3 → NNReal) (hx : x 2 = 1) :
    ((Q01513 (c0159 t) x).map A.mulVec).support =
      cone0154 (A01514 A (c0159 t) x) (fun i => A i 2) := by
  simpa only [zero_add, table_translation A t ht x hx] using
    image_support01514 A 0 hA (c0159 t) (table_scale_nonneg t ht.le) x

lemma point_support015 {d : ℕ} (x : Fin d → ℝ) : (Measure.dirac x).support = {x} := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_singleton (by simp)
  · rintro y rfl
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    simp [Measure.dirac_apply' _ hU.measurableSet, hxU]

lemma conditional_point_moments {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ) (hY : Measurable[G] Y) (hI : ∀ j, Integrable (fun ω => Y ω j) μ) :
    ∀ j, μ[fun ω => Y ω j | G] = (fun ω => Y ω j) ∧ Var[fun ω => Y ω j; μ | G] = 0 := by
  intro j
  have hm : StronglyMeasurable[G] (fun ω => Y ω j) := ((measurable_pi_apply j).comp hY).stronglyMeasurable
  have he := condExp_of_stronglyMeasurable hG hm (hI j)
  refine ⟨he, ?_⟩
  simp [condVar, he]

lemma actual_coefficient0154 {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ) :
    A0154 g b ρ α T t = Standalone.StochasticMeetingVariance.A
      (Standalone.StochasticMeetingVariance.kernel0136 g b ρ (fun j _ => α j) (fun _ _ => 0) T)
      (fun _ _ => 0) T t := by
  ext n j
  simp [A0154, K0154, Standalone.StochasticMeetingVariance.A,
    Standalone.StochasticMeetingVariance.kernel0136, Standalone.StochasticMeetingVariance.F,
    Standalone.StochasticMeetingVariance.R, Standalone.StochasticMeetingVariance.E]

lemma actual_coefficient_nonneg {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (hT : ∀ n, t ≤ T n) (hρ : ∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) :
    ∀ n j, 0 ≤ A0154 g b ρ α T t n j := by
  rw [actual_coefficient0154]
  exact StochasticMeetingVarianceProof.A_nonneg hT
    (StochasticMeetingVarianceProof.full_kernel_nonneg g b ρ (fun j _ => α j) (fun _ _ => 0) T hρ)

lemma actual_variance0154 {m d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → NNReal) (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (h : H0154 G μ Y Z I01314 v g b ρ α T t) :
    V0150 G μ Y =ᵐ[μ] fun ω => (A0154 g b ρ α T t).mulVec (fun j => (v ω j : ℝ)) := by
  have hn (n) : Var[Y n; μ | G] =ᵐ[μ]
      fun ω => ∑ j, (A0154 g b ρ α T t) n j * v ω j := by
    have he := StochasticMeetingVarianceProof.conditional_variance Ω mΩ μ inferInstance G hG d
      (Y n) (Z n) (I01314 n) (K0154 g b ρ α T n) (fun _ _ => 0)
      (fun j ω => (v ω j : ℝ)) t (T n) (h.1 n) (h.2.1 n) (h.2.2.1 n) (h.2.2.2.1 n)
      (fun j => by simpa [Standalone.StochasticMeetingVariance.E] using h.2.2.2.2 n j)
    simpa [Standalone.StochasticMeetingVariance.E, intervalIntegral.integral_mul_const, A0154] using he
  filter_upwards [ae_all_iff.2 hn] with ω hω
  ext n
  exact hω n

lemma actual_variance_measurable {m : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (hG : G ≤ mΩ) (Y : Fin m → Ω → ℝ) :
    Measurable (V0150 G μ Y) := by
  have hm : Measurable[G] (V0150 G μ Y) := by
    let : MeasurableSpace Ω := G
    apply measurable_pi_iff.mpr
    intro j
    exact (stronglyMeasurable_condVar (m := G) (μ := μ) (X := Y j)).measurable
  exact hm.mono hG le_rfl

lemma actual_variance_law {m d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → NNReal) (hv : Measurable v) (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (h : H0154 G μ Y Z I01314 v g b ρ α T t)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal)
    (hlaw : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * v ω j)) ∂μ) =
        Real.exp (-(∑ j, (x j : ℝ) * l j / (1 + c j * l j)))) :
    μ.map (V0150 G μ Y) = (Q01513 c x).map (A0154 g b ρ α T t).mulVec := by
  let f : Ω → Fin d → ℝ := fun ω j => v ω j
  have hf : Measurable f := by fun_prop
  have he : μ.map f = Q01513 c x := by
    apply law_of_vector_transform c hc
    · apply (ae_map_iff hf.aemeasurable (show MeasurableSet {y : Fin d → ℝ | ∀ j, 0 ≤ y j} from
        measurableSet_setOfPred.mpr (by fun_prop))).2
      exact ae_of_all _ fun ω j => (v ω j).coe_nonneg
    · intro l hl
      rw [integral_map hf.aemeasurable
        (show Continuous (fun y : Fin d → ℝ => Real.exp (-(∑ j, l j * y j))) by fun_prop).aestronglyMeasurable]
      exact hlaw l hl
  rw [Measure.map_congr (actual_variance0154 G μ hG Y Z I01314 v g b ρ α T t h)]
  change μ.map ((A0154 g b ρ α T t).mulVec ∘ f) = _
  have hA : Measurable (A0154 g b ρ α T t).mulVec :=
    (A0154 g b ρ α T t).mulVecLin.continuous_of_finiteDimensional.measurable
  rw [← Measure.map_map hA hf, he]

lemma actual_variance_conditional_law {m d : ℕ} {Ω : Type} (G H : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hG : G ≤ mΩ) (hH : H ≤ G)
    (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → NNReal) (hv : Measurable v) (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (α : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (h : H0154 G μ Y Z I01314 v g b ρ α T t)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (S : Ω → Fin d → NNReal) (hS : Measurable[H] S)
    (hlaw : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * v ω j)) | H] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (S ω j : ℝ) * l j / (1 + c j * l j)))) :
    (∀ B, MeasurableSet B → Measurable[H]
      (fun ω => ((Q01513 c (S ω)).map (A0154 g b ρ α T t).mulVec) B)) ∧
    ∀ D, MeasurableSet[H] D → ∀ B, MeasurableSet B →
      (μ.restrict D).map (V0150 G μ Y) B =
        ∫⁻ ω in D, ((Q01513 c (S ω)).map (A0154 g b ρ α T t).mulVec) B ∂μ := by
  have hf : Measurable (fun ω j => (v ω j : ℝ)) := by fun_prop
  have he := conditional_vector_image_law H μ (hH.trans hG) c hc S hS
    (fun ω j => (v ω j : ℝ)) hf (ae_of_all _ fun ω j => (v ω j).coe_nonneg)
    hlaw (A0154 g b ρ α T t) 0
  simp only [zero_add] at he
  refine ⟨he.1, ?_⟩
  intro D hD B hB
  rw [Measure.map_congr (ae_restrict_of_ae (actual_variance0154 G μ hG Y Z I01314 v g b ρ α T t h))]
  exact he.2 D hD B hB

lemma moments_of_image_law {m d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Fin m → ℝ) (hV : Measurable V)
    (A : Matrix (Fin m) (Fin d) ℝ) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) (x : Fin d → NNReal)
    (h : μ.map V = (Q01513 c x).map A.mulVec) :
    (∀ i, MemLp (fun ω => V ω i) 2 μ ∧ (∫ ω, V ω i ∂μ) = ∑ j, A i j * x j) ∧
    ∀ i k, cov[fun ω => V ω i, fun ω => V ω k; μ] = cov0157 A (fun j => 2 * c j * x j) i k := by
  have hA : Measurable A.mulVec := A.mulVecLin.continuous_of_finiteDimensional.measurable
  have := vector_probability c hc x
  have hm := vector_image_moments A 0 c hc x
  simp only [Pi.zero_apply, zero_add] at hm
  constructor
  · intro i
    constructor
    · have hLp : MemLp (fun z : Fin m → ℝ => z i) 2 (μ.map V) := by
        rw [h, memLp_map_measure_iff (continuous_apply i).aestronglyMeasurable hA.aemeasurable]
        exact memLp_finsetSum Finset.univ (fun j _ => (vector_moments c hc x j).1.const_mul (A i j))
      exact (memLp_map_measure_iff (continuous_apply i).aestronglyMeasurable hV.aemeasurable).1 hLp
    · rw [← integral_map (μ := μ) (φ := V) hV.aemeasurable
        (f := fun z : Fin m → ℝ => z i) (continuous_apply i).aestronglyMeasurable, h,
        integral_map hA.aemeasurable (continuous_apply i).aestronglyMeasurable]
      exact hm.1 i
  · intro i k
    rw [← covariance_map_fun (μ := μ) (Z := V)
      (X := fun z : Fin m → ℝ => z i) (Y := fun z : Fin m → ℝ => z k)
      (continuous_apply i).aestronglyMeasurable (continuous_apply k).aestronglyMeasurable hV.aemeasurable, h,
      covariance_map_fun (continuous_apply i).aestronglyMeasurable
        (continuous_apply k).aestronglyMeasurable hA.aemeasurable]
    exact hm.2 i k

lemma q0152_denom (α T l s : ℝ) (hl : 0 ≤ l) (hs : s ≤ T) :
    0 < 1+(α^2*(T-s)/2)*l := by
  have h : 0 ≤ (α^2*(T-s)/2)*l := by positivity
  linarith

lemma q0152_nonneg (α T l s : ℝ) (hl : 0 ≤ l) (hs : s ≤ T) : 0 ≤ q0152 α T l s :=
  div_nonneg hl (q0152_denom α T l s hl hs).le

lemma q0152_terminal (α T l : ℝ) : q0152 α T l T = l := by simp [q0152]

lemma q0152_derivative (α T l s : ℝ) (hl : 0 ≤ l) (hs : s ≤ T) :
    HasDerivAt (q0152 α T l) (α^2*(q0152 α T l s)^2/2) s := by
  have hd : HasDerivAt (fun s : ℝ => 1+(α^2*(T-s)/2)*l) (-(α^2/2)*l) s := by
    convert ((((hasDerivAt_id s).const_sub T).const_mul (α^2)).div_const 2 |>.mul_const l).const_add 1 using 1
    · funext u; simp
    · ring
  have he := (hasDerivAt_const s l).fun_div hd (q0152_denom α T l s hl hs).ne'
  convert he using 1
  · rfl
  · dsimp only [q0152]
    field_simp
    ring

lemma E0152_bounds {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ)
    (hl : ∀ j, 0 ≤ l j) (hs : s ≤ T) (hx : ∀ j, 0 ≤ x j) :
    0 < E0152 α l T s x ∧ E0152 α l T s x ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  exact neg_nonpos.2 (Finset.sum_nonneg fun j _ => mul_nonneg (q0152_nonneg _ _ _ _ (hl j) hs) (hx j))

lemma E0152_time_derivative {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ)
    (hl : ∀ j, 0 ≤ l j) (hs : s ≤ T) :
    HasDerivAt (fun s => E0152 α l T s x)
      (-(∑ j, α j^2*(q0152 (α j) T (l j) s)^2/2*x j)*E0152 α l T s x) s := by
  have he := ((HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (q0152_derivative (α j) T (l j) s (hl j) hs).mul_const (x j)).neg).exp
  simpa only [E0152, Pi.neg_apply, mul_comm] using he

lemma E0152_coordinate_derivative {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ)
    (j : Fin d) (u : ℝ) :
    HasDerivAt (fun u => E0152 α l T s (Function.update x j u))
      (-q0152 (α j) T (l j) s*E0152 α l T s (Function.update x j u)) u := by
  classical
  have hd (k : Fin d) : HasDerivAt (fun u => q0152 (α k) T (l k) s * Function.update x j u k)
      (if k = j then q0152 (α j) T (l j) s else 0) u := by
    by_cases hk : k = j
    · subst k
      simpa using (hasDerivAt_id u).const_mul (q0152 (α j) T (l j) s)
    · simpa [Function.update_of_ne hk, hk] using hasDerivAt_const u (q0152 (α k) T (l k) s*x k)
  have he := ((HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hd k).neg).exp
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  simpa only [E0152, Pi.neg_apply, mul_comm] using he

lemma E0152_coordinate_second {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ)
    (j : Fin d) (u : ℝ) :
    HasDerivAt (deriv (fun u => E0152 α l T s (Function.update x j u)))
      ((q0152 (α j) T (l j) s)^2*E0152 α l T s (Function.update x j u)) u := by
  have hd : deriv (fun u => E0152 α l T s (Function.update x j u)) =
      fun u => -q0152 (α j) T (l j) s*E0152 α l T s (Function.update x j u) :=
    funext fun u => (E0152_coordinate_derivative α l T s x j u).deriv
  rw [hd]
  convert (E0152_coordinate_derivative α l T s x j u).const_mul (-q0152 (α j) T (l j) s) using 1
  ring

lemma E0152_generator {d : ℕ} (α l : Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ)
    (hl : ∀ j, 0 ≤ l j) (hs : s ≤ T) :
    deriv (fun s => E0152 α l T s x) s +
      ∑ j, (α j^2*x j/2) * deriv (deriv (fun u => E0152 α l T s (Function.update x j u))) (x j) = 0 := by
  rw [(E0152_time_derivative α l T s x hl hs).deriv]
  simp_rw [(E0152_coordinate_second α l T s x _ _).deriv, Function.update_eq_self]
  rw [neg_mul, neg_add_eq_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bounded_limit_martingale {ι Ω : Type} [Preorder ι] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ι mΩ)
    (f : ι → Ω → ℝ) (fn : ℕ → ι → Ω → ℝ)
    (hm : ∀ n, Martingale (fn n) F μ) (hf : StronglyAdapted F f)
    (hb : ∀ t ω, ‖f t ω‖ ≤ 1) (hbn : ∀ n t ω, ‖fn n t ω‖ ≤ 1)
    (hlim : ∀ t, ∀ᵐ ω ∂μ, Tendsto (fun n => fn n t ω) atTop (𝓝 (f t ω))) : Martingale f F μ := by
  have hi (t) : Integrable (f t) μ :=
    (integrable_const (1 : ℝ)).mono' ((hf t).mono (F.le t)).aestronglyMeasurable (ae_of_all _ (hb t))
  refine ⟨hf, ?_⟩
  intro s t hst
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun D _ _ => (hi s).integrableOn) ?_ (hf s).aestronglyMeasurable).symm
  intro D hD _
  have hl (u) : Tendsto (fun n => ∫ ω in D, fn n u ω ∂μ) atTop (𝓝 (∫ ω in D, f u ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((hm n).integrable u).aestronglyMeasurable.restrict) (integrable_const 1)
      (fun n => ae_of_all _ (hbn n u)) (ae_restrict_of_ae (hlim u))
  exact tendsto_nhds_unique (hl s) ((hl t).congr (fun n => ((hm n).setIntegral_eq hst hD).symm))

lemma localized_exponential_martingale {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α l : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : H0152 μ F α l T X) :
    Martingale (fun (s : Set.Icc (0 : ℝ) T) ω => M0152 α l T X (s : ℝ) ω) (filt0152 F T) μ := by
  obtain ⟨σ, hσ, hm⟩ := hH
  apply bounded_limit_martingale μ (filt0152 F T) _ _ hm
  · intro s
    have hx : Measurable[F s.val] (fun ω j => (X s.val ω j : ℝ)) := by
      let : MeasurableSpace Ω := F s.val
      apply Measurable.of_eval
      intro j
      have hx := (measurable_pi_apply j).comp (hX s.val s.property)
      fun_prop
    have he : Measurable (fun x : Fin d → ℝ => E0152 α l T s.val x) := by unfold E0152; fun_prop
    exact (he.comp hx).stronglyMeasurable
  · intro s ω
    simp only [M0152, E0152, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (E0152_bounds α l T s.val _ hl s.property.2 (fun j => (X s.val ω j).coe_nonneg)).2
  · intro n s ω
    simp only [M0152, E0152, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (E0152_bounds α l T _ _ hl ((min_le_left _ _).trans s.property.2)
      (fun j => (X _ ω j).coe_nonneg)).2
  · intro s
    filter_upwards [hσ] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    rw [hn, min_eq_left s.property.2]

lemma localized_conditional_transform {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α l : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : H0152 μ F α l T X) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    μ[fun ω => Real.exp (-(∑ j, l j * X T ω j)) | F s] =ᵐ[μ]
      fun ω => Real.exp (-(∑ j, (X s ω j : ℝ)*l j/(1+(α j^2*((T : ℝ)-s)/2)*l j))) := by
  have hm := localized_exponential_martingale μ F α l T X hl hX hH
  have he := hm.condExp_ae_eq (i := ⟨s, hs⟩) (j := ⟨T, T.coe_nonneg, le_rfl⟩) hs.2
  change μ[M0152 α l T X T | F s] =ᵐ[μ] M0152 α l T X s at he
  have hterm : M0152 α l T X T = fun ω => Real.exp (-(∑ j, l j * X T ω j)) := by
    funext ω
    simp [M0152, E0152, q0152_terminal]
  rw [hterm] at he
  convert he using 1
  funext ω
  unfold M0152 E0152 q0152
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma localized_initial_transform {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α l : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : H0152 μ F α l T X) (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) :
    (∫ ω, Real.exp (-(∑ j, l j * X T ω j)) ∂μ) =
      Real.exp (-(∑ j, (x j : ℝ)*l j/(1+(α j^2*(T : ℝ)/2)*l j))) := by
  have he := localized_conditional_transform μ F α l T X hl hX hH 0 ⟨le_rfl, T.coe_nonneg⟩
  have hconst : μ[fun ω => Real.exp (-(∑ j, l j * X T ω j)) | F 0] =ᵐ[μ]
      fun _ => Real.exp (-(∑ j, (x j : ℝ)*l j/(1+(α j^2*(T : ℝ)/2)*l j))) := by
    filter_upwards [he, h0] with ω hω hx
    simpa [hx] using hω
  have hint := integral_congr_ae hconst
  rw [integral_condExp (F.le 0), integral_const] at hint
  simpa using hint

lemma localized_state_law {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) :
    μ.map (fun ω j => (X T ω j : ℝ)) = Q01513 (fun j => α j^2*(T : ℝ)/2) x := by
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  apply law_of_vector_transform _ (fun j => by positivity)
  · apply (ae_map_iff hm.aemeasurable (show MeasurableSet {y : Fin d → ℝ | ∀ j, 0 ≤ y j} from
      measurableSet_setOfPred.mpr (by fun_prop))).2
    exact ae_of_all _ fun ω j => (X T ω j).coe_nonneg
  · intro l hl
    rw [integral_map hm.aemeasurable (show Continuous (fun y : Fin d → ℝ => Real.exp (-(∑ j, l j*y j))) by fun_prop).aestronglyMeasurable]
    exact localized_initial_transform μ F α l T X hl hX (hH l hl) x h0

lemma localized_conditional_state_law {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    (∀ B, MeasurableSet B → Measurable[F s]
      (fun ω => Q01513 (fun j => α j^2*((T : ℝ)-s)/2) (X s ω) B)) ∧
    ∀ D, MeasurableSet[F s] D → ∀ B, MeasurableSet B →
      (μ.restrict D).map (fun ω j => (X T ω j : ℝ)) B =
        ∫⁻ ω in D, Q01513 (fun j => α j^2*((T : ℝ)-s)/2) (X s ω) B ∂μ := by
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  exact conditional_vector_law (F s) μ (F.le s) _
    (fun j => div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.2 hs.2)) (by norm_num))
    (X s) (hX s hs) _ hm (ae_of_all _ fun ω j => (X T ω j).coe_nonneg)
    (fun l hl => localized_conditional_transform μ F α l T X hl hX (hH l hl) s hs)

/-- Transfer an integrable test function through a conditional-law kernel. -/
lemma conditional_kernel_integral {E Ω : Type} [MeasurableSpace E]
    (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hG : G ≤ mΩ) (κ : Kernel Ω E) [IsMarkovKernel κ]
    (Y : Ω → E) (hY : Measurable Y)
    (hlaw : ∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D)
    (f : E → ℝ) (hf : StronglyMeasurable f) (hi : Integrable (fun ω => f (Y ω)) μ)
    (g : Ω → ℝ) (hg : Measurable[G] g) (he : ∀ ω, (∫ y, f y ∂κ ω) = g ω) :
    μ[fun ω => f (Y ω) | G] =ᵐ[μ] g := by
  have himap (D : Set Ω) : Integrable f ((μ.restrict D).map Y) :=
    (integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable).2 hi.restrict
  have hκ (D : Set Ω) (hD : MeasurableSet[G] D) : Integrable f (κ ∘ₘ μ.restrict D) :=
    hlaw D hD ▸ himap D
  have hgi : Integrable g μ := by
    have hiκ := hκ univ MeasurableSet.univ
    rw [Measure.restrict_univ, Measure.comp_eq_comp_const_apply] at hiκ
    have hi' := hiκ.integral_comp
    change Integrable (fun ω => ∫ y, f y ∂κ ω) μ at hi'
    simpa only [he] using hi'
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun D _ _ => hgi.integrableOn) ?_ hg.aestronglyMeasurable).symm
  intro D hD _
  have hiκ := hκ D hD
  have h := integral_map (μ := μ.restrict D) hY.aemeasurable hf.aestronglyMeasurable
  rw [hlaw D hD, Measure.comp_eq_comp_const_apply] at h
  rw [Measure.comp_eq_comp_const_apply] at hiκ
  rw [Kernel.integral_comp hiκ] at h
  change (∫ ω in D, ∫ y, f y ∂κ ω ∂μ) = ∫ ω in D, f (Y ω) ∂μ at h
  simpa only [he] using h

lemma vector_second_moment {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (x : Fin d → NNReal) (j : Fin d) :
    (∫ y, (y j)^2 ∂Q01513 c x) = (x j : ℝ)^2+2*c j*x j := by
  have := vector_probability c hc x
  have hm := vector_moments c hc x j
  have hv := variance_eq_sub hm.1
  rw [hm.2.1, hm.2.2] at hv
  simp only [Pi.pow_apply] at hv
  linarith

lemma localized_state_memLp {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) (j : Fin d) :
    MemLp (fun ω => (X T ω j : ℝ)) 2 μ := by
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  have he := localized_state_law μ F α T X hX hH x h0
  have hi := (vector_moments (fun j => α j^2*(T : ℝ)/2) (fun j => by positivity) x j).1
  rw [← he] at hi
  exact hi.comp_of_map hm.aemeasurable

lemma localized_state_conditional_moments {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (j : Fin d) :
    (μ[fun ω => (X T ω j : ℝ) | F s] =ᵐ[μ] fun ω => (X s ω j : ℝ)) ∧
    (μ[fun ω => (X T ω j : ℝ)^2 | F s] =ᵐ[μ]
      fun ω => (X s ω j : ℝ)^2+α j^2*((T : ℝ)-s)*X s ω j) ∧
    (Var[fun ω => (X T ω j : ℝ); μ | F s] =ᵐ[μ]
      fun ω => α j^2*((T : ℝ)-s)*X s ω j) := by
  let c := fun j => α j^2*((T : ℝ)-s)/2
  have hc : ∀ j, 0 ≤ c j := fun j =>
    div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.2 hs.2)) (by norm_num)
  let κ : Kernel Ω (Fin d → ℝ) := ⟨fun ω => Q01513 c (X s ω),
    (vector_measurable c hc).comp ((hX s hs).mono (F.le s) le_rfl)⟩
  have : IsMarkovKernel κ := ⟨fun ω => vector_probability c hc _⟩
  have hlaw : ∀ D, MeasurableSet[F s] D →
      (μ.restrict D).map (fun ω j => (X T ω j : ℝ)) = κ ∘ₘ μ.restrict D := by
    intro D hD
    apply Measure.ext
    intro B hB
    rw [Measure.bind_apply hB κ.aemeasurable]
    exact (localized_conditional_state_law μ F α T X hX hH s hs).2 D hD B hB
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  have hms : Measurable[F s] (fun ω => (X s ω j : ℝ)) := by
    let : MeasurableSpace Ω := F s
    have hx := (measurable_pi_apply j).comp (hX s hs)
    fun_prop
  have hi := localized_state_memLp μ F α T X hX hH x h0 j
  have hmean : μ[fun ω => (X T ω j : ℝ) | F s] =ᵐ[μ] fun ω => (X s ω j : ℝ) :=
    conditional_kernel_integral (F s) μ (F.le s) κ _ hm hlaw (fun y => y j)
      (continuous_apply j).stronglyMeasurable (hi.integrable one_le_two) _ hms
      (fun ω => (vector_moments c hc (X s ω) j).2.1)
  have hsecond : μ[fun ω => (X T ω j : ℝ)^2 | F s] =ᵐ[μ]
      fun ω => (X s ω j : ℝ)^2+α j^2*((T : ℝ)-s)*X s ω j := by
    apply conditional_kernel_integral (F s) μ (F.le s) κ _ hm hlaw (fun y => (y j)^2)
      (by fun_prop) hi.integrable_sq _ (hms.pow_const 2 |>.add (measurable_const.mul hms))
    intro ω
    change (∫ y, (y j)^2 ∂Q01513 c (X s ω)) = _
    rw [vector_second_moment c hc]
    dsimp [c]
    ring
  refine ⟨hmean, hsecond, ?_⟩
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (F.le s) hi
  filter_upwards [hv, hmean, hsecond] with ω hv hm hs
  change Var[fun ω => (X T ω j : ℝ); μ | F s] ω =
    μ[fun ω => (X T ω j : ℝ)^2 | F s] ω - (μ[fun ω => (X T ω j : ℝ) | F s] ω)^2 at hv
  rw [hm, hs] at hv
  linarith

lemma localized_state_moments {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) (j : Fin d) :
    (∫ ω, (X T ω j : ℝ) ∂μ) = x j ∧
    Var[fun ω => (X T ω j : ℝ); μ] = α j^2*(T : ℝ)*x j := by
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  have he := localized_state_law μ F α T X hX hH x h0
  have hc : ∀ j, 0 ≤ α j^2*(T : ℝ)/2 := fun j => by positivity
  have hv := (vector_moments _ hc x j).2
  constructor
  · rw [← integral_map hm.aemeasurable (continuous_apply j).aestronglyMeasurable, he]
    exact hv.1
  · have hmap := variance_map (μ := μ) (X := fun y : Fin d → ℝ => y j)
      (continuous_apply j).aemeasurable hm.aemeasurable
    change Var[fun y : Fin d → ℝ => y j; μ.map (fun ω j => (X T ω j : ℝ))] =
      Var[fun ω => (X T ω j : ℝ); μ] at hmap
    rw [← hmap, he, hv.2]
    ring

lemma localized_state_martingale {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) (j : Fin d) :
    Martingale (fun (s : Icc (0 : ℝ) T) ω => (X s.val ω j : ℝ)) (filt0152 F T) μ := by
  apply (martingale_condExp (fun ω => (X T ω j : ℝ)) (filt0152 F T) μ).congr
  · intro s
    have hm : Measurable[F s.val] (fun ω => (X s.val ω j : ℝ)) := by
      let : MeasurableSpace Ω := F s.val
      have hx := (measurable_pi_apply j).comp (hX s.val s.property)
      fun_prop
    exact hm.stronglyMeasurable
  · intro s
    exact (localized_state_conditional_moments μ F α T X hX hH x h0 s.val s.property j).1

lemma localized_state_absorption {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (j : Fin d) :
    ∀ᵐ ω ∂μ, X s ω j = 0 → X T ω j = 0 := by
  let D := {ω | X s ω j = 0}
  have hD : MeasurableSet[F s] D :=
    measurableSet_eq_fun ((measurable_pi_apply j).comp (hX s hs)) measurable_const
  have hi := (localized_state_memLp μ F α T X hX hH x h0 j).integrable one_le_two
  have hm := (localized_state_conditional_moments μ F α T X hX hH x h0 s hs j).1
  have he : (∫ ω in D, (X T ω j : ℝ) ∂μ) = 0 := by
    rw [← setIntegral_condExp (F.le s) hi hD,
      integral_congr_ae (ae_restrict_of_ae hm)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (F.le s D hD)] with ω hω
    simp only [D, mem_ofPred_eq] at hω
    simp [hω]
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => (X T ω j).coe_nonneg) hi.restrict).1 he
  filter_upwards [ae_imp_of_ae_restrict hae] with ω hω
  intro hs0
  have heq : (X T ω j : ℝ) = 0 := hω hs0
  exact_mod_cast heq

lemma localized_state_constant {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) (j : Fin d) (hj : α j = 0) :
    ∀ᵐ ω ∂μ, X T ω j = x j := by
  have hi := localized_state_memLp μ F α T X hX hH x h0 j
  have hm := localized_state_moments μ F α T X hX hH x h0 j
  have hv : Var[fun ω => (X T ω j : ℝ); μ] = 0 := by simpa [hj] using hm.2
  have he := ae_eq_integral_of_variance_eq_zero hi hv
  rw [hm.1] at he
  filter_upwards [he] with ω hω
  exact_mod_cast hω

lemma localized_state_independence {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) :
    iIndepFun (fun j ω => (X T ω j : ℝ)) μ := by
  have hm : Measurable (fun ω j => (X T ω j : ℝ)) := by
    have hx := (hX T ⟨T.coe_nonneg, le_rfl⟩).mono (F.le T) le_rfl
    fun_prop
  let c := fun j => α j^2*(T : ℝ)/2
  have hc : ∀ j, 0 ≤ c j := fun j => by dsimp [c]; positivity
  have he := localized_state_law μ F α T X hX hH x h0
  have : ∀ j, IsProbabilityMeasure (T01513 (c j) (x j)) :=
    fun j => scalar_probability _ (hc j) _
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun j => ((measurable_pi_apply j).comp hm).aemeasurable)).2
  have hj (j : Fin d) : μ.map (fun ω => (X T ω j : ℝ)) = T01513 (c j) (x j) := by
    have hmap := Measure.map_map (μ := μ) (measurable_pi_apply j) hm
    change (μ.map (fun ω j => (X T ω j : ℝ))).map (fun y => y j) =
      μ.map (fun ω => (X T ω j : ℝ)) at hmap
    rw [← hmap, he]
    exact (measurePreserving_eval (fun j => T01513 (c j) (x j)) j).map_eq
  change μ.map (fun ω j => (X T ω j : ℝ)) = Measure.pi (fun j => μ.map (fun ω => (X T ω j : ℝ)))
  simp_rw [hj]
  exact he

/-- Conditional Fubini for a deterministic weight and a common conditional mean. -/
lemma conditional_weighted_integral {ι Ω : Type} [MeasurableSpace ι]
    (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (ν : Measure ι) [SFinite ν] (K : ι → ℝ) (Z : ι → Ω → ℝ)
    (Y : Ω → ℝ) (hY : Measurable[G] Y) (hiY : Integrable Y μ)
    (hprod : Integrable (fun p : ι × Ω => K p.1*Z p.1 p.2) (ν.prod μ))
    (hcond : ∀ᵐ u ∂ν, μ[fun ω => K u*Z u ω | G] =ᵐ[μ] fun ω => K u*Y ω) :
    Integrable (fun ω => ∫ u, K u*Z u ω ∂ν) μ ∧
    (μ[fun ω => ∫ u, K u*Z u ω ∂ν | G] =ᵐ[μ] fun ω => (∫ u, K u ∂ν)*Y ω) := by
  have hi := hprod.integral_prod_right
  refine ⟨hi, ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun D _ _ => (hiY.const_mul _).integrableOn) ?_
    (measurable_const.mul hY).aestronglyMeasurable).symm
  intro D hD _
  have hpr : Integrable (fun p : ι × Ω => K p.1*Z p.1 p.2) (ν.prod (μ.restrict D)) :=
    hprod.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [integral_const_mul, ← integral_integral_swap hpr]
  have he : (∫ u, K u ∂ν)*(∫ ω in D, Y ω ∂μ) = ∫ u, K u*(∫ ω in D, Y ω ∂μ) ∂ν :=
    (integral_mul_const _ _).symm
  rw [he]
  apply integral_congr_ae
  filter_upwards [hcond, hprod.prod_right_ae] with u hu hiu
  rw [← setIntegral_condExp hG hiu hD, integral_congr_ae (ae_restrict_of_ae hu), integral_const_mul]

/-- Adaptation and continuous paths give the joint measurability used by Fubini. -/
lemma localized_state_jointly_measurable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (j : Fin d) (hcont : ∀ ω, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ T) :
    AEStronglyMeasurable (fun p : ℝ × Ω => (X p.1 p.2 j : ℝ))
      ((volume.restrict (Ioc a b)).prod μ) := by
  let c : ℝ → Icc (0 : ℝ) T := fun u =>
    ⟨min (T : ℝ) (max 0 u), le_min T.coe_nonneg (le_max_left _ _), min_le_left _ _⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    fun_prop
  have hZ : StronglyMeasurable (fun p : ℝ × Ω => (X (c p.1).val p.2 j : ℝ)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun u ω => (X (c u).val ω j : ℝ))
    · intro ω
      exact (hcont ω).comp hc
    · intro u
      have hx := ((measurable_pi_apply j).comp (hX (c u).val (c u).property)).mono (F.le _) le_rfl
      exact (show Measurable (fun ω => (X (c u).val ω j : ℝ)) by fun_prop).stronglyMeasurable
  apply hZ.aestronglyMeasurable.congr
  have hmem : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, p.1 ∈ Ioc a b :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  have hp0 : 0 ≤ p.1 := ha.trans hp.1.le
  have hpT : p.1 ≤ T := hp.2.trans hb
  simp only [c, max_eq_right hp0, min_eq_right hpT]

lemma localized_weighted_integral {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (α : Fin d → ℝ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hH : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → H0152 μ F α l T X)
    (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (j : Fin d)
    (K : ℝ → ℝ) (hK : IntervalIntegrable K volume a b)
    (hjoint : AEStronglyMeasurable (fun p : ℝ × Ω => (X p.1 p.2 j : ℝ))
      ((volume.restrict (Ioc a b)).prod μ)) :
    Integrable (fun ω => ∫ u in a..b, K u*X u ω j) μ ∧
    (μ[fun ω => ∫ u in a..b, K u*X u ω j | F a] =ᵐ[μ]
      fun ω => ∫ u in a..b, K u*X a ω j) := by
  let ν := volume.restrict (Ioc a b)
  have hia : a ∈ Icc (0 : ℝ) T := ⟨ha, hab.trans hb⟩
  have hu : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) T ∧ a ≤ u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact ⟨⟨ha.trans hu.1.le, hu.2.trans hb⟩, hu.1.le⟩
  have hm := localized_state_martingale μ F α T X hX hH x h0 j
  have hiu (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : Integrable (fun ω => (X u ω j : ℝ)) μ :=
    hm.integrable ⟨u, hu⟩
  have hmean (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : (∫ ω, (X u ω j : ℝ) ∂μ) = x j := by
    have he := integral_congr_ae (localized_state_conditional_moments μ F α T X hX hH x h0 u hu j).1
    rw [integral_condExp (F.le u), (localized_state_moments μ F α T X hX hH x h0 j).1] at he
    exact he.symm
  have hKν : Integrable K ν := hK.1
  have hprod : Integrable (fun p : ℝ × Ω => K p.1*(X p.1 p.2 j : ℝ)) (ν.prod μ) := by
    have hkm : AEStronglyMeasurable (fun p : ℝ × Ω => K p.1*(X p.1 p.2 j : ℝ)) (ν.prod μ) :=
      hKν.aestronglyMeasurable.comp_fst.mul hjoint
    apply (integrable_prod_iff hkm).2
    constructor
    · filter_upwards [hu] with u hu
      exact (hiu u hu.1).const_mul (K u)
    · apply (hKν.norm.mul_const (x j : ℝ)).congr
      filter_upwards [hu] with u hu
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (X u _ j).coe_nonneg]
      rw [integral_const_mul, hmean u hu.1]
  have hma : Measurable[F a] (fun ω => (X a ω j : ℝ)) := by
    let : MeasurableSpace Ω := F a
    have hx := (measurable_pi_apply j).comp (hX a hia)
    fun_prop
  have hcond : ∀ᵐ u ∂ν, μ[fun ω => K u*(X u ω j : ℝ) | F a] =ᵐ[μ]
      fun ω => K u*(X a ω j : ℝ) := by
    filter_upwards [hu] with u hu
    have he := hm.condExp_ae_eq (i := ⟨a, hia⟩) (j := ⟨u, hu.1⟩) hu.2
    have hk := condExp_smul (μ := μ) (m := F a) (K u) (fun ω => (X u ω j : ℝ))
    filter_upwards [he, hk] with ω he hk
    change μ[fun ω => K u*(X u ω j : ℝ) | F a] ω =
      K u*μ[fun ω => (X u ω j : ℝ) | F a] ω at hk
    change μ[fun ω => (X u ω j : ℝ) | F a] ω = (X a ω j : ℝ) at he
    rw [he] at hk
    exact hk
  have hout := conditional_weighted_integral (F a) μ (F.le a) ν K
    (fun u ω => (X u ω j : ℝ)) (fun ω => (X a ω j : ℝ)) hma (hiu a hia) hprod hcond
  simpa only [intervalIntegral.integral_of_le hab, integral_mul_const, ν] using hout


lemma bounded_coefficient_integrable (f : ℝ → ℝ) (a b C : ℝ)
    (hab : a ≤ b) (hm : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hC : ∀ u ∈ Icc a b, |f u| ≤ C) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  exact Integrable.of_bound hm C ((ae_restrict_mem measurableSet_Icc).mono
    fun u hu => by simpa only [Real.norm_eq_abs] using hC u hu)

lemma backward_integral_regular (b : ℝ → ℝ) (t T B : ℝ) (ht : t ≤ T)
    (hm : AEStronglyMeasurable b (volume.restrict (Icc t T)))
    (hB : ∀ u ∈ Icc t T, |b u| ≤ B) :
    ContinuousOn (fun u => ∫ s in u..T, b s) (Icc t T) ∧
    ∀ u ∈ Icc t T, |∫ s in u..T, b s| ≤ B*(T-t) := by
  have hi := bounded_coefficient_integrable b t T B ht hm hB
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB t ⟨le_rfl, ht⟩)
  constructor
  · simpa only [uIcc_of_le ht] using
      intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff' (by finiteness)).1 hi)
  · intro u hu
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T)
      (f := b) (C := B) (fun s hs => by
        rw [uIoc_of_le hu.2] at hs
        simpa only [Real.norm_eq_abs] using hB s ⟨hu.1.trans hs.1.le, hs.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hu.2)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hu.1 T) hB0)

lemma full_kernel_bound (g ρ α R G D : ℝ) (hg : |g| ≤ G) (hr : |ρ| ≤ 1)
    (hR : |R| ≤ D) :
    |g^2+2*ρ*g*α*R+α^2*R^2| ≤ (G+|α| * D)^2 := by
  have hG : 0 ≤ G := (abs_nonneg _).trans hg
  have hD : 0 ≤ D := (abs_nonneg _).trans hR
  calc
    |g^2+2*ρ*g*α*R+α^2*R^2| ≤ |g^2|+|2*ρ*g*α*R|+|α^2*R^2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |g|^2+2*|ρ| * |g| * |α| * |R|+|α|^2*|R|^2 := by
      norm_num only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ G^2+2*1*G*|α| * D+|α|^2*D^2 := by gcongr
    _ = (G+|α| * D)^2 := by ring

lemma full_kernel_regular (g b ρ : ℝ → ℝ) (α t T G B : ℝ) (ht : t ≤ T)
    (hg : AEStronglyMeasurable g (volume.restrict (Icc t T)))
    (hb : AEStronglyMeasurable b (volume.restrict (Icc t T)))
    (hr : AEStronglyMeasurable ρ (volume.restrict (Icc t T)))
    (hG : ∀ u ∈ Icc t T, |g u| ≤ G)
    (hB : ∀ u ∈ Icc t T, |b u| ≤ B)
    (hρ : ∀ u ∈ Icc t T, |ρ u| ≤ 1) :
    IntervalIntegrable (fun u => (g u)^2+2*ρ u*g u*α*(∫ s in u..T, b s)+
      α^2*(∫ s in u..T, b s)^2) volume t T := by
  have hR := backward_integral_regular b t T B ht hb hB
  have hmR := hR.1.aestronglyMeasurable (μ := volume) measurableSet_Icc
  apply bounded_coefficient_integrable _ t T ((G+|α| * (B*(T-t)))^2) ht
  · exact ((hg.pow 2).add ((((hr.const_mul 2).mul hg).mul_const α).mul hmR)).add
      ((hmR.pow 2).const_mul (α^2))
  · intro u hu
    exact full_kernel_bound _ _ _ _ _ _ (hG u hu) (hρ u hu) (hR.2 u hu)

lemma integration_assembly : integrationAssemblyStatement := by
  intro m d Ω mΩ μ hμ F α U X hX hcont hH x h0 g b ρ T t ht hT hK Y Z h1 h2 h3 h4
  let := hμ
  have h5 (n : Fin m) (j : Fin d) :
      μ[I0154 g b ρ α T t X n j | F t] =ᵐ[μ]
        fun ω => ∫ u in t..T n, K0154 g b ρ α T n j u * X t ω j :=
    (localized_weighted_integral μ F α U X hX hH x h0 t (T n) ht (hT n).1 (hT n).2 j
      (K0154 g b ρ α T n j) (hK n j)
      (localized_state_jointly_measurable μ F U X hX j (fun ω => hcont ω j) t (T n) ht (hT n).2)).2
  have h : H0154 (F t) μ Y Z (I0154 g b ρ α T t X) (X t) g b ρ α T t := ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h, actual_variance0154 (F t) μ (F.le t) Y Z (I0154 g b ρ α T t X) (X t) g b ρ α T t h⟩

lemma meeting_count_measurable {N : ℕ} (T : Fin N → ℝ) : Measurable (j01530 T) := by
  unfold j01530
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite measurableSet_Ici measurable_const
lemma meeting_count_le {N : ℕ} (T : Fin N → ℝ) (s : ℝ) : j01530 T s ≤ N := by
  calc
    j01530 T s ≤ ∑ _i : Fin N, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = N := by simp
lemma finite_loading_bound (N : ℕ) (γ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ k ≤ N, |γ k| ≤ C) ∧
      ∀ k ≤ N, |G01530 γ k| ≤ N*C := by
  let C := ∑ i ∈ Finset.range (N+1), |γ i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hγ (k) (hk : k ≤ N) : |γ k| ≤ C :=
    Finset.single_le_sum (s := Finset.range (N+1)) (f := fun i => |γ i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  refine ⟨C, hC, hγ, fun k hk => ?_⟩
  calc
    |G01530 γ k| ≤ ∑ i ∈ Finset.range k, |γ (i+1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, C := Finset.sum_le_sum (fun i hi => hγ (i+1) (by simp at hi; omega))
    _ = (k : ℝ)*C := by simp
    _ ≤ (N : ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hC
lemma decay_joint_measurable (lam : ℝ → ℝ)
    (hi : ∀ a b, IntervalIntegrable lam volume a b) :
    Measurable (fun p : ℝ × ℝ => Real.exp (-(∫ q in p.1..p.2, lam q))) := by
  have hc := intervalIntegral.continuous_primitive hi 0
  have he (s u : ℝ) : (∫ q in s..u, lam q) = (∫ q in (0 : ℝ)..u, lam q)-(∫ q in (0 : ℝ)..s, lam q) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s u)
    linarith
  convert ((hc.measurable.comp measurable_snd).sub (hc.measurable.comp measurable_fst)).neg.exp using 1
  ext p
  exact congrArg (fun x : ℝ => Real.exp (-x)) (he p.1 p.2)
lemma source_g_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (ha : Measurable a) (hi : ∀ a b, IntervalIntegrable lam volume a b) (n : Fin N) :
    Measurable (g01530 T a lam γ n) := by
  unfold g01530
  exact (ha.mul ((decay_joint_measurable lam hi).comp (measurable_id.prodMk measurable_const))).mul
    ((measurable_of_countable γ).comp (measurable_const.sub (meeting_count_measurable T)))
lemma source_h_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (ha : Measurable a) (hi : ∀ a b, IntervalIntegrable lam volume a b) :
    Measurable (fun p : ℝ × ℝ => h01530 T a lam γ p.1 p.2) := by
  unfold h01530
  exact ((ha.comp measurable_fst).mul (decay_joint_measurable lam hi)).mul
    ((measurable_of_countable (G01530 γ)).comp
      (((meeting_count_measurable T).comp measurable_snd).sub
        ((meeting_count_measurable T).comp measurable_fst)))
lemma variable_interval_measurable (h : ℝ → ℝ → ℝ)
    (hm : Measurable (fun p : ℝ × ℝ => h p.1 p.2)) (T : ℝ) :
    Measurable (fun s => ∫ u in s..T, h s u) := by
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ T} :=
    (measurableSet_lt measurable_fst measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
  have h2 : MeasurableSet {p : ℝ × ℝ | T < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
  have hm1 := (hm.indicator h1).stronglyMeasurable.integral_prod_right' (ν := volume)
  have hm2 := (hm.indicator h2).stronglyMeasurable.integral_prod_right' (ν := volume)
  have he (s : ℝ) : (∫ u in s..T, h s u) =
      (∫ u, {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ T}.indicator (fun p => h p.1 p.2) (s,u))-
      (∫ u, {p : ℝ × ℝ | T < p.2 ∧ p.2 ≤ p.1}.indicator (fun p => h p.1 p.2) (s,u)) := by
    rw [intervalIntegral]
    congr 1 <;> rw [← integral_indicator measurableSet_Ioc] <;> rfl
  convert hm1.measurable.sub hm2.measurable using 1
  ext s
  exact he s
lemma source_b_measurable {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (ha : Measurable a) (hi : ∀ a b, IntervalIntegrable lam volume a b) (n : Fin N) :
    Measurable (b01530 T a lam γ n) :=
  (source_g_measurable T a lam γ ha hi n).mul
    (variable_interval_measurable _ (source_h_measurable T a lam γ ha hi) (T n))
lemma decay_bound (lam : ℝ → ℝ) (hl : ∀ u, 0 ≤ lam u) (s u : ℝ) (hsu : s ≤ u) :
    |Real.exp (-(∫ q in s..u, lam q))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall hsu hl)
lemma source_coefficients_bound {N : ℕ} (T : Fin N → ℝ) (a lam : ℝ → ℝ) (γ : ℕ → ℝ)
    (hl : ∀ u, 0 ≤ lam u) (n : Fin N) (t A : ℝ) (ht : t ≤ T n)
    (hA : ∀ s ∈ Icc t (T n), |a s| ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Icc t (T n), |g01530 T a lam γ n s| ≤ A*C) ∧
      (∀ s ∈ Icc t (T n), |b01530 T a lam γ n s| ≤ (A*C)*(A*(N*C)*(T n-t))) := by
  obtain ⟨C, hC, hγ, hG⟩ := finite_loading_bound N γ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA t ⟨le_rfl, ht⟩)
  have hg (s) (hs : s ∈ Icc t (T n)) : |g01530 T a lam γ n s| ≤ A*C := by
    dsimp [g01530]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ A*1*C := by
        gcongr
        · exact hA s hs
        · exact decay_bound lam hl s (T n) hs.2
        · exact hγ _ (by omega)
      _ = A*C := by ring
  refine ⟨C, hC, hg, fun s hs => ?_⟩
  have hh (u : ℝ) (hu : u ∈ Icc s (T n)) : |h01530 T a lam γ s u| ≤ A*(N*C) := by
    dsimp [h01530]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ A*1*(N*C) := by
        gcongr
        · exact hA s hs
        · exact decay_bound lam hl s u hu.1
        · exact hG _ ((Nat.sub_le _ _).trans (meeting_count_le T u))
      _ = A*(N*C) := by ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := T n)
    (C := A*(N*C)) (f := h01530 T a lam γ s) (fun u hu => by
      rw [uIoc_of_le hs.2] at hu
      simpa only [Real.norm_eq_abs] using hh u ⟨hu.1.le, hu.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hI
  have hI' : |∫ u in s..T n, h01530 T a lam γ s u| ≤ A*(N*C)*(T n-t) :=
    hI.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 _) (by positivity))
  dsimp [b01530]
  rw [abs_mul]
  exact mul_le_mul (hg s hs) hI' (abs_nonneg _) (by positivity)

lemma regular_integration_assembly : regularIntegrationAssemblyStatement := by
  intro m d Ω mΩ μ hμ F α U X hX hcont hH x h0 g b ρ T t ht hT hg hb hr hbound hρ Y Z h1 h2 h3 h4
  have hK (n : Fin m) (j : Fin d) : IntervalIntegrable (K0154 g b ρ α T n j) volume t (T n) := by
    obtain ⟨G, B, hGB⟩ := hbound n j
    exact full_kernel_regular (g n j) (b n j) (ρ j) (α j) t (T n) G B (hT n).1
      (hg n j) (hb n j) (hr n j) (fun u hu => (hGB u hu).1)
      (fun u hu => (hGB u hu).2) (hρ n j)
  exact ⟨hK, integration_assembly m d Ω mΩ μ hμ F α U X hX hcont hH x h0
    g b ρ T t ht hT hK Y Z h1 h2 h3 h4⟩

lemma primitive_interval_integrable (f : ℝ → ℝ) (hm : Measurable f)
    (hb : ∀ l r, ∃ B : ℝ, ∀ u ∈ Icc l r, |f u| ≤ B) (l r : ℝ) :
    IntervalIntegrable f volume l r := by
  rcases le_total l r with h | h
  · obtain ⟨B, hB⟩ := hb l r
    exact bounded_coefficient_integrable f l r B h hm.aestronglyMeasurable hB
  · obtain ⟨B, hB⟩ := hb r l
    exact (bounded_coefficient_integrable f r l B h hm.aestronglyMeasurable hB).symm

lemma source_coefficients : sourceCoefficientStatement := by
  intro N m d T rows a lam ρ γ α t hT ha hl hr hln hloc hbound hρ
  have hi (j) := primitive_interval_integrable (lam j) (hl j) (hloc j)
  have hm (n : Fin m) (j : Fin d) :=
    And.intro (source_g_measurable T (a j) (lam j) (γ j) (ha j) (hi j) (rows n))
      (source_b_measurable T (a j) (lam j) (γ j) (ha j) (hi j) (rows n))
  have hb (n : Fin m) (j : Fin d) : ∃ G B : ℝ, ∀ u ∈ Icc t (T (rows n)),
      |g01530 T (a j) (lam j) (γ j) (rows n) u| ≤ G ∧ |b01530 T (a j) (lam j) (γ j) (rows n) u| ≤ B := by
    obtain ⟨A, hA⟩ := hbound n j
    obtain ⟨C, _, hg, hb⟩ := source_coefficients_bound T (a j) (lam j) (γ j) (hln j) (rows n) t A (hT n) hA
    exact ⟨A*C, (A*C)*(A*(N*C)*(T (rows n)-t)), fun u hu => ⟨hg u hu, hb u hu⟩⟩
  refine ⟨hm, hb, fun n j => ?_⟩
  obtain ⟨G, B, hGB⟩ := hb n j
  exact full_kernel_regular _ _ _ _ _ _ G B (hT n) (hm n j).1.aestronglyMeasurable
    (hm n j).2.aestronglyMeasurable (hr j).aestronglyMeasurable
    (fun u hu => (hGB u hu).1) (fun u hu => (hGB u hu).2) (hρ n j)

section
variable {ι Ω : Type} [CompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [CompactSpace ι] [SecondCountableTopology ι]
omit [CompactSpace ι] [SecondCountableTopology ι] in
lemma continuous_hitting_le (Y : ι → NNReal) (hY : Continuous Y) (c : NNReal) (s : ι) :
    sInf {r | c ≤ Y r} ≤ s ↔ s = ⊤ ∨ ∃ r, r ≤ s ∧ c ≤ Y r := by
  constructor
  · intro hs
    by_cases he : ({r | c ≤ Y r} : Set ι).Nonempty
    · exact Or.inr ⟨_, hs, IsClosed.sInf_mem he (isClosed_le continuous_const hY)⟩
    · have hz : ({r | c ≤ Y r} : Set ι) = ∅ := not_nonempty_iff_eq_empty.mp he
      rw [hz, sInf_empty] at hs
      exact Or.inl (top_le_iff.mp hs)
  · rintro (rfl | ⟨r, hrs, hr⟩)
    · exact le_top
    · exact (sInf_le (s := {r | c ≤ Y r}) hr).trans hrs

lemma continuous_hit_event_measurable [mΩ : MeasurableSpace Ω] (F : Filtration ι mΩ)
    (Y : ι → Ω → NNReal) (hm : ∀ s, Measurable[F s] (Y s))
    (hc : ∀ ω, Continuous (fun s => Y s ω)) (c : NNReal) (s : ι) :
    MeasurableSet[F s] {ω | ∃ r, r ≤ s ∧ c ≤ Y r ω} := by
  have hsup : Measurable[F s] (fun ω => ⨆ r : Iic s, (Y r.val ω : ENNReal)) := by
    convert measurable_iSup_of_lowerSemicontinuous
      (fun r : Iic s => ((hm r.val).mono (F.mono r.property) le_rfl).coe_nnreal_ennreal)
      (fun ω => (ENNReal.continuous_coe.comp ((hc ω).comp continuous_subtype_val)).lowerSemicontinuous) using 1
    ext ω
    simp only [iSup_apply]
  have he (ω : Ω) : (c : ENNReal) ≤ ⨆ r : Iic s, (Y r.val ω : ENNReal) ↔
      ∃ r, r ≤ s ∧ c ≤ Y r ω := by
    obtain ⟨r, hr, hmax⟩ := isClosed_Iic.isCompact.exists_isMaxOn
      (show (Iic s).Nonempty from ⟨s, le_rfl⟩) (hc ω).continuousOn
    constructor
    · intro h
      refine ⟨r, hr, ?_⟩
      have hb : (⨆ u : Iic s, (Y u.val ω : ENNReal)) ≤ (Y r ω : ENNReal) :=
        iSup_le fun u => by exact_mod_cast hmax u.property
      exact_mod_cast h.trans hb
    · rintro ⟨u, hu, hcu⟩
      exact le_iSup_of_le (⟨u, hu⟩ : Iic s) (by exact_mod_cast hcu)
  convert measurableSet_le (measurable_const (a := (c : ENNReal))) hsup using 1
  ext ω
  exact (he ω).symm

lemma continuous_hitting_stopping [mΩ : MeasurableSpace Ω] (F : Filtration ι mΩ)
    (Y : ι → Ω → NNReal) (hm : ∀ s, Measurable[F s] (Y s))
    (hc : ∀ ω, Continuous (fun s => Y s ω)) (c : NNReal) :
    IsStoppingTime F (fun ω => (sInf {r | c ≤ Y r ω} : ι)) := by
  intro s
  by_cases hs : s = ⊤
  · subst s
    simp only [WithTop.coe_le_coe, le_top, ofPred_true]
    exact MeasurableSet.univ
  · convert continuous_hit_event_measurable F Y hm hc c s using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [continuous_hitting_le _ (hc ω)]
    simp only [hs, false_or]

omit [CompactSpace ι] [SecondCountableTopology ι] in
lemma continuous_hitting_bound [DenselyOrdered ι] (Y : ι → NNReal)
    (hc : Continuous Y) (c : NNReal) (h0 : Y ⊥ ≤ c) (s : ι)
    (hs : s ≤ sInf {r | c ≤ Y r}) : Y s ≤ c := by
  by_contra h
  have hcs : c < Y s := lt_of_not_ge h
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (show (⊥ : ι) ≤ s from bot_le)
    hc.continuousOn (show c ∈ Icc (Y ⊥) (Y s) from ⟨h0, hcs.le⟩)
  have hsr : s ≤ r := hs.trans (sInf_le (show r ∈ {r | c ≤ Y r} from he.ge))
  have hrs : r = s := le_antisymm hr.2 hsr
  exact hcs.ne (by simpa only [hrs] using he.symm)

omit [OrderTopology ι] [SecondCountableTopology ι] in
lemma continuous_hitting_eventually_top (Y : ι → NNReal) (hc : Continuous Y) :
    ∀ᶠ n : ℕ in atTop, sInf {r | (n+2 : NNReal) ≤ Y r} = (⊤ : ι) := by
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt (B : ℝ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hb : B < (n+2 : NNReal) := by
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : (B : ℝ) < (n : ℝ)+2 := by linarith
    exact_mod_cast this
  have he : {r | (n+2 : NNReal) ≤ Y r} = (∅ : Set ι) := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrB := hB (mem_image_of_mem Y (mem_univ r))
    exact (not_le_of_gt hb) (hr.trans hrB)
  rw [he, sInf_empty]
end

lemma max_coordinate_measurable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (X : Ω → Fin d → NNReal) (hm : Measurable X) :
    Measurable (fun ω => Finset.univ.sup (X ω)) := by
  classical
  have hs (s : Finset (Fin d)) : Measurable (fun ω => s.sup (X ω)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sup_empty]
      exact measurable_const
    | @insert j s hj ih =>
      simp only [Finset.sup_insert]
      convert ((measurable_pi_apply j).comp hm).sup ih using 1
      ext ω
      rfl
  exact hs _
lemma max_coordinate_continuous {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (ω : Ω)
    (hc : ∀ j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) :
    Continuous (fun s : Icc (0 : ℝ) T => Finset.univ.sup (X s.val ω)) :=
  Continuous.finset_sup_apply (fun j _ => (hc j).subtype_mk _)
lemma localizer_stopping {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) (n : ℕ) :
    IsStoppingTime (filt0152 F T) (fun ω => (σ01521 T X n ω : WithTop (Icc (0 : ℝ) T))) := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  exact continuous_hitting_stopping (filt0152 F T)
    (fun s ω => Finset.univ.sup (X s.val ω))
    (fun s => max_coordinate_measurable (mΩ := F s.val) _ (hm s.val s.property))
    (fun ω => max_coordinate_continuous T X ω (hc ω)) (n+2)
lemma localizer_eventually {d : ℕ} {Ω : Type} (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ))) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, σ01521 T X n ω = ⟨T, T.coe_nonneg, le_rfl⟩ := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  exact continuous_hitting_eventually_top _ (max_coordinate_continuous T X ω (hc ω))
lemma localizer_monotone {d : ℕ} {Ω : Type} (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (ω : Ω) : Monotone (fun n => σ01521 T X n ω) := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  intro n m hnm
  apply sInf_le_sInf
  intro s hs
  exact (show (n+2 : NNReal) ≤ m+2 by exact_mod_cast Nat.add_le_add_right hnm 2).trans hs
lemma localizer_coordinate_bound {d : ℕ} {Ω : Type} (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (ω : Ω) (h0 : ∀ j, X 0 ω j ≤ 1) (n : ℕ) (s : Icc (0 : ℝ) T)
    (hs : s ≤ σ01521 T X n ω) (j : Fin d) : X s.val ω j ≤ n+2 := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  have hmax : Finset.univ.sup (X s.val ω) ≤ (n+2 : NNReal) :=
    continuous_hitting_bound _ (max_coordinate_continuous T X ω (hc ω)) (n+2)
      (Finset.sup_le_iff.mpr (fun j _ => (h0 j).trans (by exact_mod_cast (show (1 : ℕ) ≤ n+2 by omega)))) s hs
  exact (Finset.le_sup (Finset.mem_univ j)).trans hmax
lemma q0152_bounds (α T l s : ℝ) (hl : 0 ≤ l) (hs : s ≤ T) :
    0 ≤ q0152 α T l s ∧ q0152 α T l s ≤ l := by
  have h : 0 ≤ α^2*(T-s)/2*l := by positivity
  have hd : 0 < 1+α^2*(T-s)/2*l := by linarith
  constructor
  · exact div_nonneg hl hd.le
  · apply (div_le_iff₀ hd).mpr
    nlinarith

lemma localizer_integrand_bound {d : ℕ} {Ω : Type} (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (ω : Ω) (h0 : ∀ j, X 0 ω j ≤ 1) (n : ℕ) (α l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j)
    (s : Icc (0 : ℝ) T) (j : Fin d) :
    0 ≤ (if s ≤ σ01521 T X n ω then
      (M0152 α l T X s.val ω)^2*(q0152 (α j) T (l j) s.val)^2*(α j)^2*X s.val ω j else 0) ∧
    (if s ≤ σ01521 T X n ω then
      (M0152 α l T X s.val ω)^2*(q0152 (α j) T (l j) s.val)^2*(α j)^2*X s.val ω j else 0)
      ≤ (l j)^2*(α j)^2*(n+2) := by
  constructor
  · split_ifs <;> positivity
  · split_ifs with hs
    · have hM := E0152_bounds α l T s.val (fun j => (X s.val ω j : ℝ)) hl s.property.2
        (fun j => (X s.val ω j).coe_nonneg)
      have hq := q0152_bounds (α j) T (l j) s.val (hl j) s.property.2
      have hX : (X s.val ω j : ℝ) ≤ n+2 := by
        exact_mod_cast localizer_coordinate_bound T X hc ω h0 n s hs j
      calc
        _ ≤ 1^2*(l j)^2*(α j)^2*(n+2) := by
          gcongr
          · exact hM.1.le
          · exact hM.2
          · exact hq.1
          · exact hq.2
        _ = _ := by ring
    · positivity

lemma localizer_integrand_measurable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (n : ℕ) (α l : Fin d → ℝ) (j : Fin d) :
    Measurable (Function.uncurry (B01522 T X n α l j)) := by
  classical
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let c : ℝ → Icc (0 : ℝ) T := fun s =>
    ⟨min (T : ℝ) (max 0 s), le_min T.coe_nonneg (le_max_left _ _), min_le_left _ _⟩
  have hcc : Continuous c := by
    apply Continuous.subtype_mk
    fun_prop
  have hZ (k : Fin d) : Measurable (fun p : ℝ × Ω => (X (c p.1).val p.2 k : ℝ)) := by
    apply StronglyMeasurable.measurable
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun s ω => (X (c s).val ω k : ℝ))
    · exact fun ω => (hc ω k).comp hcc
    · intro s
      exact (((measurable_pi_apply k).comp (hm (c s).val (c s).property)).subtype_val.mono
        (F.le _) le_rfl).stronglyMeasurable
  have hσ : Measurable (fun ω => (σ01521 T X n ω).val) := by
    have h := (localizer_stopping F T X hm hc n).measurable'.untopA.subtype_val
    simpa using h
  have hset : MeasurableSet {p : ℝ × Ω | p.1 ∈ Icc (0 : ℝ) (σ01521 T X n p.2).val} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hσ.comp measurable_snd))
  have hq (k : Fin d) : Measurable (fun p : ℝ × Ω => q0152 (α k) T (l k) p.1) := by
    unfold q0152
    fun_prop
  have hE : Measurable (fun p : ℝ × Ω =>
      Real.exp (-∑ k, q0152 (α k) T (l k) p.1 * (X (c p.1).val p.2 k : ℝ))) := by
    exact (Finset.measurable_sum _ (fun k _ => (hq k).mul (hZ k))).neg.exp
  have hB : Measurable (fun p : ℝ × Ω =>
      if p.1 ∈ Icc (0 : ℝ) (σ01521 T X n p.2).val then
        Real.exp (-∑ k, q0152 (α k) T (l k) p.1 * (X (c p.1).val p.2 k : ℝ)) *
          q0152 (α j) T (l j) p.1 * α j * Real.sqrt (X (c p.1).val p.2 j) else 0) :=
    (((hE.mul (hq j)).mul (measurable_const (a := α j))).mul (hZ j).sqrt).ite hset measurable_const
  convert hB using 1
  ext p
  dsimp [Function.uncurry, B01522]
  split_ifs with hs
  · have hcl : (c p.1).val = p.1 := by
      simp only [c, max_eq_right hs.1, min_eq_right (hs.2.trans (σ01521 T X n p.2).property.2)]
    simp only [hcl, M0152, E0152]
  · rfl

lemma localizer_integrand_square {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (s : Icc (0 : ℝ) T) (ω : Ω) :
    (B01522 T X n α l j s.val ω)^2 =
      if s ≤ σ01521 T X n ω then
        (M0152 α l T X s.val ω)^2*(q0152 (α j) T (l j) s.val)^2*(α j)^2*X s.val ω j
      else 0 := by
  simp only [B01522, mem_Icc, s.property.1, true_and, ← Subtype.coe_le_coe]
  split_ifs with h
  · rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (X s.val ω j).coe_nonneg]
  · norm_num

lemma localizer_integrand_integrable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (T : NNReal) (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) :
    Integrable (fun p : ℝ × Ω => (B01522 T X n α l j p.1 p.2)^2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod μ) ∧
    (∫ ω, ∫ s in Icc (0 : ℝ) T, (B01522 T X n α l j s ω)^2 ∂volume ∂μ)
      ≤ T * ((l j)^2*(α j)^2*(n+2)) := by
  let ν := volume.restrict (Icc (0 : ℝ) T)
  let C := (l j)^2*(α j)^2*(n+2 : ℝ)
  have hmeas := (localizer_integrand_measurable F T X hm hc n α l j).pow_const 2
  have hb : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, (B01522 T X n α l j p.1 p.2)^2 ≤ C := by
    have ht : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, p.1 ∈ Icc (0 : ℝ) T :=
      Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Icc)
    have hx : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, ∀ k, X 0 p.2 k ≤ 1 :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually h0
    filter_upwards [ht, hx] with p hp hx
    rw [localizer_integrand_square T X n α l j ⟨p.1, hp⟩ p.2]
    exact (localizer_integrand_bound T X hc p.2 hx n α l hl ⟨p.1, hp⟩ j).2
  have hi : Integrable (fun p : ℝ × Ω => (B01522 T X n α l j p.1 p.2)^2) (ν.prod μ) :=
    (integrable_const C).mono' hmeas.aestronglyMeasurable (by
      filter_upwards [hb] with p hp
      simpa only [Real.norm_eq_abs, abs_sq] using hp)
  refine ⟨hi, ?_⟩
  rw [← integral_integral_swap hi, ← integral_prod _ hi]
  have hbint := integral_mono_ae hi (integrable_const C) hb
  simpa [ν, C, measureReal_def, Measure.prod_apply, Real.volume_Icc, T.coe_nonneg, ENNReal.toReal_ofReal,
    mul_comm] using hbint

lemma stopped_integrand_integrability : stoppedIntegrandIntegrabilityStatement := by
  intro d Ω mΩ μ hprob F T X α l hm hc h0 hl n
  let := hprob
  have hmB (j) := localizer_integrand_measurable F T X hm hc n α l j
  have hiB (j) := localizer_integrand_integrable μ F T X α l hm hc h0 hl n j
  refine ⟨fun j => ⟨hmB j, (memLp_two_iff_integrable_sq (hmB j).aestronglyMeasurable).mpr
    (hiB j).1, (hiB j).1.integral_prod_right⟩, ?_, ?_⟩
  · exact integral_nonneg (fun ω => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun s => sq_nonneg _)))
  · rw [integral_finsetSum _ (fun j _ => (hiB j).1.integral_prod_right)]
    calc
      _ ≤ ∑ j, (T : ℝ) * ((l j)^2*(α j)^2*(n+2)) :=
        Finset.sum_le_sum (fun j _ => (hiB j).2)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

lemma r01522_zero (T : NNReal) (n : ℕ) : (r01522 T n 0).val = 0 := by
  simp [r01522, T.coe_nonneg]

lemma r01522_cell (T : NNReal) (n k : ℕ) (s : Icc (0 : ℝ) T) :
    s ∈ Ioc (r01522 T n k) (r01522 T n (k+1)) ↔
      0 < s.val ∧ Nat.ceil (s.val*(n+1)) = k+1 := by
  have hn : (0 : ℝ) < n+1 := by positivity
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
  change (min (T : ℝ) ((k : ℝ)/(n+1)) < s.val ∧
    s.val ≤ min (T : ℝ) (((k+1 : ℕ) : ℝ)/(n+1))) ↔ _
  simp only [Nat.succ_sub_one, Nat.cast_succ]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hk : (k : ℝ)/(n+1) < s.val := by
      rcases min_lt_iff.mp hlo with h | h
      · exact False.elim ((not_lt_of_ge s.property.2) h)
      · exact h
    exact ⟨lt_of_le_of_lt (by positivity) hk, (div_lt_iff₀ hn).mp hk,
      (le_div_iff₀ hn).mp (hhi.trans (min_le_right _ _))⟩
  · rintro ⟨_, hlo, hhi⟩
    exact ⟨lt_of_le_of_lt (min_le_right _ _) ((div_lt_iff₀ hn).mpr hlo),
      le_min s.property.2 ((le_div_iff₀ hn).mpr hhi)⟩

lemma r01522_sample_bounds (T : NNReal) (n : ℕ) (s : Icc (0 : ℝ) T) :
    s.val-1/(n+1) ≤ (r01522 T n (Nat.ceil (s.val*(n+1))-1)).val ∧
      (r01522 T n (Nat.ceil (s.val*(n+1))-1)).val ≤ s.val := by
  have hn : (0 : ℝ) < n+1 := by positivity
  by_cases hs : s.val = 0
  · simp [hs, r01522_zero, hn.le]
  · have hspos : 0 < s.val := lt_of_le_of_ne s.property.1 (Ne.symm hs)
    have hc : 1 ≤ Nat.ceil (s.val*(n+1)) := Nat.one_le_ceil_iff.mpr (mul_pos hspos hn)
    have he : Nat.ceil (s.val*(n+1)) = (Nat.ceil (s.val*(n+1))-1)+1 := by omega
    have hcell := (r01522_cell T n _ s).mpr ⟨hspos, he⟩
    have hlo : ((Nat.ceil (s.val*(n+1))-1 : ℕ) : ℝ)/(n+1) < s.val := by
      have hx := hcell.1
      change min (T : ℝ) _ < s.val at hx
      exact (min_lt_iff.mp hx).resolve_left (not_lt_of_ge s.property.2)
    have hclamp : (r01522 T n (Nat.ceil (s.val*(n+1))-1)).val =
        ((Nat.ceil (s.val*(n+1))-1 : ℕ) : ℝ)/(n+1) :=
      min_eq_right (hlo.le.trans s.property.2)
    rw [hclamp]
    refine ⟨?_, hlo.le⟩
    have hceil := Nat.le_ceil (s.val*(n+1))
    rw [he, Nat.cast_add, Nat.cast_one] at hceil
    apply (le_div_iff₀ hn).mpr
    have hdiv : (1/(n+1 : ℝ))*(n+1) = 1 := div_mul_cancel₀ _ hn.ne'
    nlinarith

lemma r01522_sample_tendsto (T : NNReal) (s : Icc (0 : ℝ) T) :
    Tendsto (fun n => r01522 T n (Nat.ceil (s.val*(n+1))-1)) atTop (𝓝 s) := by
  apply tendsto_subtype_rng.mpr
  have hlo : Tendsto (fun n : ℕ => s.val-1/(n+1)) atTop (𝓝 s.val) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => (r01522_sample_bounds T n s).1) (fun n => (r01522_sample_bounds T n s).2)

lemma predictable_mesh {Ω : Type} [mΩ : MeasurableSpace Ω] (T : NNReal)
    (F : Filtration (Icc (0 : ℝ) T) mΩ) (Y : Icc (0 : ℝ) T → Ω → ℝ)
    (hm : ∀ s, Measurable[F s] (Y s)) (n : ℕ) :
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    Measurable[F.predictable] (fun p : Icc (0 : ℝ) T × Ω =>
      Y (r01522 T n (Nat.ceil (p.1.val*(n+1))-1)) p.2) := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  change Measurable[F.predictable] (fun p : Icc (0 : ℝ) T × Ω =>
    Y (r01522 T n (Nat.ceil (p.1.val*(n+1))-1)) p.2)
  intro U hU
  have he : (fun p : Icc (0 : ℝ) T × Ω =>
      Y (r01522 T n (Nat.ceil (p.1.val*(n+1))-1)) p.2) ⁻¹' U =
      ({⊥} ×ˢ (Y ⊥ ⁻¹' U)) ∪ ⋃ k : ℕ,
        (Ioc (r01522 T n k) (r01522 T n (k+1)) ×ˢ (Y (r01522 T n k) ⁻¹' U)) := by
    ext p
    simp only [mem_preimage, mem_union, mem_prod, mem_singleton_iff, mem_iUnion]
    by_cases hs : p.1.val = 0
    · have hsbot : p.1 = ⊥ := Subtype.ext hs
      have hg : r01522 T n 0 = ⊥ := Subtype.ext (r01522_zero T n)
      have hsample : r01522 T n (Nat.ceil (p.1.val*(n+1))-1) = ⊥ := by
        simp only [hs, zero_mul, Nat.ceil_zero, Nat.zero_sub, hg]
      rw [hsample]
      simp only [hsbot, true_and]
      constructor
      · exact Or.inl
      · rintro (h | ⟨k, hk, _⟩)
        · exact h
        · exact False.elim (not_lt_of_ge bot_le hk.1)
    · have hspos : 0 < p.1.val := lt_of_le_of_ne p.1.property.1 (Ne.symm hs)
      have hsbot : p.1 ≠ ⊥ := fun h => hs (congrArg Subtype.val h)
      simp only [hsbot, false_and, false_or]
      constructor
      · intro h
        have hc : 1 ≤ Nat.ceil (p.1.val*(n+1)) := Nat.one_le_ceil_iff.mpr (by positivity)
        refine ⟨Nat.ceil (p.1.val*(n+1))-1, (r01522_cell T n _ p.1).mpr ⟨hspos, by omega⟩, h⟩
      · rintro ⟨k, hk, h⟩
        have hc := ((r01522_cell T n k p.1).mp hk).2
        simpa only [hc, Nat.add_sub_cancel] using h
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod (hm ⊥ hU)).union
    (MeasurableSet.iUnion fun k => measurableSet_predictable_Ioc_prod _ _ (hm (r01522 T n k) hU))

lemma continuous_adapted_predictable {Ω : Type} [mΩ : MeasurableSpace Ω] (T : NNReal)
    (F : Filtration (Icc (0 : ℝ) T) mΩ) (Y : Icc (0 : ℝ) T → Ω → ℝ)
    (hm : ∀ s, Measurable[F s] (Y s)) (hc : ∀ ω, Continuous (fun s => Y s ω)) :
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    IsStronglyPredictable F Y := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let : MeasurableSpace (Icc (0 : ℝ) T × Ω) := F.predictable
  exact (measurable_of_tendsto_metrizable (predictable_mesh T F Y hm)
    (tendsto_pi_nhds.mpr (fun p => ((hc p.2).tendsto p.1).comp
      (r01522_sample_tendsto T p.1)))).stronglyMeasurable

lemma stopping_interval_predictable {Ω ι : Type} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [DenselyOrdered ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (F : Filtration ι mΩ)
    (σ : Ω → ι) (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ι))) :
    MeasurableSet[F.predictable] {p : ι × Ω | p.1 ≤ σ p.2} := by
  obtain ⟨D, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ι
  have : Countable D := hcount.to_subtype
  have he : {p : ι × Ω | σ p.2 < p.1} =
      ⋃ r : D, Ioi r.val ×ˢ {ω | σ ω ≤ r.val} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · intro h
      obtain ⟨r, hr, hsr, hrt⟩ := hdense.exists_between h
      exact ⟨⟨r, hr⟩, hrt, hsr.le⟩
    · rintro ⟨r, hrt, hsr⟩
      exact hsr.trans_lt hrt
  have hm : MeasurableSet[F.predictable] {p : ι × Ω | σ p.2 < p.1} := by
    rw [he]
    apply MeasurableSet.iUnion
    intro r
    apply measurableSet_predictable_Ioi_prod
    simpa only [WithTop.coe_le_coe] using hσ.measurableSet_le r.val
  simpa only [compl_ofPred, not_lt] using hm.compl

lemma stopped_integrand_predictable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) :
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    IsStronglyPredictable (filt0152 F T) (fun s ω => B01522 T X n α l j s.val ω) := by
  classical
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let Y := fun (s : Icc (0 : ℝ) T) ω =>
    M0152 α l T X s.val ω * q0152 (α j) T (l j) s.val * α j * Real.sqrt (X s.val ω j)
  have hY : IsStronglyPredictable (filt0152 F T) Y := by
    apply continuous_adapted_predictable T
    · intro s
      have hx (k : Fin d) : Measurable[F s.val] (fun ω => (X s.val ω k : ℝ)) :=
        ((measurable_pi_apply k).comp (hm s.val s.property)).subtype_val
      change Measurable[F s.val] (Y s)
      dsimp [Y, M0152, E0152]
      fun_prop
    · intro ω
      have hq (k : Fin d) : Continuous (fun s : Icc (0 : ℝ) T => q0152 (α k) T (l k) s.val) := by
        apply continuous_iff_continuousAt.mpr
        intro s
        exact (q0152_derivative (α k) T (l k) s.val (hl k) s.property.2).continuousAt.comp
          continuous_subtype_val.continuousAt
      dsimp [Y, M0152, E0152]
      fun_prop
  have hset := stopping_interval_predictable (filt0152 F T) (σ01521 T X n)
    (localizer_stopping F T X hm hc n)
  have hB : Measurable[(filt0152 F T).predictable] (fun p : Icc (0 : ℝ) T × Ω =>
      if p.1 ≤ σ01521 T X n p.2 then Y p.1 p.2 else 0) :=
    hY.measurable.ite hset measurable_const
  apply Measurable.stronglyMeasurable
  convert hB using 1
  ext p
  simp only [Function.uncurry, B01522, mem_Icc, p.1.property.1, true_and, ← Subtype.coe_le_coe, Y]

lemma gaussian_multiplier {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (D H : Ω → ℝ) (v : NNReal) (hD : Measurable[mΩ] D) (hlaw : HasLaw D (gaussianReal 0 v) μ)
    (hind : Indep G (MeasurableSpace.comap D inferInstance) μ)
    (hH : Measurable[G] H) (hH2 : MemLp H 2 μ) :
    MemLp (H*D) 2 μ ∧ μ[H*D | G] =ᵐ[μ] 0 ∧
      μ[fun ω => (H ω*D ω)^2 | G] =ᵐ[μ] fun ω => (v : ℝ)*H ω^2 := by
  have hD2 : MemLp D 2 μ := hlaw.memLp (memLp_id_gaussianReal 2)
  have hInd : IndepFun H D μ := indep_of_indep_of_le_left hind hH.comap_le
  have hInd2 : IndepFun (fun ω => H ω^2) (fun ω => D ω^2) μ :=
    hInd.comp (by fun_prop : Measurable (fun x : ℝ => x^2)) (by fun_prop : Measurable (fun x : ℝ => x^2))
  have hiprod := hInd.integrable_mul (hH2.integrable (by norm_num)) (hD2.integrable (by norm_num))
  have hisq := hInd2.integrable_mul hH2.integrable_sq hD2.integrable_sq
  have hmul2 : MemLp (H*D) 2 μ := (memLp_two_iff_integrable_sq
    ((hH.mono hG le_rfl).mul hD).aestronglyMeasurable).mpr (by
      simpa only [Pi.mul_def, mul_pow] using hisq)
  have hmD : Measurable[MeasurableSpace.comap D inferInstance] D :=
    measurable_iff_comap_le.mpr le_rfl
  have hmean : (∫ ω, D ω ∂μ) = 0 := by rw [hlaw.integral_eq]; exact integral_id_gaussianReal
  have hsecond : (∫ ω, D ω^2 ∂μ) = v := by
    have hv := hlaw.variance_eq
    rw [variance_eq_integral hD.aemeasurable, hmean] at hv
    simpa using hv
  have hce := condExp_indep_eq hD.comap_le hG hmD.stronglyMeasurable hind.symm
  have hce2 := condExp_indep_eq hD.comap_le hG (hmD.pow_const 2).stronglyMeasurable hind.symm
  rw [hmean] at hce
  rw [hsecond] at hce2
  refine ⟨hmul2, ?_, ?_⟩
  · have hp := condExp_mul_of_stronglyMeasurable_left hH.stronglyMeasurable hiprod
      (hD2.integrable (by norm_num))
    filter_upwards [hp, hce] with ω hp hc
    simpa only [Pi.mul_apply, hc, mul_zero, Pi.zero_apply] using hp
  · have hp := condExp_mul_of_stronglyMeasurable_left (hH.pow_const 2).stronglyMeasurable hisq hD2.integrable_sq
    have he : (fun ω => (H ω*D ω)^2) = (fun ω => H ω^2)*(fun ω => D ω^2) := by
      funext ω; exact mul_pow _ _ _
    rw [he]
    filter_upwards [hp, hce2] with ω hp hc
    simpa only [Pi.mul_apply, hc, mul_comm] using hp

lemma elementary_brownian_interval {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (a b : NNReal) (hab : a ≤ b) (H : Ω → ℝ) (hH : Measurable[F a] H) (hH2 : MemLp H 2 μ) :
    MemLp (J01522 B H a b) 2 μ ∧ μ[J01522 B H a b | F a] =ᵐ[μ] 0 ∧
      μ[fun ω => (J01522 B H a b ω)^2 | F a] =ᵐ[μ] fun ω => ((b : ℝ)-a)*H ω^2 := by
  have hD := ((hm b).mono (F.le b) le_rfl).sub ((hm a).mono (F.le a) le_rfl)
  have h := gaussian_multiplier (mΩ := mΩ) μ (F a) (F.le a) (fun ω => B b ω-B a ω) H (nndist (b : ℝ) a)
    hD (hB.toIsPreBrownianReal.hasLaw_sub b a) (hind a b hab) hH hH2
  unfold J01522
  simpa only [Pi.mul_def, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))] using h

lemma elementary_brownian_integral : elementaryBrownianIntegralStatement := by
  intro Ω mΩ μ hμ F B hB hm hind N t H ht hH hH2
  let := hμ
  let J := fun i : Fin N => J01522 B (H i) (t i.castSucc) (t i.succ)
  have hstep := fun i : Fin N => elementary_brownian_interval μ F B hB hm hind
    (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i)) (H i) (hH i) (hH2 i)
  have hJ2 : ∀ i, MemLp (J i) 2 μ := fun i => (hstep i).1
  have hJi : ∀ i, Integrable (J i) μ := fun i => (hJ2 i).integrable one_le_two
  have hprod : ∀ i j, Integrable (fun ω => J i ω * J j ω) μ :=
    fun i j => (hJ2 i).integrable_mul (hJ2 j)
  have hJm : ∀ i, Measurable[F (t i.succ)] (J i) := by
    intro i
    exact ((hH i).mono (F.mono (ht (Fin.castSucc_le_succ i))) le_rfl).mul
      ((hm _).sub ((hm _).mono (F.mono (ht (Fin.castSucc_le_succ i))) le_rfl))
  have horth : ∀ i j, i < j → (∫ ω, J i ω * J j ω ∂μ) = 0 := by
    intro i j hij
    have hmeas := (hJm i).mono (F.mono (ht (Fin.succ_le_castSucc_iff.mpr hij))) le_rfl
    have hp := condExp_mul_of_stronglyMeasurable_left hmeas.stronglyMeasurable
      (hprod i j) (hJi j)
    have hz : μ[J i * J j | F (t j.castSucc)] =ᵐ[μ] 0 := by
      filter_upwards [hp, (hstep j).2.1] with ω hp hz
      change μ[J j | F (t j.castSucc)] ω = 0 at hz
      simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hp
    calc
      _ = ∫ ω, μ[J i * J j | F (t j.castSucc)] ω ∂μ := (integral_condExp (F.le _)).symm
      _ = 0 := by rw [integral_congr_ae hz]; simp
  have hdiag : ∀ i, (∫ ω, J i ω * J i ω ∂μ) =
      ((t i.succ : ℝ)-t i.castSucc) * ∫ ω, (H i ω)^2 ∂μ := by
    intro i
    calc
      _ = ∫ ω, μ[fun ω => (J i ω)^2 | F (t i.castSucc)] ω ∂μ := by
        rw [integral_condExp (F.le _)]; simp only [pow_two]
      _ = _ := by rw [integral_congr_ae (hstep i).2.2, integral_const_mul]
  refine ⟨hstep, horth, ?_, ?_, ?_⟩
  · exact memLp_finsetSum _ (fun i _ => hJ2 i)
  · have hz : ∀ i, μ[J i | F (t 0)] =ᵐ[μ] 0 := by
      intro i
      have hle := F.mono (ht (Fin.zero_le i.castSucc))
      have htower := condExp_condExp_of_le (μ := μ) (f := J i) hle (F.le _)
      have hc := condExp_congr_ae (m := F (t 0)) (hstep i).2.1
      exact htower.symm.trans (hc.trans (by simp))
    have hc := condExp_finsetSum (s := Finset.univ) (fun i _ => hJi i) (F (t 0))
    have hzall := ae_all_iff.mpr hz
    filter_upwards [hc, hzall] with ω hc hz
    change μ[(fun ω => ∑ i, J i ω) | F (t 0)] ω = 0
    have he : (∑ i, J i) = (fun ω => ∑ i, J i ω) := by ext ω; simp
    rw [← he]
    simpa only [Finset.sum_apply, hz, Pi.zero_apply, Finset.sum_const_zero] using hc
  · calc
      _ = ∫ ω, ∑ i, ∑ j, J i ω * J j ω ∂μ := by
        congr 1; funext ω; simp only [S01522, J, pow_two, Finset.sum_mul_sum]
      _ = ∑ i, ∑ j, ∫ ω, J i ω * J j ω ∂μ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => hprod i j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · exact hdiag i
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · simpa only [mul_comm] using horth j i hlt
          · exact horth i j hgt
        · simp

lemma elementary_process_measurable {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ) (hm : ∀ t, Measurable[F t] (B t))
    (H : Ω → ℝ) (a b : NNReal) (hab : a ≤ b) (hH : Measurable[F a] H) (s : NNReal) :
    Measurable[F s] (P01522 B H a b s) := by
  by_cases has : a ≤ s
  · unfold P01522 J01522
    rw [min_eq_right has]
    exact ((hH.mono (F.mono has) le_rfl).mul
      (((hm _).mono (F.mono (min_le_left _ _)) le_rfl).sub
        ((hm _).mono (F.mono has) le_rfl)))
  · have hs := le_of_not_ge has
    have he : P01522 B H a b s = 0 := by
      ext ω
      simp [P01522, J01522, min_eq_left hs, min_eq_left (hs.trans hab)]
    rw [he]
    exact measurable_const

lemma elementary_process_condExp {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (H : Ω → ℝ) (a b : NNReal) (hab : a ≤ b) (hH : Measurable[F a] H) (hH2 : MemLp H 2 μ)
    (s : NNReal) : μ[J01522 B H a b | F s] =ᵐ[μ] P01522 B H a b s := by
  have hwhole := elementary_brownian_interval μ F B hB hm hind a b hab H hH hH2
  by_cases hbs : b ≤ s
  · have he : P01522 B H a b s = J01522 B H a b := by
      simp [P01522, min_eq_right hbs, min_eq_right (hab.trans hbs)]
    rw [he]
    have hmJ := elementary_process_measurable F B hm H a b hab hH s
    rw [he] at hmJ
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (F.le s)
      hmJ.stronglyMeasurable (hwhole.1.integrable one_le_two))
  · have hsb := le_of_not_ge hbs
    by_cases has : a ≤ s
    · have hleft := elementary_brownian_interval μ F B hB hm hind a s has H hH hH2
      have hright := elementary_brownian_interval μ F B hB hm hind s b hsb H
        (hH.mono (F.mono has) le_rfl) hH2
      have he : J01522 B H a b = J01522 B H a s + J01522 B H s b := by
        ext ω; simp only [J01522, Pi.add_apply]; ring
      have hmL : Measurable[F s] (J01522 B H a s) :=
        (hH.mono (F.mono has) le_rfl).mul ((hm s).sub ((hm a).mono (F.mono has) le_rfl))
      rw [he]
      have hc := condExp_add (hleft.1.integrable one_le_two) (hright.1.integrable one_le_two) (F s)
      rw [condExp_of_stronglyMeasurable (F.le s) hmL.stronglyMeasurable
        (hleft.1.integrable one_le_two)] at hc
      filter_upwards [hc, hright.2.1] with ω hc hz
      simpa only [P01522, min_eq_right has, min_eq_left hsb, Pi.add_apply, hz,
        Pi.zero_apply, add_zero] using hc
    · have hsa := le_of_not_ge has
      have he : P01522 B H a b s = 0 := by
        ext ω; simp [P01522, J01522, min_eq_left hsa, min_eq_left hsb]
      rw [he]
      have htower := condExp_condExp_of_le (μ := μ) (f := J01522 B H a b)
        (F.mono hsa) (F.le a)
      have hc := condExp_congr_ae (m := F s) hwhole.2.1
      exact htower.symm.trans (hc.trans (by simp))

lemma elementary_brownian_process : elementaryBrownianProcessStatement := by
  intro Ω mΩ μ hμ F B hB hm hind N t H ht hH hH2
  let := hμ
  have hab := fun i : Fin N => ht (Fin.castSucc_le_succ i)
  have hJ2 := fun i : Fin N => (elementary_brownian_interval μ F B hB hm hind
    (t i.castSucc) (t i.succ) (hab i) (H i) (hH i) (hH2 i)).1
  have hRm : ∀ s, Measurable[F s] (R01522 B H t s) := fun s =>
    Finset.measurable_sum _ (fun i _ => elementary_process_measurable F B hm
      (H i) (t i.castSucc) (t i.succ) (hab i) (hH i) s)
  have hce : ∀ s, μ[S01522 B H t | F s] =ᵐ[μ] R01522 B H t s := by
    intro s
    have hc := condExp_finsetSum (s := Finset.univ)
      (fun i _ => (hJ2 i).integrable one_le_two) (F s)
    have hs := ae_all_iff.mpr (fun i => elementary_process_condExp μ F B hB hm hind
      (H i) (t i.castSucc) (t i.succ) (hab i) (hH i) (hH2 i) s)
    have he : S01522 B H t = ∑ i, J01522 B (H i) (t i.castSucc) (t i.succ) := by
      ext ω; simp [S01522]
    rw [he]
    filter_upwards [hc, hs] with ω hc hs
    simpa only [R01522, Finset.sum_apply, hs] using hc
  have hmart := (martingale_condExp (S01522 B H t) F μ).congr
    (fun s => (hRm s).stronglyMeasurable) hce
  refine ⟨hmart, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hB.cont] with ω hcont
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((hcont.comp (continuous_id.min continuous_const)).sub
      (hcont.comp (continuous_id.min continuous_const)))
  · intro s
    classical
    let ts := fun i : Fin (N+1) => min s (t i)
    let Hs := fun i : Fin N => if t i.castSucc ≤ s then H i else 0
    have hts : Monotone ts := fun i j hij => min_le_min_left s (ht hij)
    have hHs : ∀ i, Measurable[F (ts i.castSucc)] (Hs i) := by
      intro i
      dsimp [Hs, ts]
      split_ifs with hi
      · change Measurable[F (min s (t i.castSucc))] (H i)
        convert hH i using 1
        rw [min_eq_right hi]
      · exact measurable_const
    have hHs2 : ∀ i, MemLp (Hs i) 2 μ := by
      intro i
      dsimp [Hs]
      split_ifs
      · exact hH2 i
      · exact MemLp.zero
    have he : R01522 B H t s = S01522 B Hs ts := by
      ext ω
      apply Finset.sum_congr rfl
      intro i _
      dsimp [Hs, ts, P01522, J01522]
      split_ifs with hi
      · rfl
      · have hsi := le_of_not_ge hi
        simp [min_eq_left hsi, min_eq_left (hsi.trans (hab i))]
    have hsum := elementary_brownian_integral Ω mΩ μ hμ F B hB hm hind N ts Hs hts hHs hHs2
    refine ⟨he ▸ hsum.2.2.1, hce s, ?_⟩
    rw [he, hsum.2.2.2.2]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [Hs, ts]
    split_ifs with hi
    · rfl
    · have hsi := le_of_not_ge hi
      have hsreal : (s : ℝ) ≤ t i.succ := hsi.trans (hab i)
      simp [min_eq_left hsi, min_eq_left (hsi.trans (hab i)), min_eq_left hsreal]
  · intro s hs
    ext ω
    apply Finset.sum_eq_zero
    intro i _
    have hsa := hs.trans (ht (Fin.zero_le i.castSucc))
    simp [P01522, J01522, min_eq_left hsa, min_eq_left (hsa.trans (hab i))]
  · intro s hs
    ext ω
    apply Finset.sum_congr rfl
    intro i _
    have hbs := (ht (Fin.le_last i.succ)).trans hs
    simp [P01522, min_eq_right hbs, min_eq_right ((hab i).trans hbs)]

lemma elementary_brownian_limit : elementaryBrownianLimitStatement := by
  intro Ω mΩ μ hμ F B hB hm hind N t H ht hH hH2 X hX hC
  let := hμ
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hC
  have hR : ∀ n s, μ[(X n : Ω → ℝ) | F s] =ᵐ[μ] R01522 B (H n) (t n) s := by
    intro n s
    have hp := elementary_brownian_process Ω mΩ μ hμ F B hB hm hind
      (N n) (t n) (H n) (ht n) (hH n) (hH2 n)
    exact (condExp_congr_ae (hX n)).trans (hp.2.2.1 s).2.1
  have hbound : ∀ n s,
      eLpNorm (R01522 B (H n) (t n) s - μ[(Z : Ω → ℝ) | F s]) 2 μ ≤ edist (X n) Z := by
    intro n s
    have hc := condExp_sub ((Lp.memLp (X n)).integrable one_le_two) ((Lp.memLp Z).integrable one_le_two) (F s)
    have he : μ[((X n : Ω → ℝ) - (Z : Ω → ℝ)) | F s] =ᵐ[μ]
        R01522 B (H n) (t n) s - μ[(Z : Ω → ℝ) | F s] :=
      hc.trans ((hR n s).sub (Filter.EventuallyEq.refl _ _))
    rw [← eLpNorm_congr_ae he, Lp.edist_def]
    exact eLpNorm_condExp_le_eLpNorm _ one_le_two
  have he : Tendsto (fun n => edist (X n) Z) atTop (𝓝 0) := by
    simpa using hZ.edist (tendsto_const_nhds (x := Z))
  have hzero : μ[(Z : Ω → ℝ) | F 0] =ᵐ[μ] 0 := by
    have hz : ∀ n, R01522 B (H n) (t n) 0 = 0 := fun n =>
      (elementary_brownian_process Ω mΩ μ hμ F B hB hm hind
        (N n) (t n) (H n) (ht n) (hH n) (hH2 n)).2.2.2.1 0 zero_le
    have hn : ∀ n, eLpNorm (μ[(Z : Ω → ℝ) | F 0]) 2 μ ≤ edist (X n) Z := by
      intro n
      simpa only [hz n, zero_sub, eLpNorm_neg] using hbound n 0
    apply (eLpNorm_eq_zero_iff (p := 2) (by norm_num)).mp
    exact le_antisymm (ge_of_tendsto he (Filter.Eventually.of_forall hn)) bot_le
  refine ⟨Z, hZ, martingale_condExp (Z : Ω → ℝ) F μ, hzero,
    fun s => (Lp.memLp Z).condExp one_le_two, hbound, ?_⟩
  intro ε hε
  filter_upwards [he.eventually (eventually_lt_nhds hε)] with n hn s
  exact (hbound n s).trans_lt hn

lemma stopped_integrand_sample_tendsto {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) (s : Icc (0 : ℝ) T) (ω : Ω) :
    Tendsto (fun m => D01522 T X n α l j m s.val ω) atTop
      (𝓝 (B01522 T X n α l j s.val ω)) := by
  let Y := fun s : Icc (0 : ℝ) T =>
    M0152 α l T X s.val ω * q0152 (α j) T (l j) s.val * α j * Real.sqrt (X s.val ω j)
  have hY : Continuous Y := by
    have hq (k : Fin d) : Continuous (fun s : Icc (0 : ℝ) T => q0152 (α k) T (l k) s.val) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (q0152_derivative (α k) T (l k) u.val (hl k) u.property.2).continuousAt.comp
        continuous_subtype_val.continuousAt
    dsimp [Y, M0152, E0152]
    fun_prop
  have ha : Tendsto (fun m => a01522 T m s.val) atTop (𝓝 s) := r01522_sample_tendsto T s
  by_cases hs : s.val ≤ (σ01521 T X n ω).val
  · have hm : ∀ m, (a01522 T m s.val).val ∈ Icc (0 : ℝ) (σ01521 T X n ω).val :=
      fun m => ⟨(a01522 T m s.val).property.1, (r01522_sample_bounds T m s).2.trans hs⟩
    simpa only [D01522, ite_eq_left s.property, B01522, ite_eq_left (show s.val ∈ Icc (0 : ℝ)
      (σ01521 T X n ω).val from ⟨s.property.1, hs⟩), ite_eq_left (hm _), Y, Function.comp_def] using hY.tendsto s |>.comp ha
  · have he : ∀ᶠ m in atTop, (σ01521 T X n ω).val < (a01522 T m s.val).val :=
      (continuous_subtype_val.tendsto s |>.comp ha).eventually (eventually_gt_nhds (lt_of_not_ge hs))
    have hzero : B01522 T X n α l j s.val ω = 0 := by simp [B01522, hs]
    rw [hzero]
    apply tendsto_congr' (he.mono (fun m hm => ?_)) |>.mpr tendsto_const_nhds
    simp [D01522, s.property, B01522, not_le.mpr hm]

lemma stopped_integrand_sample_measurable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (n : ℕ) (j : Fin d) (m : ℕ) :
    Measurable (Function.uncurry (D01522 T X n α l j m)) := by
  have ha : Measurable (fun s : ℝ => (a01522 T m s).val) := by
    unfold a01522 r01522
    fun_prop
  have hB := localizer_integrand_measurable F T X hm hc n α l j
  exact (hB.comp ((ha.comp measurable_fst).prodMk measurable_snd)).ite
    (measurable_fst measurableSet_Icc) measurable_const

lemma stopped_integrand_approximation : stoppedIntegrandApproximationStatement := by
  intro d Ω mΩ μ hμ F T X α l hm hc h0 hl n j
  let := hμ
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  let C : ℝ := (l j)^2*(α j)^2*(n+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBmeas := localizer_integrand_measurable F T X hm hc n α l j
  have hDmeas := stopped_integrand_sample_measurable F T X α l hm hc n j
  have hBadapt : ∀ s : Icc (0 : ℝ) T, Measurable[F s.val] (B01522 T X n α l j s.val) := by
    intro s
    exact ((stopped_integrand_predictable F T X α l hm hc hl n j).isStronglyProgressive.stronglyAdapted s).measurable
  have hBbound : ∀ ω, (∀ k, X 0 ω k ≤ 1) → ∀ s : Icc (0 : ℝ) T,
      (B01522 T X n α l j s.val ω)^2 ≤ C := by
    intro ω hω s
    rw [localizer_integrand_square]
    exact (localizer_integrand_bound T X hc ω hω n α l hl s j).2
  have hDpoint : ∀ m s ω, (∀ k, X 0 ω k ≤ 1) → (D01522 T X n α l j m s ω)^2 ≤ C := by
    intro m s ω hω
    unfold D01522
    split_ifs
    · exact hBbound ω hω (a01522 T m s)
    · simpa using hC
  have hgood : ∀ᵐ p : ℝ × Ω ∂ν, ∀ k, X 0 p.2 k ≤ 1 :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually h0
  have htime : ∀ᵐ p : ℝ × Ω ∂ν, p.1 ∈ Icc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Icc)
  have hDint : ∀ m, Integrable (fun p : ℝ × Ω => (D01522 T X n α l j m p.1 p.2)^2) ν := by
    intro m
    apply (integrable_const C).mono' ((hDmeas m).pow_const 2).aestronglyMeasurable
    filter_upwards [hgood] with p hp
    simpa only [Function.uncurry, Real.norm_eq_abs, abs_sq] using hDpoint m p.1 p.2 hp
  refine ⟨?_, ?_, ?_⟩
  · intro m
    refine ⟨?_, ?_, ?_, ?_, hDmeas m,
      (memLp_two_iff_integrable_sq (hDmeas m).aestronglyMeasurable).mpr (hDint m), ?_⟩
    · intro k r hkr
      change min (T : ℝ) ((k : ℝ)/(m+1)) ≤ min (T : ℝ) ((r : ℝ)/(m+1))
      exact min_le_min_left _ (div_le_div_of_nonneg_right (by exact_mod_cast hkr) (by positivity))
    · change min (T : ℝ) ((Nat.ceil ((T : ℝ)*(m+1)) : ℝ)/(m+1)) = T
      apply min_eq_left
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < m+1)).mpr
      exact Nat.le_ceil _
    · intro k s hs
      have hindex := ((r01522_cell T m k s).mp hs).2
      ext ω
      simp [D01522, s.property, a01522, hindex]
    · intro k
      refine ⟨hBadapt _, (memLp_two_iff_integrable_sq
        ((hBadapt _).mono (F.le _) le_rfl).aestronglyMeasurable).mpr ?_⟩
      apply (integrable_const C).mono' (((hBadapt _).mono (F.le _) le_rfl).pow_const 2).aestronglyMeasurable
      filter_upwards [h0] with ω hω
      simpa only [Real.norm_eq_abs, abs_sq] using hBbound ω hω (r01522 T m k)
    · have hp := predictable_mesh T (filt0152 F T)
        (fun s ω => B01522 T X n α l j s.val ω) hBadapt m
      apply Measurable.stronglyMeasurable
      convert hp using 1
      ext p
      simp only [Function.uncurry, D01522, ite_eq_left p.1.property, a01522]
  · intro s hs ω
    exact stopped_integrand_sample_tendsto T X α l hc hl n j ⟨s, hs⟩ ω
  · have hdom : ∀ m, ∀ᵐ p : ℝ × Ω ∂ν,
        ‖(D01522 T X n α l j m p.1 p.2 - B01522 T X n α l j p.1 p.2)^2‖ ≤ 4*C := by
      intro m
      filter_upwards [hgood, htime] with p hω hs
      have hD := hDpoint m p.1 p.2 hω
      have hB := hBbound p.2 hω ⟨p.1, hs⟩
      rw [Real.norm_eq_abs, abs_sq]
      nlinarith [sq_nonneg (D01522 T X n α l j m p.1 p.2 + B01522 T X n α l j p.1 p.2)]
    have hlim : ∀ᵐ p : ℝ × Ω ∂ν, Tendsto
        (fun m => (D01522 T X n α l j m p.1 p.2 - B01522 T X n α l j p.1 p.2)^2) atTop (𝓝 0) := by
      filter_upwards [htime] with p hp
      have h := stopped_integrand_sample_tendsto T X α l hc hl n j ⟨p.1, hp⟩ p.2
      simpa using (h.sub (tendsto_const_nhds (x := B01522 T X n α l j p.1 p.2))).pow 2
    have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => 4*C)
      (fun m => ((hDmeas m).sub hBmeas).pow_const 2 |>.aestronglyMeasurable)
      (integrable_const _) hdom hlim
    simpa only [integral_zero, Function.uncurry, Pi.sub_apply, ν] using h

lemma elementary_disjoint {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (H K : Ω → ℝ) (a b c e : NNReal) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e)
    (hH : Measurable[F a] H) (hK : Measurable[F c] K) (hH2 : MemLp H 2 μ) (hK2 : MemLp K 2 μ) :
    (∫ ω, J01522 B H a b ω * J01522 B K c e ω ∂μ) = 0 := by
  have hJ := elementary_brownian_interval μ F B hB hm hind a b hab H hH hH2
  have hL := elementary_brownian_interval μ F B hB hm hind c e hce K hK hK2
  have hmJ : Measurable[F c] (J01522 B H a b) :=
    (hH.mono (F.mono (hab.trans hbc)) le_rfl).mul
      (((hm b).mono (F.mono hbc) le_rfl).sub ((hm a).mono (F.mono (hab.trans hbc)) le_rfl))
  have hp := condExp_mul_of_stronglyMeasurable_left hmJ.stronglyMeasurable
    (hJ.1.integrable_mul hL.1) (hL.1.integrable one_le_two)
  have hz : μ[J01522 B H a b * J01522 B K c e | F c] =ᵐ[μ] 0 := by
    filter_upwards [hp, hL.2.1] with ω hp hz
    simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hp
  calc
    _ = ∫ ω, μ[J01522 B H a b * J01522 B K c e | F c] ω ∂μ := (integral_condExp (F.le c)).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

lemma elementary_same_interval {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (H K : Ω → ℝ) (a b : NNReal) (hab : a ≤ b)
    (hH : Measurable[F a] H) (hK : Measurable[F a] K) :
    (∫ ω, J01522 B H a b ω * J01522 B K a b ω ∂μ) =
      ((b : ℝ)-a) * ∫ ω, H ω*K ω ∂μ := by
  let D := fun ω => B b ω-B a ω
  have hD : Measurable[mΩ] D := ((hm b).mono (F.le b) le_rfl).sub ((hm a).mono (F.le a) le_rfl)
  have hInd : IndepFun (H*K) D μ := indep_of_indep_of_le_left (hind a b hab) (hH.mul hK).comap_le
  have hInd2 := hInd.comp measurable_id (by fun_prop : Measurable (fun x : ℝ => x^2))
  have hsecond : (∫ ω, D ω^2 ∂μ) = (b : ℝ)-a := by
    have h := (elementary_brownian_interval μ F B hB hm hind a b hab (fun _ => 1)
      measurable_const (memLp_const 1)).2.2
    have he := integral_congr_ae h
    rw [integral_condExp (F.le a)] at he
    simpa [J01522, D] using he
  calc
    _ = ∫ ω, (H ω*K ω)*D ω^2 ∂μ := by congr 1; ext ω; dsimp [J01522, D]; ring
    _ = (∫ ω, H ω*K ω ∂μ) * ∫ ω, D ω^2 ∂μ :=
      hInd2.integral_fun_mul_eq_mul_integral ((hH.mul hK).mono (F.le a) le_rfl).aestronglyMeasurable
        (hD.pow_const 2).aestronglyMeasurable
    _ = _ := by rw [hsecond, mul_comm]

lemma elementary_cross_ordered {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (H K : Ω → ℝ) (a b c e : NNReal) (hab : a ≤ b) (hce : c ≤ e) (hac : a ≤ c)
    (hH : Measurable[F a] H) (hK : Measurable[F c] K) (hH2 : MemLp H 2 μ) (hK2 : MemLp K 2 μ) :
    (∫ ω, J01522 B H a b ω * J01522 B K c e ω ∂μ) =
      max 0 ((min b e : ℝ)-c) * ∫ ω, H ω*K ω ∂μ := by
  by_cases hbc : b ≤ c
  · rw [elementary_disjoint μ F B hB hm hind H K a b c e hab hbc hce hH hK hH2 hK2]
    have hle : (min b e : ℝ) ≤ c := (min_le_left b e).trans hbc
    rw [max_eq_left (sub_nonpos.mpr hle), zero_mul]
  · have hcb := le_of_not_ge hbc
    have hHc := hH.mono (F.mono hac) le_rfl
    have hL2 := (elementary_brownian_interval μ F B hB hm hind a c hac H hH hH2).1
    have hKce2 := (elementary_brownian_interval μ F B hB hm hind c e hce K hK hK2).1
    have hleft := elementary_disjoint μ F B hB hm hind H K a c c e hac le_rfl hce hH hK hH2 hK2
    by_cases hbe : b ≤ e
    · have hHb := hH.mono (F.mono hab) le_rfl
      have hKb := hK.mono (F.mono hcb) le_rfl
      have hHcb2 := (elementary_brownian_interval μ F B hB hm hind c b hcb H hHc hH2).1
      have hKcb2 := (elementary_brownian_interval μ F B hB hm hind c b hcb K hK hK2).1
      have hKbe2 := (elementary_brownian_interval μ F B hB hm hind b e hbe K hKb hK2).1
      have hright := elementary_disjoint μ F B hB hm hind H K c b b e hcb le_rfl hbe hHc hKb hH2 hK2
      have hdiag := elementary_same_interval μ F B hB hm hind H K c b hcb hHc hK
      calc
        _ = (∫ ω, J01522 B H a c ω * J01522 B K c e ω ∂μ) +
            ((∫ ω, J01522 B H c b ω * J01522 B K c b ω ∂μ) +
              ∫ ω, J01522 B H c b ω * J01522 B K b e ω ∂μ) := by
          have hi₁ := integral_add (hHcb2.integrable_mul hKcb2) (hHcb2.integrable_mul hKbe2)
          have hi₂ := integral_add (hL2.integrable_mul hKce2)
            ((hHcb2.integrable_mul hKcb2).add (hHcb2.integrable_mul hKbe2))
          simp only [Pi.mul_apply, Pi.add_apply] at hi₁ hi₂
          rw [← hi₁, ← hi₂]
          congr 1; ext ω; simp only [J01522]; ring
        _ = _ := by rw [hleft, hright, hdiag, min_eq_left (show (b : ℝ) ≤ e from hbe),
          max_eq_right (sub_nonneg.mpr (show (c : ℝ) ≤ b from hcb))]; ring
    · have heb := le_of_not_ge hbe
      have hHe := hH.mono (F.mono (hac.trans hce)) le_rfl
      have hHce2 := (elementary_brownian_interval μ F B hB hm hind c e hce H hHc hH2).1
      have hHeb2 := (elementary_brownian_interval μ F B hB hm hind e b heb H hHe hH2).1
      have hright : (∫ ω, J01522 B H e b ω * J01522 B K c e ω ∂μ) = 0 := by
        simpa only [mul_comm] using elementary_disjoint μ F B hB hm hind K H c e e b
          hce le_rfl heb hK hHe hK2 hH2
      have hdiag := elementary_same_interval μ F B hB hm hind H K c e hce hHc hK
      calc
        _ = (∫ ω, J01522 B H a c ω * J01522 B K c e ω ∂μ) +
            ((∫ ω, J01522 B H c e ω * J01522 B K c e ω ∂μ) +
              ∫ ω, J01522 B H e b ω * J01522 B K c e ω ∂μ) := by
          have hi₁ := integral_add (hHce2.integrable_mul hKce2) (hHeb2.integrable_mul hKce2)
          have hi₂ := integral_add (hL2.integrable_mul hKce2)
            ((hHce2.integrable_mul hKce2).add (hHeb2.integrable_mul hKce2))
          simp only [Pi.mul_apply, Pi.add_apply] at hi₁ hi₂
          rw [← hi₁, ← hi₂]
          congr 1; ext ω; simp only [J01522]; ring
        _ = _ := by rw [hleft, hright, hdiag, min_eq_right (show (e : ℝ) ≤ b from heb),
          max_eq_right (sub_nonneg.mpr (show (c : ℝ) ≤ e from hce))]; ring

lemma elementary_cross {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (H K : Ω → ℝ) (a b c e : NNReal) (hab : a ≤ b) (hce : c ≤ e)
    (hH : Measurable[F a] H) (hK : Measurable[F c] K) (hH2 : MemLp H 2 μ) (hK2 : MemLp K 2 μ) :
    (∫ ω, J01522 B H a b ω * J01522 B K c e ω ∂μ) =
      max 0 ((min b e : ℝ)-max a c) * ∫ ω, H ω*K ω ∂μ := by
  rcases le_total a c with hac | hca
  · simpa only [max_eq_right hac] using elementary_cross_ordered μ F B hB hm hind H K a b c e hab hce hac hH hK hH2 hK2
  · simpa only [max_eq_left hca, min_comm (e : ℝ) (b : ℝ), mul_comm] using
      elementary_cross_ordered μ F B hB hm hind K H c e a b hce hab hca hK hH hK2 hH2

lemma interval_indicator_product (a b c e h k : ℝ) :
    (fun s => (Ioc a b).indicator (fun _ => h) s * (Ioc c e).indicator (fun _ => k) s) =
      (Ioc (max a c) (min b e)).indicator (fun _ => h*k) := by
  have hinter : Ioc (max a c) (min b e) = Ioc a b ∩ Ioc c e := by
    ext s
    simp only [mem_Ioc, mem_inter_iff, max_lt_iff, le_min_iff]
    tauto
  rw [hinter]
  ext s
  by_cases hs : s ∈ Ioc a b <;> by_cases hr : s ∈ Ioc c e <;>
    simp only [Set.indicator, mem_inter_iff, hs, hr, ite_true, ite_false,
      and_true, and_false, zero_mul, mul_zero]

lemma interval_indicator_product_integrable (a b c e h k : ℝ) :
    Integrable (fun s => (Ioc a b).indicator (fun _ => h) s *
      (Ioc c e).indicator (fun _ => k) s) volume := by
  rw [interval_indicator_product]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (μ := volume) (s := Ioc (max a c) (min b e))
      (C := h*k) (by simp [Real.volume_Ioc]))

lemma interval_indicator_product_integral (a b c e h k : ℝ) :
    (∫ s, (Ioc a b).indicator (fun _ => h) s * (Ioc c e).indicator (fun _ => k) s) =
      max 0 (min b e-max a c) * (h*k) := by
  rw [interval_indicator_product, integral_indicator_const _ measurableSet_Ioc]
  simp only [Real.volume_real_Ioc, smul_eq_mul, max_comm]

lemma step_product_integral {Ω : Type} {N M : ℕ} (H : Fin N → Ω → ℝ) (K : Fin M → Ω → ℝ)
    (t : Fin (N+1) → NNReal) (u : Fin (M+1) → NNReal) (ω : Ω) :
    Integrable (fun s => Q01522 H t s ω * Q01522 K u s ω) volume ∧
    (∫ s, Q01522 H t s ω * Q01522 K u s ω) =
      ∑ i, ∑ j, max 0 (min (t i.succ : ℝ) (u j.succ) - max (t i.castSucc : ℝ) (u j.castSucc)) *
        (H i ω * K j ω) := by
  have he : (fun s => Q01522 H t s ω * Q01522 K u s ω) = fun s =>
      ∑ i, ∑ j, (Ioc (t i.castSucc : ℝ) (t i.succ)).indicator (fun _ => H i ω) s *
        (Ioc (u j.castSucc : ℝ) (u j.succ)).indicator (fun _ => K j ω) s := by
    ext s; simp only [Q01522, Finset.sum_mul_sum]
  have hi := fun i j => interval_indicator_product_integrable
    (t i.castSucc) (t i.succ) (u j.castSucc) (u j.succ) (H i ω) (K j ω)
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact interval_indicator_product_integral _ _ _ _ _ _

lemma elementary_cross_sum {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    {N M : ℕ} (t : Fin (N+1) → NNReal) (u : Fin (M+1) → NNReal)
    (H : Fin N → Ω → ℝ) (K : Fin M → Ω → ℝ) (ht : Monotone t) (hu : Monotone u)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hK : ∀ j, Measurable[F (u j.castSucc)] (K j))
    (hH2 : ∀ i, MemLp (H i) 2 μ) (hK2 : ∀ j, MemLp (K j) 2 μ) :
    (∫ ω, S01522 B H t ω * S01522 B K u ω ∂μ) =
      ∑ i, ∑ j, max 0 (min (t i.succ : ℝ) (u j.succ) - max (t i.castSucc : ℝ) (u j.castSucc)) *
        ∫ ω, H i ω * K j ω ∂μ := by
  have hJ := fun i => (elementary_brownian_interval μ F B hB hm hind
    (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i)) (H i) (hH i) (hH2 i)).1
  have hL := fun j => (elementary_brownian_interval μ F B hB hm hind
    (u j.castSucc) (u j.succ) (hu (Fin.castSucc_le_succ j)) (K j) (hK j) (hK2 j)).1
  have hi : ∀ i j, Integrable (fun ω => J01522 B (H i) (t i.castSucc) (t i.succ) ω *
      J01522 B (K j) (u j.castSucc) (u j.succ) ω) μ := fun i j => (hJ i).integrable_mul (hL j)
  simp only [S01522, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact elementary_cross μ F B hB hm hind (H i) (K j) _ _ _ _
    (ht (Fin.castSucc_le_succ i)) (hu (Fin.castSucc_le_succ j)) (hH i) (hK j) (hH2 i) (hK2 j)

lemma step_product_expectation {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {N M : ℕ}
    (H : Fin N → Ω → ℝ) (K : Fin M → Ω → ℝ)
    (t : Fin (N+1) → NNReal) (u : Fin (M+1) → NNReal)
    (hH : ∀ i, MemLp (H i) 2 μ) (hK : ∀ j, MemLp (K j) 2 μ) :
    Integrable (fun ω => ∫ s, Q01522 H t s ω * Q01522 K u s ω) μ ∧
    (∫ ω, ∫ s, Q01522 H t s ω * Q01522 K u s ω ∂volume ∂μ) =
      ∑ i, ∑ j, max 0 (min (t i.succ : ℝ) (u j.succ) - max (t i.castSucc : ℝ) (u j.castSucc)) *
        ∫ ω, H i ω * K j ω ∂μ := by
  let w := fun (i : Fin N) (j : Fin M) => max 0 (min (t i.succ : ℝ) (u j.succ) - max (t i.castSucc : ℝ) (u j.castSucc))
  have hi : ∀ i j, Integrable (fun ω => w i j * (H i ω*K j ω)) μ :=
    fun i j => ((hH i).integrable_mul (hK j)).const_mul _
  have he : (fun ω => ∫ s, Q01522 H t s ω * Q01522 K u s ω) =
      fun ω => ∑ i, ∑ j, w i j * (H i ω*K j ω) :=
    funext fun ω => (step_product_integral H K t u ω).2
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

lemma integral_square_difference {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hff : Integrable (fun ω => f ω*f ω) μ) (hgg : Integrable (fun ω => g ω*g ω) μ)
    (hfg : Integrable (fun ω => f ω*g ω) μ) :
    Integrable (fun ω => (f ω-g ω)^2) μ ∧
    (∫ ω, (f ω-g ω)^2 ∂μ) =
      (∫ ω, f ω*f ω ∂μ) + (∫ ω, g ω*g ω ∂μ) - 2*(∫ ω, f ω*g ω ∂μ) := by
  have he : (fun ω => (f ω-g ω)^2) =
      fun ω => (f ω*f ω+g ω*g ω)-2*(f ω*g ω) := by ext ω; ring
  rw [he]
  refine ⟨(hff.add hgg).sub (hfg.const_mul 2), ?_⟩
  have hi := integral_sub (hff.add hgg) (hfg.const_mul 2)
  simp only [Pi.add_apply] at hi
  rw [hi, integral_add hff hgg, integral_const_mul]

lemma elementary_brownian_comparison : elementaryBrownianComparisonStatement := by
  intro Ω mΩ μ hμ F B hB hm hind N M t u H K ht hu hH hK hH2 hK2
  let := hμ
  have hSH := (elementary_brownian_integral Ω mΩ μ hμ F B hB hm hind N t H ht hH hH2).2.2.1
  have hSK := (elementary_brownian_integral Ω mΩ μ hμ F B hB hm hind M u K hu hK hK2).2.2.1
  have hcross := elementary_cross_sum μ F B hB hm hind t u H K ht hu hH hK hH2 hK2
  have htime := step_product_integral H K t u
  have hexpect := step_product_expectation μ H K t u hH2 hK2
  have he := hcross.trans hexpect.2.symm
  have hHH := step_product_expectation μ H H t t hH2 hH2
  have hKK := step_product_expectation μ K K u u hK2 hK2
  have heHH := (elementary_cross_sum μ F B hB hm hind t t H H ht ht hH hH hH2 hH2).trans hHH.2.symm
  have heKK := (elementary_cross_sum μ F B hB hm hind u u K K hu hu hK hK hK2 hK2).trans hKK.2.symm
  have hsq := integral_square_difference μ (S01522 B H t) (S01522 B K u)
    (hSH.integrable_mul hSH) (hSK.integrable_mul hSK) (hSH.integrable_mul hSK)
  have htimeSq := fun ω => integral_square_difference volume (fun s => Q01522 H t s ω)
    (fun s => Q01522 K u s ω) (step_product_integral H H t t ω).1
    (step_product_integral K K u u ω).1 (htime ω).1
  have hfun : (fun ω => ∫ s, (Q01522 H t s ω-Q01522 K u s ω)^2) =
      fun ω => (∫ s, Q01522 H t s ω*Q01522 H t s ω) +
        (∫ s, Q01522 K u s ω*Q01522 K u s ω) - 2*(∫ s, Q01522 H t s ω*Q01522 K u s ω) :=
    funext fun ω => (htimeSq ω).2
  refine ⟨hSH.integrable_mul hSK, fun ω => (htime ω).1, hexpect.1, hcross, he, ?_, ?_⟩
  · rw [hfun]
    exact (hHH.1.add hKK.1).sub (hexpect.1.const_mul 2)
  · have hi := integral_sub (hHH.1.add hKK.1) (hexpect.1.const_mul 2)
    simp only [Pi.add_apply] at hi
    rw [hsq.2, heHH, heKK, he, hfun, hi, integral_add hHH.1 hKK.1, integral_const_mul]

lemma L2_distance_square {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Lp ℝ 2 μ) (f g : Ω → ℝ) (hX : (X : Ω → ℝ) =ᵐ[μ] f) (hY : (Y : Ω → ℝ) =ᵐ[μ] g) :
    dist X Y ^ 2 = ∫ ω, (f ω-g ω)^2 ∂μ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub X Y, hX, hY] with ω hsub hx hy
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hsub, Pi.sub_apply, hx, hy]

lemma elementary_brownian_cauchy : elementaryBrownianCauchyStatement := by
  intro Ω mΩ μ hμ F B hB hm hind N t H ht hH hH2 hC
  let := hμ
  have hS := fun n => (elementary_brownian_integral Ω mΩ μ hμ F B hB hm hind
    (N n) (t n) (H n) (ht n) (hH n) (hH2 n)).2.2.1
  let X : ℕ → Lp ℝ 2 μ := fun n => (hS n).toLp (S01522 B (H n) (t n))
  have hX : ∀ n, (X n : Ω → ℝ) =ᵐ[μ] S01522 B (H n) (t n) := fun n => (hS n).coeFn_toLp
  refine ⟨X, hX, Metric.cauchySeq_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := hC (ε^2) (sq_pos_of_pos hε)
  refine ⟨k, fun n hn m hm' => ?_⟩
  have hi := elementary_brownian_comparison Ω mΩ μ hμ F B hB hm hind
    (N n) (N m) (t n) (t m) (H n) (H m) (ht n) (ht m) (hH n) (hH m) (hH2 n) (hH2 m)
  have he := L2_distance_square μ (X n) (X m) _ _ (hX n) (hX m)
  rw [hi.2.2.2.2.2.2] at he
  have hlt := hk n hn m hm'
  rw [← he] at hlt
  nlinarith [dist_nonneg (x := X n) (y := X m)]

lemma finite_step_sample {Ω : Type} (T : NNReal) (m : ℕ) (Y : ℝ → Ω → ℝ)
    (s : ℝ) (hs : s ≠ 0) (ω : Ω) :
    Q01522 (fun i : Fin (N01522 T m) => Y (r01522 T m i.val).val)
      (t01522 T m) s ω = if s ∈ Icc (0 : ℝ) T then Y (a01522 T m s).val ω else 0 := by
  classical
  by_cases hst : s ∈ Icc (0 : ℝ) T
  · have hspos : 0 < s := lt_of_le_of_ne hst.1 (Ne.symm hs)
    have hceilpos : 0 < Nat.ceil (s*(m+1)) := Nat.ceil_pos.mpr (by positivity)
    have hceille : Nat.ceil (s*(m+1)) ≤ N01522 T m :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right hst.2 (by positivity))
    let k : Fin (N01522 T m) := ⟨Nat.ceil (s*(m+1))-1, by omega⟩
    have hk : s ∈ Ioc (t01522 T m k.castSucc : ℝ) (t01522 T m k.succ) :=
      (r01522_cell T m k.val ⟨s, hst⟩).mpr ⟨hspos, by dsimp [k]; omega⟩
    rw [ite_eq_left hst, Q01522, Finset.sum_eq_single k]
    · rw [indicator_of_mem hk]
      rfl
    · intro i _ hik
      apply indicator_of_notMem
      intro hi
      have hc := ((r01522_cell T m i.val ⟨s, hst⟩).mp hi).2
      change Nat.ceil (s*(m+1)) = i.val+1 at hc
      apply hik
      apply Fin.ext
      dsimp [k]
      omega
    · simp
  · rw [ite_eq_right hst, Q01522]
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    intro hi
    apply hst
    exact ⟨le_trans (r01522 T m i.val).property.1 hi.1.le,
      hi.2.trans (r01522 T m (i.val+1)).property.2⟩

lemma finite_stopped_step {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d) (m : ℕ) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ ω,
      Q01522 (H01522 T X n α l j m) (t01522 T m) s ω = D01522 T X n α l j m s ω := by
  have hz : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hz] with s hs
  intro ω
  exact finite_step_sample T m (B01522 T X n α l j) s hs ω

lemma finite_stopped_step_integral {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (m k : ℕ) (ω : Ω) :
    (∫ s, (Q01522 (H01522 T X n α l j m) (t01522 T m) s ω -
      Q01522 (H01522 T X n α l j k) (t01522 T k) s ω)^2) =
    ∫ s in Icc (0 : ℝ) T, (D01522 T X n α l j m s ω - D01522 T X n α l j k s ω)^2 := by
  trans ∫ s, (D01522 T X n α l j m s ω - D01522 T X n α l j k s ω)^2
  · apply integral_congr_ae
    filter_upwards [finite_stopped_step T X n α l j m, finite_stopped_step T X n α l j k]
      with s hm hk
    rw [hm ω, hk ω]
  · symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    simp [D01522, hs]

lemma stopped_step_cauchy {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) :
    ∀ ε : ℝ, 0 < ε → ∃ k, ∀ a ≥ k, ∀ b ≥ k,
      (∫ ω, ∫ s, (Q01522 (H01522 T X n α l j a) (t01522 T a) s ω -
        Q01522 (H01522 T X n α l j b) (t01522 T b) s ω)^2 ∂volume ∂μ) < ε := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  let D := fun m => Function.uncurry (D01522 T X n α l j m)
  let C := Function.uncurry (B01522 T X n α l j)
  have hA := stopped_integrand_approximation d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n j
  have hD : ∀ m, MemLp (D m) 2 ν := fun m => (hA.1 m).2.2.2.2.2.1
  have hC : MemLp C 2 ν :=
    ((stopped_integrand_integrability d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n).1 j).2.1
  have he : ∀ m, Integrable (fun p => (D m p-C p)^2) ν := fun m => (hD m |>.sub hC).integrable_sq
  have hab : ∀ a b, Integrable (fun p => (D a p-D b p)^2) ν :=
    fun a b => (hD a |>.sub (hD b)).integrable_sq
  have hbound (a b) : (∫ p, (D a p-D b p)^2 ∂ν) ≤
      2*(∫ p, (D a p-C p)^2 ∂ν)+2*(∫ p, (D b p-C p)^2 ∂ν) := by
    calc
      _ ≤ ∫ p, 2*(D a p-C p)^2+2*(D b p-C p)^2 ∂ν :=
        integral_mono (hab a b) (((he a).const_mul 2).add ((he b).const_mul 2))
          (fun p => by nlinarith [sq_nonneg (D a p+D b p-2*C p)])
      _ = _ := by rw [integral_add ((he a).const_mul 2) ((he b).const_mul 2), integral_const_mul, integral_const_mul]
  intro ε hε
  have hsmall : ∀ᶠ m in atTop, (∫ p, (D m p-C p)^2 ∂ν) < ε/4 :=
    hA.2.2.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨k, hk⟩ := eventually_atTop.mp hsmall
  refine ⟨k, fun a ha b hb => ?_⟩
  have hid : (∫ ω, ∫ s, (Q01522 (H01522 T X n α l j a) (t01522 T a) s ω -
      Q01522 (H01522 T X n α l j b) (t01522 T b) s ω)^2 ∂volume ∂μ) =
      ∫ p, (D a p-D b p)^2 ∂ν := by
    simp_rw [finite_stopped_step_integral]
    exact (integral_prod_symm _ (hab a b)).symm
  rw [hid]
  have h₁ := hk a ha
  have h₂ := hk b hb
  linarith [hbound a b]

lemma L2_norm_square {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Lp ℝ 2 μ) (f : Ω → ℝ) (hZ : (Z : Ω → ℝ) =ᵐ[μ] f) :
    ‖Z‖^2 = ∫ ω, (f ω)^2 ∂μ := by
  simpa using L2_distance_square μ Z 0 f 0 hZ (Lp.coeFn_zero ℝ 2 μ)

lemma L2_tendsto_of_mean_square {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] f m) (hZ : (Z : Ω → ℝ) =ᵐ[μ] g)
    (hlim : Tendsto (fun m => ∫ ω, (f m ω-g ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto Y atTop (𝓝 Z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (sq_pos_of_pos hε)))
  refine ⟨k, fun m hm => ?_⟩
  have he := L2_distance_square μ (Y m) Z (f m) g (hY m) hZ
  have hlt := hk m hm
  rw [← he] at hlt
  nlinarith [dist_nonneg (x := Y m) (y := Z)]

lemma finite_stopped_step_square {d : ℕ} {Ω : Type} (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (m : ℕ) (ω : Ω) :
    (∫ s, (Q01522 (H01522 T X n α l j m) (t01522 T m) s ω)^2) =
    ∫ s in Icc (0 : ℝ) T, (D01522 T X n α l j m s ω)^2 := by
  trans ∫ s, (D01522 T X n α l j m s ω)^2
  · apply integral_congr_ae
    filter_upwards [finite_stopped_step T X n α l j m] with s hm
    rw [hm ω]
  · symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    simp [D01522, hs]

lemma stopped_brownian_limit_isometry {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) :
    (∫ ω, (Z ω)^2 ∂μ) = ∫ ω, ∫ s in Icc (0 : ℝ) T,
      (B01522 T X n α l j s ω)^2 ∂volume ∂μ := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  let D := fun m => Function.uncurry (D01522 T X n α l j m)
  let C := Function.uncurry (B01522 T X n α l j)
  have hA := stopped_integrand_approximation d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n j
  have hD : ∀ m, MemLp (D m) 2 ν := fun m => (hA.1 m).2.2.2.2.2.1
  have hC : MemLp C 2 ν :=
    ((stopped_integrand_integrability d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n).1 j).2.1
  let U : Lp ℝ 2 ν := hC.toLp C
  let W : ℕ → Lp ℝ 2 ν := fun m => (hD m).toLp (D m)
  have hW : Tendsto W atTop (𝓝 U) := L2_tendsto_of_mean_square ν W U D C
    (fun m => (hD m).coeFn_toLp) hC.coeFn_toLp hA.2.2
  have hnorm (m : ℕ) : ‖Y m‖^2 = ‖W m‖^2 := by
    have ht : Monotone (t01522 T m) := fun a b hab => (hA.1 m).1 (show a.val ≤ b.val from hab)
    have hH : ∀ i, Measurable[F01522 F (t01522 T m i.castSucc)] (H01522 T X n α l j m i) :=
      fun i => ((hA.1 m).2.2.2.1 i.val).1
    have hH2 : ∀ i, MemLp (H01522 T X n α l j m i) 2 μ :=
      fun i => ((hA.1 m).2.2.2.1 i.val).2
    have hi := (elementary_brownian_comparison Ω mΩ μ inferInstance (F01522 F) B hB hBm hind
      (N01522 T m) (N01522 T m) (t01522 T m) (t01522 T m)
      (H01522 T X n α l j m) (H01522 T X n α l j m) ht ht hH hH hH2 hH2).2.2.2.2.1
    rw [L2_norm_square μ (Y m) _ (hY m), L2_norm_square ν (W m) _ (hD m).coeFn_toLp]
    simp only [← sq] at hi
    rw [hi]
    simp_rw [finite_stopped_step_square]
    exact (integral_prod_symm _ (hD m).integrable_sq).symm
  have hnormlim : ‖Z‖^2 = ‖U‖^2 := tendsto_nhds_unique (hZ.norm.pow 2)
    (by simpa only [hnorm] using hW.norm.pow 2)
  rw [← L2_norm_square μ Z _ Filter.EventuallyEq.rfl, hnormlim,
    L2_norm_square ν U C hC.coeFn_toLp]
  exact integral_prod_symm _ hC.integrable_sq

lemma elementary_future_sum {Ω : Type} {N : ℕ} (B : NNReal → Ω → ℝ)
    (H : Fin N → Ω → ℝ) (t : Fin (N+1) → NNReal) (s : NNReal) :
    S01522 B H (fun i => max s (t i)) = S01522 B H t - R01522 B H t s := by
  ext ω
  simp only [S01522, R01522, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hb (a : NNReal) : B (max s a) ω = B a ω+B s ω-B (min s a) ω := by
    rcases le_total s a with h | h
    · simp [max_eq_right h, min_eq_left h]
    · simp [max_eq_left h, min_eq_right h]
  simp only [J01522, P01522, hb]
  ring

lemma elementary_future_step {Ω : Type} {N : ℕ} (H : Fin N → Ω → ℝ)
    (t : Fin (N+1) → NNReal) (s : NNReal) (r : ℝ) (ω : Ω) :
    Q01522 H (fun i => max s (t i)) r ω = (Ioi (s : ℝ)).indicator
      (fun u => Q01522 H t u ω) r := by
  classical
  by_cases hs : r ∈ Ioi (s : ℝ)
  · rw [indicator_of_mem hs]
    apply Finset.sum_congr rfl
    intro i _
    have hi : r ∈ Ioc (↑(max s (t i.castSucc)) : ℝ) (↑(max s (t i.succ)) : ℝ) ↔
        r ∈ Ioc (t i.castSucc : ℝ) (t i.succ) := by
      simp only [NNReal.coe_max, mem_Ioc, max_lt_iff, le_max_iff]
      constructor
      · rintro ⟨⟨_, ha⟩, hb | hb⟩
        · exact False.elim (not_le_of_gt hs hb)
        · exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨⟨hs, ha⟩, Or.inr hb⟩
    simp only [indicator, hi]
  · rw [indicator_of_notMem hs]
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    intro hi
    exact hs (lt_of_le_of_lt (le_max_left (s : ℝ) (t i.castSucc)) hi.1)

lemma elementary_sum_indicator {Ω : Type} {N : ℕ} (B : NNReal → Ω → ℝ)
    (H : Fin N → Ω → ℝ) (t : Fin (N+1) → NNReal) (E : Set Ω) :
    S01522 B (fun i => E.indicator (H i)) t = E.indicator (S01522 B H t) := by
  classical
  ext ω
  by_cases hω : ω ∈ E <;> simp [S01522, J01522, hω]

lemma elementary_step_indicator {Ω : Type} {N : ℕ} (H : Fin N → Ω → ℝ)
    (t : Fin (N+1) → NNReal) (E : Set Ω) (r : ℝ) :
    Q01522 (fun i => E.indicator (H i)) t r = E.indicator (Q01522 H t r) := by
  classical
  ext ω
  by_cases hω : ω ∈ E <;> simp [Q01522, hω]

lemma elementary_future_set_isometry {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (N : ℕ) (t : Fin (N+1) → NNReal) (H : Fin N → Ω → ℝ) (ht : Monotone t)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hH2 : ∀ i, MemLp (H i) 2 μ)
    (s : NNReal) (E : Set Ω) (hE : MeasurableSet[F s] E) :
    (∫ ω in E, (S01522 B H t ω-R01522 B H t s ω)^2 ∂μ) =
      ∫ ω in E, ∫ r in Ioi (s : ℝ), (Q01522 H t r ω)^2 ∂volume ∂μ := by
  let u := fun i => max s (t i)
  let K := fun i => E.indicator (H i)
  have hu : Monotone u := fun i j hij => max_le_max_left s (ht hij)
  have hK : ∀ i, Measurable[F (u i.castSucc)] (K i) := fun i =>
    ((hH i).mono (F.mono (le_max_right _ _)) le_rfl).indicator
      (F.mono (le_max_left _ _) E hE)
  have hK2 : ∀ i, MemLp (K i) 2 μ := fun i => (hH2 i).indicator (F.le s E hE)
  have hi := (elementary_brownian_comparison Ω mΩ μ inferInstance F B hB hm hind N N u u K K
    hu hu hK hK hK2 hK2).2.2.2.2.1
  simp only [← sq] at hi
  have hleft : (fun ω => (S01522 B K u ω)^2) =
      E.indicator (fun ω => (S01522 B H t ω-R01522 B H t s ω)^2) := by
    rw [show K = (fun i => E.indicator (H i)) from rfl, elementary_sum_indicator]
    rw [show u = (fun i => max s (t i)) from rfl, elementary_future_sum]
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have hright : (fun ω => ∫ r, (Q01522 K u r ω)^2) =
      E.indicator (fun ω => ∫ r in Ioi (s : ℝ), (Q01522 H t r ω)^2) := by
    ext ω
    simp only [K, elementary_step_indicator]
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω]
      simp_rw [u, elementary_future_step]
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by by_cases hr : r ∈ Ioi (s : ℝ) <;> simp [hr])
    · simp [hω]
  rw [hleft, hright, integral_indicator (F.le s E hE), integral_indicator (F.le s E hE)] at hi
  exact hi

lemma L2_set_square_tendsto {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] f m) (hZ : (Z : Ω → ℝ) =ᵐ[μ] g)
    (hlim : Tendsto Y atTop (𝓝 Z)) :
    Tendsto (fun m => ∫ ω in E, (f m ω)^2 ∂μ) atTop (𝓝 (∫ ω in E, (g ω)^2 ∂μ)) := by
  have hle : μ.restrict E ≤ (1 : ENNReal) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := E)
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict E) :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ENNReal) ≠ ⊤) hle
  have hrep (V : Lp ℝ 2 μ) : (L V : Ω → ℝ) =ᵐ[μ.restrict E] V :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ hle V
  have hy (m) : ‖L (Y m)‖^2 = ∫ ω in E, (f m ω)^2 ∂μ :=
    L2_norm_square _ _ _ ((hrep (Y m)).trans (ae_restrict_of_ae (hY m)))
  have hz : ‖L Z‖^2 = ∫ ω in E, (g ω)^2 ∂μ :=
    L2_norm_square _ _ _ ((hrep Z).trans (ae_restrict_of_ae hZ))
  simpa only [Function.comp_apply, hy, hz] using (L.continuous.tendsto Z |>.comp hlim).norm.pow 2

lemma L2_condExp_rep {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (s : NNReal) (Z : Lp ℝ 2 μ) :
    (condExpL2 ℝ ℝ (F.le s) Z : Ω → ℝ) =ᵐ[μ] μ[(Z : Ω → ℝ) | F s] := by
  have h := (Lp.memLp Z).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)
  simpa only [Lp.toLp_coeFn] using h

lemma L2_future_rep {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (s : NNReal) (Z : Lp ℝ 2 μ) :
    ((Z - (condExpL2 ℝ ℝ (F.le s) Z : Lp ℝ 2 μ) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun ω => Z ω - μ[(Z : Ω → ℝ) | F s] ω := by
  filter_upwards [Lp.coeFn_sub Z (condExpL2 ℝ ℝ (F.le s) Z), L2_condExp_rep μ F s Z]
    with ω hsub hce
  exact hsub.trans (congrArg (fun x => Z ω-x) hce)

lemma product_set_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T s : NNReal) (E : Set Ω) (f : ℝ × Ω → ℝ)
    (hf : Integrable f ((volume.restrict (Icc (0 : ℝ) T)).prod μ)) :
    (∫ p in Ioc (s : ℝ) T ×ˢ E, f p ∂((volume.restrict (Icc (0 : ℝ) T)).prod μ)) =
      ∫ ω in E, ∫ r in Ioc (s : ℝ) T, f (r, ω) ∂volume ∂μ := by
  have hsub : Ioc (s : ℝ) T ⊆ Icc (0 : ℝ) T := fun _ h => ⟨s.coe_nonneg.trans h.1.le, h.2⟩
  have hmeasure : ((volume.restrict (Icc (0 : ℝ) T)).prod μ).restrict (Ioc (s : ℝ) T ×ˢ E) =
      (volume.restrict (Ioc (s : ℝ) T)).prod (μ.restrict E) := by
    rw [← Measure.prod_restrict, Measure.restrict_restrict_of_subset hsub]
  rw [hmeasure]
  apply integral_prod_symm
  rw [← hmeasure]
  exact hf.restrict

lemma finite_stopped_future_square {d : ℕ} {Ω : Type} (T s : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (n : ℕ) (α l : Fin d → ℝ) (j : Fin d)
    (m : ℕ) (ω : Ω) :
    (∫ r in Ioi (s : ℝ), (Q01522 (H01522 T X n α l j m) (t01522 T m) r ω)^2) =
    ∫ r in Ioc (s : ℝ) T, (D01522 T X n α l j m r ω)^2 := by
  trans ∫ r in Ioi (s : ℝ), (D01522 T X n α l j m r ω)^2
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (finite_stopped_step T X n α l j m)] with r hr
    rw [hr ω]
  · have h := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume.restrict (Ioi (s : ℝ))) (s := Icc (0 : ℝ) T)
      (f := fun r => (D01522 T X n α l j m r ω)^2)
      (fun r hr => by simp [D01522, hr])
    have hinter : Icc (0 : ℝ) T ∩ Ioi (s : ℝ) = Ioc (s : ℝ) T := by
      ext r
      simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, hT⟩, hs⟩; exact ⟨hs, hT⟩
      · rintro ⟨hs, hT⟩; exact ⟨⟨s.coe_nonneg.trans hs.le, hT⟩, hs⟩
    rw [Measure.restrict_restrict measurableSet_Icc, hinter] at h
    exact h.symm

lemma stopped_brownian_future_set_isometry {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (s : NNReal) (E : Set Ω) (hE : MeasurableSet[F (s : ℝ)] E) :
    (∫ ω in E, (Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 ∂μ) =
      ∫ ω in E, ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2 ∂volume ∂μ := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  let D := fun m => Function.uncurry (D01522 T X n α l j m)
  let C := Function.uncurry (B01522 T X n α l j)
  have hA := stopped_integrand_approximation d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n j
  have ht : ∀ m, Monotone (t01522 T m) := fun m a b hab =>
    (hA.1 m).1 (show a.val ≤ b.val from hab)
  have hH : ∀ m i, Measurable[F01522 F (t01522 T m i.castSucc)] (H01522 T X n α l j m i) :=
    fun m i => ((hA.1 m).2.2.2.1 i.val).1
  have hH2 : ∀ m i, MemLp (H01522 T X n α l j m i) 2 μ :=
    fun m i => ((hA.1 m).2.2.2.1 i.val).2
  have hD : ∀ m, MemLp (D m) 2 ν := fun m => (hA.1 m).2.2.2.2.2.1
  have hC : MemLp C 2 ν :=
    ((stopped_integrand_integrability d Ω mΩ μ inferInstance F T X α l hm hc h0 hl n).1 j).2.1
  let U : Lp ℝ 2 ν := hC.toLp C
  let W : ℕ → Lp ℝ 2 ν := fun m => (hD m).toLp (D m)
  have hW : Tendsto W atTop (𝓝 U) := L2_tendsto_of_mean_square ν W U D C
    (fun m => (hD m).coeFn_toLp) hC.coeFn_toLp hA.2.2
  have hright := L2_set_square_tendsto ν (Ioc (s : ℝ) T ×ˢ E) W U D C
    (fun m => (hD m).coeFn_toLp) hC.coeFn_toLp hW
  dsimp only [ν] at hright
  simp_rw [product_set_integral μ T s E _ (hD _).integrable_sq,
    product_set_integral μ T s E _ hC.integrable_sq] at hright
  let P := fun V : Lp ℝ 2 μ => (condExpL2 ℝ ℝ (F.le (s : ℝ)) V : Lp ℝ 2 μ)
  have hP : Continuous P := continuous_subtype_val.comp (condExpL2 ℝ ℝ (F.le (s : ℝ))).continuous
  have hfuture : Tendsto (fun m => Y m-P (Y m)) atTop (𝓝 (Z-P Z)) :=
    hZ.sub (hP.tendsto Z |>.comp hZ)
  have hrep : ∀ m, ((Y m-P (Y m) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun ω => S01522 B (H01522 T X n α l j m) (t01522 T m) ω -
        R01522 B (H01522 T X n α l j m) (t01522 T m) s ω := by
    intro m
    have hce := (condExp_congr_ae (m := F (s : ℝ)) (hY m)).trans
      ((elementary_brownian_process Ω mΩ μ inferInstance (F01522 F) B hB hBm hind
        (N01522 T m) (t01522 T m) (H01522 T X n α l j m) (ht m) (hH m) (hH2 m)).2.2.1 s).2.1
    exact (L2_future_rep μ (F01522 F) s (Y m)).trans ((hY m).sub hce)
  have hleft := L2_set_square_tendsto μ E (fun m => Y m-P (Y m)) (Z-P Z)
    _ _ hrep (L2_future_rep μ (F01522 F) s Z) hfuture
  have he (m : ℕ) : (∫ ω in E,
      (S01522 B (H01522 T X n α l j m) (t01522 T m) ω -
        R01522 B (H01522 T X n α l j m) (t01522 T m) s ω)^2 ∂μ) =
      ∫ ω in E, ∫ r in Ioc (s : ℝ) T, (D01522 T X n α l j m r ω)^2 ∂volume ∂μ := by
    rw [elementary_future_set_isometry μ (F01522 F) B hB hBm hind
      (N01522 T m) (t01522 T m) (H01522 T X n α l j m) (ht m) (hH m) (hH2 m) s E hE]
    simp_rw [finite_stopped_future_square]
  exact tendsto_nhds_unique hleft (by simpa only [he, D, C, Function.uncurry] using hright)

lemma stopped_integrand_future_integrable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) (s : NNReal) :
    Integrable (fun ω => ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) μ := by
  have h := (localizer_integrand_integrable μ F T X α l hm hc h0 hl n j).1
  have hsub : Ioc (s : ℝ) T ⊆ Icc (0 : ℝ) T := fun _ hr => ⟨s.coe_nonneg.trans hr.1.le, hr.2⟩
  have hle : (volume.restrict (Ioc (s : ℝ) T)).prod μ ≤
      (volume.restrict (Icc (0 : ℝ) T)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  exact (h.mono_measure hle).integral_prod_right

lemma stopped_brownian_conditional_isometry {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (s : NNReal) :
    μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 | F (s : ℝ)] =ᵐ[μ]
      μ[fun ω => ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2 | F (s : ℝ)] := by
  have hi := stopped_integrand_future_integrable μ F T X α l hm hc h0 hl n j s
  have hsq : Integrable (fun ω => (Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2) μ :=
    ((Lp.memLp Z).sub ((Lp.memLp Z).condExp one_le_two)).integrable_sq
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le (s : ℝ)) hi
    (fun E _ _ => integrable_condExp.integrableOn) _ stronglyMeasurable_condExp.aestronglyMeasurable
  intro E hE _
  rw [setIntegral_condExp (F.le (s : ℝ)) hsq hE]
  exact stopped_brownian_future_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ s E hE

lemma stopped_brownian_after_horizon {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (s : NNReal) (hs : T ≤ s) :
    μ[(Z : Ω → ℝ) | F (s : ℝ)] =ᵐ[μ] Z := by
  have h := stopped_brownian_future_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind
    n j Y Z hY hZ s univ MeasurableSet.univ
  have he : Ioc (s : ℝ) T = ∅ := Ioc_eq_empty_of_le hs
  simp [he] at h
  have hi : Integrable (fun ω => (Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2) μ :=
    ((Lp.memLp Z).sub ((Lp.memLp Z).condExp one_le_two)).integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hi).mp h
  filter_upwards [hz] with ω hω
  have hω' : Z ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω = 0 := (sq_eq_zero_iff).mp hω
  linarith

lemma conditional_projection_cross {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (Z : Lp ℝ 2 μ) (s t : NNReal) (hst : s ≤ t) (E : Set Ω) (hE : MeasurableSet[F s] E) :
    (∫ ω in E, (Z ω-μ[(Z : Ω → ℝ) | F t] ω)*
      (μ[(Z : Ω → ℝ) | F t] ω-μ[(Z : Ω → ℝ) | F s] ω) ∂μ) = 0 := by
  let A : Ω → ℝ := (Z : Ω → ℝ)-μ[(Z : Ω → ℝ) | F t]
  let B : Ω → ℝ := μ[(Z : Ω → ℝ) | F t]-μ[(Z : Ω → ℝ) | F s]
  have hA : MemLp A 2 μ := (Lp.memLp Z).sub ((Lp.memLp Z).condExp one_le_two)
  have hB : MemLp B 2 μ := ((Lp.memLp Z).condExp one_le_two).sub ((Lp.memLp Z).condExp one_le_two)
  have hmt : StronglyMeasurable[F t] (μ[(Z : Ω → ℝ) | F t]) := stronglyMeasurable_condExp
  have hms : StronglyMeasurable[F s] (μ[(Z : Ω → ℝ) | F s]) := stronglyMeasurable_condExp
  have hBm : Measurable[F t] B := hmt.measurable.sub
    (hms.measurable.mono (F.mono hst) le_rfl)
  have hW : MemLp (E.indicator B) 2 μ := hB.indicator (F.le s E hE)
  have hWm : Measurable[F t] (E.indicator B) := hBm.indicator (F.mono hst E hE)
  have hce : μ[A | F t] =ᵐ[μ] 0 := by
    have h := condExp_sub (g := μ[(Z : Ω → ℝ) | F t])
      ((Lp.memLp Z).integrable one_le_two) integrable_condExp (F t)
    rw [condExp_of_stronglyMeasurable (F.le t) hmt integrable_condExp] at h
    filter_upwards [h] with ω hω
    simpa only [Pi.sub_apply, sub_self, Pi.zero_apply] using hω
  have hp := condExp_mul_of_stronglyMeasurable_left hWm.stronglyMeasurable
    (hW.integrable_mul hA) (hA.integrable one_le_two)
  have hp0 : μ[E.indicator B * A | F t] =ᵐ[μ] 0 := by
    filter_upwards [hp, hce] with ω hp hce
    simp only [hp, Pi.mul_apply, hce, Pi.zero_apply, mul_zero]
  have hi : (∫ ω, (E.indicator B * A) ω ∂μ) = 0 := by
    rw [← integral_condExp (F.le t), integral_congr_ae hp0]
    simp
  rw [← integral_indicator (F.le s E hE)]
  convert hi using 1
  congr 1
  funext ω
  by_cases hω : ω ∈ E <;> simp [A, B, hω, mul_comm]

lemma conditional_projection_set_square {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (Z : Lp ℝ 2 μ) (s t : NNReal) (hst : s ≤ t) (E : Set Ω) (hE : MeasurableSet[F s] E) :
    (∫ ω in E, (μ[(Z : Ω → ℝ) | F t] ω-μ[(Z : Ω → ℝ) | F s] ω)^2 ∂μ) =
      (∫ ω in E, (Z ω-μ[(Z : Ω → ℝ) | F s] ω)^2 ∂μ) -
      (∫ ω in E, (Z ω-μ[(Z : Ω → ℝ) | F t] ω)^2 ∂μ) := by
  let A : Ω → ℝ := (Z : Ω → ℝ)-μ[(Z : Ω → ℝ) | F t]
  let B : Ω → ℝ := μ[(Z : Ω → ℝ) | F t]-μ[(Z : Ω → ℝ) | F s]
  have hA : MemLp A 2 μ := (Lp.memLp Z).sub ((Lp.memLp Z).condExp one_le_two)
  have hB : MemLp B 2 μ := ((Lp.memLp Z).condExp one_le_two).sub ((Lp.memLp Z).condExp one_le_two)
  have hi := (integral_square_difference (μ.restrict E) A (-B)
    (hA.integrable_mul hA).restrict (hB.neg.integrable_mul hB.neg).restrict
    (hA.integrable_mul hB.neg).restrict).2
  have hcross : (∫ ω in E, A ω*B ω ∂μ) = 0 := conditional_projection_cross μ F Z s t hst E hE
  simp only [Pi.neg_apply, mul_neg, ← sq, neg_sq, integral_neg, hcross, neg_zero, mul_zero, sub_zero] at hi
  have he (ω : Ω) : A ω - -B ω = Z ω-μ[(Z : Ω → ℝ) | F s] ω := by dsimp [A, B]; ring
  simp_rw [he] at hi
  dsimp only [A, Pi.sub_apply] at hi
  change (∫ ω in E, (B ω)^2 ∂μ) = _
  linarith

lemma stopped_integrand_interval {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d)
    (s t : NNReal) (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2) μ ∧
    (∫ ω, ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2 ∂volume ∂μ) ≤
      ((t : ℝ)-s)*((l j)^2*(α j)^2*(n+2)) := by
  let ν := volume.restrict (Ioc (s : ℝ) t)
  let C := (l j)^2*(α j)^2*(n+2 : ℝ)
  have hb : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, (B01522 T X n α l j p.1 p.2)^2 ≤ C := by
    have ht : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, p.1 ∈ Ioc (s : ℝ) t :=
      Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioc)
    have hx : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, ∀ k, X 0 p.2 k ≤ 1 :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually h0
    filter_upwards [ht, hx] with p hp hx
    have hpT : p.1 ∈ Icc (0 : ℝ) T := ⟨s.coe_nonneg.trans hp.1.le, hp.2.trans htT⟩
    rw [localizer_integrand_square T X n α l j ⟨p.1, hpT⟩ p.2]
    exact (localizer_integrand_bound T X hc p.2 hx n α l hl ⟨p.1, hpT⟩ j).2
  have hmeas := (localizer_integrand_measurable F T X hm hc n α l j).pow_const 2
  have hi : Integrable (fun p : ℝ × Ω => (B01522 T X n α l j p.1 p.2)^2) (ν.prod μ) :=
    (integrable_const C).mono' hmeas.aestronglyMeasurable (by
      filter_upwards [hb] with p hp
      simpa only [Real.norm_eq_abs, abs_sq] using hp)
  refine ⟨hi.integral_prod_right, ?_⟩
  rw [← integral_prod_symm _ hi]
  have hbound := integral_mono_ae hi (integrable_const C) hb
  simpa [ν, C, measureReal_def, Measure.prod_apply, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)), mul_comm] using hbound

lemma stopped_integrand_interval_split {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d)
    (s t : NNReal) (hst : s ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, (∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) -
      (∫ r in Ioc (t : ℝ) T, (B01522 T X n α l j r ω)^2) =
      ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2 := by
  have hi := (localizer_integrand_integrable μ F T X α l hm hc h0 hl n j).1
  filter_upwards [hi.prod_left_ae] with ω hω
  have hst' : Ioc (s : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun _ hr => ⟨s.coe_nonneg.trans hr.1.le, hr.2.trans htT⟩
  have htT' : Ioc (t : ℝ) T ⊆ Icc (0 : ℝ) T :=
    fun _ hr => ⟨t.coe_nonneg.trans hr.1.le, hr.2⟩
  rw [← Ioc_union_Ioc_eq_Ioc (show (s : ℝ) ≤ t from hst) (show (t : ℝ) ≤ T from htT),
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hω.mono_measure (Measure.restrict_mono hst' le_rfl))
      (hω.mono_measure (Measure.restrict_mono htT' le_rfl)), add_sub_cancel_right]

lemma stopped_brownian_increment_set_isometry {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (s t : NNReal) (hst : s ≤ t) (htT : t ≤ T)
    (E : Set Ω) (hE : MeasurableSet[F (s : ℝ)] E) :
    (∫ ω in E, (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 ∂μ) =
      ∫ ω in E, ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2 ∂volume ∂μ := by
  have hp := conditional_projection_set_square μ (F01522 F) Z s t hst E hE
  dsimp only [F01522] at hp
  rw [hp,
    stopped_brownian_future_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ s E hE,
    stopped_brownian_future_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ t E
      (F.mono hst E hE)]
  rw [← integral_sub (stopped_integrand_future_integrable μ F T X α l hm hc h0 hl n j s).restrict
    (stopped_integrand_future_integrable μ F T X α l hm hc h0 hl n j t).restrict]
  exact integral_congr_ae (ae_restrict_of_ae
    (stopped_integrand_interval_split μ F T X α l hm hc h0 hl n j s t hst htT))

lemma L2_projection_continuous {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (Z : Lp ℝ 2 μ) (T : NNReal) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s t : NNReal, s ≤ t → t ≤ T →
      (∫ ω, (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 ∂μ) ≤
        ((t : ℝ)-s)*C) :
    Continuous (fun s : Icc (0 : NNReal) T =>
      (condExpL2 ℝ ℝ (F.le (s.val : ℝ)) Z : Lp ℝ 2 μ)) := by
  let P := fun s : Icc (0 : NNReal) T =>
    (condExpL2 ℝ ℝ (F.le (s.val : ℝ)) Z : Lp ℝ 2 μ)
  have hord (s t : Icc (0 : NNReal) T) (hst : s ≤ t) : dist (P t) (P s)^2 ≤ C*dist s t := by
    have he := L2_distance_square μ (P t) (P s) _ _
      (L2_condExp_rep μ (F01522 F) t.val Z) (L2_condExp_rep μ (F01522 F) s.val Z)
    rw [he]
    have hd : dist s t = (t.val : ℝ)-s.val := by
      change |(s.val : ℝ)-(t.val : ℝ)| = _
      rw [abs_of_nonpos (sub_nonpos.mpr (show (s.val : ℝ) ≤ t.val from hst))]
      ring
    rw [hd, mul_comm]
    exact hbound s.val t.val hst t.property.2
  have hd (s t : Icc (0 : NNReal) T) : dist (P s) (P t)^2 ≤ C*dist s t := by
    rcases le_total s t with h | h
    · simpa only [dist_comm] using hord s t h
    · simpa only [dist_comm] using hord t s h
  apply Metric.continuous_iff.mpr
  intro s ε hε
  refine ⟨ε^2/(C+1), by positivity, fun t ht => ?_⟩
  have hδ := (lt_div_iff₀ (by positivity : 0 < C+1)).mp ht
  have hbd := hd t s
  nlinarith [dist_nonneg (x := t) (y := s), dist_nonneg (x := P t) (y := P s)]

lemma stopped_brownian_increment_isometry {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (s t : NNReal) (hst : s ≤ t) (htT : t ≤ T)
 :
    Integrable (fun ω => ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2) μ ∧
    μ[fun ω => (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 | F (s : ℝ)] =ᵐ[μ]
      μ[fun ω => ∫ r in Ioc (s : ℝ) t, (B01522 T X n α l j r ω)^2 | F (s : ℝ)] ∧
    (∫ ω, (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2 ∂μ) ≤
      ((t : ℝ)-s)*((l j)^2*(α j)^2*(n+2)) := by
  have hi := stopped_integrand_interval μ F T X α l hm hc h0 hl n j s t hst htT
  have hsq : Integrable (fun ω =>
      (μ[(Z : Ω → ℝ) | F (t : ℝ)] ω-μ[(Z : Ω → ℝ) | F (s : ℝ)] ω)^2) μ :=
    (((Lp.memLp Z).condExp one_le_two).sub ((Lp.memLp Z).condExp one_le_two)).integrable_sq
  refine ⟨hi.1, ?_, ?_⟩
  · apply ae_eq_condExp_of_forall_setIntegral_eq (F.le (s : ℝ)) hi.1
      (fun E _ _ => integrable_condExp.integrableOn) _ stronglyMeasurable_condExp.aestronglyMeasurable
    intro E hE _
    rw [setIntegral_condExp (F.le (s : ℝ)) hsq hE]
    exact stopped_brownian_increment_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind
      n j Y Z hY hZ s t hst htT E hE
  · have he := stopped_brownian_increment_set_isometry μ F T X α l hm hc h0 hl B hB hBm hind
      n j Y Z hY hZ s t hst htT univ MeasurableSet.univ
    simp only [setIntegral_univ] at he
    rw [he]
    exact hi.2

lemma martingale_abs_maximal_grid {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → ℝ) (hM : Martingale M F μ)
    (q : ℕ → NNReal) (hq : Monotone q) (n : ℕ) (T : NNReal) (hT : q n ≤ T) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M (q k) ω|} ≤
      ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k), fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have ha : Submartingale (fun k ω => |M (q k) ω|) G μ := by
    refine ⟨fun k => (hM.stronglyMeasurable (q k)).norm, ?_, fun k => (hM.integrable (q k)).abs⟩
    intro i j hij
    have hc := hM.condExp_ae_eq (hq hij)
    have hn := abs_condExp_ae_le_condExp_abs (μ := μ) (m := F (q i)) (M (q j))
    filter_upwards [hc, hn] with ω hc hn
    change |M (q i) ω| ≤ μ[abs (M (q j)) | F (q i)] ω
    simpa only [Pi.abs_apply, hc] using hn
  have hm := maximal_ineq ha (fun _ _ => abs_nonneg _) (ε := ε) n
  have he : {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M (q k) ω|} =
      {ω | (ε : ℝ) ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => |M (q k) ω|)} := by
    ext ω
    simp only [mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [he]
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  apply (setIntegral_le_integral (hM.integrable (q n)).abs (Eventually.of_forall fun _ => abs_nonneg _)).trans
  have hc := hM.condExp_ae_eq hT
  have he' : (fun ω => |M (q n) ω|) =ᵐ[μ] fun ω => |μ[M T | F (q n)] ω| := by
    filter_upwards [hc] with ω hω
    simp only [hω]
  rw [integral_congr_ae he']
  exact integral_abs_condExp_le _

lemma martingale_abs_maximal_finset {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → ℝ) (hM : Martingale M F μ)
    (S : Finset NNReal) (T : NNReal) (hT : ∀ s ∈ S, s ≤ T) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ s ∈ S, (ε : ℝ) ≤ |M s ω|} ≤
      ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
  classical
  let q : ℕ → NNReal := fun k => if h : k < S.card then S.orderEmbOfFin rfl ⟨k, h⟩ else T
  have hq : Monotone q := by
    intro i j hij
    dsimp [q]
    split_ifs with hi hj hj
    · exact (S.orderEmbOfFin rfl).monotone hij
    · exact hT _ (S.orderEmbOfFin_mem rfl _)
    · exact False.elim (hi (hij.trans_lt hj))
    · rfl
  have hn : q S.card ≤ T := by simp [q]
  have hs : {ω | ∃ s ∈ S, (ε : ℝ) ≤ |M s ω|} ⊆
      {ω | ∃ k ≤ S.card, (ε : ℝ) ≤ |M (q k) ω|} := by
    rintro ω ⟨s, hs, hε⟩
    let i := (S.orderIsoOfFin rfl).symm ⟨s, hs⟩
    have hi : S.orderEmbOfFin rfl i = s := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨s, hs⟩)
    refine ⟨i.val, i.isLt.le, ?_⟩
    simpa only [q, dite_eq_left i.isLt, hi] using hε
  have hh : (ε : ENNReal)*μ {ω | ∃ s ∈ S, (ε : ℝ) ≤ |M s ω|} ≤
      (ε : ENNReal)*μ {ω | ∃ k ≤ S.card, (ε : ℝ) ≤ |M (q k) ω|} := by
    gcongr
  exact hh.trans (martingale_abs_maximal_grid μ F M hM q hq S.card T hn ε)

lemma martingale_abs_maximal_sequence {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → ℝ) (hM : Martingale M F μ)
    (q : ℕ → NNReal) (T : NNReal) (hT : ∀ n, q n ≤ T) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ n, (ε : ℝ) ≤ |M (q n) ω|} ≤
      ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
  classical
  let E := fun n => {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M (q k) ω|}
  have hmono : Monotone E := by
    intro i j hij ω hω
    obtain ⟨k, hk, hε⟩ := hω
    exact ⟨k, hk.trans hij, hε⟩
  have he : {ω | ∃ n, (ε : ℝ) ≤ |M (q n) ω|} = ⋃ n, E n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, E]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩⟩
  rw [he, hmono.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  have hh := martingale_abs_maximal_finset μ F M hM ((Finset.range (n+1)).image q) T
    (fun s hs => by obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs; exact hT k) ε
  simpa only [Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff, exists_exists_and_eq_and, E] using hh

lemma martingale_abs_maximal_continuous {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → ℝ) (hM : Martingale M F μ) (T : NNReal)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T => M s.val ω)) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) T, (ε : ℝ) < |M s ω|} ≤
      ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
  let : Nonempty (Icc (0 : NNReal) T) := ⟨⟨0, zero_le, zero_le⟩⟩
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (Icc (0 : NNReal) T)
  have he : {ω | ∃ s ∈ Icc (0 : NNReal) T, (ε : ℝ) < |M s ω|} ≤ᵐ[μ]
      {ω | ∃ n, (ε : ℝ) ≤ |M (q n).val ω|} := by
    filter_upwards [hc] with ω hc
    rintro ⟨s, hs, hε⟩
    by_contra hn
    push Not at hn
    have hall : ∀ s : Icc (0 : NNReal) T, |M s.val ω| ≤ ε := by
      intro t
      exact hq.induction_on t (isClosed_le hc.abs continuous_const) (fun n => (hn n).le)
    exact (not_le.mpr hε) (hall ⟨s, hs⟩)
  have hh := martingale_abs_maximal_sequence μ F M hM (fun n => (q n).val) T
    (fun n => (q n).property.2) ε
  exact (mul_le_mul le_rfl (measure_mono_ae he) bot_le bot_le).trans hh

lemma martingale_abs_maximal_L2 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → ℝ) (hM : Martingale M F μ) (T : NNReal)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T => M s.val ω))
    (Z : Lp ℝ 2 μ) (hZ : μ[(Z : Ω → ℝ) | F T] =ᵐ[μ] M T) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) T, (ε : ℝ) < |M s ω|} ≤ eLpNorm Z 2 μ := by
  apply (martingale_abs_maximal_continuous μ F M hM T hc ε).trans
  have he : (fun ω => |M T ω|) =ᵐ[μ] fun ω => |μ[(Z : Ω → ℝ) | F T] ω| := by
    filter_upwards [hZ] with ω hω
    simp only [hω]
  rw [integral_congr_ae he]
  apply (ENNReal.ofReal_le_ofReal (integral_abs_condExp_le (Z : Ω → ℝ))).trans
  have hnorm : ENNReal.ofReal (∫ ω, |Z ω| ∂μ) = eLpNorm Z 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.memLp Z).aestronglyMeasurable,
      ofReal_integral_eq_lintegral_ofReal ((Lp.memLp Z).integrable one_le_two).abs
        (Eventually.of_forall fun _ => abs_nonneg _)]
    simp only [Real.enorm_eq_ofReal_abs]
  rw [hnorm]
  exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two

lemma elementary_process_maximal {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    {N M : ℕ} (t : Fin (N+1) → NNReal) (u : Fin (M+1) → NNReal)
    (H : Fin N → Ω → ℝ) (K : Fin M → Ω → ℝ) (ht : Monotone t) (hu : Monotone u)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hK : ∀ j, Measurable[F (u j.castSucc)] (K j))
    (hH2 : ∀ i, MemLp (H i) 2 μ) (hK2 : ∀ j, MemLp (K j) 2 μ)
    (X Y : Lp ℝ 2 μ) (hX : (X : Ω → ℝ) =ᵐ[μ] S01522 B H t)
    (hY : (Y : Ω → ℝ) =ᵐ[μ] S01522 B K u) (T : NNReal) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) T,
      (ε : ℝ) < |R01522 B H t s ω-R01522 B K u s ω|} ≤ edist X Y := by
  have hp := elementary_brownian_process Ω mΩ μ inferInstance F B hB hm hind N t H ht hH hH2
  have hq := elementary_brownian_process Ω mΩ μ inferInstance F B hB hm hind M u K hu hK hK2
  have hc : ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T =>
      R01522 B H t s.val ω-R01522 B K u s.val ω) := by
    filter_upwards [hp.2.1, hq.2.1] with ω hp hq
    exact (hp.sub hq).comp continuous_subtype_val
  have hce : μ[((X-Y : Lp ℝ 2 μ) : Ω → ℝ) | F T] =ᵐ[μ]
      (R01522 B H t-R01522 B K u) T := by
    refine (condExp_congr_ae (Lp.coeFn_sub X Y)).trans ?_
    refine (condExp_sub ((Lp.memLp X).integrable one_le_two) ((Lp.memLp Y).integrable one_le_two) (F T)).trans ?_
    exact ((condExp_congr_ae hX).trans (hp.2.2.1 T).2.1).sub
      ((condExp_congr_ae hY).trans (hq.2.2.1 T).2.1)
  have hb := martingale_abs_maximal_L2 μ F _ (hp.1.sub hq.1) T hc (X-Y) hce ε
  have he : eLpNorm (X-Y : Lp ℝ 2 μ) 2 μ = edist X Y := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (Lp.coeFn_sub X Y)
  exact hb.trans_eq he

lemma continuous_subsequence_of_maximal {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ℕ → NNReal → Ω → ℝ) (X : ℕ → Lp ℝ 2 μ)
    (hC : CauchySeq X)
    (hc : ∀ n T, ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T => M n s.val ω))
    (hb : ∀ n m T (ε : NNReal),
      (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) T, (ε : ℝ) < |M n s ω-M m s ω|} ≤ edist (X n) (X m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ T : NNReal, ∀ᵐ ω ∂μ,
      ∃ g : C(Icc (0 : NNReal) T, ℝ),
        TendstoUniformly (fun n s => M (φ n) s.val ω) g atTop := by
  let a : ℕ → NNReal := fun n => (1/2)^n
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  obtain ⟨φ, hφ, hstep⟩ := hC.subseq_mem (V := fun n =>
    {p : Lp ℝ 2 μ × Lp ℝ 2 μ | edist p.1 p.2 < (a n : ENNReal)*(a n : ENNReal)})
    (fun n => edist_mem_uniformity (by exact_mod_cast mul_pos (ha n) (ha n)))
  refine ⟨φ, hφ, ?_⟩
  intro T
  let E := fun n => {ω | ∃ s ∈ Icc (0 : NNReal) T, (a n : ℝ) < |M (φ (n+1)) s ω-M (φ n) s ω|}
  have hE (n : ℕ) : μ (E n) ≤ a n := by
    have h := (hb (φ (n+1)) (φ n) T (a n)).trans (hstep n).le
    by_contra hn
    have hh := ENNReal.mul_lt_mul_left (show (a n : ENNReal) ≠ 0 by exact_mod_cast (ha n).ne')
      ENNReal.coe_ne_top (lt_of_not_ge hn)
    have he : μ (E n)*(a n : ENNReal) = (a n : ENNReal)*μ (E n) := mul_comm _ _
    exact (not_lt_of_ge h) (he ▸ hh)
  have hs : (∑' n, μ (E n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∑' n, ((1/2 : ENNReal)^n)) ?_ ?_
    · rw [ENNReal.tsum_geometric]
      norm_num
    · apply ENNReal.tsum_le_tsum
      intro n
      have ha' : (a n : ENNReal) = (1/2 : ENNReal)^n := by
        norm_num [a, ENNReal.coe_pow, ENNReal.coe_div]
      exact (hE n).trans_eq ha'
  have hcont : ∀ᵐ ω ∂μ, ∀ n, Continuous (fun s : Icc (0 : NNReal) T => M (φ n) s.val ω) :=
    ae_all_iff.mpr (fun n => hc (φ n) T)
  filter_upwards [hcont, ae_eventually_notMem hs] with ω hcont hω
  let f : ℕ → C(Icc (0 : NNReal) T, ℝ) := fun n => ⟨fun s => M (φ n) s.val ω, hcont n⟩
  obtain ⟨k, hk⟩ := eventually_atTop.mp hω
  have hdist (n : ℕ) (hn : k ≤ n) : dist (f n) (f (n+1)) ≤ (a n : ℝ) := by
    apply (ContinuousMap.dist_le (a n).coe_nonneg).mpr
    intro s
    have hnot := hk n hn
    have he : |M (φ (n+1)) s.val ω-M (φ n) s.val ω| ≤ a n :=
      le_of_not_gt (fun h => hnot ⟨s.val, s.property, h⟩)
    simpa only [Real.dist_eq, f, ContinuousMap.coe_mk, abs_sub_comm] using he
  have hsum : Summable (fun n : ℕ => (a (n+k) : ℝ)) := by
    simpa only [a, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      (summable_nat_add_iff k).mpr (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  have hcau : CauchySeq (fun n => f (n+k)) := cauchySeq_of_dist_le_of_summable _
    (fun n => by simpa only [Nat.succ_add] using hdist (n+k) (Nat.le_add_left _ _)) hsum
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcau
  have hfg : Tendsto f atTop (𝓝 g) := (tendsto_add_atTop_iff_nat k).mp hg
  exact ⟨g, ContinuousMap.tendsto_iff_tendstoUniformly.mp hfg⟩

lemma continuous_nnreal_of_Icc (f : NNReal → ℝ)
    (h : ∀ n : ℕ, Continuous (fun s : Icc (0 : NNReal) n => f s.val)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hc : ContinuousOn f (Icc (0 : NNReal) n) := continuousOn_iff_continuous_domRestrict.mpr (h n)
  exact hc.continuousAt (Filter.mem_of_superset (Iio_mem_nhds hn) (fun _ hx => ⟨zero_le, hx.le⟩))

lemma continuous_martingale_difference_maximal {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (M C : NNReal → Ω → ℝ) (hM : Martingale M F μ) (hC : Martingale C F μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun s => M s ω)) (hcC : ∀ᵐ ω ∂μ, Continuous (fun s => C s ω))
    (X Z : Lp ℝ 2 μ) (T : NNReal)
    (hX : μ[(X : Ω → ℝ) | F T] =ᵐ[μ] M T) (hZ : μ[(Z : Ω → ℝ) | F T] =ᵐ[μ] C T) (ε : NNReal) :
    (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) T, (ε : ℝ) < |M s ω-C s ω|} ≤ edist X Z := by
  have hc : ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T => M s.val ω-C s.val ω) := by
    filter_upwards [hcM, hcC] with ω hm hc
    exact (hm.sub hc).comp continuous_subtype_val
  have hce : μ[((X-Z : Lp ℝ 2 μ) : Ω → ℝ) | F T] =ᵐ[μ] (M-C) T :=
    (condExp_congr_ae (Lp.coeFn_sub X Z)).trans
      ((condExp_sub ((Lp.memLp X).integrable one_le_two) ((Lp.memLp Z).integrable one_le_two) (F T)).trans (hX.sub hZ))
  have hb := martingale_abs_maximal_L2 μ F (M-C) (hM.sub hC) T hc (X-Z) hce ε
  have he : eLpNorm (X-Z : Lp ℝ 2 μ) 2 μ = edist X Z := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (Lp.coeFn_sub X Z)
  exact hb.trans_eq he

lemma elementary_continuous_limit {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (N : ℕ → ℕ) (t : ∀ n, Fin (N n+1) → NNReal) (H : ∀ n, Fin (N n) → Ω → ℝ)
    (ht : ∀ n, Monotone (t n)) (hH : ∀ n i, Measurable[F (t n i.castSucc)] (H n i))
    (hH2 : ∀ n i, MemLp (H n i) 2 μ) (X : ℕ → Lp ℝ 2 μ)
    (hX : ∀ n, (X n : Ω → ℝ) =ᵐ[μ] S01522 B (H n) (t n))
    (Z : Lp ℝ 2 μ) (hZ : Tendsto X atTop (𝓝 Z)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : NNReal → Ω → ℝ,
      Martingale C F μ ∧ (∀ s, C s =ᵐ[μ] μ[(Z : Ω → ℝ) | F s]) ∧
      (∀ᵐ ω ∂μ, Continuous (fun s => C s ω)) ∧
      ∀ T : NNReal, ∀ᵐ ω ∂μ,
        TendstoUniformly (fun n (s : Icc (0 : NNReal) T) => R01522 B (H (φ n)) (t (φ n)) s.val ω)
          (fun s => C s.val ω) atTop := by
  let M := fun n => R01522 B (H n) (t n)
  have hp := fun n => elementary_brownian_process Ω mΩ μ inferInstance F B hB hm hind
    (N n) (t n) (H n) (ht n) (hH n) (hH2 n)
  have hc : ∀ n T, ∀ᵐ ω ∂μ, Continuous (fun s : Icc (0 : NNReal) T => M n s.val ω) := by
    intro n T
    filter_upwards [(hp n).2.1] with ω hω
    exact hω.comp continuous_subtype_val
  have hb := fun n m T ε => elementary_process_maximal μ F B hB hm hind
    (t n) (t m) (H n) (H m) (ht n) (ht m) (hH n) (hH m) (hH2 n) (hH2 m)
    (X n) (X m) (hX n) (hX m) T ε
  obtain ⟨φ, hφ, hφlim⟩ := continuous_subsequence_of_maximal μ M X hZ.cauchySeq hc hb
  let C : NNReal → Ω → ℝ := fun s ω => limUnder atTop (fun n => M (φ n) s ω)
  have hCm : StronglyAdapted F C := by
    intro s
    let : MeasurableSpace Ω := F s
    exact StronglyMeasurable.limUnder (fun n => (hp (φ n)).1.stronglyMeasurable s)
  have hCu : ∀ T : NNReal, ∀ᵐ ω ∂μ,
      Continuous (fun s : Icc (0 : NNReal) T => C s.val ω) ∧
      TendstoUniformly (fun n (s : Icc (0 : NNReal) T) => M (φ n) s.val ω) (fun s => C s.val ω) atTop := by
    intro T
    filter_upwards [hφlim T] with ω hω
    obtain ⟨g, hg⟩ := hω
    have he : (fun s : Icc (0 : NNReal) T => C s.val ω) = g :=
      funext (fun s => (hg.tendsto_at s).limUnder_eq)
    rw [he]
    exact ⟨g.continuous, hg⟩
  have hCe : ∀ s, C s =ᵐ[μ] μ[(Z : Ω → ℝ) | F s] := by
    intro s
    have hpae : ∀ᵐ ω ∂μ, Tendsto (fun n => M (φ n) s ω) atTop (𝓝 (C s ω)) := by
      filter_upwards [hCu s] with ω hω
      exact hω.2.tendsto_at ⟨s, zero_le, le_rfl⟩
    have hprobC := tendstoInMeasure_of_tendsto_ae
      (fun n => ((hp (φ n)).1.stronglyMeasurable s).mono (F.le s) |>.aestronglyMeasurable) hpae
    let P := fun W : Lp ℝ 2 μ => (condExpL2 ℝ ℝ (F.le s) W : Lp ℝ 2 μ)
    have hPc : Continuous P := continuous_subtype_val.comp (condExpL2 ℝ ℝ (F.le s)).continuous
    have hprobP := tendstoInMeasure_of_tendsto_Lp ((hPc.tendsto Z).comp (hZ.comp hφ.tendsto_atTop))
    have hprobM : TendstoInMeasure μ (fun n => M (φ n) s) atTop (P Z) := by
      apply hprobP.congr_left
      intro n
      exact (L2_condExp_rep μ F s (X (φ n))).trans
        ((condExp_congr_ae (hX (φ n))).trans ((hp (φ n)).2.2.1 s).2.1)
    exact (tendstoInMeasure_ae_unique hprobC hprobM).trans (L2_condExp_rep μ F s Z)
  refine ⟨φ, hφ, C, (martingale_condExp (Z : Ω → ℝ) F μ).congr hCm (fun s => (hCe s).symm),
    hCe, ?_, fun T => (hCu T).mono (fun _ h => h.2)⟩
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, Continuous (fun s : Icc (0 : NNReal) n => C s.val ω) :=
    ae_all_iff.mpr (fun n => (hCu n).mono (fun _ h => h.1))
  exact hall.mono (fun ω hω => continuous_nnreal_of_Icc (fun s => C s ω) hω)

lemma measure_tendsto_zero_of_maximal {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (X : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hZ : Tendsto X atTop (𝓝 Z)) (ε : NNReal) (hε : 0 < ε)
    (hb : ∀ n, (ε : ENNReal)*μ (E n) ≤ edist (X n) Z) :
    Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
  have hε0 : (ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
  have he : Tendsto (fun n => edist (X n) Z) atTop (𝓝 0) := by
    simpa using hZ.edist (tendsto_const_nhds (x := Z))
  have hd : Tendsto (fun n => edist (X n) Z/(ε : ENNReal)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const he (Or.inr hε0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd (fun _ => bot_le)
  intro n
  apply (ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.coe_ne_top)).mpr
  simpa only [mul_comm] using hb n

lemma stopped_square_integral_measurable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (T : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) (s : NNReal) (hs : s ≤ T) :
    StronglyMeasurable[F (s : ℝ)]
      (fun ω => ∫ r in Ioc (0 : ℝ) s, (B01522 T X n α l j r ω)^2) := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  let t : Icc (0 : ℝ) T := ⟨s, s.coe_nonneg, hs⟩
  let c : ℝ → Iic t := fun r =>
    ⟨⟨min (s : ℝ) (max 0 r), le_min s.coe_nonneg (le_max_left _ _),
      (min_le_left _ _).trans hs⟩, (show min (s : ℝ) (max 0 r) ≤ s from min_le_left _ _)⟩
  have hcm : Measurable c := by
    apply Measurable.subtype_mk
    apply Measurable.subtype_mk
    fun_prop
  have hp := (stopped_integrand_predictable F T X α l hm hc hl n j).isStronglyProgressive t
  let : MeasurableSpace Ω := F (s : ℝ)
  have hb : StronglyMeasurable (fun p : ℝ × Ω =>
      (B01522 T X n α l j (c p.1).val.val p.2)^2) :=
    (hp.comp_measurable ((hcm.comp measurable_fst).prodMk measurable_snd)).pow 2
  have hi := StronglyMeasurable.integral_prod_left
    (f := fun r ω => (B01522 T X n α l j (c r).val.val ω)^2)
    (μ := volume.restrict (Ioc (0 : ℝ) s)) hb
  convert hi using 1
  funext ω
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  simp only [c, max_eq_right hr.1.le, min_eq_right hr.2]

lemma stopped_square_integral_paths {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j) (n : ℕ) (j : Fin d) :
    ∀ᵐ ω ∂μ,
      Continuous (fun s : Icc (0 : ℝ) T => ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) ∧
      Monotone (fun s : Icc (0 : ℝ) T => ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) := by
  have hi := (localizer_integrand_integrable μ F T X α l hm hc h0 hl n j).1
  filter_upwards [hi.prod_left_ae] with ω hω
  have hcont := intervalIntegral.continuousOn_primitive_interval (μ := (volume : Measure ℝ))
    (show IntegrableOn (fun r => (B01522 T X n α l j r ω)^2) (uIcc (0 : ℝ) T) volume by
      simpa only [uIcc_of_le T.coe_nonneg, IntegrableOn] using hω)
  rw [uIcc_of_le T.coe_nonneg] at hcont
  constructor
  · have he : (fun s : Icc (0 : ℝ) T => ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) =
        (fun s : Icc (0 : ℝ) T => ∫ r in (0 : ℝ)..s.val, (B01522 T X n α l j r ω)^2) := by
      funext s
      exact (intervalIntegral.integral_of_le s.property.1).symm
    rw [he]
    exact continuousOn_iff_continuous_domRestrict.mp hcont
  · intro s t hst
    have hsub : Ioc (0 : ℝ) t.val ⊆ Icc (0 : ℝ) T :=
      fun _ hr => ⟨hr.1.le, hr.2.trans t.property.2⟩
    apply setIntegral_mono_set
      (hω.mono_measure (Measure.restrict_mono hsub le_rfl))
      (Filter.Eventually.of_forall (fun r => sq_nonneg _))
    exact Filter.Eventually.of_forall (fun r hr => ⟨hr.1, hr.2.trans hst⟩)

lemma square_compensator_condExp {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (Z : Lp ℝ 2 μ) (A D : Ω → ℝ) (hA : Integrable A μ) (hD : Integrable D μ)
    (hmD : StronglyMeasurable[G] D)
    (hiso : μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | G] ω)^2 | G] =ᵐ[μ] μ[A-D | G]) :
    μ[fun ω => (Z ω)^2-A ω | G] =ᵐ[μ]
      fun ω => (μ[(Z : Ω → ℝ) | G] ω)^2-D ω := by
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp hG (Lp.memLp Z)
  have hs := condExp_sub (Lp.memLp Z).integrable_sq hA G
  have hd := condExp_sub hA hD G
  rw [condExp_of_stronglyMeasurable hG hmD hD] at hd
  filter_upwards [hv, hs, hd, hiso] with ω hv hs hd hiso
  change μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | G] ω)^2 | G] ω =
    μ[fun ω => (Z ω)^2 | G] ω-(μ[(Z : Ω → ℝ) | G] ω)^2 at hv
  change μ[fun ω => (Z ω)^2-A ω | G] ω =
    μ[fun ω => (Z ω)^2 | G] ω-μ[A | G] ω at hs
  change μ[A-D | G] ω = μ[A | G] ω-D ω at hd
  linarith

lemma stopped_square_martingale {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ) (T : NNReal)
    (X : ℝ → Ω → Fin d → NNReal) (α l : Fin d → ℝ)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, Measurable[F s] (X s))
    (hc : ∀ ω j, Continuous (fun s : Icc (0 : ℝ) T => (X s.val ω j : ℝ)))
    (h0 : ∀ᵐ ω ∂μ, ∀ j, X 0 ω j ≤ 1) (hl : ∀ j, 0 ≤ l j)
    (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : ∀ s : NNReal, Measurable[F (s : ℝ)] (B s))
    (hind : ∀ a b : NNReal, a ≤ b → Indep (F (a : ℝ))
      (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (n : ℕ) (j : Fin d) (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H01522 T X n α l j m) (t01522 T m))
    (hZ : Tendsto Y atTop (𝓝 Z))
    (C : NNReal → Ω → ℝ) (hC : Martingale C (F01522 F) μ)
    (hCe : ∀ s, C s =ᵐ[μ] μ[(Z : Ω → ℝ) | F (s : ℝ)]) :
    Martingale (fun s : Icc (0 : ℝ) T => fun ω =>
      (C ⟨s.val, s.property.1⟩ ω)^2-
        ∫ r in Ioc (0 : ℝ) s.val, (B01522 T X n α l j r ω)^2) (filt0152 F T) μ := by
  let A : Ω → ℝ := fun ω => ∫ r in Ioc (0 : ℝ) T, (B01522 T X n α l j r ω)^2
  let D : NNReal → Ω → ℝ := fun s ω => ∫ r in Ioc (0 : ℝ) s, (B01522 T X n α l j r ω)^2
  have hA : Integrable A μ := stopped_integrand_future_integrable μ F T X α l hm hc h0 hl n j 0
  have hD (s : NNReal) (hs : s ≤ T) : Integrable (D s) μ :=
    (stopped_integrand_interval μ F T X α l hm hc h0 hl n j 0 s zero_le hs).1
  have hDm (s : NNReal) (hs : s ≤ T) : StronglyMeasurable[F (s : ℝ)] (D s) :=
    stopped_square_integral_measurable F T X α l hm hc hl n j s hs
  have he (s : NNReal) (hs : s ≤ T) :
      μ[fun ω => (Z ω)^2-A ω | F (s : ℝ)] =ᵐ[μ] fun ω => (C s ω)^2-D s ω := by
    have hsplit : (fun ω => ∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) =ᵐ[μ] A-D s := by
      filter_upwards [stopped_integrand_interval_split μ F T X α l hm hc h0 hl n j 0 s zero_le hs]
        with ω hω
      change A ω-(∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) = D s ω at hω
      change (∫ r in Ioc (s : ℝ) T, (B01522 T X n α l j r ω)^2) = A ω-D s ω
      linarith
    have hi := (stopped_brownian_conditional_isometry μ F T X α l hm hc h0 hl B hB hBm hind
      n j Y Z hY hZ s).trans (condExp_congr_ae hsplit)
    have h := square_compensator_condExp μ (F (s : ℝ)) (F.le _) Z A (D s) hA (hD s hs) (hDm s hs) hi
    filter_upwards [h, hCe s] with ω hω hce
    simpa only [hce] using hω
  apply (martingale_condExp (fun ω => (Z ω)^2-A ω) (filt0152 F T) μ).congr
  · intro s
    exact ((hC.stronglyMeasurable ⟨s.val, s.property.1⟩).pow 2).sub
      (hDm ⟨s.val, s.property.1⟩ s.property.2)
  · intro s
    exact he ⟨s.val, s.property.1⟩ s.property.2

lemma continuous_versions_ae_eq {Ω ι : Type} [MeasurableSpace Ω]
    [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι] [Nonempty ι]
    (μ : Measure Ω) (C D : ι → Ω → ℝ)
    (hC : ∀ᵐ ω ∂μ, Continuous (fun s => C s ω))
    (hD : ∀ᵐ ω ∂μ, Continuous (fun s => D s ω))
    (he : ∀ s, C s =ᵐ[μ] D s) : ∀ᵐ ω ∂μ, ∀ s, C s ω = D s ω := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq ι
  have hcount : ∀ᵐ ω ∂μ, ∀ n : ℕ, C (q n) ω = D (q n) ω := ae_all_iff.mpr (fun n => he (q n))
  filter_upwards [hC, hD, hcount] with ω hC hD he
  intro s
  exact hq.induction_on s (isClosed_eq hC hD) he

lemma stopped_brownian_limit : stoppedBrownianLimitStatement := by
  intro d Ω mΩ μ hμ F T X α l hm hc h0 hl B hB hBm hind n j
  let := hμ
  let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
  have hA := stopped_integrand_approximation d Ω mΩ μ hμ F T X α l hm hc h0 hl n j
  have ht : ∀ m, Monotone (t01522 T m) := by
    intro m a b hab
    exact (hA.1 m).1 (show a.val ≤ b.val from hab)
  have hH : ∀ m i, Measurable[F01522 F (t01522 T m i.castSucc)] (H01522 T X n α l j m i) :=
    fun m i => ((hA.1 m).2.2.2.1 i.val).1
  have hH2 : ∀ m i, MemLp (H01522 T X n α l j m i) 2 μ :=
    fun m i => ((hA.1 m).2.2.2.1 i.val).2
  have hC := stopped_step_cauchy μ F T X α l hm hc h0 hl n j
  obtain ⟨Y, hY, hYC⟩ := elementary_brownian_cauchy Ω mΩ μ hμ (F01522 F) B hB hBm hind
    (N01522 T) (t01522 T) (H01522 T X n α l j) ht hH hH2 hC
  obtain ⟨Z, hZ⟩ := elementary_brownian_limit Ω mΩ μ hμ (F01522 F) B hB hBm hind
    (N01522 T) (t01522 T) (H01522 T X n α l j) ht hH hH2 Y hY hYC
  have hiso := stopped_brownian_limit_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ.1
  refine ⟨finite_stopped_step T X n α l j, hC, Y, Z, hY, hZ.1, hZ.2.1,
    hZ.2.2.1, hZ.2.2.2.1, hZ.2.2.2.2.1, hZ.2.2.2.2.2, hiso, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hiso]
    exact (localizer_integrand_integrable μ F T X α l hm hc h0 hl n j).2
  · intro s
    exact ⟨stopped_integrand_future_integrable μ F T X α l hm hc h0 hl n j s,
      stopped_brownian_conditional_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ.1 s⟩
  · exact stopped_brownian_after_horizon μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ.1
  · exact stopped_brownian_increment_isometry μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ.1
  · apply L2_projection_continuous μ F Z T ((l j)^2*(α j)^2*(n+2)) (by positivity)
    intro s t hst htT
    exact (stopped_brownian_increment_isometry μ F T X α l hm hc h0 hl B hB hBm hind
      n j Y Z hY hZ.1 s t hst htT).2.2

  · obtain ⟨φ, hφ, C, hC, hCe, hCc, hCu⟩ := elementary_continuous_limit μ (F01522 F) B hB hBm hind
      (N01522 T) (t01522 T) (H01522 T X n α l j) ht hH hH2 Y hY Z hZ.1
    have hbound : ∀ m (U ε : NNReal),
        (ε : ENNReal)*μ {ω | ∃ s ∈ Icc (0 : NNReal) U,
          (ε : ℝ) < |R01522 B (H01522 T X n α l j m) (t01522 T m) s ω-C s ω|} ≤ edist (Y m) Z := by
      intro m U ε
      have hp := elementary_brownian_process Ω mΩ μ hμ (F01522 F) B hB hBm hind
        (N01522 T m) (t01522 T m) (H01522 T X n α l j m) (ht m) (hH m) (hH2 m)
      exact continuous_martingale_difference_maximal μ (F01522 F) _ C hp.1 hC hp.2.1 hCc (Y m) Z U
        ((condExp_congr_ae (hY m)).trans (hp.2.2.1 U).2.1) (hCe U).symm ε
    refine ⟨φ, hφ, C, hC, hCe, hCc, hCu, hbound, ?_, ?_, ?_, ?_, ?_⟩
    · intro U ε hε
      exact measure_tendsto_zero_of_maximal μ _ Y Z hZ.1 ε hε (fun m => hbound m U ε)
    · exact stopped_square_martingale μ F T X α l hm hc h0 hl B hB hBm hind n j Y Z hY hZ.1 C hC hCe
    · exact stopped_square_integral_paths μ F T X α l hm hc h0 hl n j
    · have hzero : C 0 =ᵐ[μ] 0 := (hCe 0).trans hZ.2.2.1
      have htail : ∀ᵐ ω ∂μ, ∀ s : Ici T, C s.val ω = Z ω := by
        apply continuous_versions_ae_eq μ (fun s : Ici T => C s.val) (fun _ => (Z : Ω → ℝ))
        · exact hCc.mono (fun ω hω => hω.comp continuous_subtype_val)
        · exact Filter.Eventually.of_forall (fun _ => continuous_const)
        · intro s
          exact (hCe s.val).trans
            (stopped_brownian_after_horizon μ F T X α l hm hc h0 hl B hB hBm hind
              n j Y Z hY hZ.1 s.val s.property)
      filter_upwards [hzero, htail] with ω hzero htail
      exact ⟨hzero, fun s hs => htail ⟨s, hs⟩⟩
    · intro D hDc hDe
      exact continuous_versions_ae_eq μ C D hCc hDc (fun s => (hCe s).trans (hDe s).symm)

lemma indep_pair_components {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (X Y : Ω → ℝ)
    (h : Indep G (MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance) μ) :
    Indep G (MeasurableSpace.comap X inferInstance) μ ∧
      Indep G (MeasurableSpace.comap Y inferInstance) μ := by
  have hm : Measurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => (X ω, Y ω)) := measurable_iff_comap_le.mpr le_rfl
  exact ⟨indep_of_indep_of_le_right h hm.fst.comap_le,
    indep_of_indep_of_le_right h hm.snd.comap_le⟩

lemma elementary_two_disjoint {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B C : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (hmB : ∀ t, Measurable[F t] (B t)) (hmC : ∀ t, Measurable[F t] (C t))
    (hindB : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    (hindC : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => C b ω-C a ω) inferInstance) μ)
    (H K : Ω → ℝ) (a b c e : NNReal) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e)
    (hH : Measurable[F a] H) (hK : Measurable[F c] K) (hH2 : MemLp H 2 μ) (hK2 : MemLp K 2 μ) :
    (∫ ω, J01522 B H a b ω * J01522 C K c e ω ∂μ) = 0 := by
  have hJ := elementary_brownian_interval μ F B hB hmB hindB a b hab H hH hH2
  have hL := elementary_brownian_interval μ F C hC hmC hindC c e hce K hK hK2
  have hmJ : Measurable[F c] (J01522 B H a b) :=
    (hH.mono (F.mono (hab.trans hbc)) le_rfl).mul
      (((hmB b).mono (F.mono hbc) le_rfl).sub ((hmB a).mono (F.mono (hab.trans hbc)) le_rfl))
  have hp := condExp_mul_of_stronglyMeasurable_left hmJ.stronglyMeasurable
    (hJ.1.integrable_mul hL.1) (hL.1.integrable one_le_two)
  have hz : μ[J01522 B H a b * J01522 C K c e | F c] =ᵐ[μ] 0 := by
    filter_upwards [hp, hL.2.1] with ω hp hz
    simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hp
  calc
    _ = ∫ ω, μ[J01522 B H a b * J01522 C K c e | F c] ω ∂μ := (integral_condExp (F.le c)).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

lemma elementary_two_same {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B C : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (_hC : IsBrownianReal C μ)
    (hmB : ∀ t, Measurable[F t] (B t)) (hmC : ∀ t, Measurable[F t] (C t))
    (H K : Ω → ℝ) (a b : NNReal)
    (hpair : Indep (F a) (MeasurableSpace.comap (fun ω => (B b ω-B a ω, C b ω-C a ω)) inferInstance) μ)
    (hBC : IndepFun (fun ω => B b ω-B a ω) (fun ω => C b ω-C a ω) μ)
    (hH : Measurable[F a] H) (hK : Measurable[F a] K) :
    (∫ ω, J01522 B H a b ω * J01522 C K a b ω ∂μ) = 0 := by
  let D := fun ω => B b ω-B a ω
  let E := fun ω => C b ω-C a ω
  have hmD : Measurable D := ((hmB b).mono (F.le b) le_rfl).sub ((hmB a).mono (F.le a) le_rfl)
  have hmE : Measurable E := ((hmC b).mono (F.le b) le_rfl).sub ((hmC a).mono (F.le a) le_rfl)
  have hInd : IndepFun (H*K) (fun ω => (D ω, E ω)) μ :=
    indep_of_indep_of_le_left hpair (hH.mul hK).comap_le
  have hprod := hInd.comp measurable_id (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1*p.2))
  have hzD : (∫ ω, D ω ∂μ) = 0 := by
    exact (hB.toIsPreBrownianReal.hasLaw_sub b a).integral_eq.trans integral_id_gaussianReal
  have hz : (∫ ω, D ω*E ω ∂μ) = 0 := by
    rw [hBC.integral_fun_mul_eq_mul_integral hmD.aestronglyMeasurable hmE.aestronglyMeasurable, hzD, zero_mul]
  calc
    _ = ∫ ω, (H ω*K ω)*(D ω*E ω) ∂μ := by congr 1; ext ω; dsimp [J01522, D, E]; ring
    _ = (∫ ω, H ω*K ω ∂μ)*(∫ ω, D ω*E ω ∂μ) :=
      hprod.integral_fun_mul_eq_mul_integral ((hH.mul hK).mono (F.le a) le_rfl).aestronglyMeasurable
        (hmD.mul hmE).aestronglyMeasurable
    _ = 0 := by rw [hz, mul_zero]

lemma elementary_two_sum {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B C : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (hmB : ∀ t, Measurable[F t] (B t)) (hmC : ∀ t, Measurable[F t] (C t))
    (hpair : ∀ a b, a ≤ b → Indep (F a)
      (MeasurableSpace.comap (fun ω => (B b ω-B a ω, C b ω-C a ω)) inferInstance) μ)
    (hBC : ∀ a b, a ≤ b → IndepFun (fun ω => B b ω-B a ω) (fun ω => C b ω-C a ω) μ)
    {N : ℕ} (t : Fin (N+1) → NNReal) (H K : Fin N → Ω → ℝ) (ht : Monotone t)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hK : ∀ i, Measurable[F (t i.castSucc)] (K i))
    (hH2 : ∀ i, MemLp (H i) 2 μ) (hK2 : ∀ i, MemLp (K i) 2 μ) :
    Integrable (fun ω => S01522 B H t ω*S01522 C K t ω) μ ∧
      (∫ ω, S01522 B H t ω*S01522 C K t ω ∂μ) = 0 := by
  have hiB := fun a b hab => (indep_pair_components μ (F a) _ _ (hpair a b hab)).1
  have hiC := fun a b hab => (indep_pair_components μ (F a) _ _ (hpair a b hab)).2
  have hJ := fun i : Fin N => (elementary_brownian_interval μ F B hB hmB hiB
    _ _ (ht (Fin.castSucc_le_succ i)) (H i) (hH i) (hH2 i)).1
  have hL := fun i : Fin N => (elementary_brownian_interval μ F C hC hmC hiC
    _ _ (ht (Fin.castSucc_le_succ i)) (K i) (hK i) (hK2 i)).1
  have hprod (i j : Fin N) : Integrable (fun ω =>
      J01522 B (H i) (t i.castSucc) (t i.succ) ω * J01522 C (K j) (t j.castSucc) (t j.succ) ω) μ :=
    (hJ i).integrable_mul (hL j)
  have hz (i j : Fin N) : (∫ ω, J01522 B (H i) (t i.castSucc) (t i.succ) ω *
      J01522 C (K j) (t j.castSucc) (t j.succ) ω ∂μ) = 0 := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact elementary_two_disjoint μ F B C hB hC hmB hmC hiB hiC (H i) (K j) _ _ _ _
        (ht (Fin.castSucc_le_succ i)) (ht (Fin.succ_le_castSucc_iff.mpr hij))
        (ht (Fin.castSucc_le_succ j)) (hH i) (hK j) (hH2 i) (hK2 j)
    · exact elementary_two_same μ F B C hB hC hmB hmC (H i) (K i) _ _
        (hpair _ _ (ht (Fin.castSucc_le_succ i))) (hBC _ _ (ht (Fin.castSucc_le_succ i))) (hH i) (hK i)
    · simpa only [mul_comm] using elementary_two_disjoint μ F C B hC hB hmC hmB hiC hiB (K j) (H i) _ _ _ _
        (ht (Fin.castSucc_le_succ j)) (ht (Fin.succ_le_castSucc_iff.mpr hji))
        (ht (Fin.castSucc_le_succ i)) (hK j) (hH i) (hK2 j) (hH2 i)
  have hSH : MemLp (S01522 B H t) 2 μ := memLp_finsetSum _ (fun i _ => hJ i)
  have hSK : MemLp (S01522 C K t) 2 μ := memLp_finsetSum _ (fun i _ => hL i)
  refine ⟨hSH.integrable_mul hSK, ?_⟩
  calc
    _ = ∫ ω, ∑ i, ∑ j, J01522 B (H i) (t i.castSucc) (t i.succ) ω *
        J01522 C (K j) (t j.castSucc) (t j.succ) ω ∂μ := by
      congr 1; ext ω; simp only [S01522, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∫ ω, J01522 B (H i) (t i.castSucc) (t i.succ) ω *
        J01522 C (K j) (t j.castSucc) (t j.succ) ω ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
      exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hprod i j))
    _ = 0 := by simp only [hz, Finset.sum_const_zero]

lemma elementary_two_future_set {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B C : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (hmB : ∀ t, Measurable[F t] (B t)) (hmC : ∀ t, Measurable[F t] (C t))
    (hpair : ∀ a b, a ≤ b → Indep (F a)
      (MeasurableSpace.comap (fun ω => (B b ω-B a ω, C b ω-C a ω)) inferInstance) μ)
    (hBC : ∀ a b, a ≤ b → IndepFun (fun ω => B b ω-B a ω) (fun ω => C b ω-C a ω) μ)
    {N : ℕ} (t : Fin (N+1) → NNReal) (H K : Fin N → Ω → ℝ) (ht : Monotone t)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hK : ∀ i, Measurable[F (t i.castSucc)] (K i))
    (hH2 : ∀ i, MemLp (H i) 2 μ) (hK2 : ∀ i, MemLp (K i) 2 μ)
    (s : NNReal) (E : Set Ω) (hE : MeasurableSet[F s] E) :
    (∫ ω in E, (S01522 B H t ω-R01522 B H t s ω)*(S01522 C K t ω-R01522 C K t s ω) ∂μ) = 0 := by
  let u := fun i => max s (t i)
  have hu : Monotone u := fun i j hij => max_le_max_left s (ht hij)
  have hEH : ∀ i, Measurable[F (u i.castSucc)] (E.indicator (H i)) := fun i =>
    ((hH i).mono (F.mono (le_max_right _ _)) le_rfl).indicator (F.mono (le_max_left _ _) E hE)
  have hEK : ∀ i, Measurable[F (u i.castSucc)] (E.indicator (K i)) := fun i =>
    ((hK i).mono (F.mono (le_max_right _ _)) le_rfl).indicator (F.mono (le_max_left _ _) E hE)
  have hz := (elementary_two_sum μ F B C hB hC hmB hmC hpair hBC u
    (fun i => E.indicator (H i)) (fun i => E.indicator (K i)) hu hEH hEK
    (fun i => (hH2 i).indicator (F.le s E hE)) (fun i => (hK2 i).indicator (F.le s E hE))).2
  rw [← integral_indicator (F.le s E hE)]
  convert hz using 1
  congr 1
  ext ω
  simp only [elementary_sum_indicator]
  simp only [u, elementary_future_sum]
  by_cases hω : ω ∈ E <;> simp [hω]

lemma L2_set_product_tendsto {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (Y X : ℕ → Lp ℝ 2 μ) (Z W : Lp ℝ 2 μ)
    (f g : ℕ → Ω → ℝ) (z w : Ω → ℝ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] f m) (hX : ∀ m, (X m : Ω → ℝ) =ᵐ[μ] g m)
    (hZ : (Z : Ω → ℝ) =ᵐ[μ] z) (hW : (W : Ω → ℝ) =ᵐ[μ] w)
    (hlimY : Tendsto Y atTop (𝓝 Z)) (hlimX : Tendsto X atTop (𝓝 W)) :
    Tendsto (fun m => ∫ ω in E, f m ω*g m ω ∂μ) atTop (𝓝 (∫ ω in E, z ω*w ω ∂μ)) := by
  have hle : μ.restrict E ≤ (1 : ENNReal) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := E)
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict E) :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ENNReal) ≠ ⊤) hle
  have hrep (V : Lp ℝ 2 μ) : (L V : Ω → ℝ) =ᵐ[μ.restrict E] V :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ hle V
  have he (V U : Lp ℝ 2 μ) (a b : Ω → ℝ) (ha : (V : Ω → ℝ) =ᵐ[μ] a) (hb : (U : Ω → ℝ) =ᵐ[μ] b) :
      inner ℝ (L V) (L U) = ∫ ω in E, a ω*b ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep V, hrep U, ae_restrict_of_ae ha, ae_restrict_of_ae hb] with ω hv hu ha hb
    simp [RCLike.inner_apply, hv, hu, ha, hb, mul_comm]
  have h := ((L.continuous.tendsto Z).comp hlimY).inner (𝕜 := ℝ) ((L.continuous.tendsto W).comp hlimX)
  simpa only [Function.comp_apply, he _ _ _ _ hZ hW, he _ _ _ _ (hY _) (hX _)] using h

lemma elementary_future_L2_rep {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hm : ∀ t, Measurable[F t] (B t))
    (hind : ∀ a b, a ≤ b → Indep (F a) (MeasurableSpace.comap (fun ω => B b ω-B a ω) inferInstance) μ)
    {N : ℕ} (t : Fin (N+1) → NNReal) (H : Fin N → Ω → ℝ) (ht : Monotone t)
    (hH : ∀ i, Measurable[F (t i.castSucc)] (H i)) (hH2 : ∀ i, MemLp (H i) 2 μ)
    (Y : Lp ℝ 2 μ) (hY : (Y : Ω → ℝ) =ᵐ[μ] S01522 B H t) (s : NNReal) :
    ((Y-(condExpL2 ℝ ℝ (F.le s) Y : Lp ℝ 2 μ) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun ω => S01522 B H t ω-R01522 B H t s ω := by
  have hce := (condExp_congr_ae (m := F s) hY).trans
    ((elementary_brownian_process Ω mΩ μ inferInstance F B hB hm hind N t H ht hH hH2).2.2.1 s).2.1
  exact (L2_future_rep μ F s Y).trans (hY.sub hce)

lemma elementary_two_limit_conditional {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ) (B C : NNReal → Ω → ℝ)
    (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (hmB : ∀ t, Measurable[F t] (B t)) (hmC : ∀ t, Measurable[F t] (C t))
    (hpair : ∀ a b, a ≤ b → Indep (F a)
      (MeasurableSpace.comap (fun ω => (B b ω-B a ω, C b ω-C a ω)) inferInstance) μ)
    (hBC : ∀ a b, a ≤ b → IndepFun (fun ω => B b ω-B a ω) (fun ω => C b ω-C a ω) μ)
    (N : ℕ → ℕ) (t : ∀ m, Fin (N m+1) → NNReal)
    (H K : ∀ m, Fin (N m) → Ω → ℝ) (ht : ∀ m, Monotone (t m))
    (hH : ∀ m i, Measurable[F (t m i.castSucc)] (H m i))
    (hK : ∀ m i, Measurable[F (t m i.castSucc)] (K m i))
    (hH2 : ∀ m i, MemLp (H m i) 2 μ) (hK2 : ∀ m i, MemLp (K m i) 2 μ)
    (Y X : ℕ → Lp ℝ 2 μ) (Z W : Lp ℝ 2 μ)
    (hY : ∀ m, (Y m : Ω → ℝ) =ᵐ[μ] S01522 B (H m) (t m))
    (hX : ∀ m, (X m : Ω → ℝ) =ᵐ[μ] S01522 C (K m) (t m))
    (hZ : Tendsto Y atTop (𝓝 Z)) (hW : Tendsto X atTop (𝓝 W)) (s : NNReal) :
    μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | F s] ω)*(W ω-μ[(W : Ω → ℝ) | F s] ω) | F s] =ᵐ[μ] 0 := by
  have hiB := fun a b hab => (indep_pair_components μ (F a) _ _ (hpair a b hab)).1
  have hiC := fun a b hab => (indep_pair_components μ (F a) _ _ (hpair a b hab)).2
  let P := fun V : Lp ℝ 2 μ => (condExpL2 ℝ ℝ (F.le s) V : Lp ℝ 2 μ)
  have hP : Continuous P := continuous_subtype_val.comp (condExpL2 ℝ ℝ (F.le s)).continuous
  have hYZ := hZ.sub ((hP.tendsto Z).comp hZ)
  have hXW := hW.sub ((hP.tendsto W).comp hW)
  have hi : Integrable (fun ω => (Z ω-μ[(Z : Ω → ℝ) | F s] ω)*(W ω-μ[(W : Ω → ℝ) | F s] ω)) μ :=
    ((Lp.memLp Z).sub ((Lp.memLp Z).condExp one_le_two)).integrable_mul
      ((Lp.memLp W).sub ((Lp.memLp W).condExp one_le_two))
  have hset (E : Set Ω) (hE : MeasurableSet[F s] E) :
      (∫ ω in E, (Z ω-μ[(Z : Ω → ℝ) | F s] ω)*(W ω-μ[(W : Ω → ℝ) | F s] ω) ∂μ) = 0 := by
    have hlim := L2_set_product_tendsto μ E (fun m => Y m-P (Y m)) (fun m => X m-P (X m))
      (Z-P Z) (W-P W) _ _ _ _
      (fun m => elementary_future_L2_rep μ F B hB hmB hiB (t m) (H m) (ht m) (hH m) (hH2 m) (Y m) (hY m) s)
      (fun m => elementary_future_L2_rep μ F C hC hmC hiC (t m) (K m) (ht m) (hK m) (hK2 m) (X m) (hX m) s)
      (L2_future_rep μ F s Z) (L2_future_rep μ F s W) hYZ hXW
    have he := fun m => elementary_two_future_set μ F B C hB hC hmB hmC hpair hBC
      (t m) (H m) (K m) (ht m) (hH m) (hK m) (hH2 m) (hK2 m) s E hE
    exact tendsto_nhds_unique hlim (by simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ))))
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hi
    (fun E _ _ => (integrable_const (0 : ℝ)).integrableOn) _ stronglyMeasurable_zero.aestronglyMeasurable
  intro E hE _
  simpa only [Pi.zero_apply, integral_zero] using (hset E hE).symm

lemma conditional_centered_product {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (Z W : Lp ℝ 2 μ) :
    μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | G] ω)*(W ω-μ[(W : Ω → ℝ) | G] ω) | G] =ᵐ[μ]
      fun ω => μ[fun ω => Z ω*W ω | G] ω-μ[(Z : Ω → ℝ) | G] ω*μ[(W : Ω → ℝ) | G] ω := by
  let P : Ω → ℝ := μ[(Z : Ω → ℝ) | G]
  let Q : Ω → ℝ := μ[(W : Ω → ℝ) | G]
  let A : Ω → ℝ := (Z : Ω → ℝ)-P
  have hP : MemLp P 2 μ := (Lp.memLp Z).condExp one_le_two
  have hQ : MemLp Q 2 μ := (Lp.memLp W).condExp one_le_two
  have hA : MemLp A 2 μ := (Lp.memLp Z).sub hP
  have hPm : StronglyMeasurable[G] P := stronglyMeasurable_condExp
  have hQm : StronglyMeasurable[G] Q := stronglyMeasurable_condExp
  have hzero : μ[A | G] =ᵐ[μ] 0 := by
    have h := condExp_sub ((Lp.memLp Z).integrable one_le_two) (hP.integrable one_le_two) G
    rw [condExp_of_stronglyMeasurable hG hPm (hP.integrable one_le_two)] at h
    filter_upwards [h] with ω hω
    simpa only [A, P, Pi.sub_apply, sub_self, Pi.zero_apply] using hω
  have h1 := condExp_mul_of_stronglyMeasurable_right hQm (hA.integrable_mul hQ) (hA.integrable one_le_two)
  have h2 := condExp_mul_of_stronglyMeasurable_left hPm (hP.integrable_mul (Lp.memLp W))
    ((Lp.memLp W).integrable one_le_two)
  have h3 := condExp_sub ((Lp.memLp Z).integrable_mul (Lp.memLp W)) (hP.integrable_mul (Lp.memLp W)) G
  rw [← sub_mul] at h3
  have h4 := condExp_sub (hA.integrable_mul (Lp.memLp W)) (hA.integrable_mul hQ) G
  rw [← mul_sub] at h4
  filter_upwards [hzero, h1, h2, h3, h4] with ω hzero h1 h2 h3 h4
  change μ[A*((W : Ω → ℝ)-Q) | G] ω = μ[(Z : Ω → ℝ)*(W : Ω → ℝ) | G] ω-P ω*Q ω
  change μ[A*(W : Ω → ℝ) | G] ω = μ[(Z : Ω → ℝ)*(W : Ω → ℝ) | G] ω-μ[P*(W : Ω → ℝ) | G] ω at h3
  simp only [Pi.sub_apply, Pi.mul_apply, hzero, Pi.zero_apply, zero_mul] at h1 h2 h3 h4
  change μ[P*(W : Ω → ℝ) | G] ω = P ω*Q ω at h2
  linarith

lemma conditional_product_martingale {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration NNReal mΩ)
    (Z W : Lp ℝ 2 μ) (U V : NNReal → Ω → ℝ) (hU : Martingale U F μ) (hV : Martingale V F μ)
    (hUe : ∀ s, U s =ᵐ[μ] μ[(Z : Ω → ℝ) | F s])
    (hVe : ∀ s, V s =ᵐ[μ] μ[(W : Ω → ℝ) | F s])
    (horth : ∀ s, μ[fun ω => (Z ω-μ[(Z : Ω → ℝ) | F s] ω)*
      (W ω-μ[(W : Ω → ℝ) | F s] ω) | F s] =ᵐ[μ] 0) :
    Martingale (fun s ω => U s ω*V s ω) F μ := by
  apply (martingale_condExp (fun ω => Z ω*W ω) F μ).congr
  · intro s
    exact (hU.stronglyMeasurable s).mul (hV.stronglyMeasurable s)
  · intro s
    filter_upwards [conditional_centered_product μ (F s) (F.le s) Z W,
      horth s, hUe s, hVe s] with ω h hzero hu hv
    simp only [hu, hv]
    change _ = 0 at hzero
    linarith

lemma stopped_brownian_orthogonality : stoppedBrownianOrthogonalityStatement := by
  intro d Ω mΩ μ hμ F T X α l hm hc h0 hl B C hB hC hmB hmC hpair hBC n i j
  let := hμ
  have hiB := fun (a b : NNReal) (hab : a ≤ b) => (indep_pair_components μ (F (a : ℝ)) _ _ (hpair a b hab)).1
  have hiC := fun (a b : NNReal) (hab : a ≤ b) => (indep_pair_components μ (F (a : ℝ)) _ _ (hpair a b hab)).2
  obtain ⟨_, _, Y₁, Z, hY₁, hZ, _⟩ := stopped_brownian_limit d Ω mΩ μ hμ F T X α l hm hc h0 hl B hB hmB hiB n i
  obtain ⟨_, _, Y₂, W, hY₂, hW, _⟩ := stopped_brownian_limit d Ω mΩ μ hμ F T X α l hm hc h0 hl C hC hmC hiC n j
  have hA := fun k => stopped_integrand_approximation d Ω mΩ μ hμ F T X α l hm hc h0 hl n k
  have ht : ∀ m, Monotone (t01522 T m) := by
    intro m a b hab
    exact ((hA i).1 m).1 (show a.val ≤ b.val from hab)
  have hH : ∀ k m a, Measurable[F01522 F (t01522 T m a.castSucc)] (H01522 T X n α l k m a) :=
    fun k m a => (((hA k).1 m).2.2.2.1 a.val).1
  have hH2 : ∀ k m a, MemLp (H01522 T X n α l k m a) 2 μ :=
    fun k m a => (((hA k).1 m).2.2.2.1 a.val).2
  obtain ⟨_, _, U, hU, hUe, hUc, _⟩ := elementary_continuous_limit μ (F01522 F) B hB hmB hiB
    (N01522 T) (t01522 T) (H01522 T X n α l i) ht (hH i) (hH2 i) Y₁ hY₁ Z hZ
  obtain ⟨_, _, V, hV, hVe, hVc, _⟩ := elementary_continuous_limit μ (F01522 F) C hC hmC hiC
    (N01522 T) (t01522 T) (H01522 T X n α l j) ht (hH j) (hH2 j) Y₂ hY₂ W hW
  have horth := elementary_two_limit_conditional μ (F01522 F) B C hB hC hmB hmC hpair hBC
    (N01522 T) (t01522 T) (H01522 T X n α l i) (H01522 T X n α l j)
    ht (hH i) (hH j) (hH2 i) (hH2 j) Y₁ Y₂ Z W hY₁ hY₂ hZ hW
  refine ⟨Y₁, Y₂, Z, W, U, V, hY₁, hY₂, hZ, hW, hU, hV, hUe, hVe, hUc.and hVc,
    conditional_product_martingale μ (F01522 F) Z W U V hU hV hUe hVe horth, ?_⟩
  intro s
  have hU2 : MemLp (U s) 2 μ := ((Lp.memLp Z).condExp one_le_two).ae_eq (hUe s).symm
  have hV2 : MemLp (V s) 2 μ := ((Lp.memLp W).condExp one_le_two).ae_eq (hVe s).symm
  refine ⟨((Lp.memLp Z).sub hU2).integrable_mul ((Lp.memLp W).sub hV2), ?_⟩
  apply EventuallyEq.trans (condExp_congr_ae (m := F (s : ℝ)) ?_) (horth s)
  filter_upwards [hUe s, hVe s] with ω hu hv
  simp only [hu, hv]

theorem zeroMeanReversionVarianceSupport : Standalone.ZeroMeanReversionVarianceSupport.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m d A b hA
    exact ⟨closed_translate A b hA, affine_hull A b, A.rank_le_width, nullity A,
      support_image A b hA, affine_equalities A b, zero_image A hA b⟩
  · intro m d A q hq
    exact ⟨quadratic_form A q, covariance_kernel A q hq, covariance_rank A q hq⟩
  · intro m d A b hA μ hprob hμ
    let := hprob
    exact ⟨product_support μ hμ, support_image A b hA _ (product_support μ hμ),
      product_atom A b hA μ hμ⟩
  · intro Ω mΩ μ hprob m d A b X q hX hind hq
    let := hprob
    exact covariance_image A μ b X q hX hind hq
  · intro m d A b hA μ r hprob hμ hr
    let := hprob
    exact exponential_atom A b hA μ r hμ hr

  · constructor
    · intro d μ ν hμ hν h
      let := hμ
      let := hν
      exact laplace_unique_nnreal μ ν h
    · intro d μ ν hμ hν hμpos hνpos h
      let := hμ
      let := hν
      exact laplace_unique μ ν hμpos hνpos h
  · intro d μ hμ v c h
    let := hμ
    exact independence_of_laplace μ v c h
  · intro d Ω G mΩ μ hμ hG X hX κ hκ hm h
    let := hμ
    let := hκ
    exact ⟨hm, conditional_laplace_unique G μ hG X hX κ h⟩
  · exact ⟨poisson_power_integral, poisson_transform⟩
  · intro c hc
    refine ⟨(κ01513 c).measurable, (fun x => poisson_sum_probability c hc _),
      transition_zero c hc, ?_, ?_⟩
    · intro x
      exact ⟨transition_laplace c hc x, transition_atom c hc x, transition_support c hc x⟩
    · intro x μ hμ hpos h
      let := hμ
      exact law_of_scalar_transform c hc x μ hpos h
  · intro Ω G mΩ μ hμ hG c hc S hS X hX hpos h
    let := hμ
    exact conditional_scalar_law G μ hG c hc S hS X hX hpos h
  · exact transition_moments
  · intro d c hc
    refine ⟨vector_measurable c hc, fun x => ?_⟩
    refine ⟨vector_probability c hc x, vector_nonneg c hc x, vector_transform c hc x,
      vector_independence c hc x, vector_moments c hc x, vector_support c hc x, ?_⟩
    intro μ hμ hpos h
    let := hμ
    exact law_of_vector_transform c hc x μ hpos h
  · intro d Ω G mΩ μ hμ hG c hc S hS X hX hpos h
    let := hμ
    exact ⟨conditional_vector_law G μ hG c hc S hS X hX hpos h,
      fun m A b => conditional_vector_image_law G μ hG c hc S hS X hX hpos h A b⟩
  · intro m d A b hA c hc x
    have hB : ∀ i j, 0 ≤ A01514 A c x i j := by
      intro i j
      dsimp [A01514]
      split_ifs <;> simp_all
    have hs := image_support01514 A b hA c hc x
    have hm := vector_image_moments A b c hc x
    have hr := vector_covariance_rank A c hc x
    exact ⟨hs, closed_translate _ _ hB, affine_hull _ _, affine_equalities _ _ _ hs,
      vector_rank_bound A c x, hr.1, hr.2, hm.1, hm.2, vector_image_atom A b hA c hc x⟩



  · intro m A hA
    refine ⟨table_image A, fun t ht => ?_⟩
    have hs := table_support A hA t ht
    refine ⟨table_scale t ht, hs, closed_translate _ _ (fun i j => hA i j.castSucc),
      affine_hull _ _, (A0159 A).rank_le_width, nullity (A0159 A),
      affine_equalities _ _ _ hs, ?_⟩
    intro x hx
    have hsx := table_conditional_support A hA t ht x hx
    have hr := table_conditional_rank A t x
    exact ⟨hsx, affine_hull _ _, hr, nullity_of_rank_le _ hr, affine_equalities _ _ _ hsx⟩
  · refine ⟨fun d => vector_zero_scale, fun d => vector_zero_start, ?_, ?_, ?_⟩
    · intro d m Ω mΩ μ hμ X hX A
      let := hμ
      have he := initial_image_law μ X hX A
      exact ⟨he, he ▸ point_support015 _⟩
    · intro d Ω G mΩ μ hG Y hY
      have he := conditional_point_law G μ hG Y hY
      refine ⟨he.1, he.2, fun ω => point_support015 (Y ω), ?_⟩
      intro hμ hI
      let := hμ
      exact conditional_point_moments G μ hG Y hY hI
    · intro d Ω G mΩ μ hG Y
      have hm : Measurable[G] (V0150 G μ Y) := by
        let : MeasurableSpace Ω := G
        apply measurable_pi_iff.mpr
        intro j
        exact (stronglyMeasurable_condVar (m := G) (μ := μ) (X := Y j)).measurable
      have he := conditional_point_law G μ hG (V0150 G μ Y) hm
      exact ⟨he.1, he.2, fun ω => point_support015 (V0150 G μ Y ω)⟩

  · intro m d Ω G H mΩ μ hμ hG hH Y Z I01314 v hv g b ρ α T t hT hρ h
    let := hμ
    let A := A0154 g b ρ α T t
    have hA : ∀ n j, 0 ≤ A n j := actual_coefficient_nonneg g b ρ α T t hT hρ
    have hv' := hv.mono hG le_rfl
    refine ⟨hA, actual_variance0154 G μ hG Y Z I01314 v g b ρ α T t h, fun c hc => ?_⟩
    constructor
    · intro x hlaw
      have he := actual_variance_law G μ hG Y Z I01314 v hv' g b ρ α T t h c hc x hlaw
      have hs : (μ.map (V0150 G μ Y)).support = cone0154 (A01514 A c x) (b01514 A 0 c x) := by
        rw [he]
        simpa only [zero_add] using image_support01514 A 0 hA c hc x
      have hB : ∀ i j, 0 ≤ A01514 A c x i j := by
        intro i j
        dsimp [A01514]
        split_ifs <;> simp_all
      have hm := moments_of_image_law μ (V0150 G μ Y) (actual_variance_measurable G μ hG Y)
        A c hc x he
      have hr := vector_covariance_rank A c hc x
      refine ⟨he, hs, closed_translate _ _ hB, affine_hull _ _, affine_equalities _ _ _ hs,
        hm.1, hm.2, hr.1, hr.2, ?_⟩
      rw [he]
      simpa only [zero_add] using vector_image_atom A 0 hA c hc x
    · intro S hS hlaw
      have he := actual_variance_conditional_law G H μ hG hH Y Z I01314 v hv'
        g b ρ α T t h c hc S hS hlaw
      refine ⟨he.1, he.2, fun ω => ?_⟩
      simpa only [zero_add] using image_support01514 A 0 hA c hc (S ω)

  · intro d α l T s x hl hs
    exact ⟨fun j => q0152_derivative (α j) T (l j) s (hl j) hs,
      E0152_bounds α l T s x hl hs, E0152_generator α l T s x hl hs⟩
  · intro d Ω mΩ μ hμ F α T X hX hH
    let := hμ
    refine ⟨localized_state_law μ F α T X hX hH, fun s hs => ?_⟩
    exact ⟨fun l hl => localized_conditional_transform μ F α l T X hl hX (hH l hl) s hs,
      localized_conditional_state_law μ F α T X hX hH s hs⟩
  · intro m d Ω mΩ μ hμ F α t X hX hH Y Z I01314 g b ρ T hT hρ h
    let := hμ
    let A := A0154 g b ρ α T t
    have hA : ∀ n j, 0 ≤ A n j := actual_coefficient_nonneg g b ρ α T t hT hρ
    have hv := (hX t ⟨t.coe_nonneg, le_rfl⟩).mono (F.le t) le_rfl
    constructor
    · intro x h0
      let c := fun j => (α j)^2*(t : ℝ)/2
      have hc : ∀ j, 0 ≤ c j := fun j => by dsimp [c]; positivity
      have he := actual_variance_law (F t) μ (F.le t) Y Z I01314 (X t) hv
        g b ρ α T t h c hc x
        (fun l hl => localized_initial_transform μ F α l t X hl hX (hH l hl) x h0)
      refine ⟨he, ?_⟩
      rw [he]
      simpa only [zero_add] using image_support01514 A 0 hA c hc x
    · intro s hs
      let c := fun j => (α j)^2*((t : ℝ)-s)/2
      have hc : ∀ j, 0 ≤ c j := fun j =>
        div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.2 hs.2)) (by norm_num)
      have he := actual_variance_conditional_law (F t) (F s) μ (F.le t) (F.mono hs.2)
        Y Z I01314 (X t) hv g b ρ α T t h c hc (X s) (hX s hs)
        (fun l hl => localized_conditional_transform μ F α l t X hl hX (hH l hl) s hs)
      refine ⟨he.1, he.2, fun ω => ?_⟩
      simpa only [zero_add] using image_support01514 A 0 hA c hc (X s ω)

  · intro d Ω mΩ μ hμ F α T X hX hH x h0
    let := hμ
    refine ⟨localized_state_independence μ F α T X hX hH x h0, fun j => ?_⟩
    have hi := localized_state_memLp μ F α T X hX hH x h0 j
    have hm := localized_state_moments μ F α T X hX hH x h0 j
    refine ⟨hi, hm.1, hm.2, localized_state_martingale μ F α T X hX hH x h0 j,
      localized_state_constant μ F α T X hX hH x h0 j, fun s hs => ?_⟩
    have hc := localized_state_conditional_moments μ F α T X hX hH x h0 s hs j
    have his : MemLp (fun ω => (X s ω j : ℝ)) 2 μ := (hi.condExp one_le_two).ae_eq hc.1
    exact ⟨his, hc.1, hc.2.1, hc.2.2, localized_state_absorption μ F α T X hX hH x h0 s hs j⟩

  · intro d Ω mΩ μ hμ F α U X hX hcont hH x h0 a b ha hab hb j K hK
    let := hμ
    exact localized_weighted_integral μ F α U X hX hH x h0 a b ha hab hb j K hK
      (localized_state_jointly_measurable μ F U X hX j (fun ω => hcont ω j) a b ha hb)
  · exact integration_assembly
  · intro m d g b ρ α T t hT hg hb hr G B hG hB hρ n j
    have hR := backward_integral_regular (b n j) t (T n) (B n j) (hT n) (hb n j) (hB n j)
    refine ⟨hR.1, full_kernel_regular (g n j) (b n j) (ρ j) (α j) t (T n)
      (G n j) (B n j) (hT n) (hg n j) (hb n j) (hr n j) (hG n j) (hB n j) (hρ n j), hR.2, ?_⟩
    intro u hu
    have hc := abs_le.mp (hρ n j u hu)
    exact ⟨StochasticMeetingVarianceProof.F_nonneg _ _ _ _ hc.1 hc.2,
      (le_abs_self _).trans (full_kernel_bound _ _ _ _ _ _ (hG n j u hu)
        (hρ n j u hu) (hR.2 u hu))⟩
  · exact regular_integration_assembly
  · exact source_coefficients
  · intro m d Ω mΩ μ hμ F α U X hX hcont hH x h0 N a lam ρ γ T rows t ht hT ha hl hr hln hloc hbound hρ Y Z h1 h2 h3 h4
    have hc := source_coefficients N m d T rows a lam ρ γ α t (fun n => (hT n).1)
      ha hl hr hln hloc hbound hρ
    exact regular_integration_assembly m d Ω mΩ μ hμ F α U X hX hcont hH x h0
      (fun n j => g01530 T (a j) (lam j) (γ j) (rows n))
      (fun n j => b01530 T (a j) (lam j) (γ j) (rows n)) ρ (fun n => T (rows n)) t ht hT
      (fun n j => (hc.1 n j).1.aestronglyMeasurable)
      (fun n j => (hc.1 n j).2.aestronglyMeasurable)
      (fun _ j => (hr j).aestronglyMeasurable) hc.2.1 hρ Y Z h1 h2 h3 h4
  · intro d Ω mΩ F T X hm hc
    refine ⟨localizer_stopping F T X hm hc, localizer_monotone T X,
      localizer_eventually T X hc, localizer_coordinate_bound T X hc, ?_⟩
    intro μ α l hstop
    exact ⟨σ01521 T X, Filter.Eventually.of_forall (localizer_eventually T X hc), hstop⟩
  · intro d Ω T X hc ω h0 n α l hl s j
    exact localizer_integrand_bound T X hc ω h0 n α l hl s j
  · exact stopped_integrand_integrability
  · intro d Ω mΩ F T X α l hm hc hl
    let : Fact ((0 : ℝ) ≤ T) := ⟨T.coe_nonneg⟩
    dsimp only
    intro n j
    have h := stopped_integrand_predictable F T X α l hm hc hl n j
    exact ⟨h, h.isStronglyProgressive⟩

  · exact elementary_brownian_integral
  · exact elementary_brownian_process
  · exact elementary_brownian_limit
  · exact stopped_integrand_approximation
  · exact elementary_brownian_comparison
  · exact elementary_brownian_cauchy
  · exact stopped_brownian_limit
  · exact stopped_brownian_orthogonality

/-- Specialization of Claim 013's actual coefficient definitions. -/
lemma coefficients_zero (K : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ) (t : ℝ) :
    Standalone.StochasticMeetingVariance.C K (fun _ _ => 0) T t = 0 ∧
    Standalone.StochasticMeetingVariance.A K (fun _ _ => 0) T t =
      fun n j => ∫ u in t..T n, K n j u := by
  constructor
  · ext n
    simp [Standalone.StochasticMeetingVariance.C, Standalone.StochasticMeetingVariance.E]
  · ext n j
    simp [Standalone.StochasticMeetingVariance.A, Standalone.StochasticMeetingVariance.E]

/-- The remaining integral retains both the random HJM drift and the correlation term. -/
lemma full_kernel_zero (g b : Fin m → Fin d → ℝ → ℝ) (ρ α : Fin d → ℝ → ℝ)
    (T : Fin m → ℝ) (t : ℝ) (hT : ∀ n, t ≤ T n)
    (hρ : ∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) :
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ α (fun _ _ => 0) T
    (∀ n j, Standalone.StochasticMeetingVariance.A K (fun _ _ => 0) T t n j =
      ∫ u in t..T n, Standalone.StochasticMeetingVariance.F (g n j u) (ρ j u) (α j u)
        (∫ s in u..T n, b n j s)) ∧
    (∀ n j, 0 ≤ Standalone.StochasticMeetingVariance.A K (fun _ _ => 0) T t n j) := by
  dsimp only
  constructor
  · intro n j
    simp [Standalone.StochasticMeetingVariance.A, Standalone.StochasticMeetingVariance.kernel0136,
      Standalone.StochasticMeetingVariance.R, Standalone.StochasticMeetingVariance.E]
  · exact StochasticMeetingVarianceProof.A_nonneg hT
      (StochasticMeetingVarianceProof.full_kernel_nonneg g b ρ α (fun _ _ => 0) T hρ)

end Novel.ZeroMeanReversionVarianceSupportProof

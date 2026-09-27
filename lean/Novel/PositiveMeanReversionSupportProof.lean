import Standalone.PositiveMeanReversionSupport
import Upstream.Predictability
import Mathlib.Data.Finset.Max
import Novel.ZeroMeanReversionVarianceSupportProof
import Novel.StochasticMeetingVarianceProof
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Probability.Kernel.CondDistrib

open MeasureTheory Set Matrix Filter
open Standalone.ZeroMeanReversionVarianceSupport (cone0154)
open Standalone.PositiveMeanReversionSupport
open Novel.ZeroMeanReversionVarianceSupportProof

namespace Novel.PositiveMeanReversionSupportProof

/-! ### The backward Riccati flow (23.2) -/

section Riccati

lemma exp_flow_deriv (θ t u : ℝ) :
    HasDerivAt (fun u => Real.exp (-θ * (t - u))) (θ * Real.exp (-θ * (t - u))) u := by
  have h : HasDerivAt (fun u => -θ * (t - u)) θ u := by
    convert ((hasDerivAt_id' u).const_sub t).const_mul (-θ) using 1
    ring
  convert h.exp using 1
  ring

lemma Q_deriv_zero (α l t u : ℝ) (hl : 0 ≤ l) (hα : 0 ≤ α) (hu : u ≤ t) :
    HasDerivAt (fun u => Qflow 0 α l (t - u))
      (0 * Qflow 0 α l (t - u) + α^2 * (Qflow 0 α l (t - u))^2 / 2) u := by
  have hD : 0 < 1 + α^2 * (t - u) * l / 2 := by
    have : 0 ≤ α^2 * (t - u) * l / 2 := by
      have := sub_nonneg.2 hu
      positivity
    linarith
  have hQ : (fun u => Qflow 0 α l (t - u)) = fun u => l / (1 + α^2 * (t - u) * l / 2) := by
    funext u
    simp [Qflow]
  rw [hQ]
  have hden : HasDerivAt (fun u => 1 + α^2 * (t - u) * l / 2) (-(α^2 * l / 2)) u := by
    convert ((((hasDerivAt_id' u).const_sub t).const_mul (α^2)).mul_const l).div_const 2
      |>.const_add 1 using 1
    ring
  have h := (hasDerivAt_const u l).div hden hD.ne'
  convert h using 1
  simp only [Qflow, if_true]
  field_simp
  ring

lemma Q_deriv_pos (θ α l t u : ℝ) (hθ : 0 < θ) (hl : 0 ≤ l) (hu : u ≤ t) :
    HasDerivAt (fun u => Qflow θ α l (t - u))
      (θ * Qflow θ α l (t - u) + α^2 * (Qflow θ α l (t - u))^2 / 2) u := by
  have hθ' : θ ≠ 0 := hθ.ne'
  have hE := exp_flow_deriv θ t u
  have hE1 : Real.exp (-θ * (t - u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := sub_nonneg.2 hu
    nlinarith
  have hD : 0 < 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))) := by
    have : 0 ≤ l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))) := by
      have h1 : 0 ≤ 1 - Real.exp (-θ * (t - u)) := by linarith
      positivity
    linarith
  have hQ : (fun u => Qflow θ α l (t - u)) = fun u =>
      l * Real.exp (-θ * (t - u)) /
        (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u)))) := by
    funext u
    simp [Qflow, hθ']
  rw [hQ]
  have hnum : HasDerivAt (fun u => l * Real.exp (-θ * (t - u)))
      (l * (θ * Real.exp (-θ * (t - u)))) u := hE.const_mul l
  have hden : HasDerivAt (fun u => 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))))
      (-(l * (α^2 / (2 * θ)) * (θ * Real.exp (-θ * (t - u))))) u := by
    have := ((hE.const_sub 1).const_mul (l * (α^2 / (2 * θ)))).const_add 1
    convert this using 1
    ring
  have h := hnum.div hden hD.ne'
  convert h using 1
  simp only [Qflow, hθ', if_false]
  field_simp
  ring

lemma R_deriv (θ α l t u : ℝ) (hθ : 0 ≤ θ) (hl : 0 ≤ l) (hu : u ≤ t) :
    HasDerivAt (fun u => Rflow θ α l (t - u)) (-(θ * Qflow θ α l (t - u))) u := by
  rcases hθ.eq_or_lt with hθ0 | hθp
  · subst hθ0
    have hR : (fun u => Rflow 0 α l (t - u)) = fun _ => 0 := by
      funext u; simp [Rflow]
    rw [hR]
    simpa using hasDerivAt_const u (0 : ℝ)
  · have hθ' : θ ≠ 0 := hθp.ne'
    have hE := exp_flow_deriv θ t u
    by_cases hα : α = 0
    · subst hα
      have hR : (fun u => Rflow θ 0 l (t - u)) = fun u => l * (1 - Real.exp (-θ * (t - u))) := by
        funext u; simp [Rflow, hθ']
      rw [hR]
      have h := (hE.const_sub 1).const_mul l
      convert h using 1
      simp [Qflow, hθ'] <;> ring
    · have hE1 : Real.exp (-θ * (t - u)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := sub_nonneg.2 hu
        nlinarith
      have hD : 0 < 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))) := by
        have : 0 ≤ l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))) := by
          have h1 : 0 ≤ 1 - Real.exp (-θ * (t - u)) := by linarith
          positivity
        linarith
      have hR : (fun u => Rflow θ α l (t - u)) = fun u =>
          (2 * θ / α^2) * Real.log (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u)))) := by
        funext u; simp [Rflow, hθ', hα]
      rw [hR]
      have hden : HasDerivAt (fun u => 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * (t - u))))
          (-(l * (α^2 / (2 * θ)) * (θ * Real.exp (-θ * (t - u))))) u := by
        have := ((hE.const_sub 1).const_mul (l * (α^2 / (2 * θ)))).const_add 1
        convert this using 1
        ring
      have h := (hden.log hD.ne').const_mul (2 * θ / α^2)
      convert h using 1
      simp only [Qflow, hθ', if_false]
      field_simp

lemma riccati : riccatiStatement := by
  intro θ α l t hθ hα hl
  refine ⟨fun u hu => ?_, fun u hu => R_deriv θ α l t u hθ hl hu, ?_, ?_, fun v s => ⟨?_, ?_⟩,
    fun hθp h hh => ?_⟩
  · rcases hθ.eq_or_lt with hθ0 | hθp
    · subst hθ0
      exact Q_deriv_zero α l t u hl hα hu
    · exact Q_deriv_pos θ α l t u hθp hl hu
  · by_cases hθ0 : θ = 0 <;> simp [Qflow, hθ0]
  · by_cases hθ0 : θ = 0 <;> simp [Rflow, hθ0]
  · intro u
    unfold lflow
    have hE : HasDerivAt (fun u => Real.exp (-θ * (u - s))) (-θ * Real.exp (-θ * (u - s))) u := by
      have h : HasDerivAt (fun u => -θ * (u - s)) (-θ) u := by
        convert ((hasDerivAt_id' u).sub_const s).const_mul (-θ) using 1
        ring
      convert h.exp using 1
      ring
    have h := (hE.const_mul (v - 1)).const_add 1
    convert h using 1
    ring
  · simp [lflow]
  · simp only [lflow]
    have : Real.exp (-θ * h) < 1 := by
      have h1 : Real.exp (-θ * h) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
      rwa [Real.exp_zero] at h1
    nlinarith

end Riccati

/-! ### The translated cone (23.6) -/

section Cone
variable {m d : ℕ}

lemma activeCols_nonneg (A : Matrix (Fin m) (Fin d) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (J : Finset (Fin d)) : ∀ i j, 0 ≤ activeCols A J i j := by
  intro i j
  unfold activeCols
  split_ifs
  · exact hA i j
  · exact le_rfl

/-- The image of a point of the support through the active columns. -/
lemma image_shift (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ) (ℓ : Fin d → ℝ)
    (J : Finset (Fin d)) (z : Fin d → ℝ) (hz : ∀ j, j ∉ J → z j = ℓ j) :
    C + A.mulVec z = (C + A.mulVec ℓ) +
      (activeCols A J).mulVec (fun j => if j ∈ J then z j - ℓ j else 0) := by
  classical
  ext i
  simp only [Pi.add_apply, mulVec, dotProduct, activeCols]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ J
  · simp only [hj, if_true]
    ring
  · simp only [hj, if_false, hz j hj]
    ring

lemma translatedCone : translatedConeStatement := by
  intro m d A C ℓ J hA μ hprob hJ hJc
  intro B b'
  have hBd : B = activeCols A J := rfl
  have hb'd : b' = C + A.mulVec ℓ := rfl
  clear_value B b'
  subst hBd hb'd
  classical
  have : ∀ j, IsProbabilityMeasure (μ j) := hprob
  let f : (Fin d → ℝ) → (Fin m → ℝ) := fun x => C + A.mulVec x
  have hf : Continuous f := continuous_const.add A.mulVecLin.continuous_of_finiteDimensional
  have hB : ∀ i j, 0 ≤ (activeCols A J) i j := activeCols_nonneg A hA J
  have hclosed := closed_translate (activeCols A J) (C + A.mulVec ℓ) hB
  have hsupp : (Measure.pi μ).support =
      {y | ∀ j, if j ∈ J then ℓ j ≤ y j else y j = ℓ j} := by
    rw [product_support015]
    ext y
    simp only [mem_ofPred_eq]
    refine forall_congr' fun j => ?_
    by_cases hj : j ∈ J
    · rw [hJ j hj]; simp [hj]
    · rw [hJc j hj]; simp [hj]
  -- the image of the support is the translated cone
  have he : f '' (Measure.pi μ).support = cone0154 (activeCols A J) (C + A.mulVec ℓ) := by
    rw [hsupp]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨fun j => if j ∈ J then z j - ℓ j else 0, fun j => ?_, ?_⟩
      · have := hz j
        by_cases hj : j ∈ J
        · simp only [hj, if_true] at this ⊢; linarith
        · simp [hj]
      · exact image_shift A C ℓ J z fun j hj => by simpa [hj] using hz j
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j => if j ∈ J then ℓ j + x j else ℓ j, fun j => ?_, ?_⟩
      · by_cases hj : j ∈ J
        · simp only [hj, if_true]; linarith [hx j]
        · simp [hj]
      · show C + A.mulVec (fun j => if j ∈ J then ℓ j + x j else ℓ j) = _
        rw [image_shift A C ℓ J _ fun j hj => by simp [hj]]
        congr 1
        ext i
        simp only [mulVec, dotProduct, activeCols]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ J <;> simp [hj]
  have hsupportImage : ((Measure.pi μ).map f).support = cone0154 (activeCols A J) (C + A.mulVec ℓ) := by
    apply Subset.antisymm
    · apply Measure.support_subset_of_isClosed hclosed
      apply (ae_map_iff hf.measurable.aemeasurable hclosed.measurableSet).2
      filter_upwards [(Measure.pi μ).support_mem_ae] with y hy
      have hh : f y ∈ cone0154 (activeCols A J) (C + A.mulVec ℓ) := by
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
  -- the rank bound through the zero columns off `J`
  have hrank : (activeCols A J).rank ≤ J.card := by
    rw [← rank_transpose]
    apply rank_le_card_of_support_subset
    intro j hj
    by_contra h
    apply hj
    ext i
    have h' : j ∉ J := fun hh => h (Finset.mem_coe.mpr hh)
    simp [Matrix.row, activeCols, h']
  -- the vertex mass
  have hatom : ((Measure.pi μ).map f) {(C + A.mulVec ℓ)} = ∏ j, if (∃ i, (activeCols A J) i j ≠ 0) then μ j {ℓ j} else 1 := by
    let s : Fin d → Set ℝ := fun j => if (∃ i, (activeCols A J) i j ≠ 0) then {ℓ j} else univ
    have hae : ∀ᵐ x ∂Measure.pi μ, ∀ j, if j ∈ J then ℓ j ≤ x j else x j = ℓ j := by
      have h := (Measure.pi μ).support_mem_ae
      rw [hsupp] at h
      exact h
    have heq : f ⁻¹' {(C + A.mulVec ℓ)} =ᵐ[Measure.pi μ] univ.pi s := by
      filter_upwards [hae] with x hx
      apply propext
      simp only [mem_preimage, mem_singleton_iff, Set.mem_pi, mem_univ, forall_const]
      have hoff : ∀ j, j ∉ J → x j = ℓ j := fun j hj => by simpa [hj] using hx j
      show C + A.mulVec x = C + A.mulVec ℓ ↔ _
      rw [image_shift A C ℓ J x hoff]
      rw [zero_image (activeCols A J) hB (C + A.mulVec ℓ) _ fun j => by
        by_cases hj : j ∈ J
        · have := hx j; simp only [hj, if_true] at this ⊢; linarith
        · simp [hj]]
      apply forall_congr'
      intro j
      by_cases hj : ∃ i, (activeCols A J) i j ≠ 0
      · simp only [s, hj, if_true, mem_singleton_iff, true_implies]
        by_cases hjJ : j ∈ J
        · simp only [hjJ, if_true]
          constructor
          · intro h; linarith
          · intro h; linarith
        · simp [hjJ, hoff j hjJ]
      · have h0 : ∀ i, (activeCols A J) i j = 0 := fun i => by
          by_contra h
          exact hj ⟨i, h⟩
        simp [s, hj, h0]
    rw [Measure.map_apply hf.measurable (measurableSet_singleton _), measure_congr heq,
      Measure.pi_pi]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : ∃ i, (activeCols A J) i j ≠ 0 <;> simp [s, hj]
  exact ⟨hsupportImage, hclosed, affine_hull (activeCols A J) (C + A.mulVec ℓ), hrank,
    fun w => affine_equalities (activeCols A J) (C + A.mulVec ℓ) _ hsupportImage w, hatom⟩

end Cone

/-! ### The noncentral chi-square parametrization -/

section ChiSquare

lemma chiSquareParameter : chiSquareParameterStatement := by
  intro θ α h l v hθ hα hh hl
  have hθ' : θ ≠ 0 := hθ.ne'
  have hα' : α ≠ 0 := hα.ne'
  have hE : Real.exp (-θ * h) < 1 := by
    have h1 : Real.exp (-θ * h) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
    rwa [Real.exp_zero] at h1
  have hEpos : 0 < Real.exp (-θ * h) := Real.exp_pos _
  have h1E : 0 < 1 - Real.exp (-θ * h) := by linarith
  have h1E' : 1 - Real.exp (-θ * h) ≠ 0 := h1E.ne'
  have h1E'' : 1 - Real.exp (-(θ * h)) ≠ 0 := by rwa [neg_mul] at h1E'
  have ha : 0 < chiScale θ α h := by unfold chiScale; positivity
  have hν : 0 < chiDof θ α := by unfold chiDof; positivity
  have hη : 0 < chiRate θ α h := by unfold chiRate; positivity
  have haη : chiScale θ α h * chiRate θ α h = Real.exp (-θ * h) := by
    unfold chiScale chiRate
    field_simp
    ring
  have hden : 0 < 1 + 2 * chiScale θ α h * l := by positivity
  have hR : Rflow θ α l h = (chiDof θ α / 2) * Real.log (1 + 2 * chiScale θ α h * l) := by
    unfold Rflow chiDof chiScale
    simp only [hθ', hα', if_false]
    have hx : 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) =
        1 + 2 * (α^2 / (2 * θ) * (1 - Real.exp (-θ * h)) / 2) * l := by ring
    rw [hx]
    ring
  have hQ : Qflow θ α l h = chiScale θ α h * chiRate θ α h * l / (1 + 2 * chiScale θ α h * l) := by
    unfold Qflow
    simp only [hθ', if_false]
    rw [haη]
    unfold chiScale
    rw [show 1 + 2 * (α^2 / (2 * θ) * (1 - Real.exp (-θ * h)) / 2) * l =
      1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) by ring]
    ring
  have e1 : Real.exp (-((chiDof θ α / 2) * Real.log (1 + 2 * chiScale θ α h * l))) =
      (1 + 2 * chiScale θ α h * l) ^ (-(chiDof θ α / 2)) := by
    rw [Real.rpow_def_of_pos hden]
    congr 1
    ring
  refine ⟨ha, hν, hη, haη, hR, hQ, ?_⟩
  rw [hQ, hR, neg_add, Real.exp_add, e1, mul_comm]
  congr 1
  ring

end ChiSquare

/-! ### The deterministic half of (e) -/

section SourceColumn

lemma sourceColumn : sourceColumnStatement := by
  refine ⟨fun αLast hpos => ?_, ⟨by norm_num [θ0235], by norm_num [θ0235], by norm_num [θ0235]⟩,
    fun m A C hA μ hprob hsupp => ?_⟩
  · ext j
    simp [activeLast, hpos j]
  · have h := translatedCone m 3 A C 0 Finset.univ hA μ hprob
      (fun j _ => by rw [hsupp j]; simp) (fun j hj => absurd (Finset.mem_univ j) hj)
    have hact : activeCols A Finset.univ = A := by
      ext i j
      simp [activeCols]
    simp only [hact, Matrix.mulVec_zero, add_zero] at h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    have := h.2.2.2.1
    simpa using this

end SourceColumn

/-! ### The composition of the flow over pieces and the conditional mean -/

section Composition

lemma exp_le_one_of_nonneg (θ h : ℝ) (hθ : 0 ≤ θ) (hh : 0 ≤ h) : Real.exp (-θ * h) ≤ 1 := by
  rw [Real.exp_le_one_iff]; nlinarith

lemma Qflow_nonneg (θ α l h : ℝ) (hθ : 0 ≤ θ) (hl : 0 ≤ l) (hh : 0 ≤ h) : 0 ≤ Qflow θ α l h := by
  unfold Qflow
  split_ifs with h0
  · apply div_nonneg hl
    have : 0 ≤ α^2 * h * l / 2 := by positivity
    linarith
  · have he := exp_le_one_of_nonneg θ h hθ hh
    apply div_nonneg (mul_nonneg hl (Real.exp_pos _).le)
    have hθ' : 0 < θ := lt_of_le_of_ne hθ (Ne.symm h0)
    have : 0 ≤ l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) := by
      have h1 : 0 ≤ 1 - Real.exp (-θ * h) := by linarith
      positivity
    linarith

lemma Rflow_nonneg (θ α l h : ℝ) (hθ : 0 ≤ θ) (hl : 0 ≤ l) (hh : 0 ≤ h) : 0 ≤ Rflow θ α l h := by
  unfold Rflow
  have he := exp_le_one_of_nonneg θ h hθ hh
  have h1 : 0 ≤ 1 - Real.exp (-θ * h) := by linarith
  split_ifs with h0 hα
  · exact le_rfl
  · exact mul_nonneg hl h1
  · have hθ' : 0 < θ := lt_of_le_of_ne hθ (Ne.symm h0)
    have hα' : 0 < α^2 := by positivity
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have : 0 ≤ l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) := by positivity
    linarith

lemma Qflow_zero (θ α h : ℝ) : Qflow θ α 0 h = 0 := by
  unfold Qflow; split_ifs <;> simp

lemma Rflow_zero (θ α h : ℝ) : Rflow θ α 0 h = 0 := by
  unfold Rflow; split_ifs <;> simp

lemma Qflow_hasDerivAt_zero (θ α h : ℝ) :
    HasDerivAt (fun l => Qflow θ α l h) (Real.exp (-θ * h)) 0 := by
  by_cases h0 : θ = 0
  · subst h0
    have hf : (fun l => Qflow 0 α l h) = fun l => l / (1 + α^2 * h * l / 2) := by
      funext l; simp [Qflow]
    rw [hf]
    have hden : HasDerivAt (fun l : ℝ => 1 + α^2 * h * l / 2) (α^2 * h / 2) 0 := by
      convert (((hasDerivAt_id' (0:ℝ)).const_mul (α^2 * h)).div_const 2).const_add 1 using 1
      ring
    have h := (hasDerivAt_id' (0:ℝ)).div hden (by norm_num)
    convert h using 1
    simp
  · have hf : (fun l => Qflow θ α l h) =
        fun l => l * Real.exp (-θ * h) / (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))) := by
      funext l; simp [Qflow, h0]
    rw [hf]
    have hnum : HasDerivAt (fun l : ℝ => l * Real.exp (-θ * h)) (Real.exp (-θ * h)) 0 := by
      convert (hasDerivAt_id' (0:ℝ)).mul_const (Real.exp (-θ * h)) using 1
      ring
    have hden : HasDerivAt (fun l : ℝ => 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))
        ((α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))) 0 := by
      convert (((hasDerivAt_id' (0:ℝ)).mul_const (α^2 / (2 * θ))).mul_const
        (1 - Real.exp (-θ * h))).const_add 1 using 1
      ring
    have h := hnum.div hden (by norm_num)
    convert h using 1
    simp

lemma Rflow_hasDerivAt_zero (θ α h : ℝ) :
    HasDerivAt (fun l => Rflow θ α l h) (1 - Real.exp (-θ * h)) 0 := by
  by_cases h0 : θ = 0
  · subst h0
    have hf : (fun l => Rflow 0 α l h) = fun _ => 0 := by funext l; simp [Rflow]
    rw [hf]
    simpa using hasDerivAt_const (0:ℝ) (0:ℝ)
  · by_cases hα : α = 0
    · subst hα
      have hf : (fun l => Rflow θ 0 l h) = fun l => l * (1 - Real.exp (-θ * h)) := by
        funext l; simp [Rflow, h0]
      rw [hf]
      convert (hasDerivAt_id' (0:ℝ)).mul_const (1 - Real.exp (-θ * h)) using 1
      ring
    · have hf : (fun l => Rflow θ α l h) = fun l =>
          (2 * θ / α^2) * Real.log (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))) := by
        funext l; simp [Rflow, h0, hα]
      rw [hf]
      have hin : HasDerivAt (fun l : ℝ => 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))
          ((α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))) 0 := by
        convert (((hasDerivAt_id' (0:ℝ)).mul_const (α^2 / (2 * θ))).mul_const
          (1 - Real.exp (-θ * h))).const_add 1 using 1
        ring
      have hlog := (hin.log (by norm_num)).const_mul (2 * θ / α^2)
      convert hlog using 1
      have hα2 : α^2 ≠ 0 := pow_ne_zero 2 hα
      field_simp
      ring

lemma piFlow_cons (θ : ℝ) (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    piFlow θ (p :: ps) = fun l => piFlow θ ps (Qflow θ p.1 l p.2) := rfl

lemma rhoFlow_cons (θ : ℝ) (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    rhoFlow θ (p :: ps) = fun l => Rflow θ p.1 l p.2 + rhoFlow θ ps (Qflow θ p.1 l p.2) := rfl

lemma piFlow_zero (θ : ℝ) (ps : List (ℝ × ℝ)) : piFlow θ ps 0 = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [piFlow_cons, Qflow_zero, ih]

lemma rhoFlow_zero (θ : ℝ) (ps : List (ℝ × ℝ)) : rhoFlow θ ps 0 = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [rhoFlow_cons, Qflow_zero, Rflow_zero, ih, add_zero]

lemma flow_nonneg (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    ∀ l, 0 ≤ l → 0 ≤ piFlow θ ps l ∧ 0 ≤ rhoFlow θ ps l := by
  induction ps with
  | nil => intro l hl; exact ⟨hl, le_rfl⟩
  | cons p ps ih =>
    intro l hl
    have hp := hps p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    have hQ := Qflow_nonneg θ p.1 l p.2 hθ hl hp.2
    rw [piFlow_cons, rhoFlow_cons]
    exact ⟨(ih' _ hQ).1, add_nonneg (Rflow_nonneg θ p.1 l p.2 hθ hl hp.2) (ih' _ hQ).2⟩

lemma flow_append (θ : ℝ) (ps qs : List (ℝ × ℝ)) (l : ℝ) :
    piFlow θ (qs ++ ps) l = piFlow θ ps (piFlow θ qs l) ∧
      rhoFlow θ (qs ++ ps) l = rhoFlow θ qs l + rhoFlow θ ps (piFlow θ qs l) := by
  induction qs generalizing l with
  | nil => simp [piFlow, rhoFlow]
  | cons p qs ih =>
    simp only [List.cons_append, piFlow_cons, rhoFlow_cons]
    obtain ⟨h1, h2⟩ := ih (Qflow θ p.1 l p.2)
    rw [h1, h2, add_assoc]
    exact ⟨rfl, rfl⟩

lemma totalLength_cons (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    totalLength (p :: ps) = p.2 + totalLength ps := by
  simp [totalLength]

lemma flow_hasDerivAt (θ : ℝ) (ps : List (ℝ × ℝ)) :
    HasDerivAt (piFlow θ ps) (Real.exp (-θ * totalLength ps)) 0 ∧
      HasDerivAt (rhoFlow θ ps) (1 - Real.exp (-θ * totalLength ps)) 0 := by
  induction ps with
  | nil =>
    simp only [totalLength, List.map_nil, List.sum_nil, mul_zero, Real.exp_zero, sub_self]
    exact ⟨hasDerivAt_id' 0, hasDerivAt_const 0 0⟩
  | cons p ps ih =>
    obtain ⟨hpi, hrho⟩ := ih
    have hQ := Qflow_hasDerivAt_zero θ p.1 p.2
    have hQ0 : Qflow θ p.1 0 p.2 = 0 := Qflow_zero θ p.1 p.2
    rw [← hQ0] at hpi hrho
    have hpi' := hpi.comp (0:ℝ) hQ
    have hrho' := (Rflow_hasDerivAt_zero θ p.1 p.2).add (hrho.comp (0:ℝ) hQ)
    rw [piFlow_cons, rhoFlow_cons, totalLength_cons]
    constructor
    · convert hpi' using 1
      · rfl
      · rw [show -θ * (p.2 + totalLength ps) = -θ * totalLength ps + -θ * p.2 by ring,
          Real.exp_add]
    · convert hrho' using 1
      · rfl
      · rw [show -θ * (p.2 + totalLength ps) = -θ * totalLength ps + -θ * p.2 by ring,
          Real.exp_add]
        ring

lemma composition : compositionStatement := by
  intro θ ps hθ hps
  obtain ⟨hpi, hrho⟩ := flow_hasDerivAt θ ps
  refine ⟨flow_nonneg θ ps hθ hps, fun qs l => flow_append θ ps qs l, piFlow_zero θ ps,
    rhoFlow_zero θ ps, hpi, hrho, fun v => ?_⟩
  have hsum : HasDerivAt (fun l => piFlow θ ps l * v + rhoFlow θ ps l)
      (lflow θ v (totalLength ps)) 0 := by
    convert (hpi.mul_const v).add hrho using 1
    unfold lflow; ring
  refine ⟨hsum, ?_⟩
  convert hsum.neg.exp using 1
  simp [piFlow_zero, rhoFlow_zero]

end Composition

/-! ### The transform at large `λ` -/

section Atom

lemma noise_free_exponent (θ h v l : ℝ) :
    Qflow θ 0 l h * v + Rflow θ 0 l h = l * lflow θ v h := by
  unfold Qflow Rflow lflow
  by_cases h0 : θ = 0
  · subst h0; simp
  · simp only [h0, if_false, if_true]
    ring

/-- For `θ > 0`, `α > 0`, `h > 0`, the accumulated `R` tends to infinity with `λ`. -/
lemma Rflow_tendsto_atTop (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    Filter.Tendsto (fun l => Rflow θ α l h) Filter.atTop Filter.atTop := by
  have hf : (fun l => Rflow θ α l h) = fun l =>
      (2 * θ / α^2) * Real.log (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))) := by
    funext l; simp [Rflow, hθ.ne', hα.ne']
  rw [hf]
  have he : Real.exp (-θ * h) < 1 := by
    have := Real.exp_lt_exp.2 (show -θ * h < 0 by nlinarith)
    simpa using this
  have hc : 0 < (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) := by
    have : 0 < 1 - Real.exp (-θ * h) := by linarith
    positivity
  have h1 : Filter.Tendsto (fun l : ℝ => 1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))
      Filter.atTop Filter.atTop := by
    have := (Filter.tendsto_id.const_mul_atTop hc)
    refine (Filter.tendsto_atTop_add_const_left _ 1 this).congr fun l => ?_
    simp only [id]; ring
  exact (Real.tendsto_log_atTop.comp h1).const_mul_atTop (by positivity)

lemma composed_no_atom (θ α h v : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) (hv : 0 ≤ v)
    (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    Filter.Tendsto
      (fun l => Real.exp (-(piFlow θ ((α, h) :: ps) l * v + rhoFlow θ ((α, h) :: ps) l)))
      Filter.atTop (nhds 0) := by
  have hR := Rflow_tendsto_atTop θ α h hθ hα hh
  have hup : Filter.Tendsto (fun l => Real.exp (-(Rflow θ α l h))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hR)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun l => (Real.exp_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with l hl
  apply Real.exp_le_exp.2
  simp only [piFlow_cons, rhoFlow_cons]
  have hQ := Qflow_nonneg θ α l h hθ.le hl hh.le
  have hpi := (flow_nonneg θ ps hθ.le hps _ hQ).1
  have hrho := (flow_nonneg θ ps hθ.le hps _ hQ).2
  nlinarith [mul_nonneg hpi hv]

lemma zero_reversion_atom (α h v : ℝ) (hα : 0 < α) (hh : 0 < h) :
    Filter.Tendsto (fun l => Real.exp (-(Qflow 0 α l h * v + Rflow 0 α l h))) Filter.atTop
      (nhds (Real.exp (-(2 * v / (α^2 * h))))) := by
  have hc : 0 < α^2 * h / 2 := by positivity
  have hf : (fun l => Qflow 0 α l h * v + Rflow 0 α l h) = fun l => l / (1 + α^2 * h * l / 2) * v := by
    funext l; simp [Qflow, Rflow]
  have hQ : Filter.Tendsto (fun l : ℝ => l / (1 + α^2 * h * l / 2)) Filter.atTop
      (nhds (1 / (α^2 * h / 2))) := by
    have h1 : Filter.Tendsto (fun l : ℝ => 1 / l + α^2 * h / 2) Filter.atTop
        (nhds (0 + α^2 * h / 2)) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).add_const (α^2 * h / 2)
    rw [zero_add] at h1
    have h2 : Filter.Tendsto (fun l : ℝ => 1 / (1 / l + α^2 * h / 2)) Filter.atTop
        (nhds (1 / (α^2 * h / 2))) := tendsto_const_nhds.div h1 hc.ne'
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with l hl
    field_simp
  have hf' : (fun l => Real.exp (-(Qflow 0 α l h * v + Rflow 0 α l h))) =
      fun l => Real.exp (-(l / (1 + α^2 * h * l / 2) * v)) := by
    funext l; simp [Qflow, Rflow]
  rw [hf']
  have hval : 2 * v / (α^2 * h) = 1 / (α^2 * h / 2) * v := by field_simp
  rw [hval]
  exact (Real.continuous_exp.tendsto _).comp ((hQ.mul_const v).neg)

lemma atom : atomStatement := by
  intro θ α h v hθ hh hv
  refine ⟨noise_free_exponent θ h v, fun h0 hα => ?_, fun hθ' hα => ?_,
    fun hθ' hα ps hps => composed_no_atom θ α h v hθ' hα hh hv ps hps⟩
  · subst h0; exact zero_reversion_atom α h v hα hh
  · have := composed_no_atom θ α h v hθ' hα hh hv [] (by simp)
    simpa [piFlow, rhoFlow] using this

end Atom

/-! ### The conditional variance from the second derivative of the exponent -/

section Variance

lemma denom_hasDerivAt (a l : ℝ) : HasDerivAt (fun l : ℝ => 1 + l * a) a l := by
  convert ((hasDerivAt_id' l).mul_const a).const_add 1 using 1
  ring

lemma variance : varianceStatement := by
  intro θ α h v hα hh hv
  constructor
  · intro hθ e κ
    have he : e < 1 := by
      calc e = Real.exp (-θ * h) := rfl
        _ < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
        _ = 1 := Real.exp_zero
    have he0 : 0 < e := Real.exp_pos _
    have hκ : 0 < κ := by positivity
    have ha : 0 < κ * (1 - e) := mul_pos hκ (by linarith)
    have hD : ∀ l : ℝ, 0 ≤ l → 0 < 1 + l * κ * (1 - e) := fun l hl => by
      have : 0 ≤ l * κ * (1 - e) := by
        have : 0 ≤ 1 - e := by linarith
        positivity
      linarith
    have hDd : ∀ l : ℝ, HasDerivAt (fun l : ℝ => 1 + l * κ * (1 - e)) (κ * (1 - e)) l := by
      intro l
      convert denom_hasDerivAt (κ * (1 - e)) l using 1
      funext l; ring
    have hQf : (fun l => Qflow θ α l h) = fun l => l * e / (1 + l * κ * (1 - e)) := by
      funext l; simp [Qflow, hθ.ne', e, κ]
    have hRf : (fun l => Rflow θ α l h) = fun l => (2 * θ / α^2) * Real.log (1 + l * κ * (1 - e)) := by
      funext l; simp [Rflow, hθ.ne', hα.ne', e, κ]
    have hκθ : 2 * θ / α^2 * κ = 1 := by
      simp only [κ]; field_simp
    refine ⟨fun l hl => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hQf]
      have hnum : HasDerivAt (fun l : ℝ => l * e) e l := by
        simpa using (hasDerivAt_id' l).mul_const e
      convert hnum.div (hDd l) (hD l hl).ne' using 1
      field_simp
      ring
    · rw [hRf]
      have hval : 2 * θ / α^2 * (κ * (1 - e) / (1 + l * κ * (1 - e))) =
          (1 - e) / (1 + l * κ * (1 - e)) := by
        rw [← mul_div_assoc, ← mul_assoc, hκθ, one_mul]
      exact (((hDd l).log (hD l hl).ne').const_mul (2 * θ / α^2)).congr_deriv hval
    · have hD0 : (1 + (0:ℝ) * κ * (1 - e)) ≠ 0 := by simp
      convert (hasDerivAt_const (0:ℝ) e).div ((hDd 0).pow 2) (pow_ne_zero 2 hD0) using 1
      simp
      ring
    · have hD0 : (1 + (0:ℝ) * κ * (1 - e)) ≠ 0 := by simp
      convert (hasDerivAt_const (0:ℝ) (1 - e)).div (hDd 0) hD0 using 1
      simp
      ring
    · have h1 : 0 < κ * (1 - e)^2 := by
        have : 0 < 1 - e := by linarith
        positivity
      have h2 : 0 ≤ 2 * e * κ * (1 - e) * v := by
        have : 0 ≤ 1 - e := by linarith
        positivity
      linarith
  · intro h0 c
    subst h0
    have hc : 0 < c := by positivity
    have hD : ∀ l : ℝ, 0 ≤ l → 0 < 1 + c * l := fun l hl => by
      have : 0 ≤ c * l := by positivity
      linarith
    have hDd : ∀ l : ℝ, HasDerivAt (fun l : ℝ => 1 + c * l) c l := by
      intro l
      convert denom_hasDerivAt c l using 1
      funext l; ring
    have hQf : (fun l => Qflow 0 α l h) = fun l => l / (1 + c * l) := by
      funext l; simp only [Qflow, if_true, c]; ring_nf
    refine ⟨fun l hl => ?_, fun l => by simp [Rflow], ?_, ?_⟩
    · rw [hQf]
      convert (hasDerivAt_id' l).div (hDd l) (hD l hl).ne' using 1
      field_simp
      ring
    · have hD0 : (1 + c * (0:ℝ)) ≠ 0 := by simp
      convert (hasDerivAt_const (0:ℝ) (1:ℝ)).div ((hDd 0).pow 2) (pow_ne_zero 2 hD0) using 1
      simp
    · constructor
      · intro h1; by_contra h2; nlinarith [not_lt.mp h2]
      · intro h1; positivity

end Variance

/-! ### The generator identity behind (a) -/

section Generator

lemma generator : generatorStatement := by
  intro θ α l t hθ hα hl u x hu q
  have hq : HasDerivAt (fun u => Qflow θ α l (t - u))
      (θ * Qflow θ α l (t - u) + α^2 * (Qflow θ α l (t - u))^2 / 2) u := by
    rcases hθ.eq_or_lt with hθ0 | hθp
    · subst hθ0
      exact Q_deriv_zero α l t u hl hα hu
    · exact Q_deriv_pos θ α l t u hθp hl hu
  have hr := R_deriv θ α l t u hθ hl hu
  have hin : HasDerivAt (fun u => -(Qflow θ α l (t - u) * x + Rflow θ α l (t - u)))
      (-((θ * Qflow θ α l (t - u) + α^2 * (Qflow θ α l (t - u))^2 / 2) * x +
        -(θ * Qflow θ α l (t - u)))) u :=
    ((hq.mul_const x).add hr).neg
  have hx : HasDerivAt (fun x => -(Qflow θ α l (t - u) * x + Rflow θ α l (t - u)))
      (-(Qflow θ α l (t - u) * 1)) x :=
    (((hasDerivAt_id' x).const_mul _).add_const _).neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hin.exp
    convert h using 1
    all_goals first | rfl | (simp only [backwardExp, q]; ring)
  · have h := hx.exp
    convert h using 1
    all_goals first | rfl | (simp only [backwardExp, q]; ring)
  · have h := hx.exp.const_mul (-Qflow θ α l (t - u))
    convert h using 1
    all_goals first | rfl | (simp only [backwardExp, q]; ring)
  · simp only [q]; ring

end Generator

/-! ### The globally `C²` extension of the joint backward exponential -/

section Extension
open Standalone.ZeroMeanReversionUpstreamBridge (g0155)
open Novel.ZeroMeanReversionUpstreamBridgeProof (g_eq_of_le g_ge g_contDiff)

variable {d : ℕ}

/-- The reciprocal width of the factor `j`. -/
noncomputable def invWidth (θ α l : ℝ) : ℝ :=
  if θ = 0 then 1 + α^2 * l else θ / Real.log (1 + 1 / (1 + 2 * l * (α^2 / (2 * θ))))

lemma invWidth_nonneg (θ α l : ℝ) (hθ : 0 ≤ θ) (hl : 0 ≤ l) : 0 ≤ invWidth θ α l := by
  unfold invWidth
  split_ifs with h0
  · positivity
  · have hθ' : 0 < θ := lt_of_le_of_ne hθ (Ne.symm h0)
    have hlog : 0 < Real.log (1 + 1 / (1 + 2 * l * (α^2 / (2 * θ)))) := by
      apply Real.log_pos
      have : 0 < 1 / (1 + 2 * l * (α^2 / (2 * θ))) := by positivity
      linarith
    positivity

lemma δ0235_def (θ α l : Fin d → ℝ) :
    δ0235 θ α l = 1 / (1 + ∑ j, invWidth (θ j) (α j) (l j)) := rfl

lemma δ0235_pos (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) : 0 < δ0235 θ α l := by
  rw [δ0235_def]
  have : 0 ≤ ∑ j, invWidth (θ j) (α j) (l j) :=
    Finset.sum_nonneg fun j _ => invWidth_nonneg _ _ _ (hθ j) (hl j)
  positivity

/-- The width times the reciprocal width of any factor is below one. -/
lemma δ0235_mul_le (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (j : Fin d) :
    invWidth (θ j) (α j) (l j) * δ0235 θ α l < 1 := by
  rw [δ0235_def]
  have hsum : 0 ≤ ∑ i, invWidth (θ i) (α i) (l i) :=
    Finset.sum_nonneg fun i _ => invWidth_nonneg _ _ _ (hθ i) (hl i)
  have hle : invWidth (θ j) (α j) (l j) ≤ ∑ i, invWidth (θ i) (α i) (l i) :=
    Finset.single_le_sum (f := fun i => invWidth (θ i) (α i) (l i))
      (fun i _ => invWidth_nonneg _ _ _ (hθ i) (hl i)) (Finset.mem_univ j)
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

/-- For `θ_j = 0`: the denominator of the flow stays positive past the horizon. -/
lemma denom_zero_pos (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t : ℝ)
    (j : Fin d) (h0 : θ j = 0) (u : ℝ) :
    0 < 1 + (α j)^2 * g0155 t (δ0235 θ α l) u * l j / 2 := by
  have hδ := δ0235_pos θ α l hθ hl
  have hg := g_ge t (δ0235 θ α l) u hδ
  have hsmall := δ0235_mul_le θ α l hθ hl j
  rw [invWidth, if_pos h0] at hsmall
  have h1 : (α j)^2 * (-δ0235 θ α l) * l j / 2 ≤ (α j)^2 * g0155 t (δ0235 θ α l) u * l j / 2 := by
    have := mul_le_mul_of_nonneg_left hg (sq_nonneg (α j))
    have := mul_le_mul_of_nonneg_right this (hl j)
    linarith
  nlinarith

/-- For `θ_j > 0`: the denominator of the flow stays positive past the horizon. -/
lemma denom_pos_pos (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t : ℝ)
    (j : Fin d) (hp : 0 < θ j) (u : ℝ) :
    0 < 1 + l j * ((α j)^2 / (2 * θ j)) * (1 - Real.exp (-θ j * g0155 t (δ0235 θ α l) u)) := by
  have hδ := δ0235_pos θ α l hθ hl
  have hg := g_ge t (δ0235 θ α l) u hδ
  have hsmall := δ0235_mul_le θ α l hθ hl j
  rw [invWidth, if_neg hp.ne'] at hsmall
  set κ := (α j)^2 / (2 * θ j) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hlκ : 0 ≤ l j * κ := mul_nonneg (hl j) hκ0
  set c := 1 / (1 + 2 * l j * κ) with hc
  have hc0 : 0 < c := by rw [hc]; exact one_div_pos.2 (by nlinarith)
  have hlog : 0 < Real.log (1 + c) := Real.log_pos (by linarith)
  -- `θ δ < log (1 + c)`
  have hθδ : θ j * δ0235 θ α l < Real.log (1 + c) := by
    rw [div_mul_eq_mul_div, div_lt_one hlog] at hsmall
    exact hsmall
  have hexp : Real.exp (-θ j * g0155 t (δ0235 θ α l) u) ≤ 1 + c := by
    calc Real.exp (-θ j * g0155 t (δ0235 θ α l) u) ≤ Real.exp (θ j * δ0235 θ α l) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ ≤ Real.exp (Real.log (1 + c)) := Real.exp_le_exp.2 hθδ.le
      _ = 1 + c := Real.exp_log (by linarith)
  -- `l κ c < 1` since `c = 1/(1 + 2 l κ)`
  have hlkc : l j * κ * c < 1 := by
    rw [hc, mul_one_div, div_lt_one (by nlinarith)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hexp hlκ]

lemma QExt_contDiff (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t : ℝ)
    (j : Fin d) : ContDiff ℝ 2 (fun u => QExt (θ j) (α j) (l j) t (δ0235 θ α l) u) := by
  have hg := g_contDiff t (δ0235 θ α l)
  rcases (hθ j).eq_or_lt with h0 | hp
  · have hf : (fun u => QExt (θ j) (α j) (l j) t (δ0235 θ α l) u) =
        fun u => l j / (1 + (α j)^2 * g0155 t (δ0235 θ α l) u * l j / 2) := by
      funext u; simp [QExt, Qflow, ← h0]
    rw [hf]
    refine contDiff_const.div ?_ (fun u => (denom_zero_pos θ α l hθ hl t j h0.symm u).ne')
    exact contDiff_const.add (((contDiff_const.mul hg).mul contDiff_const).div_const 2)
  · have hf : (fun u => QExt (θ j) (α j) (l j) t (δ0235 θ α l) u) =
        fun u => l j * Real.exp (-θ j * g0155 t (δ0235 θ α l) u) /
          (1 + l j * ((α j)^2 / (2 * θ j)) * (1 - Real.exp (-θ j * g0155 t (δ0235 θ α l) u))) := by
      funext u; simp [QExt, Qflow, hp.ne']
    rw [hf]
    have he : ContDiff ℝ 2 fun u => Real.exp (-θ j * g0155 t (δ0235 θ α l) u) :=
      Real.contDiff_exp.comp (contDiff_const.mul hg)
    refine (contDiff_const.mul he).div ?_ (fun u => (denom_pos_pos θ α l hθ hl t j hp u).ne')
    exact contDiff_const.add ((contDiff_const.mul contDiff_const).mul (contDiff_const.sub he))

lemma RExt_contDiff (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t : ℝ)
    (j : Fin d) : ContDiff ℝ 2 (fun u => RExt (θ j) (α j) (l j) t (δ0235 θ α l) u) := by
  have hg := g_contDiff t (δ0235 θ α l)
  rcases (hθ j).eq_or_lt with h0 | hp
  · have hf : (fun u => RExt (θ j) (α j) (l j) t (δ0235 θ α l) u) = fun _ => 0 := by
      funext u; simp [RExt, Rflow, ← h0]
    rw [hf]; exact contDiff_const
  · have he : ContDiff ℝ 2 fun u => Real.exp (-θ j * g0155 t (δ0235 θ α l) u) :=
      Real.contDiff_exp.comp (contDiff_const.mul hg)
    by_cases hα : α j = 0
    · have hf : (fun u => RExt (θ j) (α j) (l j) t (δ0235 θ α l) u) =
          fun u => l j * (1 - Real.exp (-θ j * g0155 t (δ0235 θ α l) u)) := by
        funext u; simp [RExt, Rflow, hp.ne', hα]
      rw [hf]
      exact contDiff_const.mul (contDiff_const.sub he)
    · have hf : (fun u => RExt (θ j) (α j) (l j) t (δ0235 θ α l) u) = fun u =>
          (2 * θ j / (α j)^2) * Real.log (1 + l j * ((α j)^2 / (2 * θ j)) *
            (1 - Real.exp (-θ j * g0155 t (δ0235 θ α l) u))) := by
        funext u; simp [RExt, Rflow, hp.ne', hα]
      rw [hf]
      refine contDiff_const.mul (ContDiff.log ?_ (fun u => (denom_pos_pos θ α l hθ hl t j hp u).ne'))
      exact contDiff_const.add ((contDiff_const.mul contDiff_const).mul (contDiff_const.sub he))

lemma EExt023_contDiff (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t : ℝ) :
    ContDiff ℝ 2 (EExt023 θ α l t (δ0235 θ α l)) := by
  unfold EExt023
  refine Real.contDiff_exp.comp (ContDiff.neg (ContDiff.sum fun j _ => ?_))
  exact (((QExt_contDiff θ α l hθ hl t j).comp contDiff_fst).mul
    ((contDiff_apply ℝ ℝ j).comp contDiff_snd)).add
    ((RExt_contDiff θ α l hθ hl t j).comp contDiff_fst)

lemma EExt023_eq (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t u : ℝ)
    (x : Fin d → ℝ) (hu : u ≤ t) :
    EExt023 θ α l t (δ0235 θ α l) (u, x) = Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) (t - u) * x j +
      Rflow (θ j) (α j) (l j) (t - u)))) := by
  simp only [EExt023, QExt, RExt, g_eq_of_le t _ u (δ0235_pos θ α l hθ hl) hu]

lemma extension : extensionStatement := by
  intro d θ α l t hθ hα hl
  exact ⟨EExt023 θ α l t (δ0235 θ α l), EExt023_contDiff θ α l hθ hl t,
    fun u x hu => EExt023_eq θ α l hθ hl t u x hu⟩

end Extension

/-! ### The Itô representation of (a) on one piece -/

section ItoStep
open scoped NNReal Topology
open ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge
open Novel.ZeroMeanReversionUpstreamBridgeProof (U4_zero zero_integral Hdrv_U4 quad_sum)

variable {d : ℕ}

/-- The time derivative of the joint exponential, in closed form. -/
lemma E023_time (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j) (hl : ∀ j, 0 ≤ l j)
    (t s : ℝ) (hs : s ≤ t) (x : Fin d → ℝ) :
    HasDerivAt (fun u => E023 θ α l t u x)
      (-(∑ j, ((θ j * Qflow (θ j) (α j) (l j) (t - s) +
        (α j)^2 * (Qflow (θ j) (α j) (l j) (t - s))^2 / 2) * x j +
        -(θ j * Qflow (θ j) (α j) (l j) (t - s)))) * E023 θ α l t s x) s := by
  have hq : ∀ j, HasDerivAt (fun u => Qflow (θ j) (α j) (l j) (t - u))
      (θ j * Qflow (θ j) (α j) (l j) (t - s) +
        (α j)^2 * (Qflow (θ j) (α j) (l j) (t - s))^2 / 2) s := by
    intro j
    rcases (hθ j).eq_or_lt with h0 | hp
    · rw [← h0]; exact Q_deriv_zero (α j) (l j) t s (hl j) (hα j) hs
    · exact Q_deriv_pos (θ j) (α j) (l j) t s hp (hl j) hs
  have hr : ∀ j, HasDerivAt (fun u => Rflow (θ j) (α j) (l j) (t - u))
      (-(θ j * Qflow (θ j) (α j) (l j) (t - s))) s := fun j => R_deriv _ _ _ t s (hθ j) (hl j) hs
  have hsum : HasDerivAt (fun u => ∑ j, (Qflow (θ j) (α j) (l j) (t - u) * x j +
      Rflow (θ j) (α j) (l j) (t - u)))
      (∑ j, ((θ j * Qflow (θ j) (α j) (l j) (t - s) +
        (α j)^2 * (Qflow (θ j) (α j) (l j) (t - s))^2 / 2) * x j +
        -(θ j * Qflow (θ j) (α j) (l j) (t - s)))) s := by
    have hsumPi := HasDerivAt.sum (u := Finset.univ)
      fun j (_ : j ∈ Finset.univ) => ((hq j).mul_const (x j)).add (hr j)
    convert hsumPi using 1
    funext u
    simp only [Finset.sum_apply, Pi.add_apply]
  have hin := hsum.neg
  have h := hin.exp
  convert h using 1
  all_goals first | rfl | (simp only [E023, Pi.neg_apply]; rw [mul_comm]) | (simp only [E023, Pi.neg_apply]; ring)

/-- The joint exponential along the coordinate `i` is an exponential of an affine function. -/
lemma E023_update (θ α l : Fin d → ℝ) (t s : ℝ) (x : Fin d → ℝ) (i : Fin d) (y : ℝ) :
    E023 θ α l t s (Function.update x i y) =
      Real.exp (-(Qflow (θ i) (α i) (l i) (t - s) * y +
        (∑ j, (Qflow (θ j) (α j) (l j) (t - s) * x j + Rflow (θ j) (α j) (l j) (t - s)) -
          Qflow (θ i) (α i) (l i) (t - s) * x i))) := by
  unfold E023
  congr 2
  have : ∀ j, Qflow (θ j) (α j) (l j) (t - s) * Function.update x i y j +
      Rflow (θ j) (α j) (l j) (t - s) =
      (Qflow (θ j) (α j) (l j) (t - s) * x j + Rflow (θ j) (α j) (l j) (t - s)) +
        (if j = i then Qflow (θ i) (α i) (l i) (t - s) * (y - x i) else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, if_true]; ring
    · simp only [Function.update_of_ne hj, if_neg hj]; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]
  ring

lemma E023_coord (θ α l : Fin d → ℝ) (t s : ℝ) (x : Fin d → ℝ) (i : Fin d) (y : ℝ) :
    HasDerivAt (fun y => E023 θ α l t s (Function.update x i y))
      (-Qflow (θ i) (α i) (l i) (t - s) * E023 θ α l t s (Function.update x i y)) y := by
  have hf : (fun y => E023 θ α l t s (Function.update x i y)) = fun y =>
      Real.exp (-(Qflow (θ i) (α i) (l i) (t - s) * y +
        (∑ j, (Qflow (θ j) (α j) (l j) (t - s) * x j + Rflow (θ j) (α j) (l j) (t - s)) -
          Qflow (θ i) (α i) (l i) (t - s) * x i))) := funext fun y => E023_update θ α l t s x i y
  rw [E023_update θ α l t s x i y, hf]
  have hin : HasDerivAt (fun y => -(Qflow (θ i) (α i) (l i) (t - s) * y +
      (∑ j, (Qflow (θ j) (α j) (l j) (t - s) * x j + Rflow (θ j) (α j) (l j) (t - s)) -
        Qflow (θ i) (α i) (l i) (t - s) * x i))) (-(Qflow (θ i) (α i) (l i) (t - s) * 1)) y :=
    (((hasDerivAt_id' y).const_mul _).add_const _).neg
  have h := hin.exp
  convert h using 1
  ring

lemma E023_coord_second (θ α l : Fin d → ℝ) (t s : ℝ) (x : Fin d → ℝ) (i : Fin d) (y : ℝ) :
    HasDerivAt (fun y => -Qflow (θ i) (α i) (l i) (t - s) * E023 θ α l t s (Function.update x i y))
      ((Qflow (θ i) (α i) (l i) (t - s))^2 * E023 θ α l t s (Function.update x i y)) y := by
  have h := (E023_coord θ α l t s x i y).const_mul (-Qflow (θ i) (α i) (l i) (t - s))
  convert h using 1
  ring

variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma driverForm_eq023 (k : Fin d → Fin S.m) (θ α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (x0 : Fin d → NNReal) (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) t ω =
      fun i => (X t ω i : ℝ) := by
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hs : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω := ae_all_iff.2 hsde
  filter_upwards [hz, hs, hx0] with ω hz hs hx0
  intro t
  funext i
  have hx0i : X 0 ω i = x0 i := congrFun hx0 i
  simp only [driverForm]
  rw [Finset.sum_eq_single (k i)]
  · simp only [Hdrv, eq_self_iff_true, ite_true]
    rw [hs i t, hx0i]
  · intro k' _ hk'
    simp only [Hdrv, ite_eq_right hk']
    exact hz k' t
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma dT_eq023 (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j) (hl : ∀ j, 0 ≤ l j)
    (t s : ℝ) (hs : s < t) (x : Fin d → ℝ) :
    dT (EExt023 θ α l t (δ0235 θ α l)) (s, x) =
      -(∑ j, ((θ j * Qflow (θ j) (α j) (l j) (t - s) +
        (α j)^2 * (Qflow (θ j) (α j) (l j) (t - s))^2 / 2) * x j +
        -(θ j * Qflow (θ j) (α j) (l j) (t - s)))) * E023 θ α l t s x := by
  have hf := (EExt023_contDiff θ α l hθ hl t).differentiable (by norm_num)
  have hL : HasDerivAt (fun u : ℝ => (u, x)) ((1 : ℝ), (0 : Fin d → ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h := (hf (s, x)).hasFDerivAt.comp_hasDerivAt s hL
  have heq : (EExt023 θ α l t (δ0235 θ α l) ∘ fun u : ℝ => (u, x)) =ᶠ[𝓝 s]
      fun u => E023 θ α l t u x := by
    filter_upwards [Iio_mem_nhds hs] with u hu
    exact EExt023_eq θ α l hθ hl t u x (le_of_lt hu)
  rw [dT, ← h.deriv, heq.deriv_eq]
  exact (E023_time θ α l hθ hα hl t s hs.le x).deriv

lemma dX_eq023 (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j)
    (t s : ℝ) (hs : s ≤ t) (x : Fin d → ℝ) (i : Fin d) :
    dX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i =
      -Qflow (θ i) (α i) (l i) (t - s) * E023 θ α l t s x := by
  classical
  have hfd : Differentiable ℝ (EExt023 θ α l t (δ0235 θ α l)) :=
    (EExt023_contDiff θ α l hθ hl t).differentiable (by norm_num)
  have hL : HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)) (x i) :=
    (hasDerivAt_const _ s).prodMk (hasDerivAt_update x i (x i))
  have hg : HasDerivAt (fun u => EExt023 θ α l t (δ0235 θ α l) (s, Function.update x i u))
      (fderiv ℝ (EExt023 θ α l t (δ0235 θ α l)) (s, Function.update x i (x i)) (0, Pi.single i 1))
      (x i) :=
    (hfd _).hasFDerivAt.comp_hasDerivAt (x i) hL
  rw [Function.update_eq_self] at hg
  have hgE : (fun u => EExt023 θ α l t (δ0235 θ α l) (s, Function.update x i u)) =
      fun u => E023 θ α l t s (Function.update x i u) :=
    funext fun u => EExt023_eq θ α l hθ hl t s _ hs
  rw [hgE] at hg
  have h2 := E023_coord θ α l t s x i (x i)
  rw [Function.update_eq_self] at h2
  unfold dX
  exact hg.unique h2

lemma dXX_eq023 (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j)
    (t s : ℝ) (hs : s ≤ t) (x : Fin d → ℝ) (i : Fin d) :
    dXX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i i =
      (Qflow (θ i) (α i) (l i) (t - s))^2 * E023 θ α l t s x := by
  classical
  have hf : ContDiff ℝ 2 (EExt023 θ α l t (δ0235 θ α l)) := EExt023_contDiff θ α l hθ hl t
  have hfd : Differentiable ℝ (EExt023 θ α l t (δ0235 θ α l)) := hf.differentiable (by norm_num)
  have hf' : Differentiable ℝ (fderiv ℝ (EExt023 θ α l t (δ0235 θ α l))) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hL : ∀ u, HasDerivAt (fun u : ℝ => (s, Function.update x i u))
      ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)) u :=
    fun u => (hasDerivAt_const u s).prodMk (hasDerivAt_update x i u)
  have hg : ∀ u, HasDerivAt (fun u => EExt023 θ α l t (δ0235 θ α l) (s, Function.update x i u))
      (fderiv ℝ (EExt023 θ α l t (δ0235 θ α l)) (s, Function.update x i u) (0, Pi.single i 1)) u :=
    fun u => (hfd _).hasFDerivAt.comp_hasDerivAt u (hL u)
  have hgE : (fun u => EExt023 θ α l t (δ0235 θ α l) (s, Function.update x i u)) =
      fun u => E023 θ α l t s (Function.update x i u) :=
    funext fun u => EExt023_eq θ α l hθ hl t s _ hs
  have hderiv : (fun u => fderiv ℝ (EExt023 θ α l t (δ0235 θ α l)) (s, Function.update x i u)
      (0, Pi.single i 1)) =
      fun u => -Qflow (θ i) (α i) (l i) (t - s) * E023 θ α l t s (Function.update x i u) := by
    funext u
    have h1 := hg u
    rw [hgE] at h1
    exact h1.unique (E023_coord θ α l t s x i u)
  have h2 : HasDerivAt (fun u => fderiv ℝ (EExt023 θ α l t (δ0235 θ α l)) (s, Function.update x i u)
        (0, Pi.single i 1))
      (fderiv ℝ (fderiv ℝ (EExt023 θ α l t (δ0235 θ α l))) (s, Function.update x i (x i))
        (0, Pi.single i 1) (0, Pi.single i 1)) (x i) := by
    have hc : HasDerivAt (fun u => fderiv ℝ (EExt023 θ α l t (δ0235 θ α l)) (s, Function.update x i u))
        (fderiv ℝ (fderiv ℝ (EExt023 θ α l t (δ0235 θ α l))) (s, Function.update x i (x i))
          (0, Pi.single i 1)) (x i) :=
      (hf' _).hasFDerivAt.comp_hasDerivAt (x i) (hL (x i))
    have := hc.clm_apply (hasDerivAt_const (x i) ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)))
    simpa using this
  rw [hderiv] at h2
  have h3 := E023_coord_second θ α l t s x i (x i)
  rw [Function.update_eq_self] at h2 h3
  unfold dXX
  exact h2.unique h3

/-- The finite-variation term of the Itô formula vanishes pointwise before the horizon. -/
lemma drift_pointwise023 (k : Fin d → Fin S.m) (θ α l : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j) (hl : ∀ j, 0 ≤ l j)
    (t s : ℝ) (hs : s < t) (ω : Ω) :
    dT (EExt023 θ α l t (δ0235 θ α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      (∑ i, dX (EExt023 θ α l t (δ0235 θ α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
        Kdrv θ X i (Real.toNNReal s) ω) +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l',
        dXX (EExt023 θ α l t (δ0235 θ α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i j *
          Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s) = 0 := by
  classical
  set x : Fin d → ℝ := fun i => (X (Real.toNNReal s) ω i : ℝ) with hx
  have hq : ∀ i j, (∑ k', ∑ l', dXX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i j *
      Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
        S.c k' l' (Real.toNNReal s)) =
      if i = j then dXX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i i * ((α i) ^ 2 * x i) else 0 := by
    intro i j
    rw [quad_sum S k α X (fun i j => dXX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i j) i j, hc]
    split_ifs with hij
    · subst hij
      simp only [hx, mul_one]
      have hsq : Real.sqrt (X (Real.toNNReal s) ω i : ℝ) * Real.sqrt (X (Real.toNNReal s) ω i : ℝ) =
          (X (Real.toNNReal s) ω i : ℝ) := Real.mul_self_sqrt (NNReal.coe_nonneg _)
      linear_combination (dXX (EExt023 θ α l t (δ0235 θ α l)) (s, x) i i * (α i) ^ 2) * hsq
    · simp
  simp_rw [hq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [dT_eq023 θ α l hθ hα hl t s hs x]
  simp_rw [dX_eq023 θ α l hθ hl t s hs.le x, dXX_eq023 θ α l hθ hl t s hs.le x]
  have hK : ∀ i, Kdrv θ X i (Real.toNNReal s) ω = θ i * (1 - x i) := fun i => rfl
  simp_rw [hK]
  rw [Finset.mul_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => by ring

lemma ito_representation023 (k : Fin d → Fin S.m) (θ α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω)
    (t : ℝ) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    (∀ i, U4 S.ℱ S.μ (Gint023 S k θ α l t x0 X i)) ∧
    ∀ᵐ ω ∂S.μ, ∀ u : ℝ≥0, (u : ℝ) ≤ t →
      E023 θ α l t u (fun i => (X u ω i : ℝ)) =
        E023 θ α l t 0 (fun i => (x0 i : ℝ)) + ∑ i, S.I (k i) (Gint023 S k θ α l t x0 X i) u ω := by
  classical
  obtain ⟨hU4, hae⟩ := S.ito_formula d (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X)
    (EExt023 θ α l t (δ0235 θ α l)) (fun i k' => Hdrv_U4 S k α X hU i k') hK
    (EExt023_contDiff θ α l hθ hl t)
  refine ⟨fun i => hU4 i (k i), ?_⟩
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  filter_upwards [hae, driverForm_eq023 S k θ α X x0 hx0 hsde, hz] with ω hω hdf hz
  intro u hu
  have h0t : (0 : ℝ) ≤ t := u.coe_nonneg.trans hu
  have h := hω u
  have hsum : ∀ i, (∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (EExt023 θ α l t (δ0235 θ α l))
      ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) s ω) i *
        Hdrv k α X i k' s ω) u ω) = S.I (k i) (Gint023 S k θ α l t x0 X i) u ω := by
    intro i
    rw [Finset.sum_eq_single (k i)]
    · rfl
    · intro k' _ hk'
      have hzero : (fun (s : ℝ≥0) ω => dX (EExt023 θ α l t (δ0235 θ α l))
          ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) s ω) i *
            Hdrv k α X i k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        simp [Hdrv, ite_eq_right hk']
      rw [hzero]
      exact hz k' u
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  simp only [hsum] at h
  have hdrift : (∫ s in (0 : ℝ)..u, (dT (EExt023 θ α l t (δ0235 θ α l))
      (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) (Real.toNNReal s) ω) +
      ∑ i, dX (EExt023 θ α l t (δ0235 θ α l))
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) (Real.toNNReal s) ω) i *
          Kdrv θ X i (Real.toNNReal s) ω +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l', dXX (EExt023 θ α l t (δ0235 θ α l))
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) (Real.toNNReal s) ω)
          i j * Hdrv k α X i k' (Real.toNNReal s) ω * Hdrv k α X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s))) = 0 := by
    refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
    have hT : ∀ᵐ s : ℝ, s ∉ ({t} : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton t)
    filter_upwards [hT] with s hsT hsI
    rw [Set.uIoc_of_le u.coe_nonneg] at hsI
    have hst : s < t := lt_of_le_of_ne (hsI.2.trans hu) (fun h => hsT (by simp [h]))
    rw [hdf (Real.toNNReal s)]
    exact drift_pointwise023 S k θ α l X hc hθ hα hl t s hst ω
  rw [hdrift, add_zero, hdf u, EExt023_eq θ α l hθ hl t _ _ hu, EExt023_eq θ α l hθ hl t 0 _ h0t]
    at h
  exact h

lemma ito023 : Standalone.PositiveMeanReversionSupport.itoStatement := by
  intro d Ω mΩ S k θ α X x0 hc hθ hα hx0 hU hK hsde t l hl
  exact ito_representation023 S k θ α X x0 hc hθ hα hx0 hU hK hsde t l hl

end ItoStep

/-! ### The localization of (a) on one piece -/

section Localization
open scoped NNReal Topology
open ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.ZeroMeanReversionVarianceSupport (filt0152 σ01521)
open Novel.ZeroMeanReversionUpstreamBridgeProof (stoppedInt stoppedInt_U5 martingale_finsum
  coe_min_Icc localizer_stoppingTime)
open Novel.ZeroMeanReversionVarianceSupportProof (localizer_stopping localizer_eventually
  localizer_coordinate_bound)

variable {d : ℕ}

lemma Qflow_le (θ α l h : ℝ) (hθ : 0 ≤ θ) (hl : 0 ≤ l) (hh : 0 ≤ h) : Qflow θ α l h ≤ l := by
  unfold Qflow
  split_ifs with h0
  · have : 0 ≤ α^2 * h * l / 2 := by positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have hθ' : 0 < θ := lt_of_le_of_ne hθ (Ne.symm h0)
    have he := exp_le_one_of_nonneg θ h hθ hh
    have he0 := Real.exp_pos (-θ * h)
    have hD : 0 ≤ l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) := by
      have : 0 ≤ 1 - Real.exp (-θ * h) := by linarith
      positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith

lemma E023_bounds (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (t s : ℝ)
    (hs : s ≤ t) (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) :
    0 < E023 θ α l t s x ∧ E023 θ α l t s x ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  refine neg_nonpos.2 (Finset.sum_nonneg fun j _ => add_nonneg ?_ ?_)
  · exact mul_nonneg (Qflow_nonneg _ _ _ _ (hθ j) (hl j) (sub_nonneg.2 hs)) (hx j)
  · exact Rflow_nonneg _ _ _ _ (hθ j) (hl j) (sub_nonneg.2 hs)

lemma measurable_E023 (θ α l : Fin d → ℝ) (t : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => E023 θ α l t p.1 p.2) := by
  unfold E023
  refine Real.measurable_exp.comp (Measurable.neg (Finset.measurable_sum _ fun j _ => ?_))
  refine Measurable.add (Measurable.mul ?_ ((measurable_pi_apply j).comp measurable_snd)) ?_
  · by_cases h0 : θ j = 0
    · simp only [Qflow, h0, if_true]
      fun_prop
    · simp only [Qflow, h0, if_false]
      fun_prop
  · by_cases h0 : θ j = 0
    · simp only [Rflow, h0, if_true]
      fun_prop
    · by_cases hα : α j = 0
      · simp only [Rflow, h0, hα, if_false, if_true]
        fun_prop
      · simp only [Rflow, h0, hα, if_false]
        fun_prop

variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma Gint023_bound (k : Fin d → Fin S.m) (θ α l : Fin d → ℝ) (hθ : ∀ j, 0 ≤ θ j)
    (hl : ∀ j, 0 ≤ l j) (t : ℝ) (x0 : Fin d → NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d)
    (s : ℝ≥0) (ω : Ω)
    (hdf : driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) s ω =
      fun j => (X s ω j : ℝ))
    (hs : (s : ℝ) ≤ t) (C : ℝ) (hX : (X s ω i : ℝ) ≤ C) :
    |Gint023 S k θ α l t x0 X i s ω| ≤ l i * |α i| * Real.sqrt C := by
  simp only [Gint023, hdf, Hdrv, ite_true]
  rw [dX_eq023 θ α l hθ hl t s hs]
  have hq0 := Qflow_nonneg (θ i) (α i) (l i) (t - s) (hθ i) (hl i) (sub_nonneg.2 hs)
  have hql := Qflow_le (θ i) (α i) (l i) (t - s) (hθ i) (hl i) (sub_nonneg.2 hs)
  have hE := E023_bounds θ α l hθ hl t s hs (fun j => (X s ω j : ℝ)) (fun j => NNReal.coe_nonneg _)
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq0, abs_of_pos hE.1, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : Real.sqrt (X s ω i : ℝ) ≤ Real.sqrt C := Real.sqrt_le_sqrt hX
  calc Qflow (θ i) (α i) (l i) (t - s) * E023 θ α l t s (fun j => (X s ω j : ℝ)) *
        (|α i| * Real.sqrt (X s ω i : ℝ))
      ≤ l i * 1 * (|α i| * Real.sqrt C) :=
        mul_le_mul (mul_le_mul hql hE.2 hE.1.le (hl i))
          (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg (hl i) zero_le_one)
    _ = l i * |α i| * Real.sqrt C := by ring

/-- The stopped joint exponential is adapted to the real-time filtration. -/
lemma stopped_adapted023 (t : NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hcont : ∀ ω j, Continuous fun u => (X u ω j : ℝ)) (hadapt : ∀ u, Measurable[S.ℱ u] (X u))
    (θ α l : Fin d → ℝ) (n : ℕ) (s : Set.Icc (0 : ℝ) t) :
    StronglyMeasurable[filt0152 (filtR S.ℱ) t s]
      (fun ω => M023 θ α l t (stateR X) (min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ)) ω) := by
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, t.coe_nonneg⟩⟩
  let u : Set.Icc (0 : ℝ) t → Ω → ℝ × (Fin d → ℝ) :=
    fun s ω => ((s : ℝ), fun j => (stateR X (s : ℝ) ω j : ℝ))
  have hu_ad : StronglyAdapted (filt0152 (filtR S.ℱ) t) u := by
    intro s
    refine (measurable_const.prodMk ?_).stronglyMeasurable
    have hcoe : Measurable (fun v : Fin d → NNReal => fun j => (v j : ℝ)) :=
      measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp (measurable_pi_apply j)
    exact hcoe.comp (hadapt (Real.toNNReal (s : ℝ)))
  have hu_cont : ∀ ω, Continuous fun s => u s ω := fun ω =>
    continuous_subtype_val.prodMk (continuous_pi fun j =>
      (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val))
  have hprog := hu_ad.isStronglyProgressive_of_continuous hu_cont
  have hτ := localizer_stopping (filtR S.ℱ) t (stateR X) (fun s _ => hadapt _)
    (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)) n
  have hsp := (hprog.stoppedProcess hτ).stronglyAdapted s
  have hE := measurable_E023 θ α l t
  have heq : (fun ω => M023 θ α l t (stateR X) (min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ)) ω) =
      fun ω => E023 θ α l t
        (stoppedProcess u (fun ω => (σ01521 t (stateR X) n ω : WithTop (Set.Icc (0 : ℝ) t))) s ω).1
        (stoppedProcess u (fun ω => (σ01521 t (stateR X) n ω : WithTop (Set.Icc (0 : ℝ) t))) s ω).2 := by
    funext ω
    simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopD_coe, u, M023, coe_min_Icc]
  rw [heq]
  exact (hE.comp hsp.measurable).stronglyMeasurable

/-- The stopped joint exponential along the localizers is a martingale, from the fields. -/
lemma localization_martingale023 (k : Fin d → Fin S.m) (θ α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j)
    (hcont : ∀ ω j, Continuous fun u => (X u ω j : ℝ)) (hadapt : ∀ u, Measurable[S.ℱ u] (X u))
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j)))
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ u, (X u ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) u ω +
        ∫ s in (0 : ℝ)..u, Kdrv θ X j (Real.toNNReal s) ω)
    (t : NNReal) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) (n : ℕ) :
    Martingale (fun (s : Set.Icc (0 : ℝ) t) ω =>
      M023 θ α l t (stateR X) (min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ)) ω)
      (filt0152 (filtR S.ℱ) t) S.μ := by
  classical
  have hc' : ∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) t => (stateR X s.val ω j : ℝ)) :=
    fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  obtain ⟨hU4G, hito⟩ := ito_representation023 S k θ α X x0 hc hθ hα hx0 hU hK hsde t l hl
  set τ : Ω → ℝ≥0 := fun ω => Real.toNNReal (σ01521 t (stateR X) n ω).val with hτdef
  have hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0)) :=
    localizer_stoppingTime S t X hcont hadapt n
  have hτT : ∀ ω, τ ω ≤ t := fun ω =>
    (Real.toNNReal_le_toNNReal (σ01521 t (stateR X) n ω).2.2).trans_eq Real.toNNReal_coe
  set G := Gint023 S k θ α l t x0 X with hGdef
  have hGb : ∀ i, ∀ᵐ ω ∂S.μ, ∀ s, s ≤ τ ω →
      |G i s ω| ≤ l i * |α i| * Real.sqrt ((n : ℝ) + 2) := by
    intro i
    filter_upwards [driverForm_eq023 S k θ α X x0 hx0 hsde, hx0] with ω hdf hx0ω s hs
    have hst : (s : ℝ) ≤ t := by exact_mod_cast hs.trans (hτT ω)
    have h0 : ∀ j, stateR X 0 ω j ≤ 1 := fun j => by
      have hx : X 0 ω j = x0 j := congrFun hx0ω j
      simp only [stateR, Real.toNNReal_zero, hx]
      exact hx0le j
    have hsσ : (⟨(s : ℝ), s.coe_nonneg, hst⟩ : Set.Icc (0 : ℝ) t) ≤ σ01521 t (stateR X) n ω :=
      (Real.le_toNNReal_iff_coe_le (σ01521 t (stateR X) n ω).2.1).mp hs
    have hXb := localizer_coordinate_bound t (stateR X) hc' ω h0 n
      ⟨(s : ℝ), s.coe_nonneg, hst⟩ hsσ i
    have hXb' : (X s ω i : ℝ) ≤ (n : ℝ) + 2 := by
      simp only [stateR, Real.toNNReal_coe] at hXb
      exact_mod_cast hXb
    exact Gint023_bound S k θ α l hθ hl t x0 X i s ω (hdf s) hst _ hXb'
  have hU5 : ∀ i, U5 S.ℱ S.μ (stoppedInt τ (G i)) t := fun i =>
    stoppedInt_U5 S τ hτ (G i) (hU4G i) _ (hGb i) t
  set c0 : ℝ := E023 θ α l t 0 (fun i => (x0 i : ℝ)) with hc0
  have hg : Martingale (fun u ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min u t) ω)
      S.ℱ S.μ :=
    (martingale_const S.ℱ S.μ c0).add
      (martingale_finsum _ S.ℱ S.μ fun i => (S.int_martingale (k i) _ t (hU5 i)).1)
  have hid : ∀ s : Set.Icc (0 : ℝ) t,
      (fun ω => M023 θ α l t (stateR X) (min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ)) ω) =ᵐ[S.μ]
        fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s) t) ω := by
    intro s
    have hst : ∀ᵐ ω ∂S.μ, ∀ i, S.I (k i) (G i) (min (Real.toNNReal s) (τ ω)) ω =
        S.I (k i) (stoppedInt τ (G i)) (Real.toNNReal s) ω :=
      ae_all_iff.2 fun i => S.int_stopped (k i) (G i) τ (hU4G i) hτ (Real.toNNReal s)
    filter_upwards [hito, hst] with ω hω hst
    have hmin : Real.toNNReal (min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ)) =
        min (Real.toNNReal s) (τ ω) := by
      rcases le_total (s : ℝ) (σ01521 t (stateR X) n ω : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.toNNReal_le_toNNReal h)]
      · rw [min_eq_right h, min_eq_right (Real.toNNReal_le_toNNReal h)]
    have hle : ((min (Real.toNNReal s) (τ ω) : ℝ≥0) : ℝ) ≤ t := by
      have : min (Real.toNNReal s) (τ ω) ≤ τ ω := min_le_right _ _
      exact_mod_cast this.trans (hτT ω)
    have hcoe : ((min (Real.toNNReal s) (τ ω) : ℝ≥0) : ℝ) =
        min (s : ℝ) (σ01521 t (stateR X) n ω : ℝ) := by
      rw [← hmin, Real.coe_toNNReal _ (le_min s.2.1 (σ01521 t (stateR X) n ω).2.1)]
    have hsT : min (Real.toNNReal s) t = Real.toNNReal s :=
      min_eq_left ((Real.toNNReal_le_toNNReal s.2.2).trans_eq Real.toNNReal_coe)
    simp only [M023, stateR, hmin, hsT]
    rw [← hcoe, hω _ hle]
    simp only [hst]
  refine ⟨fun s => stopped_adapted023 S t X hcont hadapt θ α l n s, fun s s' hss' => ?_⟩
  have hts : Real.toNNReal (s : ℝ) ≤ Real.toNNReal (s' : ℝ) :=
    Real.toNNReal_le_toNNReal (Subtype.coe_le_coe.mpr hss')
  have h1 : S.μ[(fun ω => M023 θ α l t (stateR X) (min (s' : ℝ) (σ01521 t (stateR X) n ω : ℝ)) ω)
      | filt0152 (filtR S.ℱ) t s] =ᵐ[S.μ]
      S.μ[(fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s') t) ω)
      | filt0152 (filtR S.ℱ) t s] := condExp_congr_ae (hid s')
  have h2 : S.μ[(fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s') t) ω)
      | filt0152 (filtR S.ℱ) t s] =ᵐ[S.μ]
      fun ω => c0 + ∑ i, S.I (k i) (stoppedInt τ (G i)) (min (Real.toNNReal s) t) ω :=
    hg.condExp_ae_eq hts
  exact h1.trans (h2.trans (hid s).symm)

lemma localization023 : Standalone.PositiveMeanReversionSupport.localizationStatement := by
  intro d Ω mΩ S k θ α X x0 hc hθ hα hcont hadapt hx0 hx0le hU hK hsde t l hl
  exact ⟨σ01521 t (stateR X), Eventually.of_forall fun ω => localizer_eventually t (stateR X)
    (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)) ω,
    fun n => localization_martingale023 S k θ α X x0 hc hθ hα hcont hadapt hx0 hx0le hU hK hsde
      t l hl n⟩

end Localization

/-! ### (23.3) on one piece from the stopped-martingale premise -/

section Transform
open scoped NNReal Topology
open ProbabilityTheory
open Standalone.ZeroMeanReversionVarianceSupport (filt0152)
open Novel.ZeroMeanReversionVarianceSupportProof (bounded_limit_martingale)

variable {d : ℕ}

lemma Qflow_len_zero (θ α l : ℝ) : Qflow θ α l 0 = l := by
  unfold Qflow; split_ifs <;> simp

lemma Rflow_len_zero (θ α l : ℝ) : Rflow θ α l 0 = 0 := by
  unfold Rflow; split_ifs <;> simp

lemma measurable_E023_state (θ α l : Fin d → ℝ) (t s : ℝ) :
    Measurable (fun x : Fin d → ℝ => E023 θ α l t s x) := by
  unfold E023
  refine Real.measurable_exp.comp (Measurable.neg (Finset.measurable_sum _ fun j _ => ?_))
  exact (measurable_const.mul (measurable_pi_apply j)).add measurable_const

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

lemma exponential_martingale023 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (θ α l : Fin d → ℝ) (t : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[F s] (X s))
    (hH : H023 μ F θ α l t X) :
    Martingale (fun (s : Set.Icc (0 : ℝ) t) ω => M023 θ α l t X (s : ℝ) ω) (filt0152 F t) μ := by
  obtain ⟨σ, hσ, hm⟩ := hH
  refine bounded_limit_martingale μ (filt0152 F t) (fun s ω => M023 θ α l t X (s : ℝ) ω)
    (fun n s ω => M023 θ α l t X (min (s : ℝ) (σ n ω : ℝ)) ω) hm ?_ ?_ ?_ ?_
  · intro s
    have hx : Measurable[F s.val] (fun ω j => (X s.val ω j : ℝ)) := by
      let : MeasurableSpace Ω := F s.val
      apply Measurable.of_eval
      intro j
      have hx := (measurable_pi_apply j).comp (hX s.val s.property)
      fun_prop
    exact ((measurable_E023_state θ α l t s.val).comp hx).stronglyMeasurable
  · intro s ω
    simp only [M023, Real.norm_eq_abs]
    rw [abs_of_pos (E023_bounds θ α l hθ hl t s.val s.property.2 _
      (fun j => (X s.val ω j).coe_nonneg)).1]
    exact (E023_bounds θ α l hθ hl t s.val s.property.2 _ (fun j => (X s.val ω j).coe_nonneg)).2
  · intro n s ω
    simp only [M023, Real.norm_eq_abs]
    have hle : min (s : ℝ) (σ n ω : ℝ) ≤ t := (min_le_left _ _).trans s.property.2
    rw [abs_of_pos (E023_bounds θ α l hθ hl t _ hle _ (fun j => (X _ ω j).coe_nonneg)).1]
    exact (E023_bounds θ α l hθ hl t _ hle _ (fun j => (X _ ω j).coe_nonneg)).2
  · intro s
    filter_upwards [hσ] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    rw [hn, min_eq_left s.property.2]

omit mΩ in
lemma M023_terminal (θ α l : Fin d → ℝ) (t : ℝ) (X : ℝ → Ω → Fin d → NNReal) :
    M023 θ α l t X t = fun ω => Real.exp (-(∑ j, l j * X t ω j)) := by
  funext ω
  simp only [M023, E023, sub_self, Qflow_len_zero, Rflow_len_zero, add_zero]

lemma conditional_transform023 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (θ α l : Fin d → ℝ) (t : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[F s] (X s))
    (hH : H023 μ F θ α l t X) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
    μ[fun ω => Real.exp (-(∑ j, l j * X t ω j)) | F s] =ᵐ[μ]
      fun ω => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) ((t : ℝ) - s) * X s ω j +
        Rflow (θ j) (α j) (l j) ((t : ℝ) - s)))) := by
  have hm := exponential_martingale023 μ F θ α l t X hθ hl hX hH
  have he := hm.condExp_ae_eq (i := ⟨s, hs⟩) (j := ⟨t, t.coe_nonneg, le_rfl⟩) hs.2
  change μ[M023 θ α l t X t | F s] =ᵐ[μ] M023 θ α l t X s at he
  rw [M023_terminal] at he
  exact he

lemma initial_transform023 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (θ α l : Fin d → ℝ) (t : NNReal) (X : ℝ → Ω → Fin d → NNReal)
    (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (hX : ∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[F s] (X s))
    (hH : H023 μ F θ α l t X) (x : Fin d → NNReal) (h0 : X 0 =ᵐ[μ] fun _ => x) :
    (∫ ω, Real.exp (-(∑ j, l j * X t ω j)) ∂μ) =
      Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) t * x j + Rflow (θ j) (α j) (l j) t))) := by
  have he := conditional_transform023 μ F θ α l t X hθ hl hX hH 0 ⟨le_rfl, t.coe_nonneg⟩
  have hconst : μ[fun ω => Real.exp (-(∑ j, l j * X t ω j)) | F 0] =ᵐ[μ]
      fun _ => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) t * x j + Rflow (θ j) (α j) (l j) t))) := by
    filter_upwards [he, h0] with ω hω hx
    rw [hω, hx]
    simp only [sub_zero]
  have hint := integral_congr_ae hconst
  rw [integral_condExp (F.le 0), integral_const] at hint
  simpa using hint

lemma conditionalTransform : conditionalTransformStatement := by
  intro d Ω mΩ μ hμ F θ α l t X hθ hl hX hH
  exact ⟨fun s hs => conditional_transform023 μ F θ α l t X hθ hl hX hH s hs,
    fun x h0 => initial_transform023 μ F θ α l t X hθ hl hX hH x h0⟩

end Transform

/-! ### The composition over pieces by the tower property -/

section Pieces
open ProbabilityTheory

variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The exponential of a nonnegative combination of the states is bounded, measurable in the
filtration at its time, and integrable. -/
lemma expSum_measurable (F : Filtration ℝ mΩ) (X : ℝ → Ω → Fin d → NNReal)
    (hX : ∀ s, Measurable[F s] (X s)) (c : Fin d → ℝ) (s : ℝ) :
    Measurable[F s] (fun ω => Real.exp (-(∑ j, c j * X s ω j))) := by
  let : MeasurableSpace Ω := F s
  have hx : ∀ j, Measurable (fun ω => (X s ω j : ℝ)) := fun j =>
    NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (hX s))
  exact Real.measurable_exp.comp (Measurable.neg (Finset.measurable_sum _ fun j _ =>
    (hx j).const_mul (c j)))

lemma expSum_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (X : ℝ → Ω → Fin d → NNReal) (hX : ∀ s, Measurable[F s] (X s)) (c : Fin d → ℝ)
    (hc : ∀ j, 0 ≤ c j) (s : ℝ) :
    Integrable (fun ω => Real.exp (-(∑ j, c j * X s ω j))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (((expSum_measurable F X hX c s).mono (F.le s) le_rfl).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hc j) (NNReal.coe_nonneg _)))

lemma leftEnd_cons (b : ℝ) (p : (Fin d → ℝ) × ℝ) (ps : List ((Fin d → ℝ) × ℝ)) :
    leftEnd b (p :: ps) = leftEnd (b - p.2) ps := by
  simp [leftEnd]; ring

lemma leftEnd_le (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.2) :
    leftEnd b ps ≤ b := by
  unfold leftEnd
  have : 0 ≤ (ps.map Prod.snd).sum := List.sum_nonneg fun h hh => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hh
    exact hps p hp
  linarith

lemma pieceComposition_aux (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ mΩ)
    (θ : Fin d → ℝ) (X : ℝ → Ω → Fin d → NNReal) (hθ : ∀ j, 0 ≤ θ j)
    (hX : ∀ s, Measurable[F s] (X s)) (ps : List ((Fin d → ℝ) × ℝ)) :
    ∀ (b : ℝ), (∀ p ∈ ps, 0 ≤ p.2) → PiecesOK μ F θ X b ps →
      ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * X b ω j)) | F (leftEnd b ps)] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j,
            (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * X (leftEnd b ps) ω j +
              rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j)))) := by
  induction ps with
  | nil =>
    intro b _ _ l hl
    have hb : leftEnd b ([] : List ((Fin d → ℝ) × ℝ)) = b := by simp [leftEnd]
    rw [hb]
    simp only [List.map_nil, piFlow, rhoFlow, add_zero]
    rw [condExp_of_stronglyMeasurable (F.le b) (expSum_measurable F X hX l b).stronglyMeasurable
      (expSum_integrable μ F X hX l hl b)]
  | cons p ps ih =>
    intro b hps hok l hl
    obtain ⟨hone, hrest⟩ := hok
    have hp2 : 0 ≤ p.2 := hps p (List.mem_cons_self ..)
    have hrest' : ∀ q ∈ ps, 0 ≤ q.2 := fun q hq => hps q (List.mem_cons_of_mem p hq)
    -- the composed flow of the first piece
    set Q : Fin d → ℝ := fun j => Qflow (θ j) (p.1 j) (l j) p.2 with hQ
    have hQ0 : ∀ j, 0 ≤ Q j := fun j => Qflow_nonneg _ _ _ _ (hθ j) (hl j) hp2
    have hs : leftEnd b (p :: ps) ≤ b - p.2 := by
      rw [leftEnd_cons]; exact leftEnd_le _ _ hrest'
    -- the one-piece transform at the left end of the first piece
    have h1 := hone l hl (b - p.2) ⟨le_rfl, by linarith⟩
    rw [sub_sub_cancel] at h1
    -- the split of the one-piece exponential into the constant and the state part
    have hsplit : (fun ω => Real.exp (-(∑ j, (Qflow (θ j) (p.1 j) (l j) p.2 * X (b - p.2) ω j +
        Rflow (θ j) (p.1 j) (l j) p.2)))) =
        Real.exp (-(∑ j, Rflow (θ j) (p.1 j) (l j) p.2)) •
          fun ω => Real.exp (-(∑ j, Q j * X (b - p.2) ω j)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, hQ]
      rw [← Real.exp_add, Finset.sum_add_distrib]
      congr 1; ring
    -- the tower property
    have htower := condExp_condExp_of_le (μ := μ)
      (f := fun ω => Real.exp (-(∑ j, l j * X b ω j))) (F.mono hs) (F.le (b - p.2))
    have h2 := condExp_congr_ae (m := F (leftEnd b (p :: ps))) h1
    rw [hsplit] at h2
    have h3 := condExp_smul (μ := μ) (Real.exp (-(∑ j, Rflow (θ j) (p.1 j) (l j) p.2)))
      (fun ω => Real.exp (-(∑ j, Q j * X (b - p.2) ω j))) (F (leftEnd b (p :: ps)))
    have h4 := ih (b - p.2) hrest' hrest Q hQ0
    rw [← leftEnd_cons] at h4
    refine htower.symm.trans (h2.trans (h3.trans ?_))
    have h5 : (Real.exp (-(∑ j, Rflow (θ j) (p.1 j) (l j) p.2)) •
        μ[fun ω => Real.exp (-(∑ j, Q j * X (b - p.2) ω j)) | F (leftEnd b (p :: ps))]) =ᵐ[μ]
        Real.exp (-(∑ j, Rflow (θ j) (p.1 j) (l j) p.2)) • fun ω => Real.exp (-(∑ j,
          (piFlow (θ j) (ps.map fun q => (q.1 j, q.2)) (Q j) * X (leftEnd b (p :: ps)) ω j +
            rhoFlow (θ j) (ps.map fun q => (q.1 j, q.2)) (Q j)))) :=
      h4.mono fun ω hω => by simp only [Pi.smul_apply, hω]
    refine h5.trans (Eventually.of_forall fun ω => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, List.map_cons, piFlow_cons, rhoFlow_cons, hQ]
    rw [← Real.exp_add]
    congr 1
    simp only [Finset.sum_add_distrib]
    ring

lemma pieceComposition : pieceCompositionStatement := by
  intro d Ω mΩ μ hμ F θ X hθ hX b ps hps hok l hl
  exact pieceComposition_aux μ F θ X hθ hX ps b hps hok l hl

end Pieces

/-! ### The Itô representation of the increment over a piece -/

section Increment
open scoped NNReal Topology
open ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge
open Novel.ZeroMeanReversionUpstreamBridgeProof (U4_zero zero_integral)

variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma Hpw_U4 (k : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) (i : Fin d) (k' : Fin S.m) :
    U4 S.ℱ S.μ (Hpw k αf X i k') := by
  unfold Hpw
  split_ifs
  · exact hU i
  · exact U4_zero S

lemma driverForm_eq_pw (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal) (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) t ω =
      fun i => (X t ω i : ℝ) := by
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hs : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω := ae_all_iff.2 hsde
  filter_upwards [hz, hs, hx0] with ω hz hs hx0
  intro t
  funext i
  have hx0i : X 0 ω i = x0 i := congrFun hx0 i
  simp only [driverForm]
  rw [Finset.sum_eq_single (k i)]
  · simp only [Hpw, ite_true]
    rw [hs i t, hx0i]
  · intro k' _ hk'
    simp only [Hpw, ite_eq_right hk']
    exact hz k' t
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma quad_sum_pw (k : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (D : Fin d → Fin d → ℝ) (i j : Fin d) (s : ℝ≥0) (ω : Ω) :
    (∑ k', ∑ l', D i j * Hpw k αf X i k' s ω * Hpw k αf X j l' s ω * S.c k' l' s) =
      D i j * (αf i s * Real.sqrt (X s ω i)) * (αf j s * Real.sqrt (X s ω j)) *
        S.c (k i) (k j) s := by
  classical
  rw [Finset.sum_eq_single (k i)]
  · rw [Finset.sum_eq_single (k j)]
    · simp only [Hpw, ite_true]
    · intro l' _ hl'
      simp [Hpw, ite_eq_right hl']
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k' _ hk'
    simp [Hpw, ite_eq_right hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The finite-variation integrand, reduced by the diagonal covariation: a continuous part plus
the quadratic part carrying the squared coefficient. -/
lemma drift_reduce_pw (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (f : ℝ × (Fin d → ℝ) → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) (s : ℝ) (ω : Ω) :
    dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      (∑ i, dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i * Kdrv θ X i (Real.toNNReal s) ω) +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l',
        dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i j *
          Hpw k αf X i k' (Real.toNNReal s) ω * Hpw k αf X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s) =
    (dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      ∑ i, dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
        (θ i * (1 - (X (Real.toNNReal s) ω i : ℝ)))) +
      (1 / 2 : ℝ) * ∑ i, (dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i *
        (X (Real.toNNReal s) ω i : ℝ)) * (αf i (Real.toNNReal s)) ^ 2 := by
  classical
  set x : Fin d → ℝ := fun i => (X (Real.toNNReal s) ω i : ℝ) with hx
  have hq : ∀ i j, (∑ k', ∑ l', dXX f (s, x) i j *
      Hpw k αf X i k' (Real.toNNReal s) ω * Hpw k αf X j l' (Real.toNNReal s) ω *
        S.c k' l' (Real.toNNReal s)) =
      if i = j then (dXX f (s, x) i i * x i) * (αf i (Real.toNNReal s)) ^ 2 else 0 := by
    intro i j
    rw [quad_sum_pw S k αf X (fun i j => dXX f (s, x) i j) i j, hc]
    split_ifs with hij
    · subst hij
      simp only [hx, mul_one]
      have hsq : Real.sqrt (X (Real.toNNReal s) ω i : ℝ) * Real.sqrt (X (Real.toNNReal s) ω i : ℝ) =
          (X (Real.toNNReal s) ω i : ℝ) := Real.mul_self_sqrt (NNReal.coe_nonneg _)
      linear_combination (dXX f (s, x) i i * (αf i (Real.toNNReal s)) ^ 2) * hsq
    · simp
  simp_rw [hq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- The finite-variation integrand vanishes on the piece before the horizon. -/
lemma drift_zero_pw (k : Fin d → Fin S.m) (θ α l : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j) (hl : ∀ j, 0 ≤ l j)
    (b s : ℝ) (hs : s < b) (hαs : ∀ j, αf j (Real.toNNReal s) = α j) (ω : Ω) :
    (dT (EExt023 θ α l b (δ0235 θ α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      ∑ i, dX (EExt023 θ α l b (δ0235 θ α l)) (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
        (θ i * (1 - (X (Real.toNNReal s) ω i : ℝ)))) +
      (1 / 2 : ℝ) * ∑ i, (dXX (EExt023 θ α l b (δ0235 θ α l))
        (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i *
        (X (Real.toNNReal s) ω i : ℝ)) * (αf i (Real.toNNReal s)) ^ 2 = 0 := by
  set x : Fin d → ℝ := fun i => (X (Real.toNNReal s) ω i : ℝ) with hx
  simp_rw [hαs]
  rw [dT_eq023 θ α l hθ hα hl b s hs x]
  simp_rw [dX_eq023 θ α l hθ hl b s hs.le x, dXX_eq023 θ α l hθ hl b s hs.le x]
  rw [Finset.mul_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => by ring

/-- The reduced finite-variation integrand is interval integrable on every `[0, u]`. -/
lemma drift_intervalIntegrable_pw (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (f : ℝ × (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (X : ℝ≥0 → Ω → Fin d → NNReal) (ω : Ω)
    (hcont : ∀ j, Continuous fun t => (X t ω j : ℝ))
    (hαm : ∀ j, Measurable (αf j)) (hαb : ∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) (u : ℝ) (hu : 0 ≤ u) :
    IntervalIntegrable (fun s : ℝ =>
      (dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
        ∑ i, dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
          (θ i * (1 - (X (Real.toNNReal s) ω i : ℝ)))) +
      (1 / 2 : ℝ) * ∑ i, (dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i *
        (X (Real.toNNReal s) ω i : ℝ)) * (αf i (Real.toNNReal s)) ^ 2) volume 0 u := by
  have hX : ∀ i, Continuous fun s : ℝ => (X (Real.toNNReal s) ω i : ℝ) := fun i =>
    (hcont i).comp continuous_real_toNNReal
  have hpair : Continuous fun s : ℝ => ((s, fun i => (X (Real.toNNReal s) ω i : ℝ)) :
      ℝ × (Fin d → ℝ)) :=
    continuous_id.prodMk (continuous_pi fun i => hX i)
  have hf1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hdT : Continuous fun s : ℝ => dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) :=
    (hf1.comp hpair).clm_apply continuous_const
  have hdX : ∀ i, Continuous fun s : ℝ =>
      dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i := fun i =>
    (hf1.comp hpair).clm_apply continuous_const
  have hdXX : ∀ i, Continuous fun s : ℝ =>
      dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i := fun i =>
    ((hf2.comp hpair).clm_apply continuous_const).clm_apply continuous_const
  have hC : Continuous fun s : ℝ => dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      ∑ i, dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
        (θ i * (1 - (X (Real.toNNReal s) ω i : ℝ))) :=
    hdT.add (continuous_finset_sum _ fun i _ => (hdX i).mul (continuous_const.mul
      (continuous_const.sub (hX i))))
  refine (hC.intervalIntegrable 0 u).add ?_
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu]
  refine (integrable_finset_sum _ fun i _ => ?_).const_mul _
  obtain ⟨C, hCb⟩ := hαb i (Real.toNNReal u)
  have hsq : IntegrableOn (fun s : ℝ => (αf i (Real.toNNReal s)) ^ 2) (Set.Icc 0 u) := by
    refine (integrable_const (C ^ 2)).mono'
      (((hαm i).comp measurable_real_toNNReal).pow_const 2).aestronglyMeasurable
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (hCb _ (Real.toNNReal_le_toNNReal hs.2)) 2
  have hg : ContinuousOn (fun s : ℝ => dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i *
      (X (Real.toNNReal s) ω i : ℝ)) (Set.Icc 0 u) :=
    ((hdXX i).mul (hX i)).continuousOn
  have := hsq.mul_continuousOn hg isCompact_Icc
  refine this.congr_fun (fun s _ => ?_) measurableSet_Icc
  ring

lemma ito_increment_pw (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ))
    (hαm : ∀ j, Measurable (αf j)) (hαb : ∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j)))
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω)
    (a b : ℝ≥0) (l : Fin d → ℝ) (hab : a ≤ b) (hl : ∀ j, 0 ≤ l j)
    (hpiece : ∀ j (s : ℝ≥0), a < s → s < b → αf j s = α j) :
    (∀ i, U4 S.ℱ S.μ (GintPw S k θ αf α l b x0 X i)) ∧
    ∀ᵐ ω ∂S.μ, ∀ u : ℝ≥0, a ≤ u → u ≤ b →
      E023 θ α l b u (fun i => (X u ω i : ℝ)) - E023 θ α l b a (fun i => (X a ω i : ℝ)) =
        ∑ i, (S.I (k i) (GintPw S k θ αf α l b x0 X i) u ω -
          S.I (k i) (GintPw S k θ αf α l b x0 X i) a ω) := by
  classical
  set f := EExt023 θ α l b (δ0235 θ α l) with hfdef
  have hfC : ContDiff ℝ 2 f := EExt023_contDiff θ α l hθ hl b
  obtain ⟨hU4, hae⟩ := S.ito_formula d (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) f
    (fun i k' => Hpw_U4 S k αf X hU i k') hK hfC
  refine ⟨fun i => hU4 i (k i), ?_⟩
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  filter_upwards [hae, driverForm_eq_pw S k θ αf X x0 hx0 hsde, hz] with ω hω hdf hz
  intro u hau hub
  -- the driver integrals collapse to the driver `k i`
  have hsum : ∀ (i : Fin d) (t : ℝ≥0), (∑ k', S.I k' (fun (s : ℝ≥0) ω => dX f
      ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) s ω) i *
        Hpw k αf X i k' s ω) t ω) = S.I (k i) (GintPw S k θ αf α l b x0 X i) t ω := by
    intro i t
    rw [Finset.sum_eq_single (k i)]
    · rfl
    · intro k' _ hk'
      have hzero : (fun (s : ℝ≥0) ω => dX f
          ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) s ω) i *
            Hpw k αf X i k' s ω) = fun _ _ => (0 : ℝ) := by
        funext s ω
        simp [Hpw, ite_eq_right hk']
      rw [hzero]
      exact hz k' t
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  -- the finite-variation integrand, written with the states and reduced
  set D : ℝ → ℝ := fun s =>
    (dT f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) +
      ∑ i, dX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i *
        (θ i * (1 - (X (Real.toNNReal s) ω i : ℝ)))) +
      (1 / 2 : ℝ) * ∑ i, (dXX f (s, fun i => (X (Real.toNNReal s) ω i : ℝ)) i i *
        (X (Real.toNNReal s) ω i : ℝ)) * (αf i (Real.toNNReal s)) ^ 2 with hD
  have hDeq : (fun s : ℝ => dT f
      (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) (Real.toNNReal s) ω) +
      ∑ i, dX f (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X)
        (Real.toNNReal s) ω) i * Kdrv θ X i (Real.toNNReal s) ω +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k', ∑ l', dXX f
        (s, driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) (Real.toNNReal s) ω)
          i j * Hpw k αf X i k' (Real.toNNReal s) ω * Hpw k αf X j l' (Real.toNNReal s) ω *
          S.c k' l' (Real.toNNReal s)) = D := by
    funext s
    rw [hdf (Real.toNNReal s)]
    exact drift_reduce_pw S k θ αf f X hc s ω
  have hint : ∀ v : ℝ, 0 ≤ v → IntervalIntegrable D volume 0 v := fun v hv =>
    drift_intervalIntegrable_pw θ αf f hfC X ω (hcont ω) hαm hαb v hv
  have hu := hω u
  have ha := hω a
  rw [hDeq] at hu ha
  simp only [hsum] at hu ha
  -- the difference of the two representations
  have hdiff : f ((u : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) u ω) -
      f ((a : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) a ω) =
      (∫ s in (a : ℝ)..u, D s) + ∑ i, (S.I (k i) (GintPw S k θ αf α l b x0 X i) u ω -
        S.I (k i) (GintPw S k θ αf α l b x0 X i) a ω) := by
    rw [hu, ha, ← intervalIntegral.integral_interval_sub_left (hint u u.coe_nonneg)
      (hint a a.coe_nonneg), Finset.sum_sub_distrib]
    ring
  -- the integrand vanishes on the piece
  have hzero : (∫ s in (a : ℝ)..u, D s) = 0 := by
    refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
    have hb : ∀ᵐ s : ℝ, s ∉ ({(b : ℝ)} : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton _)
    filter_upwards [hb] with s hsb hsI
    rw [Set.uIoc_of_le (NNReal.coe_le_coe.mpr hau)] at hsI
    have hs0 : (0 : ℝ) ≤ s := a.coe_nonneg.trans hsI.1.le
    have hsu : s ≤ u := hsI.2
    have hsb' : s < b := lt_of_le_of_ne (hsu.trans (NNReal.coe_le_coe.mpr hub))
      (fun h => hsb (by simp [h]))
    have has : a < Real.toNNReal s := by
      rw [← Real.toNNReal_coe (r := a)]
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg a.coe_nonneg).mpr hsI.1
    have hsb'' : Real.toNNReal s < b := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
      exact hsb'
    have hαs : ∀ j, αf j (Real.toNNReal s) = α j := fun j => hpiece j _ has hsb''
    exact drift_zero_pw S k θ α l αf X hc hθ hα hl b s hsb' hαs ω
  rw [hzero, zero_add] at hdiff
  rw [hdf u, hdf a] at hdiff
  rw [hfdef] at hdiff
  rw [EExt023_eq θ α l hθ hl b (u : ℝ) _ (NNReal.coe_le_coe.mpr hub),
    EExt023_eq θ α l hθ hl b (a : ℝ) _ (NNReal.coe_le_coe.mpr (hau.trans hub))] at hdiff
  exact hdiff

lemma itoIncrement : itoIncrementStatement := by
  intro d Ω mΩ S k θ αf α X x0 hc hθ hα hcont hαm hαb hx0 hU hK hsde a b l hab hl hpiece
  exact ito_increment_pw S k θ αf α X x0 hc hθ hα hcont hαm hαb hx0 hU hK hsde a b l hab hl hpiece

end Increment

/-! ### The one-piece transform on `[a, b]` from the fields -/

section OnePieceFields
open scoped NNReal Topology
open ProbabilityTheory
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.ZeroMeanReversionVarianceSupport (filt0152 σ01521)
open Novel.ZeroMeanReversionUpstreamBridgeProof (stoppedInt stoppedInt_U5 martingale_finsum
  localizer_stoppingTime)
open Novel.ZeroMeanReversionVarianceSupportProof (localizer_eventually localizer_coordinate_bound
  bounded_limit_martingale)

variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

lemma GintPw_bound (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ) (α l : Fin d → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hl : ∀ j, 0 ≤ l j) (b : ℝ) (x0 : Fin d → NNReal)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) (s : ℝ≥0) (ω : Ω)
    (hdf : driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) s ω =
      fun j => (X s ω j : ℝ))
    (hs : (s : ℝ) ≤ b) (C Cx : ℝ) (hC : |αf i s| ≤ C) (hX : (X s ω i : ℝ) ≤ Cx) :
    |GintPw S k θ αf α l b x0 X i s ω| ≤ l i * C * Real.sqrt Cx := by
  simp only [GintPw, hdf, Hpw, ite_true]
  rw [dX_eq023 θ α l hθ hl b s hs]
  have hq0 := Qflow_nonneg (θ i) (α i) (l i) (b - s) (hθ i) (hl i) (sub_nonneg.2 hs)
  have hql := Qflow_le (θ i) (α i) (l i) (b - s) (hθ i) (hl i) (sub_nonneg.2 hs)
  have hE := E023_bounds θ α l hθ hl b s hs (fun j => (X s ω j : ℝ)) (fun j => NNReal.coe_nonneg _)
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq0, abs_of_pos hE.1, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : Real.sqrt (X s ω i : ℝ) ≤ Real.sqrt Cx := Real.sqrt_le_sqrt hX
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  calc Qflow (θ i) (α i) (l i) (b - s) * E023 θ α l b s (fun j => (X s ω j : ℝ)) *
        (|αf i s| * Real.sqrt (X s ω i : ℝ))
      ≤ l i * 1 * (C * Real.sqrt Cx) :=
        mul_le_mul (mul_le_mul hql hE.2 hE.1.le (hl i))
          (mul_le_mul hC hsq (Real.sqrt_nonneg _) hC0)
          (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg (hl i) zero_le_one)
    _ = l i * C * Real.sqrt Cx := by ring

/-- The stopped joint exponential of the piece along the localizers is a martingale on `[a, b]`. -/
lemma stopped_increment_martingale (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hαm : ∀ j, Measurable (αf j)) (hαb : ∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j)))
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω)
    (a b : ℝ≥0) (hab : a ≤ b) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j)
    (hpiece : ∀ j (s : ℝ≥0), a < s → s < b → αf j s = α j) (n : ℕ) :
    Martingale (fun (u : Set.Icc (a : ℝ) b) ω =>
      M023 θ α l b (stateR X) (min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω)
      (filtI (filtR S.ℱ) a b) S.μ := by
  classical
  have hc' : ∀ ω j, Continuous (fun s : Set.Icc (0 : ℝ) b => (stateR X s.val ω j : ℝ)) :=
    fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  obtain ⟨hU4G, hinc⟩ :=
    ito_increment_pw S k θ αf α X x0 hc hθ hα hcont hαm hαb hx0 hU hK hsde a b l hab hl hpiece
  set τ : Ω → ℝ≥0 := fun ω => Real.toNNReal (σ01521 b (stateR X) n ω).val with hτdef
  have hτ : IsStoppingTime S.ℱ (fun ω => (τ ω : WithTop ℝ≥0)) :=
    localizer_stoppingTime S b X hcont hadapt n
  have hτT : ∀ ω, τ ω ≤ b := fun ω =>
    (Real.toNNReal_le_toNNReal (σ01521 b (stateR X) n ω).2.2).trans_eq Real.toNNReal_coe
  set G := GintPw S k θ αf α l b x0 X with hGdef
  choose C hC using fun j => hαb j b
  have hGb : ∀ i, ∀ᵐ ω ∂S.μ, ∀ s, s ≤ τ ω →
      |G i s ω| ≤ l i * C i * Real.sqrt ((n : ℝ) + 2) := by
    intro i
    filter_upwards [driverForm_eq_pw S k θ αf X x0 hx0 hsde, hx0] with ω hdf hx0ω s hs
    have hsb : (s : ℝ) ≤ b := by exact_mod_cast hs.trans (hτT ω)
    have h0 : ∀ j, stateR X 0 ω j ≤ 1 := fun j => by
      have hx : X 0 ω j = x0 j := congrFun hx0ω j
      simp only [stateR, Real.toNNReal_zero, hx]
      exact hx0le j
    have hsσ : (⟨(s : ℝ), s.coe_nonneg, hsb⟩ : Set.Icc (0 : ℝ) b) ≤ σ01521 b (stateR X) n ω :=
      (Real.le_toNNReal_iff_coe_le (σ01521 b (stateR X) n ω).2.1).mp hs
    have hXb := localizer_coordinate_bound b (stateR X) hc' ω h0 n
      ⟨(s : ℝ), s.coe_nonneg, hsb⟩ hsσ i
    have hXb' : (X s ω i : ℝ) ≤ (n : ℝ) + 2 := by
      simp only [stateR, Real.toNNReal_coe] at hXb
      exact_mod_cast hXb
    exact GintPw_bound S k θ αf α l hθ hl b x0 X i s ω (hdf s) hsb _ _ (hC i s (hs.trans (hτT ω))) hXb'
  have hU5 : ∀ i, U5 S.ℱ S.μ (stoppedInt τ (G i)) b := fun i =>
    stoppedInt_U5 S τ hτ (G i) (hU4G i) _ (hGb i) b
  -- the martingale of the stopped driver integrals
  set N : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i, S.I (k i) (stoppedInt τ (G i)) (min t b) ω with hNdef
  have hg : Martingale N S.ℱ S.μ :=
    martingale_finsum _ S.ℱ S.μ fun i => (S.int_martingale (k i) _ b (hU5 i)).1
  -- the stopped exponential on `[a, b]` is the stopped exponential at `a` plus the increment of `N`
  have hid : ∀ u : Set.Icc (a : ℝ) b,
      (fun ω => M023 θ α l b (stateR X) (min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω) =ᵐ[S.μ]
        fun ω => (M023 θ α l b (stateR X) (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω -
          N a ω) + N (Real.toNNReal u) ω := by
    intro u
    have hst : ∀ᵐ ω ∂S.μ, ∀ i, S.I (k i) (G i) (min (Real.toNNReal u) (τ ω)) ω =
        S.I (k i) (stoppedInt τ (G i)) (Real.toNNReal u) ω :=
      ae_all_iff.2 fun i => S.int_stopped (k i) (G i) τ (hU4G i) hτ (Real.toNNReal u)
    have hsta : ∀ᵐ ω ∂S.μ, ∀ i, S.I (k i) (G i) (min a (τ ω)) ω =
        S.I (k i) (stoppedInt τ (G i)) a ω :=
      ae_all_iff.2 fun i => S.int_stopped (k i) (G i) τ (hU4G i) hτ a
    filter_upwards [hinc, hst, hsta] with ω hω hst hsta
    have hub : (u : ℝ) ≤ b := u.2.2
    have hau : (a : ℝ) ≤ u := u.2.1
    have hσ0 := (σ01521 b (stateR X) n ω).2.1
    have hmin : Real.toNNReal (min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ)) =
        min (Real.toNNReal u) (τ ω) := by
      rcases le_total (u : ℝ) (σ01521 b (stateR X) n ω : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.toNNReal_le_toNNReal h)]
      · rw [min_eq_right h, min_eq_right (Real.toNNReal_le_toNNReal h)]
    have hmina : Real.toNNReal (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) =
        min a (τ ω) := by
      rcases le_total (a : ℝ) (σ01521 b (stateR X) n ω : ℝ) with h | h
      · have h' : a ≤ τ ω := by simpa [hτdef] using Real.toNNReal_le_toNNReal h
        rw [min_eq_left h, Real.toNNReal_coe, min_eq_left h']
      · have h' : τ ω ≤ a := by simpa [hτdef] using Real.toNNReal_le_toNNReal h
        rw [min_eq_right h, min_eq_right h']
    have hNu : N (Real.toNNReal u) ω = ∑ i, S.I (k i) (stoppedInt τ (G i)) (Real.toNNReal u) ω := by
      simp only [hNdef, min_eq_left ((Real.toNNReal_le_toNNReal hub).trans_eq Real.toNNReal_coe)]
    have hNa : N a ω = ∑ i, S.I (k i) (stoppedInt τ (G i)) a ω := by
      simp only [hNdef, min_eq_left hab]
    rw [hNu, hNa]
    simp only [M023, stateR, hmin, hmina]
    simp only [← hst, ← hsta]
    rcases le_or_gt a (τ ω) with haτ | haτ
    · -- the localizer is past `a`: the increment identity at `u ∧ τ`
      have hmin_a : min a (τ ω) = a := min_eq_left haτ
      rw [hmin_a]
      set u' := min (Real.toNNReal u) (τ ω) with hu'
      have hau_nn : a ≤ Real.toNNReal u := by simpa using Real.toNNReal_le_toNNReal hau
      have hau' : a ≤ u' := le_min hau_nn haτ
      have hu'b : u' ≤ b := (min_le_right _ _).trans (hτT ω)
      have hcoe : ((u' : ℝ≥0) : ℝ) = min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ) := by
        rw [← hmin, Real.coe_toNNReal _ (le_min (a.coe_nonneg.trans hau) hσ0)]
      have h := hω u' hau' hu'b
      rw [hcoe] at h
      rw [Finset.sum_sub_distrib] at h
      have hτσ : ((τ ω : ℝ≥0) : ℝ) = (σ01521 b (stateR X) n ω : ℝ) := Real.coe_toNNReal _ hσ0
      have haσ : (a : ℝ) ≤ σ01521 b (stateR X) n ω := by
        have := NNReal.coe_le_coe.mpr haτ
        rw [hτσ] at this
        exact this
      have hr2 : min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ) = a := min_eq_left haσ
      rw [hr2]
      linarith [h]
    · -- the localizer is before `a`: both sides are the stopped value at `τ`
      have hau_nn : a ≤ Real.toNNReal u := by simpa using Real.toNNReal_le_toNNReal hau
      have h1 : min (Real.toNNReal u) (τ ω) = τ ω := min_eq_right (haτ.le.trans hau_nn)
      have h2 : min a (τ ω) = τ ω := min_eq_right haτ.le
      have hτσ : ((τ ω : ℝ≥0) : ℝ) = (σ01521 b (stateR X) n ω : ℝ) := Real.coe_toNNReal _ hσ0
      have hσa : (σ01521 b (stateR X) n ω : ℝ) < a := by
        have := NNReal.coe_lt_coe.mpr haτ
        rw [hτσ] at this
        exact this
      have hr1 : min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ) = σ01521 b (stateR X) n ω :=
        min_eq_right (by linarith)
      have hr2 : min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ) = σ01521 b (stateR X) n ω :=
        min_eq_right (by linarith)
      rw [h1, h2, hr1, hr2]
      ring
  refine ⟨fun u => ?_, fun u u' huu' => ?_⟩
  · exact stopped_adapted023 S b X hcont hadapt θ α l n ⟨u.val, a.coe_nonneg.trans u.2.1, u.2.2⟩
  · have hts : Real.toNNReal (u : ℝ) ≤ Real.toNNReal (u' : ℝ) :=
      Real.toNNReal_le_toNNReal (Subtype.coe_le_coe.mpr huu')
    have hau : a ≤ Real.toNNReal (u : ℝ) := by simpa using Real.toNNReal_le_toNNReal u.2.1
    -- the `F_a`-measurable summand
    have hZmeas : StronglyMeasurable[filtI (filtR S.ℱ) a b u]
        (fun ω => M023 θ α l b (stateR X) (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω - N a ω) := by
      have hM := stopped_adapted023 S b X hcont hadapt θ α l n ⟨(a : ℝ), a.coe_nonneg, hab⟩
      have hMu : StronglyMeasurable[filtI (filtR S.ℱ) a b u]
          (fun ω => M023 θ α l b (stateR X) (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω) := by
        refine hM.mono ?_
        show S.ℱ (Real.toNNReal (a : ℝ)) ≤ S.ℱ (Real.toNNReal (u : ℝ))
        exact S.ℱ.mono (by rw [Real.toNNReal_coe]; exact hau)
      have hNa : StronglyMeasurable[filtI (filtR S.ℱ) a b u] (N a) :=
        (hg.stronglyAdapted a).mono (S.ℱ.mono hau)
      exact hMu.sub hNa
    have hZint : Integrable (fun ω => M023 θ α l b (stateR X)
        (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω - N a ω) S.μ := by
      refine Integrable.sub ?_ (hg.integrable a)
      have hM := stopped_adapted023 S b X hcont hadapt θ α l n ⟨(a : ℝ), a.coe_nonneg, hab⟩
      refine (integrable_const (1 : ℝ)).mono' (hM.mono (S.ℱ.le _)).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      simp only [M023, Real.norm_eq_abs]
      have hle : min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ) ≤ b :=
        (min_le_right _ _).trans (σ01521 b (stateR X) n ω).2.2
      rw [abs_of_pos (E023_bounds θ α l hθ hl b _ hle _ (fun j => (stateR X _ ω j).coe_nonneg)).1]
      exact (E023_bounds θ α l hθ hl b _ hle _ (fun j => (stateR X _ ω j).coe_nonneg)).2
    have h1 := condExp_congr_ae (m := filtI (filtR S.ℱ) a b u) (hid u')
    have h2 := condExp_add (μ := S.μ) hZint (hg.integrable (Real.toNNReal u'))
      (filtI (filtR S.ℱ) a b u)
    have h3 := condExp_of_stronglyMeasurable ((filtI (filtR S.ℱ) a b).le u) hZmeas hZint
    have h4 : S.μ[N (Real.toNNReal u') | filtI (filtR S.ℱ) a b u] =ᵐ[S.μ] N (Real.toNNReal u) :=
      hg.condExp_ae_eq hts
    refine h1.trans (h2.trans ?_)
    rw [h3]
    have h5 : ((fun ω => M023 θ α l b (stateR X) (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω -
          N a ω) + S.μ[N (Real.toNNReal u') | filtI (filtR S.ℱ) a b u]) =ᵐ[S.μ]
        fun ω => (M023 θ α l b (stateR X) (min (a : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω -
          N a ω) + N (Real.toNNReal u) ω :=
      h4.mono fun ω hω => by simp only [Pi.add_apply, hω]
    exact h5.trans (hid u).symm

/-- The joint exponential of the piece is a martingale on `[a, b]`. -/
lemma exponential_martingale_piece (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j)
    (hcont : ∀ ω j, Continuous fun t => (X t ω j : ℝ)) (hadapt : ∀ t, Measurable[S.ℱ t] (X t))
    (hαm : ∀ j, Measurable (αf j)) (hαb : ∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C)
    (hx0 : X 0 =ᵐ[S.μ] fun _ => x0) (hx0le : ∀ j, x0 j ≤ 1)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j)))
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j))
    (hsde : ∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω)
    (a b : ℝ≥0) (hab : a ≤ b) (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j)
    (hpiece : ∀ j (s : ℝ≥0), a < s → s < b → αf j s = α j) :
    Martingale (fun (u : Set.Icc (a : ℝ) b) ω => M023 θ α l b (stateR X) (u : ℝ) ω)
      (filtI (filtR S.ℱ) a b) S.μ := by
  have hm := fun n => stopped_increment_martingale S k θ αf α X x0 hc hθ hα hcont hadapt hαm hαb
    hx0 hx0le hU hK hsde a b hab l hl hpiece n
  refine bounded_limit_martingale S.μ (filtI (filtR S.ℱ) a b)
    (fun u ω => M023 θ α l b (stateR X) (u : ℝ) ω)
    (fun n u ω => M023 θ α l b (stateR X) (min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ)) ω)
    hm ?_ ?_ ?_ ?_
  · intro u
    have hx : Measurable[filtI (filtR S.ℱ) a b u] (fun ω j => (stateR X u.val ω j : ℝ)) := by
      let : MeasurableSpace Ω := filtI (filtR S.ℱ) a b u
      apply Measurable.of_eval
      intro j
      have hx := (measurable_pi_apply j).comp (hadapt (Real.toNNReal u.val))
      exact NNReal.continuous_coe.measurable.comp hx
    exact ((measurable_E023_state θ α l b u.val).comp hx).stronglyMeasurable
  · intro u ω
    simp only [M023, Real.norm_eq_abs]
    rw [abs_of_pos (E023_bounds θ α l hθ hl b u.val u.2.2 _ (fun j => (stateR X _ ω j).coe_nonneg)).1]
    exact (E023_bounds θ α l hθ hl b u.val u.2.2 _ (fun j => (stateR X _ ω j).coe_nonneg)).2
  · intro n u ω
    simp only [M023, Real.norm_eq_abs]
    have hle : min (u : ℝ) (σ01521 b (stateR X) n ω : ℝ) ≤ b := (min_le_left _ _).trans u.2.2
    rw [abs_of_pos (E023_bounds θ α l hθ hl b _ hle _ (fun j => (stateR X _ ω j).coe_nonneg)).1]
    exact (E023_bounds θ α l hθ hl b _ hle _ (fun j => (stateR X _ ω j).coe_nonneg)).2
  · intro u
    have hev := localizer_eventually b (stateR X)
      (fun ω j => (hcont ω j).comp (continuous_real_toNNReal.comp continuous_subtype_val))
    refine Eventually.of_forall fun ω => ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [hev ω] with n hn
    rw [hn, min_eq_left u.2.2]

lemma onePiece_of_fields : onePieceStatement := by
  intro d Ω mΩ S k θ αf α X x0 hc hθ hα hcont hadapt hαm hαb hx0 hx0le hU hK hsde a b hab hpiece
  intro l hl s hs
  have hm := exponential_martingale_piece S k θ αf α X x0 hc hθ hα hcont hadapt hαm hαb hx0 hx0le
    hU hK hsde a b hab l hl hpiece
  have he := hm.condExp_ae_eq (i := ⟨s, hs⟩) (j := ⟨b, hab, le_rfl⟩) hs.2
  change S.μ[M023 θ α l b (stateR X) b | filtR S.ℱ s] =ᵐ[S.μ] M023 θ α l b (stateR X) s at he
  rw [M023_terminal] at he
  exact he

end OnePieceFields

/-! ### The independence of the coordinates from the factorized transform -/

section Independence
open ProbabilityTheory
open Novel.ZeroMeanReversionVarianceSupportProof (laplace_unique)

variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- A nonnegative random vector whose joint Laplace transform is the product of the marginal
ones has independent coordinates. -/
lemma iIndepFun_of_laplace_factor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin d → ℝ) (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j)
    (h : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) = ∏ j, ∫ ω, Real.exp (-(l j * Y ω j)) ∂μ) :
    iIndepFun (fun j ω => Y ω j) μ := by
  have hYj : ∀ j, Measurable fun ω => Y ω j := fun j => (measurable_pi_apply j).comp hY
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hYj j).aemeasurable)]
  set ν : Fin d → Measure ℝ := fun j => μ.map (fun ω => Y ω j) with hν
  have : ∀ j, IsProbabilityMeasure (ν j) := fun j =>
    (Measure.isProbabilityMeasure_map_iff (hYj j).aemeasurable).2 inferInstance
  have hνnn : ∀ j, ∀ᵐ y ∂ν j, 0 ≤ y := fun j => by
    rw [hν]
    refine (ae_map_iff (hYj j).aemeasurable measurableSet_Ici).2 ?_
    filter_upwards [hY0] with ω hω
    exact hω j
  change μ.map Y = Measure.pi ν
  apply laplace_unique
  · refine (ae_map_iff hY.aemeasurable (show MeasurableSet {y : Fin d → ℝ | ∀ j, 0 ≤ y j} from
      measurableSet_setOfPred.mpr (by fun_prop))).2 hY0
  · rw [ae_all_iff]
    intro j
    have hmap := (measurePreserving_eval ν j).map_eq
    have := (ae_map_iff (measurable_pi_apply j).aemeasurable measurableSet_Ici).1
      (by rw [hmap]; exact hνnn j)
    exact this
  · intro l hl
    rw [integral_map hY.aemeasurable
      (show Continuous (fun y : Fin d → ℝ => Real.exp (-(∑ j, l j * y j))) by fun_prop).aestronglyMeasurable,
      h l hl]
    have he (y : Fin d → ℝ) : Real.exp (-(∑ j, l j * y j)) = ∏ j, Real.exp (-(l j * y j)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
    simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun j (y : ℝ) => Real.exp (-(l j * y)))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hν]
    rw [integral_map (hYj j).aemeasurable
      (show Continuous (fun y : ℝ => Real.exp (-(l j * y))) by fun_prop).aestronglyMeasurable]

lemma independence : independenceStatement := by
  intro d Ω mΩ μ hμ Y hY hY0 θ ps x h
  -- the marginal transforms, from the joint one at `λ` supported on a single coordinate
  have hmarg : ∀ (j : Fin d) (l : ℝ), 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω j)) ∂μ) =
      Real.exp (-(piFlow (θ j) (ps j) l * x j + rhoFlow (θ j) (ps j) l)) := by
    intro j l hl
    have hl' : ∀ k, 0 ≤ (Pi.single j l : Fin d → ℝ) k := fun k => by
      by_cases hk : k = j
      · subst hk; simp [hl]
      · simp [Pi.single_eq_of_ne hk]
    have hs : ∀ ω, (∑ k, (Pi.single j l : Fin d → ℝ) k * Y ω k) = l * Y ω j := by
      intro ω
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj; simp [Pi.single_eq_of_ne hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hv : (∑ k, (piFlow (θ k) (ps k) ((Pi.single j l : Fin d → ℝ) k) * x k +
        rhoFlow (θ k) (ps k) ((Pi.single j l : Fin d → ℝ) k))) =
        piFlow (θ j) (ps j) l * x j + rhoFlow (θ j) (ps j) l := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [Pi.single_eq_of_ne hkj, piFlow_zero, rhoFlow_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have := h (Pi.single j l) hl'
    simp only [hs, hv] at this
    exact this
  refine ⟨?_, hmarg⟩
  apply iIndepFun_of_laplace_factor μ Y hY hY0
  intro l hl
  rw [h l hl]
  simp_rw [hmarg _ _ (hl _)]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

end Independence

/-! ### The atom at zero from the transform -/

section AtomMass
open scoped Topology

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The Laplace transform of a nonnegative random variable tends to its mass at zero. -/
lemma transform_tendsto_atom (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) :
    Filter.Tendsto (fun l : ℝ => ∫ ω, Real.exp (-(l * Y ω)) ∂μ) Filter.atTop
      (𝓝 (μ.real {ω | Y ω = 0})) := by
  have hs : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  rw [← integral_indicator_one hs]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun l => (Real.measurable_exp.comp
      ((measurable_const.mul hY).neg)).aestronglyMeasurable) ?_ (integrable_const 1) ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with l hl
    filter_upwards [hY0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl hω))
  · filter_upwards [hY0] with ω hω
    by_cases h0 : Y ω = 0
    · simp only [h0, mul_zero, neg_zero, Real.exp_zero]
      have : ({ω | Y ω = 0} : Set Ω).indicator (1 : Ω → ℝ) ω = 1 :=
        Set.indicator_of_mem (show ω ∈ {ω | Y ω = 0} from h0) _
      rw [this]
      exact tendsto_const_nhds
    · have hpos : 0 < Y ω := lt_of_le_of_ne hω (Ne.symm h0)
      have : ({ω | Y ω = 0} : Set Ω).indicator (1 : Ω → ℝ) ω = 0 :=
        Set.indicator_of_notMem (show ω ∉ {ω | Y ω = 0} from h0) _
      rw [this]
      refine Real.tendsto_exp_atBot.comp ?_
      have h1 : Filter.Tendsto (fun l : ℝ => (-Y ω) * l) Filter.atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith) Filter.tendsto_id
      refine h1.congr fun l => ?_
      ring

lemma atomMass : atomMassStatement := by
  intro Ω mΩ μ hμ Y hY hY0
  have hlim := transform_tendsto_atom μ Y hY hY0
  refine ⟨hlim, fun θ x ps hx hps htr => ⟨?_, ?_⟩⟩
  · rintro α h ps' hθ hα hh rfl
    have hps' : ∀ p ∈ ps', 0 ≤ p.1 ∧ 0 ≤ p.2 := fun p hp => hps p (List.mem_cons_of_mem _ hp)
    have h2 := composed_no_atom θ α h x hθ hα hh hx ps' hps'
    have h3 : Filter.Tendsto (fun l : ℝ => ∫ ω, Real.exp (-(l * Y ω)) ∂μ) Filter.atTop (𝓝 0) := by
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 0] with l hl
      exact (htr l hl).symm
    exact tendsto_nhds_unique hlim h3
  · rintro α h hθ hα hh rfl
    subst hθ
    have h2 := zero_reversion_atom α h x hα hh
    have h3 : Filter.Tendsto (fun l : ℝ => ∫ ω, Real.exp (-(l * Y ω)) ∂μ) Filter.atTop
        (𝓝 (Real.exp (-(2 * x / (α^2 * h))))) := by
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 0] with l hl
      rw [htr l hl]
      simp [piFlow, rhoFlow]
    exact tendsto_nhds_unique hlim h3

end AtomMass

/-! ### The mean from the transform -/

section Mean
open scoped Topology

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The slope of the transform at zero tends to the mean. -/
lemma transform_slope_tendsto_mean (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hYi : Integrable Y μ) :
    Filter.Tendsto (fun l : ℝ => ∫ ω, (1 - Real.exp (-(l * Y ω))) / l ∂μ) (𝓝[>] 0)
      (𝓝 (∫ ω, Y ω ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence Y ?_ ?_ hYi ?_
  · exact Filter.Eventually.of_forall fun l => ((measurable_const.sub
      (Real.measurable_exp.comp ((measurable_const.mul hY).neg))).div_const l).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : 0 < l := hl
    filter_upwards [hY0] with ω hω
    have h1 : Real.exp (-(l * Y ω)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl'.le hω))
    have h2 : 1 - l * Y ω ≤ Real.exp (-(l * Y ω)) := Real.one_sub_le_exp_neg _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hl'.le), div_le_iff₀ hl']
    nlinarith
  · filter_upwards [hY0] with ω _
    have hd : HasDerivAt (fun l : ℝ => 1 - Real.exp (-(l * Y ω))) (Y ω) 0 := by
      have h := (((hasDerivAt_id' (0:ℝ)).mul_const (Y ω)).neg.exp).const_sub 1
      convert h using 1
      simp
    have := hd.tendsto_slope.mono_left (nhdsWithin_mono _ fun l (hl : 0 < l) => ne_of_gt hl)
    refine this.congr fun l => ?_
    rw [slope_def_field]
    simp

lemma mean : meanStatement := by
  intro Ω mΩ μ hμ Y hY hY0 hYi θ x ps hθ hps htr
  have hcomp := (composition θ ps hθ hps).2.2.2.2.2.2 x
  have hψ := hcomp.2
  set ψ : ℝ → ℝ := fun l => Real.exp (-(piFlow θ ps l * x + rhoFlow θ ps l)) with hψdef
  have hψ0 : ψ 0 = 1 := by simp [hψdef, piFlow_zero, rhoFlow_zero]
  -- the slope of the composed-flow exponential
  have h1 : Filter.Tendsto (fun l : ℝ => (1 - ψ l) / l) (𝓝[>] 0)
      (𝓝 (lflow θ x (totalLength ps))) := by
    have := (hψ.tendsto_slope.mono_left
      (nhdsWithin_mono _ fun l (hl : 0 < l) => ne_of_gt hl)).neg
    rw [neg_neg] at this
    refine this.congr fun l => ?_
    rw [slope_def_field, hψ0]
    ring
  -- the slope of the transform
  have h2 : Filter.Tendsto (fun l : ℝ => (1 - ψ l) / l) (𝓝[>] 0) (𝓝 (∫ ω, Y ω ∂μ)) := by
    refine (transform_slope_tendsto_mean μ Y hY hY0 hYi).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : 0 < l := hl
    have hint : Integrable (fun ω => Real.exp (-(l * Y ω))) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        (Real.measurable_exp.comp ((measurable_const.mul hY).neg)).aestronglyMeasurable ?_
      filter_upwards [hY0] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl'.le hω))
    rw [integral_div, integral_sub (integrable_const 1) hint, integral_const, htr l hl'.le]
    simp [hψdef]
  exact tendsto_nhds_unique h2 h1

end Mean

/-! ### The variance from the transform -/

section SecondMoment
open scoped Topology
open ProbabilityTheory

/-- `e^{−t} − 1 + t ≤ t²` for `t ≥ 0`. -/
lemma exp_taylor_two_le (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) - 1 + t ≤ t^2 := by
  rcases le_or_gt t 1 with h1 | h1
  · have hb := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg ht]; exact h1) (n := 2)
      (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
      abs_of_nonneg ht] at hb
    norm_num at hb
    have := (abs_le.mp hb).2
    nlinarith
  · have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith

/-- `|e^{−t} − 1 + t − t²/2| ≤ (2/9) t³` for `0 ≤ t ≤ 1`. -/
lemma exp_taylor_three_abs (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.exp (-t) - 1 + t - t^2 / 2| ≤ 2 / 9 * t^3 := by
  have hb := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg ht]; exact ht1) (n := 3)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg ht] at hb
  norm_num at hb
  calc |Real.exp (-t) - 1 + t - t^2 / 2| = |Real.exp (-t) - (1 + -t + t^2 / 2)| := by ring_nf
    _ ≤ 2 / 9 * t^3 := by convert hb using 1; ring

/-- The second-order slope of the exponential, bounded between `0` and `y²`. -/
lemma sq_slope_bounds (t y : ℝ) (ht : 0 < t) (hy : 0 ≤ y) :
    0 ≤ (Real.exp (-(t * y)) - 1 + t * y) / (t * t) ∧
      (Real.exp (-(t * y)) - 1 + t * y) / (t * t) ≤ y^2 := by
  have hty : 0 ≤ t * y := mul_nonneg ht.le hy
  have h1 := Real.one_sub_le_exp_neg (t * y)
  have h2 := exp_taylor_two_le (t * y) hty
  have htt : 0 < t * t := mul_pos ht ht
  constructor
  · exact div_nonneg (by linarith) htt.le
  · rw [div_le_iff₀ htt]
    nlinarith

/-- The second-order slope of the exponential tends to `y²/2`. -/
lemma sq_slope_tendsto (y : ℝ) (hy : 0 ≤ y) :
    Filter.Tendsto (fun t : ℝ => (Real.exp (-(t * y)) - 1 + t * y) / (t * t)) (𝓝[>] 0)
      (𝓝 (y^2 / 2)) := by
  rcases hy.eq_or_lt with hy0 | hy0
  · subst hy0
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, add_zero, zero_div, zero_pow two_ne_zero]
    exact tendsto_const_nhds
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun t => 2 / 9 * y^3 * t)
      (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ ?_
    · have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 / y :=
        (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / y)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, h1] with t ht ht1
      have ht' : 0 < t := ht
      have hty : t * y ≤ 1 := by rw [lt_div_iff₀ hy0] at ht1; exact ht1.le
      have hb := exp_taylor_three_abs (t * y) (mul_nonneg ht'.le hy) hty
      have htt : 0 < t * t := mul_pos ht' ht'
      rw [Real.norm_eq_abs, show (Real.exp (-(t * y)) - 1 + t * y) / (t * t) - y^2 / 2 =
        (Real.exp (-(t * y)) - 1 + t * y - (t * y)^2 / 2) / (t * t) by field_simp,
        abs_div, abs_of_pos htt, div_le_iff₀ htt]
      calc |Real.exp (-(t * y)) - 1 + t * y - (t * y)^2 / 2| ≤ 2 / 9 * (t * y)^3 := hb
        _ = 2 / 9 * y^3 * t * (t * t) := by ring
    · have : Filter.Tendsto (fun t : ℝ => 2 / 9 * y^3 * t) (𝓝 0) (𝓝 (2 / 9 * y^3 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The first two moments of a nonnegative square-integrable random variable from a smooth
Laplace transform: the mean is minus the derivative at zero and the second moment the second
derivative. -/
lemma moments_of_transform (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hY2 : MemLp Y 2 μ)
    (ψ ψ' : ℝ → ℝ) (c : ℝ) (hψ0 : ψ 0 = 1) (hψd : ∀ l, 0 ≤ l → HasDerivAt ψ (ψ' l) l)
    (hψ'd : HasDerivAt ψ' c 0)
    (htr : ∀ l, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) = ψ l) :
    (∫ ω, Y ω ∂μ) = -ψ' 0 ∧ (∫ ω, Y ω ^ 2 ∂μ) = c := by
  have hYi : Integrable Y μ := hY2.integrable one_le_two
  have hYsq : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have hint : ∀ l : ℝ, 0 ≤ l → Integrable (fun ω => Real.exp (-(l * Y ω))) μ := by
    intro l hl
    refine (integrable_const (1 : ℝ)).mono'
      (Real.measurable_exp.comp ((measurable_const.mul hY).neg)).aestronglyMeasurable ?_
    filter_upwards [hY0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl hω))
  -- the mean
  have hmean : (∫ ω, Y ω ∂μ) = -ψ' 0 := by
    have h1 : Filter.Tendsto (fun l : ℝ => (1 - ψ l) / l) (𝓝[>] 0) (𝓝 (-ψ' 0)) := by
      have := (hψd 0 le_rfl).tendsto_slope_zero_right.neg
      refine this.congr fun l => ?_
      simp only [zero_add, hψ0, smul_eq_mul]
      ring
    have h2 : Filter.Tendsto (fun l : ℝ => (1 - ψ l) / l) (𝓝[>] 0) (𝓝 (∫ ω, Y ω ∂μ)) := by
      refine (transform_slope_tendsto_mean μ Y hY hY0 hYi).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : 0 < l := hl
      rw [integral_div, integral_sub (integrable_const 1) (hint l hl'.le), integral_const,
        htr l hl'.le]
      simp
    exact tendsto_nhds_unique h2 h1
  refine ⟨hmean, ?_⟩
  set m : ℝ := -ψ' 0 with hm
  -- the second-order slope of the transform
  have hL : Filter.Tendsto (fun t : ℝ => ∫ ω, (Real.exp (-(t * Y ω)) - 1 + t * Y ω) / (t * t) ∂μ)
      (𝓝[>] 0) (𝓝 ((∫ ω, Y ω ^ 2 ∂μ) / 2)) := by
    rw [← integral_div]
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => Y ω ^ 2) ?_ ?_ hYsq ?_
    · exact Filter.Eventually.of_forall fun t => (((Real.measurable_exp.comp
        ((measurable_const.mul hY).neg)).sub measurable_const).add
        (measurable_const.mul hY)).div_const _ |>.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      filter_upwards [hY0] with ω hω
      have hb := sq_slope_bounds t (Y ω) ht' hω
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
    · filter_upwards [hY0] with ω hω
      exact sq_slope_tendsto (Y ω) hω
  -- the second-order slope of the exponential, by L'Hôpital's rule
  have hR : Filter.Tendsto (fun t : ℝ => (ψ t - 1 + t * m) / (t * t)) (𝓝[>] 0) (𝓝 (c / 2)) := by
    refine HasDerivAt.lhopital_zero_right_on_Ioo (f := fun t => ψ t - 1 + t * m)
      (f' := fun t => ψ' t + m) (g := fun t => t * t) (g' := fun t => 2 * t)
      (a := 0) (b := 1) one_pos ?_ ?_ ?_ ?_ ?_ ?_
    · intro t ht
      have := ((hψd t ht.1.le).sub_const 1).add ((hasDerivAt_id' t).mul_const m)
      convert this using 1
      all_goals ring
    · intro t _
      have := (hasDerivAt_id' t).mul (hasDerivAt_id' t)
      convert this using 1
      all_goals ring
    · intro t ht
      have := ht.1
      positivity
    · have hc : Filter.Tendsto (fun t => ψ t - 1 + t * m) (𝓝 0) (𝓝 (ψ 0 - 1 + 0 * m)) :=
        (((hψd 0 le_rfl).continuousAt.sub continuousAt_const).add
          (continuousAt_id.mul continuousAt_const)).tendsto
      rw [hψ0, sub_self, zero_mul, add_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · have hc : Filter.Tendsto (fun t : ℝ => t * t) (𝓝 0) (𝓝 ((0 : ℝ) * 0)) :=
        (continuous_id.mul continuous_id).tendsto 0
      rw [mul_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · have := (hψ'd.tendsto_slope_zero_right).div_const 2
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      simp only [zero_add, smul_eq_mul, hm]
      field_simp
      ring
  -- the two slopes agree on positive arguments
  have hLR : Filter.Tendsto (fun t : ℝ => (ψ t - 1 + t * m) / (t * t)) (𝓝[>] 0)
      (𝓝 ((∫ ω, Y ω ^ 2 ∂μ) / 2)) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hi1 : Integrable (fun ω => Real.exp (-(t * Y ω)) - 1) μ :=
      (hint t ht'.le).sub (integrable_const 1)
    have hi2 : Integrable (fun ω => t * Y ω) μ := hYi.const_mul t
    rw [integral_div, integral_add hi1 hi2, integral_sub (hint t ht'.le) (integrable_const 1),
      integral_const, integral_const_mul, htr t ht'.le, hmean, hm]
    simp
  have := tendsto_nhds_unique hLR hR
  linarith

lemma secondMoment : secondMomentStatement := by
  intro Ω mΩ μ hμ Y hY hY0 hY2 θ α h x hθ hα hh hx htr
  have hv := variance θ α h x hα hh hx
  constructor
  · intro hθp
    have h1 := hv.1 hθp
    dsimp only at h1
    obtain ⟨hd, hQ'', hR'', _⟩ := h1
    set e := Real.exp (-θ * h) with he
    set κ := α^2 / (2 * θ) with hκ
    set Q' : ℝ → ℝ := fun l => e / (1 + l * κ * (1 - e))^2 with hQ'
    set R' : ℝ → ℝ := fun l => (1 - e) / (1 + l * κ * (1 - e)) with hR'
    set ψ : ℝ → ℝ := fun l => Real.exp (-(Qflow θ α l h * x + Rflow θ α l h)) with hψ
    set ψ' : ℝ → ℝ := fun l => -(Q' l * x + R' l) * ψ l with hψ'
    have hψ0 : ψ 0 = 1 := by simp [hψ, Qflow_zero, Rflow_zero]
    have hψd : ∀ l, 0 ≤ l → HasDerivAt ψ (ψ' l) l := by
      intro l hl
      have := ((((hd l hl).1.mul_const x).add (hd l hl).2).neg).exp
      convert this using 1
      simp only [hψ', hψ, hQ', hR', Pi.add_apply, Pi.neg_apply]
      ring_nf
    have hψ'd : HasDerivAt ψ' (-(-(2 * e * κ * (1 - e)) * x + -(κ * (1 - e)^2)) * ψ 0 +
        -(Q' 0 * x + R' 0) * ψ' 0) 0 :=
      (((hQ''.mul_const x).add hR'').neg).mul (hψd 0 le_rfl)
    obtain ⟨hmean, hsq⟩ := moments_of_transform μ Y hY hY0 hY2 ψ ψ' _ hψ0 hψd hψ'd htr
    rw [variance_eq_sub hY2]
    simp only [Pi.pow_apply]
    rw [hsq, hmean]
    simp only [hψ', hψ0, hQ', hR', zero_mul, zero_add, one_pow, div_one]
    ring
  · intro hθ0
    subst hθ0
    have h1 := hv.2 rfl
    dsimp only at h1
    obtain ⟨hd, hR0, hQ'', _⟩ := h1
    set c := α^2 * h / 2 with hc
    set Q' : ℝ → ℝ := fun l => 1 / (1 + c * l)^2 with hQ'
    set ψ : ℝ → ℝ := fun l => Real.exp (-(Qflow 0 α l h * x + Rflow 0 α l h)) with hψ
    set ψ' : ℝ → ℝ := fun l => -(Q' l * x) * ψ l with hψ'
    have hψ0 : ψ 0 = 1 := by simp [hψ, Qflow_zero, Rflow_zero]
    have hψd : ∀ l, 0 ≤ l → HasDerivAt ψ (ψ' l) l := by
      intro l hl
      have hf : ψ = fun l => Real.exp (-(Qflow 0 α l h * x)) := by
        funext l; simp [hψ, hR0]
      rw [hf]
      have := (((hd l hl).mul_const x).neg).exp
      convert this using 1
      simp only [hψ', hψ, hQ', hR0, add_zero, Pi.neg_apply]
      ring_nf
    have hψ'd : HasDerivAt ψ' (-(-(2 * c) * x) * ψ 0 + -(Q' 0 * x) * ψ' 0) 0 :=
      ((hQ''.mul_const x).neg).mul (hψd 0 le_rfl)
    obtain ⟨hmean, hsq⟩ := moments_of_transform μ Y hY hY0 hY2 ψ ψ' _ hψ0 hψd hψ'd htr
    rw [variance_eq_sub hY2]
    simp only [Pi.pow_apply]
    rw [hsq, hmean]
    simp only [hψ', hψ0, hQ', mul_zero, add_zero, one_pow, div_one]
    ring

end SecondMoment

/-! ### The regular conditional law and coordinate independence -/

section ConditionalLaw
open ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal

lemma conditionalLaw_of_transform {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (htr : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j))))) :
    ∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
      (∀ ω, iIndepFun (fun j (y : Fin d → ℝ≥0) => y j) (κ ω)) ∧
      ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
        (fun ω => ∫ y, Real.exp (-(l * y j)) ∂κ ω) =ᵐ[μ]
          fun ω => Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l)) := by
  let ν : Fin d → @Kernel Ω ℝ≥0 G inferInstance := fun j =>
    @condDistrib Ω Ω ℝ≥0 _ _ _ mΩ G (fun ω => Y ω j) id μ inferInstance
  have hνprob : ∀ j, IsMarkovKernel (ν j) := fun j => by dsimp [ν]; infer_instance
  have hprob : ∀ (ω : Ω) (j : Fin d), IsProbabilityMeasure (ν j ω) := fun ω j => by infer_instance
  have hmeas : @Measurable Ω (Measure (Fin d → ℝ≥0)) G _ (fun ω => Measure.pi (fun j => ν j ω)) := by
    let : MeasurableSpace Ω := G
    have : ∀ ω, IsProbabilityMeasure (Measure.pi (fun j => ν j ω)) := fun ω => by infer_instance
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (generateFrom_eq_pi (fun _ => generateFrom_measurableSet)
        (fun _ => isCountablySpanning_measurableSet)).symm
      (IsPiSystem.pi (fun _ => isPiSystem_measurableSet))
    rintro _ ⟨B, hB, rfl⟩
    rw [mem_univ_pi] at hB
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun j _ => (ν j).measurable_coe (hB j)
  let κG : @Kernel Ω (Fin d → ℝ≥0) G inferInstance :=
    @Kernel.mk Ω (Fin d → ℝ≥0) G inferInstance (fun ω => Measure.pi (fun j => ν j ω)) hmeas
  have : IsMarkovKernel κG := ⟨fun ω => by change IsProbabilityMeasure (Measure.pi _); infer_instance⟩
  let κ : Kernel Ω (Fin d → ℝ≥0) := κG.comap id (measurable_id'' hG)
  have hκ : ∀ ω, κ ω = Measure.pi (fun j => ν j ω) := fun ω => rfl
  have hmarg : ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
      (fun ω => ∫ y : ℝ≥0, Real.exp (-(l * y)) ∂ν j ω) =ᵐ[μ]
        fun ω => Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l)) := by
    intro j l hl
    have hfun : StronglyMeasurable (fun y : ℝ≥0 => Real.exp (-(l * y))) := by fun_prop
    have hi : Integrable (fun ω => Real.exp (-(l * Y ω j))) μ := by
      refine (integrable_const (1 : ℝ)).mono' (hfun.comp_measurable ((measurable_pi_apply j).comp hY)).aestronglyMeasurable ?_
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl (Y ω j).coe_nonneg))
    have hc := @condExp_ae_eq_integral_condDistrib Ω Ω ℝ≥0 ℝ _ _ _ _ mΩ μ _ id
      (fun ω => Y ω j) G _ _ (measurable_id'' hG)
      ((measurable_pi_apply j).comp hY).aemeasurable _ hfun hi
    rw [MeasurableSpace.comap_id] at hc
    have he := htr (Pi.single j l) (fun k => by by_cases hk : k = j <;> simp [hk, hl])
    have hsum (ω : Ω) : (∑ k, (Pi.single j l : Fin d → ℝ) k * Y ω k) = l * Y ω j := by
      simp [Pi.single_apply]
    have hsum' (ω : Ω) : (∑ k, (piFlow (θ k) (ps k) ((Pi.single j l : Fin d → ℝ) k) * x ω k +
        rhoFlow (θ k) (ps k) ((Pi.single j l : Fin d → ℝ) k))) =
        piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj; simp [Pi.single_eq_of_ne hkj, piFlow_zero, rhoFlow_zero]
      · simp
    simp only [hsum, hsum'] at he
    exact hc.symm.trans he
  refine ⟨κ, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro B hB
    exact κG.measurable_coe hB
  · apply Novel.ZeroMeanReversionVarianceSupportProof.conditional_laplace_unique G μ hG Y hY κ
    intro l
    have he := htr (fun j => (l j : ℝ)) (fun j => (l j).coe_nonneg)
    have hm := ae_all_iff.2 (fun j => hmarg j (l j) (l j).coe_nonneg)
    filter_upwards [he, hm] with ω hω hmω
    rw [hω, hκ]
    have hexp (y : Fin d → ℝ≥0) : Real.exp (-(∑ j, (l j : ℝ) * y j)) =
        ∏ j, Real.exp (-((l j : ℝ) * y j)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
    simp_rw [hexp]
    rw [integral_fintype_prod_eq_prod (fun j (y : ℝ≥0) => Real.exp (-((l j : ℝ) * y)))]
    simp_rw [hmω]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  · intro ω
    rw [hκ]
    exact iIndepFun_pi (fun j => measurable_id.aemeasurable)
  · intro j l hl
    filter_upwards [hmarg j l hl] with ω hω
    rw [hκ]
    have hi := integral_map (μ := Measure.pi (fun j => ν j ω))
      (measurable_pi_apply j).aemeasurable
      (f := fun y : ℝ≥0 => Real.exp (-(l * y))) (by fun_prop)
    rw [(measurePreserving_eval (fun j => ν j ω) j).map_eq] at hi
    exact hi.symm.trans hω


lemma flow_continuous_nonneg (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    Continuous (fun l : ℝ≥0 => piFlow θ ps l) ∧
      Continuous (fun l : ℝ≥0 => rhoFlow θ ps l) := by
  have hc (α h : ℝ) (hh : 0 ≤ h) :
      Continuous (fun l : ℝ≥0 => Qflow θ α l h) ∧
        Continuous (fun l : ℝ≥0 => Rflow θ α l h) := by
    have he : 0 ≤ 1 - Real.exp (-θ * h) := sub_nonneg.2 (exp_le_one_of_nonneg θ h hθ hh)
    have hk : 0 ≤ α^2 / (2 * θ) * (1 - Real.exp (-θ * h)) := by positivity
    have hn (l : ℝ≥0) : 1 + (l : ℝ) * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) ≠ 0 := by
      have : 0 ≤ (l : ℝ) * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) := by positivity
      linarith
    constructor
    · unfold Qflow
      split_ifs
      · apply Continuous.div (by fun_prop) (by fun_prop)
        intro l
        positivity
      · exact Continuous.div (by fun_prop) (by fun_prop) hn
    · unfold Rflow
      split_ifs
      · fun_prop
      · fun_prop
      · exact continuous_const.mul ((by fun_prop : Continuous (fun l : ℝ≥0 =>
          1 + (l : ℝ) * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))).log hn)
  induction ps with
  | nil => simp only [piFlow, rhoFlow]; exact ⟨by fun_prop, continuous_const⟩
  | cons p ps ih =>
    have hp := hps p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    let q : ℝ≥0 → ℝ≥0 := fun l => ⟨Qflow θ p.1 l p.2, Qflow_nonneg θ p.1 l p.2 hθ l.coe_nonneg hp.2⟩
    have hq : Continuous q := (hc p.1 p.2 hp.2).1.subtype_mk _
    exact ⟨ih'.1.comp hq, (hc p.1 p.2 hp.2).2.add (ih'.2.comp hq)⟩

lemma marginal_transform_continuous {d : ℕ} (ν : Measure (Fin d → ℝ≥0))
    [IsProbabilityMeasure ν] (j : Fin d) :
    Continuous (fun l : ℝ≥0 => ∫ y, Real.exp (-((l : ℝ) * y j)) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro l
    exact (show Continuous (fun y : Fin d → ℝ≥0 => Real.exp (-((l : ℝ) * y j))) by fun_prop).aestronglyMeasurable
  · intro l
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg l.coe_nonneg (y j).coe_nonneg))
  · exact integrable_const 1
  · exact ae_of_all _ fun y => by fun_prop

lemma simultaneous_coordinate_transform {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (κ : Kernel Ω (Fin d → ℝ≥0)) [IsMarkovKernel κ]
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (htr : ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
      (fun ω => ∫ y, Real.exp (-(l * y j)) ∂κ ω) =ᵐ[μ]
        fun ω => Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l))) :
    ∀ᵐ ω ∂μ, ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
      (∫ y, Real.exp (-(l * y j)) ∂κ ω) =
        Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l)) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have h : ∀ᵐ ω ∂μ, ∀ j, ∀ l ∈ S,
      (∫ y, Real.exp (-((l : ℝ) * y j)) ∂κ ω) =
        Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l)) := by
    apply ae_all_iff.2
    intro j
    exact (ae_ball_iff hSc).2 (fun l _ => htr j l l.coe_nonneg)
  filter_upwards [h] with ω hω
  intro j l hl
  have heq := Continuous.ext_on hSd (marginal_transform_continuous (κ ω) j)
    (Real.continuous_exp.comp (((flow_continuous_nonneg (θ j) (ps j) (hθ j) (hps j)).1.mul continuous_const |>.add
      (flow_continuous_nonneg (θ j) (ps j) (hθ j) (hps j)).2).neg)) (hω j)
  exact congrFun heq ⟨l, hl⟩
lemma conditionalLaw : conditionalLawStatement := by
  intro d Ω G mΩ μ hμ hG Y hY θ ps x hθ hps htr
  obtain ⟨κ, hκ, hm, hl, hi, ht⟩ := conditionalLaw_of_transform G μ hG Y hY θ ps x htr
  letI := hκ
  exact ⟨κ, hκ, hm, hl, hi, simultaneous_coordinate_transform μ κ θ ps x hθ hps ht⟩

end ConditionalLaw

/-! ### Conditional moments from the regular conditional law -/

section ConditionalMoments
open ProbabilityTheory
open scoped NNReal ENNReal

lemma conditional_kernel_integrable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Kernel Ω (Fin d → ℝ≥0)) [IsMarkovKernel κ]
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y) (hlaw : μ.map Y = κ ∘ₘ μ)
    (j : Fin d) (hi : Integrable (fun ω => (Y ω j : ℝ)) μ) :
    ∀ᵐ ω ∂μ, Integrable (fun y : Fin d → ℝ≥0 => (y j : ℝ)) (κ ω) := by
  have hm : AEStronglyMeasurable (fun y : Fin d → ℝ≥0 => (y j : ℝ)) (μ.map Y) :=
    (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)) by fun_prop).aestronglyMeasurable
  have hi' := (integrable_map_measure hm hY.aemeasurable).2 hi
  rw [hlaw] at hi'
  exact Measure.ae_integrable_of_integrable_comp hi'

lemma conditional_kernel_mean {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Kernel Ω (Fin d → ℝ≥0)) [IsMarkovKernel κ]
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y) (hlaw : μ.map Y = κ ∘ₘ μ)
    (hYi : ∀ j, Integrable (fun ω => (Y ω j : ℝ)) μ)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (htr : ∀ᵐ ω ∂μ, ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
      (∫ y, Real.exp (-(l * y j)) ∂κ ω) =
        Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l))) :
    ∀ᵐ ω ∂μ, ∀ j, (∫ y : Fin d → ℝ≥0, (y j : ℝ) ∂κ ω) =
      lflow (θ j) (x ω j) (totalLength (ps j)) := by
  have hi := ae_all_iff.2 (fun j => conditional_kernel_integrable μ κ Y hY hlaw j (hYi j))
  filter_upwards [htr, hi] with ω ht hiω
  intro j
  exact mean _ _ (κ ω) inferInstance (fun y => (y j : ℝ)) (by fun_prop)
    (ae_of_all _ fun y => (y j).coe_nonneg) (hiω j) (θ j) (x ω j) (ps j)
    (hθ j) (hps j) (ht j)

lemma conditional_kernel_integral_ae {E Ω : Type} [MeasurableSpace E]
    (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hG : G ≤ mΩ) (κ : Kernel Ω E) [IsMarkovKernel κ]
    (Y : Ω → E) (hY : Measurable Y)
    (hlaw : ∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D)
    (f : E → ℝ) (hf : StronglyMeasurable f) (hi : Integrable (fun ω => f (Y ω)) μ)
    (g : Ω → ℝ) (hg : Measurable[G] g)
    (he : (fun ω => ∫ y, f y ∂κ ω) =ᵐ[μ] g) :
    μ[fun ω => f (Y ω) | G] =ᵐ[μ] g := by
  have hκ (D : Set Ω) (hD : MeasurableSet[G] D) : Integrable f (κ ∘ₘ μ.restrict D) := by
    rw [← hlaw D hD]
    exact (integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable).2 hi.restrict
  have hgi : Integrable g μ := by
    have hiκ := hκ univ MeasurableSet.univ
    rw [Measure.restrict_univ, Measure.comp_eq_comp_const_apply] at hiκ
    exact hiκ.integral_comp.congr he
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun D _ _ => hgi.integrableOn) ?_ hg.aestronglyMeasurable).symm
  intro D hD _
  have hiκ := hκ D hD
  have h := integral_map (μ := μ.restrict D) hY.aemeasurable hf.aestronglyMeasurable
  rw [hlaw D hD, Measure.comp_eq_comp_const_apply] at h
  rw [Measure.comp_eq_comp_const_apply] at hiκ
  rw [Kernel.integral_comp hiκ] at h
  exact (integral_congr_ae (ae_restrict_of_ae he)).symm.trans h

lemma conditional_mean {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (hYi : ∀ j, Integrable (fun ω => (Y ω j : ℝ)) μ)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hx : Measurable[G] x)
    (hθ : ∀ j, 0 ≤ θ j) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (htr : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j))))) :
    ∀ j, μ[fun ω => (Y ω j : ℝ) | G] =ᵐ[μ]
      fun ω => lflow (θ j) (x ω j) (totalLength (ps j)) := by
  obtain ⟨κ, hκ, hm, hl, hind, ht⟩ :=
    conditionalLaw d Ω G mΩ μ inferInstance hG Y hY θ ps x hθ hps htr
  let := hκ
  have hl0 := hl univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hl0
  have he := conditional_kernel_mean μ κ Y hY hl0 hYi θ ps x hθ hps ht
  intro j
  refine conditional_kernel_integral_ae G μ hG κ Y hY hl (fun y => (y j : ℝ))
    (by fun_prop) (hYi j) _ ?_ ?_
  · let : MeasurableSpace Ω := G
    have hxj := (measurable_pi_apply j).comp hx
    unfold lflow
    fun_prop
  · filter_upwards [he] with ω hω
    exact hω j

lemma deterministic_second_moment {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hY2 : MemLp Y 2 μ) (m : ℝ)
    (ht : ∀ l : ℝ, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) = Real.exp (-(l * m))) :
    (∫ ω, Y ω ^ 2 ∂μ) = m^2 := by
  let ψ : ℝ → ℝ := fun l => Real.exp (-(l * m))
  let ψ' : ℝ → ℝ := fun l => -m * Real.exp (-(l * m))
  have hd (l : ℝ) : HasDerivAt ψ (ψ' l) l := by
    convert (((hasDerivAt_id' l).mul_const m).neg).exp using 1
    simp [ψ', mul_comm]
  have hd' : HasDerivAt ψ' (m^2) 0 := by
    convert (hd 0).const_mul (-m) using 1
    simp [ψ', pow_two]
  have h0 : ψ 0 = 1 := by simp [ψ]
  exact (moments_of_transform μ Y hY hY0 hY2 ψ ψ' (m^2) h0
    (fun l _ => hd l) hd' ht).2

lemma conditional_variance_onePiece {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (hY2 : ∀ j, MemLp (fun ω => (Y ω j : ℝ)) 2 μ)
    (θ α : Fin d → ℝ) (h : ℝ) (x : Ω → Fin d → ℝ)
    (hx : Measurable[G] x) (hx0 : ∀ ω j, 0 ≤ x ω j)
    (hθ : ∀ j, 0 ≤ θ j) (hα : ∀ j, 0 ≤ α j) (hh : 0 ≤ h)
    (htr : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) h * x ω j +
          Rflow (θ j) (α j) (l j) h)))) :
    ∀ j, ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ =ᵐ[μ]
      fun ω => if θ j = 0 then (α j)^2 * h * x ω j else
        2 * Real.exp (-θ j * h) * ((α j)^2 / (2 * θ j)) *
          (1 - Real.exp (-θ j * h)) * x ω j +
            ((α j)^2 / (2 * θ j)) * (1 - Real.exp (-θ j * h))^2 := by
  let ps : Fin d → List (ℝ × ℝ) := fun j => [(α j, h)]
  have hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    intro j p hp
    simp only [ps, List.mem_singleton] at hp
    subst p
    exact ⟨hα j, hh⟩
  have htr' : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j)))) := by
    simpa [ps, piFlow, rhoFlow] using htr
  have hYi : ∀ j, Integrable (fun ω => (Y ω j : ℝ)) μ :=
    fun j => (hY2 j).integrable one_le_two
  obtain ⟨κ, hκ, hm, hl, hind, ht⟩ :=
    conditionalLaw d Ω G mΩ μ inferInstance hG Y hY θ ps x hθ hps htr'
  let := hκ
  have hl0 := hl univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hl0
  have hkmean := conditional_kernel_mean μ κ Y hY hl0 hYi θ ps x hθ hps ht
  have hk2 : ∀ᵐ ω ∂μ, ∀ j, MemLp (fun y : Fin d → ℝ≥0 => (y j : ℝ)) 2 (κ ω) := by
    apply ae_all_iff.2
    intro j
    have hs : Integrable (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) (κ ∘ₘ μ) := by
      rw [← hl0]
      exact (integrable_map_measure
        (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) by fun_prop).aestronglyMeasurable
        hY.aemeasurable).2 (hY2 j).integrable_sq
    filter_upwards [Measure.ae_integrable_of_integrable_comp hs] with ω hω
    exact (memLp_two_iff_integrable_sq
      (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)) by fun_prop).aestronglyMeasurable).2 hω
  let v : Fin d → Ω → ℝ := fun j ω => if θ j = 0 then (α j)^2 * h * x ω j else
    2 * Real.exp (-θ j * h) * ((α j)^2 / (2 * θ j)) *
      (1 - Real.exp (-θ j * h)) * x ω j +
        ((α j)^2 / (2 * θ j)) * (1 - Real.exp (-θ j * h))^2
  have hsquare : ∀ᵐ ω ∂μ, ∀ j, (∫ y : Fin d → ℝ≥0, (y j : ℝ)^2 ∂κ ω) =
      v j ω + (lflow (θ j) (x ω j) h)^2 := by
    filter_upwards [ht, hkmean, hk2] with ω htω hmω h2ω
    intro j
    have hmj : (∫ y : Fin d → ℝ≥0, (y j : ℝ) ∂κ ω) = lflow (θ j) (x ω j) h := by
      simpa [ps, totalLength] using hmω j
    have htrj : ∀ l : ℝ, 0 ≤ l →
        (∫ y : Fin d → ℝ≥0, Real.exp (-(l * y j)) ∂κ ω) =
          Real.exp (-(Qflow (θ j) (α j) l h * x ω j + Rflow (θ j) (α j) l h)) := by
      simpa [ps, piFlow, rhoFlow] using htω j
    by_cases hz : h = 0 ∨ α j = 0
    · have hd : ∀ l : ℝ, 0 ≤ l →
          (∫ y : Fin d → ℝ≥0, Real.exp (-(l * y j)) ∂κ ω) =
            Real.exp (-(l * lflow (θ j) (x ω j) h)) := by
        intro l hl
        rw [htrj l hl]
        rcases hz with hh0 | hα0
        · simp [hh0, Qflow_len_zero, Rflow_len_zero, lflow]
        · rw [hα0, noise_free_exponent]
      have hs := deterministic_second_moment (κ ω) (fun y => (y j : ℝ)) (by fun_prop)
        (ae_of_all _ fun y => (y j).coe_nonneg) (h2ω j) (lflow (θ j) (x ω j) h) hd
      have hv0 : v j ω = 0 := by
        rcases hz with hh0 | hα0
        · simp [v, hh0]
        · simp [v, hα0]
      simpa [hv0] using hs
    have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm (not_or.mp hz).1)
    have hαpos : 0 < α j := lt_of_le_of_ne (hα j) (Ne.symm (not_or.mp hz).2)
    have hv := secondMoment _ _ (κ ω) inferInstance (fun y => (y j : ℝ)) (by fun_prop)
      (ae_of_all _ fun y => (y j).coe_nonneg) (h2ω j) (θ j) (α j) h (x ω j)
      (hθ j) hαpos hhpos (hx0 ω j) htrj
    have hv' : ProbabilityTheory.variance (fun y : Fin d → ℝ≥0 => (y j : ℝ)) (κ ω) = v j ω := by
      by_cases hz : θ j = 0
      · simpa [v, hz] using hv.2 hz
      · simpa [v, hz] using hv.1 (lt_of_le_of_ne (hθ j) (Ne.symm hz))
    rw [ProbabilityTheory.variance_eq_sub (h2ω j), hmj] at hv'
    exact eq_add_of_sub_eq hv'
  intro j
  have hsqCE : μ[fun ω => (Y ω j : ℝ)^2 | G] =ᵐ[μ]
      fun ω => v j ω + (lflow (θ j) (x ω j) h)^2 := by
    refine conditional_kernel_integral_ae G μ hG κ Y hY hl (fun y => (y j : ℝ)^2)
      (by fun_prop) (hY2 j).integrable_sq _ ?_ ?_
    · let : MeasurableSpace Ω := G
      have hxj := (measurable_pi_apply j).comp hx
      unfold v lflow
      split_ifs <;> fun_prop
    · filter_upwards [hsquare] with ω hω
      exact hω j
  have hmeanCE : μ[fun ω => (Y ω j : ℝ) | G] =ᵐ[μ]
      fun ω => lflow (θ j) (x ω j) h := by
    simpa [ps, totalLength] using conditional_mean G μ hG Y hY hYi θ ps x hx hθ hps htr' j
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp hG (hY2 j)
  filter_upwards [hv, hsqCE, hmeanCE] with ω hvω hsω hmω
  change _ = v j ω
  simp only [Pi.sub_apply, Pi.pow_apply] at hvω
  change ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ ω =
    μ[fun ω => (Y ω j : ℝ)^2 | G] ω - (μ[fun ω => (Y ω j : ℝ) | G] ω)^2 at hvω
  rw [hvω, hsω, hmω]
  ring

lemma conditionalMean : conditionalMeanStatement := by
  intro d Ω G mΩ μ hμ hG Y hY hYi θ ps x hx hθ hps htr
  exact conditional_mean G μ hG Y hY hYi θ ps x hx hθ hps htr

lemma conditionalVariance : conditionalVarianceStatement := by
  intro d Ω G mΩ μ hμ hG Y hY hY2 θ α h x hx hx0 hθ hα hh htr
  exact conditional_variance_onePiece G μ hG Y hY hY2 θ α h x hx hx0 hθ hα hh htr

end ConditionalMoments

/-! ### Variance and covariance across the pieces -/

section PiecewiseVariance
open ProbabilityTheory
open scoped Topology NNReal ENNReal

lemma scale_nonneg (θ α h : ℝ) (hθ : 0 ≤ θ) (hh : 0 ≤ h) :
    0 ≤ varianceScale θ α h := by
  have he : Real.exp (-θ * h) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  unfold varianceScale
  split_ifs <;> positivity

lemma piece_derivatives (θ α h : ℝ) (hθ : 0 ≤ θ) (hh : 0 ≤ h) :
    let e := Real.exp (-θ * h)
    let a := varianceScale θ α h
    (∀ l, 0 ≤ l → HasDerivAt (fun l => Qflow θ α l h) (e / (1 + l * a)^2) l ∧
      HasDerivAt (fun l => Rflow θ α l h) ((1-e) / (1+l*a)) l) ∧
    HasDerivAt (fun l => e / (1+l*a)^2) (-(2*e*a)) 0 ∧
    HasDerivAt (fun l => (1-e) / (1+l*a)) (-((1-e)*a)) 0 := by
  dsimp only
  set e := Real.exp (-θ*h)
  set a := varianceScale θ α h
  have ha : 0 ≤ a := scale_nonneg θ α h hθ hh
  have hD (l : ℝ) (hl : 0 ≤ l) : 0 < 1+l*a := by positivity
  have hQ : (fun l => Qflow θ α l h) = fun l => l*e/(1+l*a) := by
    funext l
    by_cases hz : θ = 0
    · subst θ; simp [Qflow, e, a, varianceScale]; congr 2 <;> ring
    · simp [Qflow, hz, e, a, varianceScale, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    constructor
    · rw [hQ]
      convert ((hasDerivAt_id' l).mul_const e).div (denom_hasDerivAt a l) (hD l hl).ne' using 1
      field_simp
      ring
    · by_cases hz : θ = 0
      · subst θ
        simpa [Rflow, e] using hasDerivAt_const l (0:ℝ)
      by_cases hα : α = 0
      · subst α
        simpa [Rflow, hz, a, varianceScale, e] using (hasDerivAt_id' l).mul_const (1-e)
      have hc : 2*θ/α^2 * a = 1-e := by
        dsimp [a, varianceScale]
        rw [ite_eq_right hz]
        dsimp [e]
        field_simp
      have hr : (fun l => Rflow θ α l h) = fun l => (2*θ/α^2)*Real.log (1+l*a) := by
        funext l
        simp [Rflow, hz, hα, a, varianceScale, mul_assoc]
      rw [hr]
      convert ((denom_hasDerivAt a l).log (hD l hl).ne').const_mul (2*θ/α^2) using 1
      rw [← mul_div_assoc, hc]
  · convert (hasDerivAt_const (0:ℝ) e).div ((denom_hasDerivAt a 0).pow 2) (by simp) using 1 <;> simp <;> ring
  · convert (hasDerivAt_const (0:ℝ) (1-e)).div (denom_hasDerivAt a 0) (by simp) using 1 <;> simp <;> ring

lemma exponent_derivatives (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    ∃ g : ℝ → ℝ,
      (∀ l, 0 ≤ l → HasDerivAt (fun l => piFlow θ ps l * x + rhoFlow θ ps l) (g l) l) ∧
      g 0 = lflow θ x (totalLength ps) ∧
      HasDerivAt g (-varianceFlow θ x ps) 0 := by
  induction ps with
  | nil =>
    refine ⟨fun _ => x, ?_, ?_, ?_⟩
    · intro l hl; simpa [piFlow, rhoFlow] using (hasDerivAt_id' l).mul_const x
    · simp [lflow, totalLength]
    · simpa [varianceFlow] using hasDerivAt_const (0:ℝ) x
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    obtain ⟨g, hg, hg0, hgd⟩ := ih hps'
    obtain ⟨hd, hQd, hRd⟩ := piece_derivatives θ p.1 p.2 hθ hp.2
    let e := Real.exp (-θ*p.2)
    let a := varianceScale θ p.1 p.2
    let g' := fun l => g (Qflow θ p.1 l p.2) * (e / (1+l*a)^2) + (1-e)/(1+l*a)
    refine ⟨g', ?_, ?_, ?_⟩
    · intro l hl
      have h := ((hg (Qflow θ p.1 l p.2) (Qflow_nonneg θ p.1 l p.2 hθ hl hp.2)).comp l
        (hd l hl).1).add (hd l hl).2
      convert h using 1
      funext z; simp only [piFlow, rhoFlow, Function.comp_apply, Pi.add_apply]; ring
    · simp only [g', Qflow_zero, zero_mul, add_zero, one_pow, div_one, hg0]
      dsimp [e]
      rw [totalLength_cons]
      unfold lflow
      rw [show -θ*(p.2+totalLength ps) = -θ*totalLength ps + -θ*p.2 by ring, Real.exp_add]
      ring
    · have hgd' : HasDerivAt g (-varianceFlow θ x ps) (Qflow θ p.1 0 p.2) := by
        simpa [Qflow_zero] using hgd
      have h := ((hgd'.comp 0 (hd 0 le_rfl).1).mul hQd).add hRd
      convert h using 1
      · rfl
      · simp only [Function.comp_apply, Qflow_zero, hg0, zero_mul, add_zero, one_pow, div_one]
        dsimp [varianceFlow, pieceVariance, e, a]
        ring

lemma piecewise_variance {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hY2 : MemLp Y 2 μ)
    (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (ht : ∀ l, 0 ≤ l → (∫ ω, Real.exp (-(l*Y ω)) ∂μ) =
      Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l))) :
    ProbabilityTheory.variance Y μ = varianceFlow θ x ps := by
  obtain ⟨g, hg, hg0, hgd⟩ := exponent_derivatives θ x ps hθ hps
  let ψ := fun l => Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l))
  let ψ' := fun l => -g l * ψ l
  have hψ0 : ψ 0 = 1 := by simp [ψ, piFlow_zero, rhoFlow_zero]
  have hd (l : ℝ) (hl : 0 ≤ l) : HasDerivAt ψ (ψ' l) l := by
    convert (hg l hl).neg.exp using 1 <;> dsimp [ψ, ψ'] <;> ring
  have hd' := hgd.neg.mul (hd 0 le_rfl)
  obtain ⟨hm, hs⟩ := moments_of_transform μ Y hY hY0 hY2 ψ ψ' _ hψ0 hd hd' ht
  rw [variance_eq_sub hY2]
  simp only [Pi.pow_apply]
  rw [hs, hm]
  simp only [ψ', hψ0, Pi.neg_apply, neg_neg, mul_one]
  ring

lemma lflow_nonneg (θ x h : ℝ) (hθ : 0 ≤ θ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    0 ≤ lflow θ x h := by
  have he : Real.exp (-θ*h) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he0 := Real.exp_pos (-θ*h)
  unfold lflow
  nlinarith

lemma pieceVariance_nonneg (θ α x h : ℝ) (hθ : 0 ≤ θ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    0 ≤ pieceVariance θ α x h := by
  have ha := scale_nonneg θ α h hθ hh
  have he : 0 ≤ 1-Real.exp (-θ*h) := sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith))
  unfold pieceVariance
  positivity

lemma pieceVariance_pos_iff (θ α x h : ℝ) (hθ : 0 ≤ θ) (hα : 0 ≤ α)
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    0 < pieceVariance θ α x h ↔ 0 < α ∧ 0 < h ∧ (0 < θ ∨ 0 < x) := by
  by_cases hα0 : α = 0
  · subst α; simp [pieceVariance, varianceScale]
  by_cases hh0 : h = 0
  · subst h; simp [pieceVariance, varianceScale]
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  by_cases hθ0 : θ = 0
  · subst θ
    have hp : 0 < α^2*h := by positivity
    have hv : pieceVariance 0 α x h = α^2*h*x := by
      simp only [pieceVariance, varianceScale, ite_true, neg_zero, zero_mul, Real.exp_zero, mul_one, sub_self, zero_mul, add_zero]; ring
    rw [hv, mul_pos_iff_of_pos_left hp]
    simp [hαp, hhp]
  · have hθp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
    have he : 0 < 1-Real.exp (-θ*h) := by
      have : Real.exp (-θ*h) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
      linarith
    have ha : 0 < varianceScale θ α h := by
      rw [varianceScale, ite_eq_right hθ0]
      positivity
    have hv : 0 < pieceVariance θ α x h := by
      unfold pieceVariance
      positivity
    simp [hv, hαp, hhp, hθp]

lemma totalLength_nonneg (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    0 ≤ totalLength ps := by
  unfold totalLength
  apply List.sum_nonneg
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
  exact (hps p hp).2

lemma varianceFlow_nonneg (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) : 0 ≤ varianceFlow θ x ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    exact add_nonneg (mul_nonneg (sq_nonneg _) (ih hps'))
      (pieceVariance_nonneg θ p.1 _ p.2 hθ
        (lflow_nonneg θ x _ hθ hx (totalLength_nonneg ps hps')) hp.2)

lemma varianceFlow_pos_iff (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    0 < varianceFlow θ x ps ↔
      (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x) := by
  induction ps with
  | nil => simp [varianceFlow]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    have hv := varianceFlow_nonneg θ x ps hθ hx hps'
    have hm := lflow_nonneg θ x _ hθ hx (totalLength_nonneg ps hps')
    have hlast := pieceVariance_nonneg θ p.1 _ p.2 hθ hm hp.2
    have he : 0 < Real.exp (-θ*p.2)^2 := by positivity
    have heq : (0 < θ ∨ 0 < lflow θ x (totalLength ps)) ↔ (0 < θ ∨ 0 < x) := by
      by_cases hz : θ = 0
      · simp [hz, lflow]
      · have hpθ : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
        simp [hpθ]
    have hsum : 0 < Real.exp (-θ*p.2)^2 * varianceFlow θ x ps +
        pieceVariance θ p.1 (lflow θ x (totalLength ps)) p.2 ↔
        0 < Real.exp (-θ*p.2)^2 * varianceFlow θ x ps ∨
        0 < pieceVariance θ p.1 (lflow θ x (totalLength ps)) p.2 := by
      have hb := mul_nonneg he.le hv
      constructor
      · intro h; by_cases h1 : 0 < Real.exp (-θ*p.2)^2 * varianceFlow θ x ps
        · exact Or.inl h1
        · exact Or.inr (by linarith)
      · rintro (h | h) <;> linarith
    rw [varianceFlow, hsum,
      mul_pos_iff_of_pos_left he, ih hps', pieceVariance_pos_iff θ p.1 _ p.2 hθ hp.1 hm hp.2,
      heq]
    constructor
    · rintro (⟨⟨q, hq, hqp⟩, hx'⟩ | ⟨hα, hh, hx'⟩)
      · exact ⟨⟨q, List.mem_cons_of_mem p hq, hqp⟩, hx'⟩
      · exact ⟨⟨p, by simp, hα, hh⟩, hx'⟩
    · rintro ⟨⟨q, hq, hqp⟩, hx'⟩
      rcases List.mem_cons.1 hq with hq | hq
      · subst q; exact Or.inr ⟨hqp.1, hqp.2, hx'⟩
      · exact Or.inl ⟨⟨q, hq, hqp⟩, hx'⟩

lemma continuous_varianceFlow (θ : ℝ) (ps : List (ℝ × ℝ)) :
    Continuous (fun x => varianceFlow θ x ps) := by
  induction ps with
  | nil => exact continuous_const
  | cons p ps ih =>
    simp only [varianceFlow, pieceVariance, lflow]
    fun_prop

lemma conditional_piecewise_variance {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (hY2 : ∀ j, MemLp (fun ω => (Y ω j : ℝ)) 2 μ)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hx : Measurable[G] x) (hθ : ∀ j, 0 ≤ θ j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (htr : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j))))) :
    ∀ j, ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ =ᵐ[μ]
      fun ω => varianceFlow (θ j) (x ω j) (ps j) := by
  have hYi : ∀ j, Integrable (fun ω => (Y ω j : ℝ)) μ :=
    fun j => (hY2 j).integrable one_le_two
  obtain ⟨κ, hκ, hm, hl, hind, ht⟩ :=
    conditionalLaw d Ω G mΩ μ inferInstance hG Y hY θ ps x hθ hps htr
  let := hκ
  have hl0 := hl univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hl0
  have hkmean := conditional_kernel_mean μ κ Y hY hl0 hYi θ ps x hθ hps ht
  have hk2 : ∀ᵐ ω ∂μ, ∀ j, MemLp (fun y : Fin d → ℝ≥0 => (y j : ℝ)) 2 (κ ω) := by
    apply ae_all_iff.2
    intro j
    have hs : Integrable (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) (κ ∘ₘ μ) := by
      rw [← hl0]
      exact (integrable_map_measure
        (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) by fun_prop).aestronglyMeasurable
        hY.aemeasurable).2 (hY2 j).integrable_sq
    filter_upwards [Measure.ae_integrable_of_integrable_comp hs] with ω hω
    exact (memLp_two_iff_integrable_sq
      (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)) by fun_prop).aestronglyMeasurable).2 hω
  have hsquare : ∀ᵐ ω ∂μ, ∀ j, (∫ y : Fin d → ℝ≥0, (y j : ℝ)^2 ∂κ ω) =
      varianceFlow (θ j) (x ω j) (ps j) + (lflow (θ j) (x ω j) (totalLength (ps j)))^2 := by
    filter_upwards [ht, hkmean, hk2] with ω htω hmω h2ω
    intro j
    have hv := piecewise_variance (κ ω) (fun y => (y j : ℝ)) (by fun_prop)
      (ae_of_all _ fun y => (y j).coe_nonneg) (h2ω j) (θ j) (x ω j) (ps j)
      (hθ j) (hps j) (htω j)
    rw [ProbabilityTheory.variance_eq_sub (h2ω j), hmω j] at hv
    exact eq_add_of_sub_eq hv
  intro j
  have hsqCE : μ[fun ω => (Y ω j : ℝ)^2 | G] =ᵐ[μ]
      fun ω => varianceFlow (θ j) (x ω j) (ps j) + (lflow (θ j) (x ω j) (totalLength (ps j)))^2 := by
    refine conditional_kernel_integral_ae G μ hG κ Y hY hl (fun y => (y j : ℝ)^2)
      (by fun_prop) (hY2 j).integrable_sq _ ?_ ?_
    · let : MeasurableSpace Ω := G
      have hxj := (measurable_pi_apply j).comp hx
      have hv := (continuous_varianceFlow (θ j) (ps j)).measurable.comp hxj
      exact hv.add (by unfold lflow; fun_prop)
    · filter_upwards [hsquare] with ω hω
      exact hω j
  have hmeanCE := conditional_mean G μ hG Y hY hYi θ ps x hx hθ hps htr j
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp hG (hY2 j)
  filter_upwards [hv, hsqCE, hmeanCE] with ω hvω hsω hmω
  simp only [Pi.sub_apply, Pi.pow_apply] at hvω
  change ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ ω =
    μ[fun ω => (Y ω j : ℝ)^2 | G] ω - (μ[fun ω => (Y ω j : ℝ) | G] ω)^2 at hvω
  rw [hvω, hsω, hmω]
  ring

lemma covariance_active {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (q : Fin d → ℝ) (hq : ∀ j, 0 ≤ q j) (J : Finset (Fin d))
    (hJ : ∀ j, 0 < q j ↔ j ∈ J) :
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank := by
  classical
  let q' : Fin d → ℝ := fun j => if j ∈ J then q j else 1
  have hq' (j) : 0 < q' j := by
    by_cases hj : j ∈ J
    · simpa [q', hj] using (hJ j).2 hj
    · simp [q', hj]
  have he : Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 (activeCols A J) q' := by
    ext i k
    simp only [Standalone.ZeroMeanReversionVarianceSupport.cov0157]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simp [activeCols, q', hj]
    · have hz : q j = 0 := le_antisymm (le_of_not_gt fun h => hj ((hJ j).1 h)) (hq j)
      simp [activeCols, q', hj, hz]
  rw [he]
  exact ⟨Novel.ZeroMeanReversionVarianceSupportProof.covariance_kernel _ q' hq',
    Novel.ZeroMeanReversionVarianceSupportProof.covariance_rank _ q' hq'⟩

lemma piecewise_covariance_rank {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (hθ : ∀ j, 0 ≤ θ j)
    (hx : ∀ j, 0 ≤ x j) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) :
    let q := fun j => varianceFlow (θ j) (x j) (ps j)
    let J := Finset.univ.filter fun j =>
      (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank := by
  apply covariance_active A _ (fun j => varianceFlow_nonneg _ _ _ (hθ j) (hx j) (hps j))
  intro j
  simpa using varianceFlow_pos_iff (θ j) (x j) (ps j) (hθ j) (hx j) (hps j)

lemma piecewise_covariance {m d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Fin d → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 μ)
    (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ))
    (hθ : ∀ j, 0 ≤ θ j) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (ht : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
        Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x j + rhoFlow (θ j) (ps j) (l j)))))
    (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ) :
    ∀ i k, ProbabilityTheory.covariance (fun ω => C i + A.mulVec (Y ω) i)
      (fun ω => C k + A.mulVec (Y ω) k) μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A
        (fun j => varianceFlow (θ j) (x j) (ps j)) i k := by
  obtain ⟨hind, htr⟩ := independence d Ω mΩ μ inferInstance Y hY hY0 θ ps x ht
  apply Novel.ZeroMeanReversionVarianceSupportProof.covariance_image A μ C _ _ hY2 hind
  intro j
  exact piecewise_variance μ _ ((measurable_pi_apply j).comp hY)
    (by filter_upwards [hY0] with ω hω; exact hω j) (hY2 j) (θ j) (x j) (ps j) (hθ j) (hps j) (htr j)

lemma conditional_piecewise_covariance {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (hY2 : ∀ j, MemLp (fun ω => (Y ω j : ℝ)) 2 μ)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hx0 : ∀ ω j, 0 ≤ x ω j) (hθ : ∀ j, 0 ≤ θ j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (htr : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j))))) :
    ∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
      ∀ᵐ ω ∂μ, ∀ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ),
        let q := fun j => varianceFlow (θ j) (x ω j) (ps j)
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x ω j)
        (∀ i k, ProbabilityTheory.covariance
          (fun y : Fin d → ℝ≥0 => C i + A.mulVec (fun j => (y j : ℝ)) i)
          (fun y : Fin d → ℝ≥0 => C k + A.mulVec (fun j => (y j : ℝ)) k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank := by
  obtain ⟨κ, hκ, hm, hl, hind, ht⟩ :=
    conditionalLaw d Ω G mΩ μ inferInstance hG Y hY θ ps x hθ hps htr
  let := hκ
  have hl0 := hl univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hl0
  have hk2 : ∀ᵐ ω ∂μ, ∀ j, MemLp (fun y : Fin d → ℝ≥0 => (y j : ℝ)) 2 (κ ω) := by
    apply ae_all_iff.2
    intro j
    have hs : Integrable (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) (κ ∘ₘ μ) := by
      rw [← hl0]
      exact (integrable_map_measure
        (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)^2) by fun_prop).aestronglyMeasurable
        hY.aemeasurable).2 (hY2 j).integrable_sq
    filter_upwards [Measure.ae_integrable_of_integrable_comp hs] with ω hω
    exact (memLp_two_iff_integrable_sq
      (show Continuous (fun y : Fin d → ℝ≥0 => (y j : ℝ)) by fun_prop).aestronglyMeasurable).2 hω
  refine ⟨κ, hκ, hm, hl, ?_⟩
  filter_upwards [ht, hk2] with ω htω h2ω
  intro m A C
  refine ⟨?_, piecewise_covariance_rank A θ (x ω) ps hθ (hx0 ω) hps⟩
  apply Novel.ZeroMeanReversionVarianceSupportProof.covariance_image A (κ ω) C _ _ (h2ω)
    ((hind ω).comp (fun _ => fun y : ℝ≥0 => (y : ℝ)) (fun _ => NNReal.continuous_coe.measurable))
  intro j
  exact piecewise_variance (κ ω) _ (by fun_prop)
    (ae_of_all _ fun y => (y j).coe_nonneg) (h2ω j) (θ j) (x ω j) (ps j) (hθ j) (hps j) (htω j)

lemma piecewiseVariance : piecewiseVarianceStatement := by
  intro Ω mΩ μ hμ Y hY hY0 hY2 θ x ps hθ hx hps ht
  have hv := piecewise_variance μ Y hY hY0 hY2 θ x ps hθ hps ht
  exact ⟨hv, hv.symm ▸ varianceFlow_pos_iff θ x ps hθ hx hps⟩

lemma conditionalPiecewiseVariance : conditionalPiecewiseVarianceStatement := by
  intro d Ω G mΩ μ hμ hG Y hY hY2 θ ps x hx hx0 hθ hps ht j
  have hv := conditional_piecewise_variance G μ hG Y hY hY2 θ ps x hx hθ hps ht j
  refine ⟨hv, ?_⟩
  filter_upwards [hv] with ω hω
  rw [hω]
  exact varianceFlow_pos_iff (θ j) (x ω j) (ps j) (hθ j) (hx0 ω j) (hps j)

lemma piecewiseCovariance : piecewiseCovarianceStatement := by
  intro m d Ω mΩ μ hμ Y hY hY0 hY2 θ x ps hθ hx hps ht A C
  exact ⟨piecewise_covariance μ Y hY hY0 hY2 θ x ps hθ hps ht A C,
    piecewise_covariance_rank A θ x ps hθ hx hps⟩

lemma conditionalPiecewiseCovariance : conditionalPiecewiseCovarianceStatement := by
  intro d Ω G mΩ μ hμ hG Y hY hY2 θ ps x hx0 hθ hps ht
  exact conditional_piecewise_covariance G μ hG Y hY hY2 θ ps x hx0 hθ hps ht

lemma source_covariance {m : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Fin 3 → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 μ)
    (ps : Fin 3 → List (ℝ × ℝ)) (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hlast : ∀ j, ∃ α h qs, ps j = (α,h)::qs ∧ 0 < α ∧ 0 < h)
    (ht : ∀ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
        Real.exp (-(∑ j, (piFlow (θ0235 j) (ps j) (l j) + rhoFlow (θ0235 j) (ps j) (l j)))))
    (A : Matrix (Fin m) (Fin 3) ℝ) (C : Fin m → ℝ) :
    let q := fun j => varianceFlow (θ0235 j) 1 (ps j)
    (∀ j, 0 < q j) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => C i + A.mulVec (Y ω) i)
      (fun ω => C k + A.mulVec (Y ω) k) μ = Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin = LinearMap.ker A.transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
    m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin) := by
  have hθ (j : Fin 3) : 0 ≤ θ0235 j := by fin_cases j <;> norm_num [θ0235]
  have hq (j : Fin 3) : 0 < varianceFlow (θ0235 j) 1 (ps j) := by
    apply (varianceFlow_pos_iff _ _ _ (hθ j) zero_le_one (hps j)).2
    obtain ⟨α, h, qs, he, hα, hh⟩ := hlast j
    exact ⟨⟨(α,h), by simp [he], hα, hh⟩, Or.inr zero_lt_one⟩
  refine ⟨hq, ?_, Novel.ZeroMeanReversionVarianceSupportProof.covariance_kernel A _ hq, Novel.ZeroMeanReversionVarianceSupportProof.covariance_rank A _ hq,
    A.rank_le_width, Novel.ZeroMeanReversionVarianceSupportProof.nullity A⟩
  apply piecewise_covariance μ Y hY hY0 hY2 θ0235 (fun _ => 1) ps hθ hps ?_ A C
  simpa using ht

lemma sourceCovariance : sourceCovarianceStatement := by
  intro m Ω mΩ μ hμ Y hY hY0 hY2 ps hps hlast ht A C
  exact source_covariance μ Y hY hY0 hY2 ps hps hlast ht A C

end PiecewiseVariance

/-! ### The coordinate laws and their exact supports -/

section CoordinateLaws
open ProbabilityTheory
open scoped NNReal ENNReal Topology

lemma gamma_nonneg (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  change ∀ᵐ x ∂volume.withDensity (gammaPDF a r), 0 ≤ x
  rw [ae_iff]
  simp only [not_le]
  change (volume.withDensity (gammaPDF a r)) (Iio 0) = 0
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma gamma_no_atoms (a r x : ℝ) : gammaMeasure a r {x} = 0 := by
  change (volume.withDensity (gammaPDF a r)) {x} = 0
  exact measure_singleton x

lemma gamma_support (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (gammaMeasure a r).support = Ici 0 := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (gamma_nonneg a r)
  · have h : Ioi (0 : ℝ) ⊆ (gammaMeasure a r).support := by
      intro x hx
      rw [Measure.support_eq_forall_isOpen]
      intro U hxU hU
      change 0 < (volume.withDensity (gammaPDF a r)) U
      rw [withDensity_apply _ hU.measurableSet, setLIntegral_pos_iff (by unfold gammaPDF; fun_prop)]
      have he : Ioi (0:ℝ) ⊆ Function.support (gammaPDF a r) := by
        intro y hy
        change ENNReal.ofReal (gammaPDFReal a r y) ≠ 0
        exact ne_of_gt (ENNReal.ofReal_pos.2 (gammaPDFReal_pos ha hr hy))
      have hp : 0 < volume (Ioi (0:ℝ) ∩ U) :=
        (isOpen_Ioi.inter hU).measure_pos volume ⟨x, hx, hxU⟩
      exact hp.trans_le (measure_mono (inter_subset_inter_left _ he))
    have hh := closure_minimal h (gammaMeasure a r).isClosed_support
    simpa only [closure_Ioi] using hh

lemma gamma_laplace (a r l : ℝ) (ha : 0 < a) (hr : 0 < r) (hl : 0 ≤ l) :
    (∫ x, Real.exp (-(l*x)) ∂gammaMeasure a r) = (r / (r+l)) ^ a := by
  have hr' : 0 < r+l := by linarith
  change (∫ x, Real.exp (-(l*x)) ∂volume.withDensity (gammaPDF a r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF a r) (by unfold gammaPDF; fun_prop)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have he (x : ℝ) : (gammaPDF a r x).toReal • Real.exp (-(l*x)) =
      (Ici 0).indicator (fun x => (r^a / Real.Gamma a) * (x^(a-1) * Real.exp (-((r+l)*x)))) x := by
    by_cases hx : 0 ≤ x
    · rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
      simp only [gammaPDFReal, ite_eq_left hx, smul_eq_mul, indicator_of_mem (show x ∈ Ici (0:ℝ) from hx),
        mul_assoc, ← Real.exp_add]
      congr 3
      ring
    · simp [gammaPDF_of_neg (lt_of_not_ge hx), indicator_of_notMem (show x ∉ Ici (0:ℝ) from hx)]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, integral_const_mul, integral_Ici_eq_integral_Ioi,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr']
  have hG := (Real.Gamma_pos_of_pos ha).ne'
  rw [Real.div_rpow hr.le hr'.le]
  rw [Real.div_rpow zero_le_one hr'.le, Real.one_rpow]
  field_simp

lemma gamma_mixture_markov (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : IsMarkovKernel (G023 a r) := by
  constructor
  intro n
  exact isProbabilityMeasure_gammaMeasure (by positivity) hr

lemma gamma_mixture_probability (a r : ℝ) (z : ℝ≥0) (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (P023 a r z) := by
  have := gamma_mixture_markov a r ha hr
  dsimp [P023]
  infer_instance

lemma gamma_mixture_nonneg (a r : ℝ) (z : ℝ≥0) (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂P023 a r z, 0 ≤ x := by
  have := gamma_mixture_markov a r ha hr
  exact Measure.ae_comp_of_ae_ae measurableSet_Ici (ae_of_all _ fun n => gamma_nonneg (a+n) r)

lemma gamma_mixture_no_atoms (a r : ℝ) (z : ℝ≥0) (x : ℝ) : P023 a r z {x} = 0 := by
  rw [P023, Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_eq_zero]
  intro n
  change _ * gammaMeasure (a+n) r {x} = 0
  rw [gamma_no_atoms, mul_zero]

lemma gamma_mixture_laplace (a r : ℝ) (z : ℝ≥0) (ha : 0 < a) (hr : 0 < r)
    (l : ℝ) (hl : 0 ≤ l) :
    (∫ x, Real.exp (-(l*x)) ∂P023 a r z) =
      (r/(r+l))^a * Real.exp ((z:ℝ)*(r/(r+l)-1)) := by
  have := gamma_mixture_markov a r ha hr
  have := gamma_mixture_probability a r z ha hr
  have hi : Integrable (fun x : ℝ => Real.exp (-(l*x))) (P023 a r z) := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
    filter_upwards [gamma_mixture_nonneg a r z ha hr] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  unfold P023 at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ n, ∫ x, Real.exp (-(l*x)) ∂G023 a r n ∂poissonMeasure z) = _
  have hq : 0 < r/(r+l) := by positivity
  have he (n : ℕ) : (∫ x, Real.exp (-(l*x)) ∂G023 a r n) = (r/(r+l))^a * (r/(r+l))^n := by
    rw [show G023 a r n = gammaMeasure (a+n) r from rfl, gamma_laplace _ _ _ (by positivity) hr hl,
      Real.rpow_add hq, Real.rpow_natCast]
  simp_rw [he]
  rw [integral_const_mul, poisson_power_integral]

lemma gamma_mixture_support (a r : ℝ) (z : ℝ≥0) (ha : 0 < a) (hr : 0 < r) :
    (P023 a r z).support = Ici 0 := by
  have := gamma_mixture_markov a r ha hr
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (gamma_mixture_nonneg a r z ha hr)
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    have hp : 0 < G023 a r 0 U := by
      apply (Measure.mem_support_iff_forall x).1 ?_ U (hU.mem_nhds hxU)
      change x ∈ (gammaMeasure (a+(0:ℕ)) r).support
      simp only [Nat.cast_zero, add_zero, gamma_support a r ha hr]
      exact hx
    have hz : 0 < poissonMeasure z {0} := by
      rw [poissonMeasure_singleton, ENNReal.ofReal_pos]
      positivity
    have hle : poissonMeasure z {0} • G023 a r 0 ≤ P023 a r z := by
      rw [P023, Measure.comp_eq_sum_of_countable]
      exact Measure.le_sum (fun n : ℕ => poissonMeasure z {n} • G023 a r n) 0
    have hpos : 0 < poissonMeasure z {0} * G023 a r 0 U := by positivity
    exact hpos.trans_le (hle U)

noncomputable def K023 (a r : ℝ) : Kernel ℝ≥0 ℝ := G023 a r ∘ₖ L01513

lemma gamma_mixture_measurable (a r : ℝ) : Measurable (P023 a r) :=
  (K023 a r).measurable

lemma positive_transition_parameters (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    0 < chiScale θ α h ∧ 0 < chiDof θ α / 2 ∧ 0 < chiRate θ α h := by
  obtain ⟨hc, hd, hr, _⟩ := chiSquareParameter θ α h 0 0 hθ hα hh le_rfl
  exact ⟨hc, by positivity, hr⟩

lemma positive_transition_probability (θ α h x : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    IsProbabilityMeasure (T023 θ α h x) := by
  obtain ⟨hc, hd, hr⟩ := positive_transition_parameters θ α h hθ hα hh
  exact gamma_mixture_probability _ _ _ hd (by positivity)

lemma positive_transition_measurable (θ α h : ℝ) : Measurable (T023 θ α h) := by
  exact (gamma_mixture_measurable _ _).comp (by fun_prop)

lemma positive_transition_nonneg (θ α h x : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    ∀ᵐ y ∂T023 θ α h x, 0 ≤ y := by
  obtain ⟨hc, hd, hr⟩ := positive_transition_parameters θ α h hθ hα hh
  exact gamma_mixture_nonneg _ _ _ hd (by positivity)

lemma positive_transition_support (θ α h x : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    (T023 θ α h x).support = Ici 0 := by
  obtain ⟨hc, hd, hr⟩ := positive_transition_parameters θ α h hθ hα hh
  exact gamma_mixture_support _ _ _ hd (by positivity)

lemma positive_transition_no_atoms (θ α h x y : ℝ) : T023 θ α h x {y} = 0 :=
  gamma_mixture_no_atoms _ _ _ y

lemma positive_transition_laplace (θ α h x l : ℝ) (hθ : 0 < θ) (hα : 0 < α)
    (hh : 0 < h) (hx : 0 ≤ x) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-(l*y)) ∂T023 θ α h x) =
      Real.exp (-(Qflow θ α l h*x + Rflow θ α l h)) := by
  obtain ⟨hc, hd, hr, hcr, hR, hQ, htr⟩ := chiSquareParameter θ α h l x hθ hα hh hl
  have hD : 0 < 1+2*chiScale θ α h*l := by positivity
  unfold T023
  rw [gamma_mixture_laplace _ _ _ (by positivity) (by positivity) l hl,
    Real.coe_toNNReal _ (by positivity), htr]
  have he : (2*chiScale θ α h)⁻¹ / ((2*chiScale θ α h)⁻¹+l) = (1+2*chiScale θ α h*l)⁻¹ := by
    field_simp
  rw [he, Real.inv_rpow (le_of_lt hD), ← Real.rpow_neg (le_of_lt hD)]
  congr 2
  field_simp
  ring

lemma positive_law_of_transform (θ α h x : ℝ) (hθ : 0 < θ) (hα : 0 < α)
    (hh : 0 < h) (hx : 0 ≤ x) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    (ht : ∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂μ) =
      Real.exp (-(Qflow θ α l h*x + Rflow θ α l h))) : μ = T023 θ α h x := by
  have := positive_transition_probability θ α h x hθ hα hh
  apply scalar_laplace_unique μ (T023 θ α h x) hμ (positive_transition_nonneg θ α h x hθ hα hh)
  intro l hl
  simpa only [neg_mul] using (ht l hl).trans (positive_transition_laplace θ α h x l hθ hα hh hx hl).symm

noncomputable def κ023 (θ α h : ℝ) : Kernel ℝ ℝ where
  toFun := T023 θ α h
  measurable' := positive_transition_measurable θ α h

lemma positive_kernel_markov (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h) :
    IsMarkovKernel (κ023 θ α h) := ⟨fun x => positive_transition_probability θ α h x hθ hα hh⟩

lemma positive_mixture_nonneg (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h)
    (μ : Measure ℝ) : ∀ᵐ y ∂(κ023 θ α h ∘ₘ μ), 0 ≤ y :=
  Measure.ae_comp_of_ae_ae measurableSet_Ici
    (ae_of_all _ fun x => positive_transition_nonneg θ α h x hθ hα hh)

lemma positive_mixture_no_atoms (θ α h : ℝ) (μ : Measure ℝ) (y : ℝ) :
    (κ023 θ α h ∘ₘ μ) {y} = 0 := by
  rw [Measure.bind_apply (measurableSet_singleton _) (κ023 θ α h).aemeasurable]
  have hz (x : ℝ) : κ023 θ α h x {y} = 0 := positive_transition_no_atoms θ α h x y
  simp only [hz, lintegral_zero]

lemma positive_mixture_support (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : (κ023 θ α h ∘ₘ μ).support = Ici 0 := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (positive_mixture_nonneg θ α h hθ hα hh μ)
  · intro y hy
    rw [Measure.support_eq_forall_isOpen]
    intro U hyU hU
    rw [Measure.bind_apply hU.measurableSet (κ023 θ α h).aemeasurable,
      lintegral_pos_iff_support ((κ023 θ α h).measurable_coe hU.measurableSet)]
    have hs : Function.support (fun x => κ023 θ α h x U) = univ := by
      apply eq_univ_of_forall
      intro x
      apply ne_of_gt
      apply (Measure.mem_support_iff_forall y).1 ?_ U (hU.mem_nhds hyU)
      change y ∈ (T023 θ α h x).support
      rw [positive_transition_support θ α h x hθ hα hh]
      exact hy
    simp [hs]

lemma positive_mixture_laplace (θ α h : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (l : ℝ) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-(l*y)) ∂(κ023 θ α h ∘ₘ μ)) =
      Real.exp (-Rflow θ α l h) * (∫ x, Real.exp (-(Qflow θ α l h*x)) ∂μ) := by
  have := positive_kernel_markov θ α h hθ hα hh
  have hi : Integrable (fun y : ℝ => Real.exp (-(l*y))) (κ023 θ α h ∘ₘ μ) := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
    filter_upwards [positive_mixture_nonneg θ α h hθ hα hh μ] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  change (∫ y, Real.exp (-(l*y)) ∂T023 θ α h x) = _
  rw [positive_transition_laplace θ α h x l hθ hα hh hx hl, ← Real.exp_add]
  congr 1
  ring

lemma positive_last_law (θ α h x : ℝ) (ps : List (ℝ × ℝ))
    (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ y ∂μ, 0 ≤ y) (hν : ∀ᵐ y ∂ν, 0 ≤ y)
    (htμ : ∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂μ) =
      Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l)))
    (htν : ∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂ν) =
      Real.exp (-(piFlow θ ((α,h)::ps) l*x + rhoFlow θ ((α,h)::ps) l))) :
    ν = κ023 θ α h ∘ₘ μ := by
  have := positive_kernel_markov θ α h hθ hα hh
  apply scalar_laplace_unique ν _ hν (positive_mixture_nonneg θ α h hθ hα hh μ)
  intro l hl
  simp only [neg_mul]
  rw [htν l hl, positive_mixture_laplace θ α h hθ hα hh μ hμ l hl,
    htμ _ (Qflow_nonneg θ α l h hθ.le hl hh.le), ← Real.exp_add]
  congr 1
  simp only [piFlow, rhoFlow]
  ring

noncomputable def κ023Piece (θ α h : ℝ) : Kernel ℝ ℝ :=
  if θ = 0 then
    ⟨fun x => Standalone.ZeroMeanReversionVarianceSupport.T01513 (α^2*h/2) x.toNNReal,
      (scalar_measurable _).comp (by fun_prop)⟩
  else if α = 0 ∨ h = 0 then
    ⟨fun x => Measure.dirac (lflow θ x h), by unfold lflow; fun_prop⟩
  else κ023 θ α h

lemma piece_kernel_markov (θ α h : ℝ) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hh : 0 ≤ h) :
    IsMarkovKernel (κ023Piece θ α h) := by
  unfold κ023Piece
  split_ifs with hz hn
  · constructor; intro x; exact scalar_probability _ (by positivity) _
  · constructor; intro x; exact Measure.dirac.isProbabilityMeasure
  · exact positive_kernel_markov θ α h (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_le_of_ne hα (Ne.symm (not_or.mp hn).1)) (lt_of_le_of_ne hh (Ne.symm (not_or.mp hn).2))

lemma piece_kernel_nonneg (θ α h x : ℝ) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ∀ᵐ y ∂κ023Piece θ α h x, 0 ≤ y := by
  unfold κ023Piece
  split_ifs with hz hn
  · exact scalar_nonneg _ (by positivity) _
  · simpa using lflow_nonneg θ x h hθ hx hh
  · exact positive_transition_nonneg θ α h x (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_le_of_ne hα (Ne.symm (not_or.mp hn).1)) (lt_of_le_of_ne hh (Ne.symm (not_or.mp hn).2))

lemma piece_kernel_laplace (θ α h x l : ℝ) (hθ : 0 ≤ θ) (hα : 0 ≤ α)
    (hh : 0 ≤ h) (hx : 0 ≤ x) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-(l*y)) ∂κ023Piece θ α h x) =
      Real.exp (-(Qflow θ α l h*x + Rflow θ α l h)) := by
  by_cases hz : θ = 0
  · subst θ
    simp only [κ023Piece, ite_true, Kernel.coe_mk]
    change (∫ y, Real.exp (-(l*y)) ∂Standalone.ZeroMeanReversionVarianceSupport.T01513
      (α^2*h/2) x.toNNReal) = _
    rw [show (fun y : ℝ => Real.exp (-(l*y))) = (fun y => Real.exp (-l*y)) by
      funext y; rw [neg_mul], scalar_transform _ (by positivity) _ l hl,
      Real.coe_toNNReal _ hx]
    congr 1
    simp only [Qflow, Rflow, ite_true]
    ring_nf
  by_cases hn : α = 0 ∨ h = 0
  · simp only [κ023Piece, hz, ite_false, hn, ite_true, Kernel.coe_mk, integral_dirac]
    congr 1
    rcases hn with hα0 | hh0
    · rw [hα0, noise_free_exponent]
    · simp [hh0, lflow, Qflow_len_zero, Rflow_len_zero]
  · simp only [κ023Piece, hz, hn, ite_false]
    exact positive_transition_laplace θ α h x l (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_le_of_ne hα (Ne.symm (not_or.mp hn).1)) (lt_of_le_of_ne hh (Ne.symm (not_or.mp hn).2)) hx hl

lemma piece_kernel_coe (θ α h : ℝ) : (κ023Piece θ α h : ℝ → Measure ℝ) = T023Piece θ α h := by
  unfold κ023Piece T023Piece
  split_ifs <;> rfl

lemma L023_cons (θ x : ℝ) (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    L023 θ (p::ps) x = κ023Piece θ p.1 p.2 ∘ₘ L023 θ ps x := by
  change (L023 θ ps x).bind _ = (L023 θ ps x).bind _
  rw [piece_kernel_coe]

lemma pieces_probability (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) (x : ℝ) : IsProbabilityMeasure (L023 θ ps x) := by
  induction ps with
  | nil => dsimp [L023]; infer_instance
  | cons p ps ih =>
    have hp := hps p (by simp)
    have := ih (fun q hq => hps q (by simp [hq]))
    have := piece_kernel_markov θ p.1 p.2 hθ hp.1 hp.2
    rw [L023_cons]
    infer_instance

lemma pieces_nonneg (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) (x : ℝ) (hx : 0 ≤ x) :
    ∀ᵐ y ∂L023 θ ps x, 0 ≤ y := by
  induction ps with
  | nil => simpa [L023] using hx
  | cons p ps ih =>
    have hp := hps p (by simp)
    rw [L023_cons]
    apply Measure.ae_comp_of_ae_ae measurableSet_Ici
    filter_upwards [ih (fun q hq => hps q (by simp [hq]))] with y hy
    exact piece_kernel_nonneg θ p.1 p.2 y hθ hp.1 hp.2 hy

lemma pieces_laplace (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) (x : ℝ) (hx : 0 ≤ x) (l : ℝ) (hl : 0 ≤ l) :
    (∫ y, Real.exp (-(l*y)) ∂L023 θ ps x) = Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l)) := by
  induction ps generalizing l with
  | nil => simp [L023, piFlow, rhoFlow, integral_dirac]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    have := pieces_probability θ ps hθ hps' x
    have := piece_kernel_markov θ p.1 p.2 hθ hp.1 hp.2
    have := pieces_probability θ (p::ps) hθ hps x
    have hi : Integrable (fun y : ℝ => Real.exp (-(l*y))) (L023 θ (p::ps) x) := by
      refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
      filter_upwards [pieces_nonneg θ (p::ps) hθ hps x hx] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    simp only [L023_cons, Measure.comp_eq_comp_const_apply] at hi ⊢
    rw [Kernel.integral_comp hi]
    change (∫ y, ∫ z, Real.exp (-(l*z)) ∂κ023Piece θ p.1 p.2 y ∂L023 θ ps x) = _
    have he : (∫ y, ∫ z, Real.exp (-(l*z)) ∂κ023Piece θ p.1 p.2 y ∂L023 θ ps x) =
        ∫ y, Real.exp (-Rflow θ p.1 l p.2) * Real.exp (-(Qflow θ p.1 l p.2*y)) ∂L023 θ ps x := by
      apply integral_congr_ae
      filter_upwards [pieces_nonneg θ ps hθ hps' x hx] with y hy
      rw [piece_kernel_laplace θ p.1 p.2 y l hθ hp.1 hp.2 hy hl, ← Real.exp_add]
      congr 1; ring
    rw [he, integral_const_mul, ih hps' _ (Qflow_nonneg θ p.1 l p.2 hθ hl hp.2), ← Real.exp_add]
    congr 1
    simp only [piFlow, rhoFlow]
    ring

lemma pieces_measurable (θ : ℝ) (ps : List (ℝ × ℝ)) : Measurable (L023 θ ps) := by
  induction ps with
  | nil => exact Measure.measurable_dirac
  | cons p ps ih =>
    have hm : Measurable (T023Piece θ p.1 p.2) := by
      rw [← piece_kernel_coe]; exact (κ023Piece θ p.1 p.2).measurable
    exact (Measure.measurable_bind' hm).comp ih

lemma pieces_law_of_transform (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) (x : ℝ) (hx : 0 ≤ x)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    (ht : ∀ l : ℝ, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂μ) =
      Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l))) : μ = L023 θ ps x := by
  have := pieces_probability θ ps hθ hps x
  apply scalar_laplace_unique μ _ hμ (pieces_nonneg θ ps hθ hps x hx)
  intro l hl
  simpa only [neg_mul] using (ht l hl).trans (pieces_laplace θ ps hθ hps x hx l hl).symm

lemma pieces_positive_last_support (θ α h x : ℝ) (ps : List (ℝ × ℝ))
    (hθ : 0 < θ) (hα : 0 < α) (hh : 0 < h)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (L023 θ ((α,h)::ps) x).support = Ici 0 ∧
    ∀ y, L023 θ ((α,h)::ps) x {y} = 0 := by
  have := pieces_probability θ ps hθ.le hps x
  simp only [L023_cons, κ023Piece, hθ.ne', hα.ne', hh.ne', or_self, ite_false]
  exact ⟨positive_mixture_support θ α h hθ hα hh _, fun y => positive_mixture_no_atoms θ α h _ y⟩

lemma deterministic_piece (θ α h : ℝ) (hθ : 0 < θ) (hz : α = 0 ∨ h = 0) (μ : Measure ℝ) :
    κ023Piece θ α h ∘ₘ μ = μ.map (fun x => lflow θ x h) := by
  simp only [κ023Piece, hθ.ne', ite_false, hz, ite_true]
  exact Measure.bind_dirac_eq_map μ (by unfold lflow; fun_prop)

lemma lflow_map_support (θ h b : ℝ) (μ : Measure ℝ) (hs : μ.support = Ici b) :
    (μ.map (fun x => lflow θ x h)).support = Ici (lflow θ b h) := by
  have hf : Continuous (fun x => lflow θ x h) := by unfold lflow; fun_prop
  have he := Real.exp_pos (-θ*h)
  have hm (x y : ℝ) : lflow θ x h ≤ lflow θ y h ↔ x ≤ y := by
    unfold lflow
    constructor <;> intro hxy <;> nlinarith
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Ici
    apply (ae_map_iff hf.measurable.aemeasurable measurableSet_Ici).2
    filter_upwards [μ.support_mem_ae] with x hx
    rw [hs] at hx
    exact (hm b x).2 hx
  · intro y hy
    let x := 1+(y-1)/Real.exp (-θ*h)
    have hxy : lflow θ x h = y := by dsimp [lflow, x]; field_simp; ring
    have hxb : b ≤ x := (hm b x).1 (by rwa [hxy])
    rw [Measure.support_eq_forall_isOpen]
    intro U hyU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    apply (Measure.mem_support_iff_forall x).1 ?_ ((fun z => lflow θ z h) ⁻¹' U) ?_
    · rw [hs]; exact hxb
    · exact (hU.preimage hf).mem_nhds (by simpa [hxy])

lemma lflow_map_no_atoms (θ h : ℝ) (μ : Measure ℝ) (hμ : ∀ x, μ {x} = 0) :
    ∀ y, (μ.map (fun x => lflow θ x h)) {y} = 0 := by
  intro y
  have hf : Measurable (fun x => lflow θ x h) := by unfold lflow; fun_prop
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  have he := Real.exp_pos (-θ*h)
  have hs : (fun x => lflow θ x h) ⁻¹' {y} ⊆ {1+(y-1)/Real.exp (-θ*h)} := by
    intro x hx
    change x = _
    change lflow θ x h = y at hx
    unfold lflow at hx
    have hh : (x-1)*Real.exp (-θ*h) = y-1 := by linarith
    have hh' := (eq_div_iff he.ne').2 hh
    linarith
  exact le_antisymm ((measure_mono hs).trans_eq (hμ _)) bot_le

lemma lflow_comp (θ x h t : ℝ) : lflow θ (lflow θ x t) h = lflow θ x (h+t) := by
  unfold lflow
  rw [show -θ*(h+t) = -θ*h + -θ*t by ring, Real.exp_add]
  ring

lemma pieces_deterministic (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 < θ)
    (hz : ∀ p ∈ ps, p.1 = 0 ∨ p.2 = 0) (x : ℝ) :
    L023 θ ps x = Measure.dirac (lflow θ x (totalLength ps)) := by
  induction ps with
  | nil => simp [L023, lflow, totalLength]
  | cons p ps ih =>
    rw [L023_cons, deterministic_piece θ p.1 p.2 hθ (hz p (by simp)),
      ih (fun q hq => hz q (by simp [hq])), Measure.map_dirac' (by unfold lflow; fun_prop),
      lflow_comp, totalLength_cons]

lemma pieces_positive_support (θ : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 < θ)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) (x : ℝ)
    (hJ : ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) :
    (L023 θ ps x).support = Ici (ell023 θ x ps) ∧ ∀ y, L023 θ ps x {y} = 0 := by
  induction ps with
  | nil => simp at hJ
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    by_cases hz : p.1 = 0 ∨ p.2 = 0
    · have hJ' : ∃ q ∈ ps, 0 < q.1 ∧ 0 < q.2 := by
        obtain ⟨q, hq, hq1, hq2⟩ := hJ
        rcases List.mem_cons.1 hq with hq | hq
        · subst q; rcases hz with hz | hz <;> simp [hz] at *
        · exact ⟨q, hq, hq1, hq2⟩
      obtain ⟨hs, ha⟩ := ih hps' hJ'
      simp only [L023_cons, deterministic_piece θ p.1 p.2 hθ hz, ell023, hz, ite_true]
      exact ⟨lflow_map_support θ p.2 _ _ hs, lflow_map_no_atoms θ p.2 _ ha⟩
    · have hp1 := lt_of_le_of_ne hp.1 (Ne.symm (not_or.mp hz).1)
      have hp2 := lt_of_le_of_ne hp.2 (Ne.symm (not_or.mp hz).2)
      simpa only [ell023, hz, ite_false] using
        pieces_positive_last_support θ p.1 p.2 x ps hθ hp1 hp2 hps'

lemma c023_nonneg (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) : 0 ≤ c023 ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih =>
    have hp := (hps p (by simp)).2
    have ht := ih (fun q hq => hps q (by simp [hq]))
    dsimp [c023]; positivity

lemma zero_flow (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (l : ℝ) (hl : 0 ≤ l) :
    piFlow 0 ps l = l/(1+c023 ps*l) ∧ rhoFlow 0 ps l = 0 := by
  induction ps generalizing l with
  | nil => simp [piFlow, rhoFlow, c023]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    have hc := c023_nonneg ps hps'
    have hQ := Qflow_nonneg 0 p.1 l p.2 le_rfl hl hp.2
    obtain ⟨hq, hr⟩ := ih hps' _ hQ
    simp only [piFlow, rhoFlow, hq, hr, Rflow, ite_true, add_zero]
    refine ⟨?_, trivial⟩
    have hph := hp.2
    have hrational (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
        (l/(1+c*l))/(1+d*(l/(1+c*l))) = l/(1+(c+d)*l) := by
      have h1 : 0 < 1+c*l := by positivity
      have h2 : 0 < 1+(c+d)*l := by positivity
      have h3 : 0 < 1+d*(l/(1+c*l)) := by positivity
      field_simp
      <;> ring
    simp only [Qflow, ite_true, c023]
    rw [show p.1^2*p.2*l/2 = (p.1^2*p.2/2)*l by ring]
    exact hrational _ _ (by positivity) hc

lemma zero_pieces_law (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (x : ℝ) (hx : 0 ≤ x) :
    L023 0 ps x = Standalone.ZeroMeanReversionVarianceSupport.T01513 (c023 ps) x.toNNReal := by
  have hc := c023_nonneg ps hps
  have := pieces_probability 0 ps le_rfl hps x
  have := scalar_probability (c023 ps) hc x.toNNReal
  apply scalar_laplace_unique _ _ (pieces_nonneg 0 ps le_rfl hps x hx) (scalar_nonneg _ hc _)
  intro l hl
  rw [scalar_transform _ hc _ l hl, Real.coe_toNNReal _ hx]
  have ht := pieces_laplace 0 ps le_rfl hps x hx l hl
  rw [(zero_flow ps hps l hl).1, (zero_flow ps hps l hl).2] at ht
  simp only [neg_mul]
  rw [ht]
  congr 1
  ring

lemma c023_pos_iff (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    0 < c023 ps ↔ ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2 := by
  induction ps with
  | nil => simp [c023]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hp2 := hp.2
    have hps' : ∀ q ∈ ps, 0 ≤ q.1 ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    have hc := c023_nonneg ps hps'
    constructor
    · intro h
      by_cases ht : 0 < c023 ps
      · obtain ⟨q, hq, hq1, hq2⟩ := (ih hps').1 ht
        exact ⟨q, List.mem_cons_of_mem p hq, hq1, hq2⟩
      · have hp' : 0 < p.1^2*p.2/2 := by change 0 < _ + _ at h; linarith
        have h1 : 0 < p.1 := by
          by_contra hn
          have hz : p.1 = 0 := le_antisymm (le_of_not_gt hn) hp.1
          simp [hz] at hp'
        have h2 : 0 < p.2 := by nlinarith [sq_nonneg p.1]
        exact ⟨p, by simp, h1, h2⟩
    · rintro ⟨q, hq, hq1, hq2⟩
      rcases List.mem_cons.1 hq with he | hq
      · subst q
        have hp' : 0 < p.1^2*p.2/2 := by positivity
        change 0 < _ + _
        linarith
      · have ht := (ih hps').2 ⟨q, hq, hq1, hq2⟩
        change 0 < _ + _
        have hp' : 0 ≤ p.1^2*p.2/2 := by positivity
        linarith

lemma ell_deterministic (θ x : ℝ) (ps : List (ℝ × ℝ))
    (hz : ∀ p ∈ ps, p.1 = 0 ∨ p.2 = 0) : ell023 θ x ps = lflow θ x (totalLength ps) := by
  induction ps with
  | nil => simp [ell023, lflow, totalLength]
  | cons p ps ih =>
    simp only [ell023, hz p (by simp), ite_true,
      ih (fun q hq => hz q (by simp [hq])), lflow_comp, totalLength_cons]

lemma no_stochastic_iff (ps : List (ℝ × ℝ)) (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (¬ ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ↔ ∀ p ∈ ps, p.1 = 0 ∨ p.2 = 0 := by
  constructor
  · intro hn p hp
    have h := hps p hp
    by_cases h1 : p.1 = 0
    · exact Or.inl h1
    · have h1p := lt_of_le_of_ne h.1 (Ne.symm h1)
      exact Or.inr (le_antisymm (le_of_not_gt fun h2 => hn ⟨p,hp,h1p,h2⟩) h.2)
  · intro hz ⟨p,hp,hp1,hp2⟩
    rcases hz p hp with h | h <;> simp_all

lemma ell_zero_active (x : ℝ) (ps : List (ℝ × ℝ))
    (hJ : ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) : ell023 0 x ps = 0 := by
  induction ps with
  | nil => simp at hJ
  | cons p ps ih =>
    by_cases hz : p.1 = 0 ∨ p.2 = 0
    · have hJ' : ∃ q ∈ ps, 0 < q.1 ∧ 0 < q.2 := by
        obtain ⟨q, hq, hq1, hq2⟩ := hJ
        rcases List.mem_cons.1 hq with hq | hq
        · subst q; rcases hz with h | h <;> simp_all
        · exact ⟨q, hq, hq1, hq2⟩
      simp [ell023, hz, lflow, ih hJ']
    · simp [ell023, hz]

lemma ell_zero_zero (ps : List (ℝ × ℝ)) : ell023 0 0 ps = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ell023, ih, lflow]

lemma pieces_inactive (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hn : ¬ ((∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x))) :
    L023 θ ps x = Measure.dirac (ell023 θ x ps) := by
  by_cases hz : θ = 0
  · subst θ
    rw [zero_pieces_law ps hps x hx]
    by_cases hc : c023 ps = 0
    · have hn' : ¬ ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2 := by
        rw [← c023_pos_iff ps hps, hc]; simp
      rw [ell_deterministic 0 x ps ((no_stochastic_iff ps hps).1 hn')]
      simp [Standalone.ZeroMeanReversionVarianceSupport.T01513, hc, Real.coe_toNNReal x hx, lflow]
    · have hc' := lt_of_le_of_ne (c023_nonneg ps hps) (Ne.symm hc)
      have hx0 : x = 0 := by
        apply le_antisymm ?_ hx
        exact le_of_not_gt fun hxp => hn ⟨(c023_pos_iff ps hps).1 hc', Or.inr hxp⟩
      subst x
      simp [Standalone.ZeroMeanReversionVarianceSupport.T01513, hc, transition_zero _ hc', ell_zero_zero]
  · have hp := lt_of_le_of_ne hθ (Ne.symm hz)
    have hn' : ¬ ∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2 := fun h => hn ⟨h, Or.inl hp⟩
    have hdet := (no_stochastic_iff ps hps).1 hn'
    rw [pieces_deterministic θ ps hp hdet x, ell_deterministic θ x ps hdet]

lemma pieces_support (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (L023 θ ps x).support = if (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x)
      then Ici (ell023 θ x ps) else {ell023 θ x ps} := by
  classical
  split_ifs with hJ
  · by_cases hz : θ = 0
    · subst θ
      have hx' : 0 < x := hJ.2.resolve_left (by simp)
      have hc := (c023_pos_iff ps hps).2 hJ.1
      have hxnn : x.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.2 hx')
      rw [zero_pieces_law ps hps x hx, scalar_support _ (c023_nonneg ps hps) _,
        ell_zero_active x ps hJ.1]
      simp [hc.ne', hxnn]
    · exact (pieces_positive_support θ ps (lt_of_le_of_ne hθ (Ne.symm hz)) hps x hJ.1).1
  · rw [pieces_inactive θ x ps hθ hx hps hJ, dirac_support015]

lemma pieces_atom (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    L023 θ ps x {ell023 θ x ps} =
      if (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x) then
        if θ = 0 then ENNReal.ofReal (Real.exp (-x/c023 ps)) else 0
      else 1 := by
  classical
  split_ifs with hJ hz
  · subst θ
    have hc := (c023_pos_iff ps hps).2 hJ.1
    rw [zero_pieces_law ps hps x hx, ell_zero_active x ps hJ.1]
    simp only [Standalone.ZeroMeanReversionVarianceSupport.T01513, hc.ne', ite_false,
      transition_atom _ hc, Real.coe_toNNReal x hx]
  · exact (pieces_positive_support θ ps (lt_of_le_of_ne hθ (Ne.symm hz)) hps x hJ.1).2 _
  · rw [pieces_inactive θ x ps hθ hx hps hJ]
    simp

lemma joint_law_from_marginals {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Fin d → ℝ) (hY : Measurable Y)
    (hind : iIndepFun (fun j ω => Y ω j) μ) (hY0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j)
    (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (hθ : ∀ j, 0 ≤ θ j) (hx : ∀ j, 0 ≤ x j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (ht : ∀ j l, 0 ≤ l → (∫ ω, Real.exp (-(l*Y ω j)) ∂μ) =
      Real.exp (-(piFlow (θ j) (ps j) l*x j + rhoFlow (θ j) (ps j) l))) :
    μ.map Y = Measure.pi (fun j => L023 (θ j) (ps j) (x j)) := by
  have hmj (j : Fin d) : Measurable (fun ω => Y ω j) := (measurable_pi_apply j).comp hY
  have hj (j : Fin d) : μ.map (fun ω => Y ω j) = L023 (θ j) (ps j) (x j) := by
    have : IsProbabilityMeasure (μ.map (fun ω => Y ω j)) :=
      (Measure.isProbabilityMeasure_map_iff (hmj j).aemeasurable).2 inferInstance
    apply pieces_law_of_transform (θ j) (ps j) (hθ j) (hps j) (x j) (hx j)
    · apply (ae_map_iff (hmj j).aemeasurable measurableSet_Ici).2
      filter_upwards [hY0] with ω hω
      exact hω j
    · intro l hl
      rw [integral_map (hmj j).aemeasurable (by fun_prop)]
      exact ht j l hl
  simp_rw [← hj]
  exact hind.map_fun_eq_pi_map (fun j => (hmj j).aemeasurable)

lemma piecewise_joint_law {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Fin d → ℝ) (hY : Measurable Y)
    (hY0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j)
    (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (hθ : ∀ j, 0 ≤ θ j) (hx : ∀ j, 0 ≤ x j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (ht : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
        Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x j + rhoFlow (θ j) (ps j) (l j))))) :
    μ.map Y = Measure.pi (fun j => L023 (θ j) (ps j) (x j)) := by
  obtain ⟨hind, htr⟩ := independence d Ω mΩ μ inferInstance Y hY hY0 θ ps x ht
  exact joint_law_from_marginals μ Y hY hind hY0 θ x ps hθ hx hps htr

lemma piecewise_image_support {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ))
    (hθ : ∀ j, 0 ≤ θ j) (hx : ∀ j, 0 ≤ x j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) :
    let J := Finset.univ.filter fun j => (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
    let ell := fun j => ell023 (θ j) (x j) (ps j)
    let B := activeCols A J
    let b := C + A.mulVec ell
    let ν := (Measure.pi (fun j => L023 (θ j) (ps j) (x j))).map (fun y => C + A.mulVec y)
    ν.support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b) ∧
    (affineSpan ℝ ν.support : Set (Fin m → ℝ)) =
      (fun y => b+y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
    B.rank ≤ J.card ∧
    (∀ w, (∀ᵐ y ∂ν, dotProduct w (y-b) = 0) ↔ B.transpose.mulVec w = 0) ∧
    ν {b} = ∏ j, if (∃ i, B i j ≠ 0) then L023 (θ j) (ps j) (x j) {ell j} else 1 := by
  classical
  dsimp only
  have hp (j : Fin d) := pieces_probability (θ j) (ps j) (hθ j) (hps j) (x j)
  let J := Finset.univ.filter fun j => (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
  have hyes (j : Fin d) (hj : j ∈ J) :
      (L023 (θ j) (ps j) (x j)).support = Ici (ell023 (θ j) (x j) (ps j)) := by
    rw [pieces_support _ _ _ (hθ j) (hx j) (hps j), ite_eq_left (Finset.mem_filter.1 hj).2]
  have hno (j : Fin d) (hj : j ∉ J) :
      (L023 (θ j) (ps j) (x j)).support = {ell023 (θ j) (x j) (ps j)} := by
    have hn : ¬ ((∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)) := by simpa [J] using hj
    rw [pieces_support _ _ _ (hθ j) (hx j) (hps j), ite_eq_right hn]
  obtain ⟨hs, hc, ha, hr, he, hm⟩ := translatedCone m d A C _ J hA
    (fun j => L023 (θ j) (ps j) (x j)) hp hyes hno
  exact ⟨hs, hc, by rwa [hs], hr, he, hm⟩

lemma conditional_piecewise_law {d : ℕ} {Ω : Type} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Ω → Fin d → ℝ≥0) (hY : Measurable Y)
    (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ)
    (hx : ∀ ω j, 0 ≤ x ω j) (hθ : ∀ j, 0 ≤ θ j)
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (ht : ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
      μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
        fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
          rhoFlow (θ j) (ps j) (l j))))) :
    ∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
      ∀ᵐ ω ∂μ, (κ ω).map (fun y j => (y j : ℝ)) = Measure.pi (fun j => L023 (θ j) (ps j) (x ω j)) := by
  obtain ⟨κ, hκ, hm, hl, hind, htr⟩ := conditionalLaw d Ω G mΩ μ inferInstance hG Y hY θ ps x hθ hps ht
  let := hκ
  refine ⟨κ, hκ, hm, hl, ?_⟩
  filter_upwards [htr] with ω hω
  exact joint_law_from_marginals (κ ω) (fun y j => (y j : ℝ)) (by fun_prop)
    ((hind ω).comp (fun _ => fun z : ℝ≥0 => (z : ℝ)) (fun _ => NNReal.continuous_coe.measurable))
    (ae_of_all _ fun y j => (y j).coe_nonneg) θ (x ω) ps hθ (hx ω) hps hω

lemma source_piecewise_support {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℝ) (C : Fin m → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (ps : Fin 3 → List (ℝ × ℝ))
    (hps : ∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hlast : ∀ j, ∃ α h qs, ps j = (α,h)::qs ∧ 0 < α ∧ 0 < h) :
    let ν := (Measure.pi (fun j => L023 (θ0235 j) (ps j) 1)).map (fun y => C + A.mulVec y)
    ν.support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ ν.support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → ν {C} = 0) := by
  classical
  have hθ (j : Fin 3) : 0 ≤ θ0235 j := by fin_cases j <;> norm_num [θ0235]
  have hJ (j : Fin 3) : (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ0235 j ∨ 0 < (1:ℝ)) := by
    obtain ⟨α,h,qs,he,hα,hh⟩ := hlast j
    exact ⟨⟨(α,h), by simp [he], hα,hh⟩, Or.inr zero_lt_one⟩
  have hell : (fun j => ell023 (θ0235 j) 1 (ps j)) = 0 := by
    funext j
    obtain ⟨α,h,qs,he,hα,hh⟩ := hlast j
    simp [he, ell023, hα.ne', hh.ne']
  have hJuniv : (Finset.univ.filter fun j => (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧
      (0 < θ0235 j ∨ 0 < (1:ℝ))) = Finset.univ := by
    apply Finset.filter_eq_self.2
    intro j _
    exact hJ j
  have hB : activeCols A Finset.univ = A := by ext i j; simp [activeCols]
  have hs := piecewise_image_support A C hA θ0235 (fun _ => 1) ps hθ (fun _ => zero_le_one) hps
  dsimp only at hs ⊢
  rw [hJuniv, hell, hB, Matrix.mulVec_zero, add_zero] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, A.rank_le_width, ?_⟩
  rintro ⟨j,hj,i,hi⟩
  rw [hs.2.2.2.2.2]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [ite_eq_left (show ∃ i, A i j ≠ 0 from ⟨i,hi⟩)]
  have hmass := (pieces_positive_support (θ0235 j) (ps j) hj (hps j) 1 (hJ j).1).2 (ell023 (θ0235 j) 1 (ps j))
  exact hmass

lemma coordinateLaw : coordinateLawStatement := by
  intro θ ps hθ hps
  refine ⟨pieces_measurable θ ps, ?_⟩
  intro x hx
  refine ⟨pieces_probability θ ps hθ hps x, pieces_laplace θ ps hθ hps x hx,
    pieces_support θ x ps hθ hx hps, pieces_atom θ x ps hθ hx hps,
    fun hp hJ => (pieces_positive_support θ ps hp hps x hJ).2,
    pieces_inactive θ x ps hθ hx hps, ?_, ?_⟩
  · intro hz; subst θ; exact zero_pieces_law ps hps x hx
  · intro μ hμ hnonneg ht
    exact pieces_law_of_transform θ ps hθ hps x hx μ hnonneg ht

lemma ell_nonneg (θ x : ℝ) (ps : List (ℝ × ℝ)) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hps : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) : 0 ≤ ell023 θ x ps := by
  induction ps with
  | nil => exact hx
  | cons p ps ih =>
    rw [ell023]
    split_ifs
    · exact lflow_nonneg θ _ p.2 hθ (ih fun q hq => hps q (List.mem_cons_of_mem p hq))
        (hps p (by simp)).2
    · exact le_rfl

lemma lowerEndpoint : lowerEndpointStatement := by
  intro θ x ps hθ hx hps
  refine ⟨ell_nonneg θ x ps hθ hx hps, ?_, ?_, ell_deterministic θ x ps⟩
  · intro α h qs he hα hh
    simp [he, ell023, hα.ne', hh.ne']
  · intro h qs he hθp hh
    have hb := ell_nonneg θ x qs hθ hx (fun q hq => hps q (by simp [he, hq]))
    have he0 := Real.exp_pos (-θ*h)
    have he1 : Real.exp (-θ*h) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    simp only [he, ell023, true_or, ite_true, lflow]
    nlinarith [mul_nonneg hb he0.le]

lemma piecewiseJointLaw : piecewiseJointLawStatement := by
  intro d Ω mΩ μ hμ Y hY hY0 θ x ps hθ hx hps ht
  exact piecewise_joint_law μ Y hY hY0 θ x ps hθ hx hps ht

lemma piecewiseImageLaw : piecewiseImageLawStatement := by
  intro m d A C hA θ x ps hθ hx hps
  exact piecewise_image_support A C hA θ x ps hθ hx hps

lemma conditionalPiecewiseLaw : conditionalPiecewiseLawStatement := by
  intro d Ω G mΩ μ hμ hG Y hY θ ps x hx hθ hps ht
  exact conditional_piecewise_law G μ hG Y hY θ ps x hx hθ hps ht

lemma sourcePiecewiseSupport : sourcePiecewiseSupportStatement := by
  intro m A C hA ps hps hlast
  exact source_piecewise_support A C hA ps hps hlast

end CoordinateLaws

section FieldsAssembly
open ProbabilityTheory
open scoped NNReal ENNReal Topology
open Standalone.ZeroMeanReversionUpstreamBridge


lemma pieces_from_fields {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal)
    (h : H0237 S k θ αf X x0) (ps : List ((Fin d → ℝ) × ℝ))
    (hps : ∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) :
    ∀ b, 0 ≤ leftEnd b ps → H0238 αf b ps → PiecesOK S.μ (filtR S.ℱ) θ (stateR X) b ps := by
  obtain ⟨hc,hθ,hcont,hadapt,hαm,hαb,hx0,hx0le,hU,hK,hsde⟩ := h
  induction ps with
  | nil => intro b hb hp; trivial
  | cons p ps ih =>
    intro b hb hp
    have hp0 := hps p (List.mem_cons_self ..)
    have hps' := fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hab : b-p.2 ≤ b := sub_le_self b hp0.2
    have ha : 0 ≤ b-p.2 := hb.trans (by
      rw [leftEnd_cons]
      exact leftEnd_le _ _ (fun q hq => (hps' q hq).2))
    have hb0 := ha.trans hab
    refine ⟨?_, ih hps' (b-p.2) (by simpa only [leftEnd_cons] using hb) hp.2⟩
    have hone := onePiece_of_fields d Ω mΩ S k θ αf p.1 X x0 hc hθ hp0.1 hcont hadapt
      hαm hαb hx0 hx0le hU hK hsde (Real.toNNReal (b-p.2)) (Real.toNNReal b)
      (Real.toNNReal_le_toNNReal hab) ?_
    · simpa only [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb0] using hone
    · intro j s hs hs'
      apply hp.1 j s
      · simpa only [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ha] using hs
      · simpa only [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hb0] using hs'

lemma fieldsTransform : fieldsTransformStatement := by
  intro d Ω mΩ S k θ αf X x0 h b ps hps hb hp
  exact pieceComposition d Ω mΩ S.μ inferInstance (filtR S.ℱ) θ (stateR X) h.2.1
    (fun s => h.2.2.2.1 (Real.toNNReal s)) b ps (fun p hp => (hps p hp).2)
    (pieces_from_fields S k θ αf X x0 h ps hps b hb hp)

lemma fieldsLaw : fieldsLawStatement := by
  intro d Ω mΩ S k θ αf X x0 h b ps hps hb hp
  have ht := fieldsTransform d Ω mΩ S k θ αf X x0 h b ps hps hb hp
  have hm (s : ℝ) : Measurable[filtR S.ℱ s] (stateR X s) := h.2.2.2.1 (Real.toNNReal s)
  have hm' (s : ℝ) : Measurable (stateR X s) := (hm s).mono ((filtR S.ℱ).le s) le_rfl
  have hpsj (j : Fin d) (p : ℝ × ℝ) (hp : p ∈ ps.map fun p => (p.1 j,p.2)) :
      0 ≤ p.1 ∧ 0 ≤ p.2 := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
    exact ⟨(hps q hq).1 j,(hps q hq).2⟩
  refine ⟨conditional_piecewise_law (filtR S.ℱ (leftEnd b ps)) S.μ ((filtR S.ℱ).le (leftEnd b ps)) (stateR X b) (hm' b)
    θ (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2)) (fun ω j => (stateR X (leftEnd b ps) ω j : ℝ))
    (fun ω j => (stateR X _ ω j).coe_nonneg) h.2.1 hpsj ht, ?_⟩
  intro hs
  apply piecewise_joint_law S.μ (fun ω j => (stateR X b ω j : ℝ))
    (measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (hm' b)))
    (ae_of_all _ fun ω j => (stateR X _ ω j).coe_nonneg) θ (fun j => (x0 j : ℝ))
    (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2)) h.2.1 (fun j => (x0 j).coe_nonneg) hpsj
  intro l hl
  have hi := expSum_integrable S.μ (filtR S.ℱ) (stateR X) hm l hl b
  have he := ht l hl
  rw [hs] at he
  have hx0 := h.2.2.2.2.2.2.1
  have he' : S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X b ω j)) | filtR S.ℱ 0] =ᵐ[S.μ]
      fun _ => Real.exp (-(∑ j, (piFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j) * x0 j +
        rhoFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j)))) := by
    filter_upwards [he, hx0] with ω hω hxω
    simpa only [stateR, Real.toNNReal_zero, hxω] using hω
  rw [← integral_condExp ((filtR S.ℱ).le 0), integral_congr_ae he']
  simp

lemma actual_variance0239 {m d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → ℝ≥0) (K : Fin m → Fin d → ℝ → ℝ)
    (θ : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ)
    (hT : ∀ n, t ≤ T n) (hK : ∀ n j u, 0 ≤ K n j u) (hθ : ∀ j, 0 ≤ θ j)
    (h : H0239 G μ Y Z I01314 v K θ T t) :
    Standalone.ZeroMeanReversionVarianceSupport.V0150 G μ Y =ᵐ[μ] fun ω =>
      Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) T t +
      (Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) T t).mulVec (fun j => (v ω j : ℝ)) := by
  have hn (n : Fin m) := Novel.StochasticMeetingVarianceProof.conditional_variance Ω mΩ μ
    inferInstance G hG d (Y n) (Z n) (I01314 n) (K n) (fun j _ => θ j)
    (fun j ω => (v ω j : ℝ)) t (T n) (h.1 n) (h.2.1 n) (h.2.2.1 n)
    (h.2.2.2.1 n) (h.2.2.2.2.1 n)
  filter_upwards [ae_all_iff.2 hn] with ω hω
  exact (Novel.StochasticMeetingVarianceProof.affine_variance m d K (fun j _ => θ j) T t
    (fun j => (v ω j : ℝ)) _ hT hK (fun j _ => hθ j) (fun j => (v ω j).coe_nonneg)
    h.2.2.2.2.2.1 h.2.2.2.2.2.2 hω).1

lemma fieldsMeetingVariance : fieldsMeetingVarianceStatement := by
  intro d Ω mΩ S k θ αf X x0 h t ps hps hs hp m Y Z I01314 K T hT hK hmoment
  let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) T t
  let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) T t
  let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (filtR S.ℱ t) S.μ Y
  have hm : Measurable (stateR X t) :=
    (h.2.2.2.1 (Real.toNNReal t)).mono ((filtR S.ℱ).le t) le_rfl
  have hreal : Measurable (fun ω j => (stateR X t ω j : ℝ)) :=
    measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp hm)
  have hstate := (fieldsLaw d Ω mΩ S k θ αf X x0 h t ps hps (by rw [hs]) hp).2 hs
  have haff := actual_variance0239 (filtR S.ℱ t) S.μ ((filtR S.ℱ).le t)
    Y Z I01314 (stateR X t) K θ T t hT hK h.2.1 hmoment
  have hlaw : S.μ.map V =
      (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
        (fun y => C + A.mulVec y) := by
    rw [Measure.map_congr haff]
    change S.μ.map ((fun y => C + A.mulVec y) ∘ (fun ω j => (stateR X t ω j : ℝ))) = _
    rw [← Measure.map_map (by fun_prop) hreal, hstate]
  refine ⟨haff, hlaw, ?_⟩
  change C02310 A C θ _ _ (S.μ.map V)
  rw [hlaw]
  apply piecewise_image_support A C (Novel.StochasticMeetingVarianceProof.A_nonneg hT hK)
    θ (fun j => (x0 j : ℝ)) (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2))
    h.2.1 (fun j => (x0 j).coe_nonneg)
  intro j p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
  exact ⟨(hps q hq).1 j,(hps q hq).2⟩


lemma fieldsConditionalMeetingVariance : fieldsConditionalMeetingVarianceStatement := by
  intro d Ω mΩ S k θ αf X x0 h t ps hps hs hp m Y Z I01314 K T hT hK hmoment
  let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) T t
  let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) T t
  let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (filtR S.ℱ t) S.μ Y
  let f : (Fin d → ℝ≥0) → Fin m → ℝ := fun y => C + A.mulVec (fun j => (y j : ℝ))
  have hf : Measurable f := by fun_prop
  have hm : Measurable (stateR X t) :=
    (h.2.2.2.1 (Real.toNNReal t)).mono ((filtR S.ℱ).le t) le_rfl
  obtain ⟨κ,hκ,hκm,hκl,hκp⟩ := (fieldsLaw d Ω mΩ S k θ αf X x0 h t ps hps hs hp).1
  let := hκ
  let η := κ.map f
  have haff := actual_variance0239 (filtR S.ℱ t) S.μ ((filtR S.ℱ).le t)
    Y Z I01314 (stateR X t) K θ T t hT hK h.2.1 hmoment
  refine ⟨η, Kernel.IsMarkovKernel.map κ hf, ?_, ?_, ?_⟩
  · intro B hB
    have he : (fun ω => η ω B) = fun ω => κ ω (f ⁻¹' B) :=
      funext fun ω => Kernel.map_apply' κ hf ω hB
    rw [he]
    exact hκm _ (hf hB)
  · intro D hD
    rw [Measure.map_congr (ae_restrict_of_ae haff)]
    change (S.μ.restrict D).map (f ∘ stateR X t) = _
    rw [← Measure.map_map hf hm, hκl D hD, Measure.map_comp _ _ hf]
  · filter_upwards [hκp] with ω hω
    have hlaw : η ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
        (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) := by
      rw [Kernel.map_apply κ hf ω]
      change (κ ω).map ((fun y => C + A.mulVec y) ∘ (fun y j => (y j : ℝ))) = _
      rw [← Measure.map_map (by fun_prop) (by fun_prop), hω]
    refine ⟨hlaw, ?_⟩
    change C02310 A C θ _ _ (η ω)
    rw [hlaw]
    apply piecewise_image_support A C (Novel.StochasticMeetingVarianceProof.A_nonneg hT hK)
      θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
      (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2))
      h.2.1 (fun j => (stateR X _ ω j).coe_nonneg)
    intro j p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
    exact ⟨(hps q hq).1 j,(hps q hq).2⟩

end FieldsAssembly

section IntegralMoments
open ProbabilityTheory
open scoped NNReal ENNReal Topology
open Standalone.ZeroMeanReversionUpstreamBridge
open Novel.ZeroMeanReversionUpstreamBridgeProof


lemma fieldsStateMean : fieldsStateMeanStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi t j
  obtain ⟨ps,hps,hs,hcoef⟩ := hp t
  have htr := fieldsTransform d Ω mΩ S k θ αf X x0 h t ps hps (by rw [hs]) hcoef
  have hadapt (s : ℝ) : Measurable[filtR S.ℱ s] (stateR X s) := h.2.2.2.1 (Real.toNNReal s)
  have hm : Measurable (stateR X t) := (hadapt t).mono ((filtR S.ℱ).le t) le_rfl
  have hx : Measurable[filtR S.ℱ (leftEnd t ps)]
      (fun ω j => (stateR X (leftEnd t ps) ω j : ℝ)) := by
    let : MeasurableSpace Ω := filtR S.ℱ (leftEnd t ps)
    exact measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp
      ((measurable_pi_apply j).comp (hadapt (leftEnd t ps)))
  have hmean := conditional_mean (filtR S.ℱ (leftEnd t ps)) S.μ ((filtR S.ℱ).le _)
    (stateR X t) hm (fun j => hi _ j) θ
    (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2))
    (fun ω j => (stateR X (leftEnd t ps) ω j : ℝ)) hx h.2.1
    (fun j p hp => by
      obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
      exact ⟨(hps q hq).1 j,(hps q hq).2⟩) htr j
  have hlen : totalLength (ps.map fun p => (p.1 j,p.2)) = t := by
    unfold totalLength
    simp only [List.map_map]
    have hsum : (ps.map Prod.snd).sum = (t : ℝ) := by
      exact (sub_eq_zero.1 hs).symm
    exact hsum
  rw [hs, hlen] at hmean
  have he : S.μ[fun ω => (X t ω j : ℝ) | filtR S.ℱ 0] =ᵐ[S.μ]
      fun _ => lflow (θ j) (x0 j) t := by
    filter_upwards [hmean, h.2.2.2.2.2.2.1] with ω hω hxω
    simpa only [stateR, Real.toNNReal_zero, Real.toNNReal_coe, hxω] using hω
  have heq : (∫ ω, (X t ω j : ℝ) ∂S.μ) = lflow (θ j) (x0 j) t := by
    have hint := integral_congr_ae he
    rw [integral_condExp ((filtR S.ℱ).le 0), integral_const] at hint
    simpa using hint
  refine ⟨heq, ?_⟩
  rw [heq, lflow]
  have hx0 : (x0 j : ℝ) ≤ 1 := by exact_mod_cast h.2.2.2.2.2.2.2.1 j
  have he0 := Real.exp_pos (-θ j*t)
  nlinarith

lemma fieldsCoefficient : fieldsCoefficientStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi hsq j K hKm hKb T
  have hpred : IsStronglyPredictable S.ℱ (fun s ω => K s * Real.sqrt (X s ω j)) :=
    Upstream.ItoCalculus.predictable_const_mul S.ℱ K hKm _ (hsq j)
  have hjm : Measurable (fun p : ℝ × Ω =>
      ENNReal.ofReal ((K (Real.toNNReal p.1) * Real.sqrt (X (Real.toNNReal p.1) p.2 j)) ^ 2)) :=
    ((predictable_joint_measurable S _ hpred).pow_const 2).ennreal_ofReal
  have hmean : ∀ s : ℝ,
      (∫⁻ ω, ENNReal.ofReal (X (Real.toNNReal s) ω j) ∂S.μ) ≤ ENNReal.ofReal 1 := by
    intro s
    rw [← ofReal_integral_eq_lintegral_ofReal (hi _ j)
      (ae_of_all _ fun ω => (X (Real.toNNReal s) ω j).coe_nonneg)]
    exact ENNReal.ofReal_le_ofReal (fieldsStateMean d Ω mΩ S k θ αf X x0 h hp hi _ j).2
  have hbound : ∀ T' : ℝ≥0, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T',
      ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2)) ∂S.μ
        < ⊤ := by
    intro T'
    obtain ⟨C, hC⟩ := hKb T'
    have hswap := lintegral_lintegral_swap (μ := S.μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
      (f := fun ω s => ENNReal.ofReal
        ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2))
      (hjm.comp measurable_swap).aemeasurable
    rw [hswap]
    calc ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ ω, ENNReal.ofReal
          ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) ∂S.μ
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T', ENNReal.ofReal (C ^ 2) * ENNReal.ofReal 1 := by
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          calc ∫⁻ ω, ENNReal.ofReal
                ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2) ∂S.μ
              ≤ ∫⁻ ω, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (X (Real.toNNReal s) ω j) ∂S.μ :=
                lintegral_mono fun ω => sq_integrand_bound K C T' hC X j s hs ω
            _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal 1 := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                exact mul_le_mul' le_rfl (hmean s)
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
  refine ⟨⟨hpred, fun t => ?_⟩, hbound T⟩
  have hmeas : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) ^ 2)) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      (hjm.comp measurable_swap)
  exact ae_lt_top' hmeas.aemeasurable (hbound t).ne

lemma fieldsIncrement : fieldsIncrementStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi hsq kw K₁ K₂ hK₁m hK₂m hK₁b hK₂b T t ht
  have hU5 : ∀ (j : Fin d) (K : ℝ≥0 → ℝ), Measurable K →
      (∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) →
      U5 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) T :=
    fun j K hKm hKb => fieldsCoefficient d Ω mΩ S k θ αf X x0 h hp hi hsq j K hKm hKb T
  refine ⟨fun j => ?_, fun i j c1 c2 c3 c4 => ?_⟩
  · obtain ⟨h1, h2⟩ := twoDriverIsometry S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
      (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ht (hU5 j (K₁ j) (hK₁m j) (hK₁b j))
      (hU5 j (K₂ j) (hK₂m j) (hK₂b j))
    refine ⟨h1, ?_⟩
    have e1 : ∀ (s : ℝ) (ω : Ω), (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (kw j) (kw j) (Real.toNNReal s) =
        K₁ j (Real.toNNReal s) ^ 2 * S.c (kw j) (kw j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := by
      intro s ω
      rw [sqrt_integrand_eq, sq]
    have e2 : ∀ (s : ℝ) (ω : Ω), (K₁ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (kw j) (k j) (Real.toNNReal s) =
        K₁ j (Real.toNNReal s) * K₂ j (Real.toNNReal s) * S.c (kw j) (k j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := fun s ω => sqrt_integrand_eq _ _ _ X j _ ω
    have e3 : ∀ (s : ℝ) (ω : Ω), (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        (K₂ j (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j)) *
        S.c (k j) (k j) (Real.toNNReal s) =
        K₂ j (Real.toNNReal s) ^ 2 * S.c (k j) (k j) (Real.toNNReal s) *
          (X (Real.toNNReal s) ω j : ℝ) := by
      intro s ω
      rw [sqrt_integrand_eq, sq]
    simp only [e1, e2, e3] at h2
    exact h2
  · exact crossFactor S (kw i) (k i) (kw j) (k j) _ _ _ _ T t ht
      (hU5 i (K₁ i) (hK₁m i) (hK₁b i)) (hU5 i (K₂ i) (hK₂m i) (hK₂b i))
      (hU5 j (K₁ j) (hK₁m j) (hK₁b j)) (hU5 j (K₂ j) (hK₂m j) (hK₂b j)) c1 c2 c3 c4

lemma bound_mul023 (f g : ℝ≥0 → ℝ)
    (hf : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |f s| ≤ C)
    (hg : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |g s| ≤ C) :
    ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |f s * g s| ≤ C := by
  intro T
  obtain ⟨Cf,hCf⟩ := hf T
  obtain ⟨Cg,hCg⟩ := hg T
  refine ⟨Cf*Cg, fun s hs => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf s hs) (hCg s hs) (abs_nonneg _) ((abs_nonneg _).trans (hCf 0 (show (0 : ℝ≥0) ≤ T from bot_le)))

lemma weighted_interval_integrable023 {d : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (ω : Ω) (j : Fin d)
    (hX : Continuous fun s => (X s ω j : ℝ)) (K : ℝ≥0 → ℝ) (hK : Measurable K)
    (hKb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) (T t : ℝ≥0) (ht : t ≤ T) :
    IntervalIntegrable (fun s : ℝ => K (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ))
      volume (t : ℝ) T := by
  have hXr := hX.comp continuous_real_toNNReal
  obtain ⟨CX,hCX⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hXr.continuousOn
  obtain ⟨C,hC⟩ := hKb T
  have hv := intervalIntegrable_bounded (fun s => K (Real.toNNReal s)) (fun _ => 1)
    (fun s => (X (Real.toNNReal s) ω j : ℝ)) (t : ℝ) T (by exact_mod_cast ht) t.coe_nonneg
    (hK.comp measurable_real_toNNReal) measurable_const hXr.measurable C 1 CX
    (fun s hs => hC _ ((Real.toNNReal_le_toNNReal hs.2).trans_eq Real.toNNReal_coe))
    (fun _ _ => by simp) (fun s hs => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hCX s hs)
  simpa only [mul_one] using hv

lemma kernel_combine023 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin d → ℝ≥0)
    (g R ρ : Fin d → ℝ≥0 → ℝ) (T t : ℝ≥0) (ht : t ≤ T) (j : Fin d)
    (hgm : Measurable (g j)) (hRm : Measurable (R j)) (hαm : Measurable (αf j))
    (hgb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |g j s| ≤ C)
    (hRb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |R j s| ≤ C)
    (hαb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |αf j s| ≤ C)
    (hcww : ∀ s, S.c (kw j) (kw j) s = 1) (hcuu : ∀ s, S.c (k j) (k j) s = 1)
    (hcwu : ∀ s, S.c (kw j) (k j) s = ρ j s) (ω : Ω)
    (hX : Continuous fun s => (X s ω j : ℝ)) :
    (∫ s in (t : ℝ)..T, g j (Real.toNNReal s)^2 * S.c (kw j) (kw j) (Real.toNNReal s) *
      (X (Real.toNNReal s) ω j : ℝ)) +
    2 * (∫ s in (t : ℝ)..T, g j (Real.toNNReal s) * (αf j (Real.toNNReal s)*R j (Real.toNNReal s)) *
      S.c (kw j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) +
    (∫ s in (t : ℝ)..T, (αf j (Real.toNNReal s)*R j (Real.toNNReal s))^2 *
      S.c (k j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) = I02312 αf X g R ρ T t j ω := by
  have hρm : Measurable (ρ j) := by
    have he : S.c (kw j) (k j) = ρ j := funext hcwu
    rw [← he]; exact S.c_measurable _ _
  have hρb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |ρ j s| ≤ C := by
    intro T
    simpa only [hcwu] using S.c_bounded_on_compacts (kw j) (k j) T
  have hkm := hαm.mul hRm
  have hkb := bound_mul023 (αf j) (R j) hαb hRb
  have hi1 := weighted_interval_integrable023 X ω j hX (fun s => g j s^2) (hgm.pow_const 2)
    (by simpa only [pow_two] using bound_mul023 (g j) (g j) hgb hgb) T t ht
  have hi2 := weighted_interval_integrable023 X ω j hX
    (fun s => g j s * (αf j s*R j s) * ρ j s) ((hgm.mul hkm).mul hρm)
    (bound_mul023 _ _ (bound_mul023 _ _ hgb hkb) hρb) T t ht
  have hi3 := weighted_interval_integrable023 X ω j hX (fun s => (αf j s*R j s)^2) (hkm.pow_const 2)
    (by simpa only [pow_two] using bound_mul023 _ _ hkb hkb) T t ht
  simp only [hcww,hcuu,hcwu,mul_one]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 (hi2.const_mul 2),
    ← intervalIntegral.integral_add (hi1.add (hi2.const_mul 2)) hi3]
  apply intervalIntegral.integral_congr
  intro s _
  change _ = Standalone.StochasticMeetingVariance.F _ _ _ _ * _
  unfold Standalone.StochasticMeetingVariance.F
  ring

lemma fieldsKernelIsometry : fieldsKernelIsometryStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi hsq kw g R ρ hgm hRm hgb hRb hcww hcwu hcrossWW hcrossWU T t ht
  have hkm (j : Fin d) := (h.2.2.2.2.1 j).mul (hRm j)
  have hkb (j : Fin d) := bound_mul023 (αf j) (R j) (h.2.2.2.2.2.1 j) (hRb j)
  obtain ⟨hiso,hcross⟩ := fieldsIncrement d Ω mΩ S k θ αf X x0 h hp hi hsq kw g
    (fun j s => αf j s * R j s) hgm hkm hgb hkb T t ht
  refine ⟨fun j => (hiso j).1, fun i j => (hiso i).1.integrable_mul (hiso j).1, ?_, ?_⟩
  · intro j
    refine (hiso j).2.trans (condExp_congr_ae (ae_of_all _ fun ω => ?_))
    exact kernel_combine023 S k kw αf X g R ρ T t ht j (hgm j) (hRm j) (h.2.2.2.2.1 j)
      (hgb j) (hRb j) (h.2.2.2.2.2.1 j) (hcww j) (fun s => by simpa using h.1 j j s)
      (hcwu j) ω (h.2.2.1 ω j)
  · intro i j hij
    exact (hcross i j (hcrossWW i j hij) (hcrossWU i j hij)
      (fun s => by rw [S.c_symm]; exact hcrossWU j i hij.symm s)
      (fun s => by simp [h.1, hij])).2

lemma backwardWeightRegularity : backwardWeightRegularityStatement := by
  intro θ b T hb
  have hi (a c : ℝ) : IntervalIntegrable
      (fun s => b s * Real.exp (-(∫ u in (0:ℝ)..s, θ))) volume a c :=
    (hb a c).mul_continuousOn (by fun_prop)
  have he : Standalone.StochasticMeetingVariance.R (fun _ => θ) b T =
      fun t => Real.exp (∫ u in (0:ℝ)..t, θ) *
        ∫ s in t..T, b s * Real.exp (-(∫ u in (0:ℝ)..s, θ)) :=
    funext fun t => Novel.StochasticMeetingVarianceProof.R_integrating_factor (fun _ => θ) b T t
      (fun _ _ => intervalIntegrable_const)
  have hi' : Continuous (fun t => ∫ s in t..T, b s * Real.exp (-(∫ u in (0:ℝ)..s, θ))) := by
    have he' : (fun t => ∫ s in t..T, b s * Real.exp (-(∫ u in (0:ℝ)..s, θ))) =
        fun t => -(∫ s in T..t, b s * Real.exp (-(∫ u in (0:ℝ)..s, θ))) :=
      funext fun t => intervalIntegral.integral_symm T t
    rw [he']
    exact (intervalIntegral.continuous_primitive hi T).neg
  have hc : Continuous (Standalone.StochasticMeetingVariance.R (fun _ => θ) b T) := by
    rw [he]
    exact (by fun_prop : Continuous (fun t => Real.exp (∫ u in (0:ℝ)..t, θ))).mul hi'
  refine ⟨hc, hc.measurable.comp NNReal.continuous_coe.measurable, ?_⟩
  intro U
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := U)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, ?_⟩
  intro s hs
  simpa only [Real.norm_eq_abs] using (hC s ⟨s.coe_nonneg, by exact_mod_cast hs⟩)

lemma kernelIdentification : kernelIdentificationStatement := by
  intro m d Ω θ αf X g b ρ T n j t ht
  funext ω
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (show (t:ℝ) ≤ T n from by exact_mod_cast ht)] at hu
  have hu0 : 0 ≤ u := t.coe_nonneg.trans hu.1
  simp only [Standalone.StochasticMeetingVariance.kernel0136, Real.coe_toNNReal u hu0]

lemma restrict_pieces023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (ps : List ((Fin d → ℝ) × ℝ))
    (hps : ∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) :
    ∀ b a, H0238 αf b ps → leftEnd b ps ≤ a → a ≤ b →
      ∃ qs, (∀ p ∈ qs, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
        leftEnd b qs = a ∧ H0238 αf b qs := by
  induction ps with
  | nil =>
    intro b a _ hlo hhi
    have he : b = a := le_antisymm (by simpa [leftEnd] using hlo) hhi
    exact ⟨[], by simp, by simpa [leftEnd] using he, trivial⟩
  | cons p ps ih =>
    intro b a hc hlo hhi
    have hp := hps p (by simp)
    have hrest : ∀ q ∈ ps, (∀ j, 0 ≤ q.1 j) ∧ 0 ≤ q.2 := fun q hq => hps q (by simp [hq])
    by_cases ha : a ≤ b-p.2
    · obtain ⟨qs,hqs,he,hcqs⟩ := ih hrest (b-p.2) a hc.2
        (by simpa only [leftEnd_cons] using hlo) ha
      refine ⟨p::qs, ?_, ?_, hc.1, hcqs⟩
      · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hp hqs
      · simpa only [leftEnd_cons] using he
    · refine ⟨[(p.1,b-a)], ?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst q
        exact ⟨hp.1, sub_nonneg.2 hhi⟩
      · simp [leftEnd]
      · refine ⟨?_, trivial⟩
        intro j s hs hsb
        apply hc.1 j s _ hsb
        linarith

lemma fieldsConditionalMean023 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0)
    (h : H0237 S k θ αf X x0) (hp : H02311 αf)
    (hi : ∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ)
    (a b : ℝ≥0) (hab : a ≤ b) (j : Fin d) :
    S.μ[fun ω => (X b ω j : ℝ) | S.ℱ a] =ᵐ[S.μ]
      fun ω => lflow (θ j) (X a ω j) ((b : ℝ)-a) := by
  obtain ⟨ps,hps,hs,hcoef⟩ := hp b
  obtain ⟨qs,hqs,hqa,hqc⟩ := restrict_pieces023 αf ps hps b a hcoef
    (by rw [hs]; exact a.coe_nonneg) (by exact_mod_cast hab)
  have htr := fieldsTransform d Ω mΩ S k θ αf X x0 h b qs hqs
    (by rw [hqa]; exact a.coe_nonneg) hqc
  have hadapt (s : ℝ) : Measurable[filtR S.ℱ s] (stateR X s) := h.2.2.2.1 (Real.toNNReal s)
  have hm : Measurable (stateR X b) := (hadapt b).mono ((filtR S.ℱ).le b) le_rfl
  have hx : Measurable[filtR S.ℱ (leftEnd b qs)]
      (fun ω j => (stateR X (leftEnd b qs) ω j : ℝ)) := by
    let : MeasurableSpace Ω := filtR S.ℱ (leftEnd b qs)
    exact measurable_pi_iff.mpr fun j => NNReal.continuous_coe.measurable.comp
      ((measurable_pi_apply j).comp (hadapt (leftEnd b qs)))
  have hmean := conditional_mean (filtR S.ℱ (leftEnd b qs)) S.μ ((filtR S.ℱ).le _)
    (stateR X b) hm (fun j => hi _ j) θ
    (fun j : Fin d => qs.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2))
    (fun ω j => (stateR X (leftEnd b qs) ω j : ℝ)) hx h.2.1
    (fun j p hp => by
      obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
      exact ⟨(hqs q hq).1 j,(hqs q hq).2⟩) htr j
  have hlen : totalLength (qs.map fun p => (p.1 j,p.2)) = (b : ℝ)-a := by
    unfold totalLength
    simp only [List.map_map]
    change (qs.map Prod.snd).sum = (b : ℝ)-a
    unfold leftEnd at hqa
    linarith
  rw [hqa, hlen] at hmean
  simpa only [stateR, filtR, Real.toNNReal_coe] using hmean

/-- Fubini applied to the affine conditional mean of the state. -/
lemma integrate_conditional_mean023 {Ω : Type} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ mΩ)
    (ν : Measure ℝ) [SFinite ν] (f g : ℝ → Ω → ℝ)
    (hf : Integrable (Function.uncurry f) (ν.prod μ))
    (hg : Integrable (Function.uncurry g) (ν.prod μ))
    (hm : Measurable[G] (fun ω => ∫ u, g u ω ∂ν))
    (hc : ∀ᵐ u ∂ν, μ[f u | G] =ᵐ[μ] g u) :
    μ[fun ω => ∫ u, f u ω ∂ν | G] =ᵐ[μ] fun ω => ∫ u, g u ω ∂ν := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hf.integral_prod_right
    (fun D _ _ => hg.integral_prod_right.integrableOn) ?_ hm.aestronglyMeasurable).symm
  intro D hD _
  have hfr := hf.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := D)))
  have hgr := hg.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := D)))
  simp only [Function.uncurry_apply_pair]
  rw [← integral_integral_swap hfr, ← integral_integral_swap hgr]
  apply integral_congr_ae
  filter_upwards [hc, hf.prod_right_ae] with u hu hiu
  change Integrable (f u) μ at hiu
  rw [← setIntegral_condExp hG hiu hD, integral_congr_ae (ae_restrict_of_ae hu)]

lemma fieldsWeightedIntegral023 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0)
    (h : H0237 S k θ αf X x0) (hp : H02311 αf)
    (hi : ∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ)
    (a b : ℝ≥0) (hab : a ≤ b) (j : Fin d) (K : ℝ → ℝ)
    (hK : IntervalIntegrable K volume (a : ℝ) b) :
    Integrable (fun ω => ∫ u in (a : ℝ)..b, K u * (stateR X u ω j : ℝ)) S.μ ∧
    (S.μ[fun ω => ∫ u in (a : ℝ)..b, K u * (stateR X u ω j : ℝ) | S.ℱ a] =ᵐ[S.μ]
      fun ω => ∫ u in (a : ℝ)..b, K u * lflow (θ j) (X a ω j) (u-a)) := by
  let ν := volume.restrict (Ioc (a : ℝ) b)
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hKν : Integrable K ν := hK.1
  have hjoint := joint_measurable_ae S X
    (fun j => ae_of_all _ fun ω => h.2.2.1 ω j) h.2.2.2.1 b j a b a.coe_nonneg le_rfl
  have hprod : Integrable (fun p : ℝ × Ω => K p.1 * (stateR X p.1 p.2 j : ℝ)) (ν.prod S.μ) := by
    have hkm : AEStronglyMeasurable (fun p : ℝ × Ω => K p.1 * (stateR X p.1 p.2 j : ℝ)) (ν.prod S.μ) :=
      hKν.aestronglyMeasurable.comp_fst.mul hjoint
    apply (integrable_prod_iff hkm).2
    refine ⟨ae_of_all _ (fun u => (hi (Real.toNNReal u) j).const_mul (K u)), ?_⟩
    have hm : IntervalIntegrable (fun u : ℝ => ‖K u‖ *
        lflow (θ j) (x0 j) (Real.toNNReal u)) volume (a : ℝ) b :=
      hK.norm.mul_continuousOn (by unfold lflow; fun_prop)
    apply hm.1.congr
    filter_upwards [] with u
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (stateR X u _ j).coe_nonneg]
    rw [integral_const_mul]
    dsimp only [stateR]
    rw [(fieldsStateMean d Ω mΩ S k θ αf X x0 h hp hi (Real.toNNReal u) j).1]
  let KA : ℝ → ℝ := fun u => K u * (1 - Real.exp (-θ j * (u-a)))
  let KB : ℝ → ℝ := fun u => K u * Real.exp (-θ j * (u-a))
  have hKA : IntervalIntegrable KA volume (a : ℝ) b := hK.mul_continuousOn (by fun_prop)
  have hKB : IntervalIntegrable KB volume (a : ℝ) b := hK.mul_continuousOn (by fun_prop)
  have he (u : ℝ) (ω : Ω) : K u * lflow (θ j) (X a ω j) (u-a) =
      KA u + KB u * (X a ω j : ℝ) := by unfold lflow KA KB; ring
  have hgp : Integrable (fun p : ℝ × Ω => K p.1 * lflow (θ j) (X a p.2 j) (p.1-a))
      (ν.prod S.μ) := by
    have h1 := hKA.1.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) S.μ)
    have h2 := hKB.1.mul_prod (hi a j)
    apply (h1.add h2).congr
    exact ae_of_all _ fun p => by simp only [mul_one]; exact (he p.1 p.2).symm
  have heint (ω : Ω) : (∫ u, K u * lflow (θ j) (X a ω j) (u-a) ∂ν) =
      (∫ u, KA u ∂ν) + (∫ u, KB u ∂ν) * (X a ω j : ℝ) := by
    simp_rw [he]
    rw [integral_add hKA.1 (hKB.1.mul_const _), integral_mul_const]
  have hma : Measurable[S.ℱ a] (fun ω => (X a ω j : ℝ)) := by
    let : MeasurableSpace Ω := S.ℱ a
    exact NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (h.2.2.2.1 a))
  have hmi : Measurable[S.ℱ a] (fun ω => ∫ u, K u * lflow (θ j) (X a ω j) (u-a) ∂ν) := by
    simp_rw [heint]
    exact measurable_const.add (measurable_const.mul hma)
  have hcond : ∀ᵐ u ∂ν, S.μ[fun ω => K u * (stateR X u ω j : ℝ) | S.ℱ a] =ᵐ[S.μ]
      fun ω => K u * lflow (θ j) (X a ω j) (u-a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 ≤ u := a.coe_nonneg.trans hu.1.le
    have hau : a ≤ Real.toNNReal u := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal u hu0]
      exact hu.1.le
    have hmean := fieldsConditionalMean023 S k θ αf X x0 h hp hi a (Real.toNNReal u) hau j
    have hk := condExp_smul (μ := S.μ) (m := S.ℱ a) (K u) (fun ω => (stateR X u ω j : ℝ))
    filter_upwards [hmean, hk] with ω heq hk
    change S.μ[fun ω => K u*(stateR X u ω j : ℝ) | S.ℱ a] ω =
      K u * S.μ[fun ω => (stateR X u ω j : ℝ) | S.ℱ a] ω at hk
    rw [hk]
    dsimp only [stateR]
    rw [heq, Real.coe_toNNReal u hu0]
  have hout := integrate_conditional_mean023 (S.ℱ a) S.μ (S.ℱ.le a) ν
    (fun u ω => K u * (stateR X u ω j : ℝ))
    (fun u ω => K u * lflow (θ j) (X a ω j) (u-a)) hprod hgp hmi hcond
  simpa only [intervalIntegral.integral_of_le habr, ν] using And.intro hprod.integral_prod_right hout

lemma coefficient_interval_integrable023 (K : ℝ≥0 → ℝ) (hK : Measurable K)
    (hKb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) (T t : ℝ≥0) (ht : t ≤ T) :
    IntervalIntegrable (fun u => K (Real.toNNReal u)) volume (t : ℝ) T := by
  obtain ⟨C,hC⟩ := hKb T
  exact bounded_coefficient_integrable _ t T C (by exact_mod_cast ht)
    (hK.comp measurable_real_toNNReal).aestronglyMeasurable
    (fun u hu => hC _ ((Real.toNNReal_le_toNNReal hu.2).trans_eq Real.toNNReal_coe))

lemma kernel_integrable023 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (αf g R ρ : Fin d → ℝ≥0 → ℝ)
    (hαm : ∀ j, Measurable (αf j)) (hgm : ∀ j, Measurable (g j)) (hRm : ∀ j, Measurable (R j))
    (hαb : ∀ j T, ∃ C, ∀ s, s ≤ T → |αf j s| ≤ C)
    (hgb : ∀ j T, ∃ C, ∀ s, s ≤ T → |g j s| ≤ C)
    (hRb : ∀ j T, ∃ C, ∀ s, s ≤ T → |R j s| ≤ C)
    (hcwu : ∀ j s, S.c (kw j) (k j) s = ρ j s) (T t : ℝ≥0) (ht : t ≤ T) (j : Fin d) :
    IntervalIntegrable (fun u => Standalone.StochasticMeetingVariance.F
      (g j (Real.toNNReal u)) (ρ j (Real.toNNReal u)) (αf j (Real.toNNReal u))
      (R j (Real.toNNReal u))) volume (t : ℝ) T := by
  have hρm : Measurable (ρ j) := by
    rw [← funext (hcwu j)]; exact S.c_measurable _ _
  have hρb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |ρ j s| ≤ C := by
    intro T
    simpa only [hcwu] using S.c_bounded_on_compacts (kw j) (k j) T
  have hkm := (hαm j).mul (hRm j)
  have hkb := bound_mul023 (αf j) (R j) (hαb j) (hRb j)
  have hi1 := coefficient_interval_integrable023 (fun s => g j s^2) ((hgm j).pow_const 2)
    (by simpa only [pow_two] using bound_mul023 _ _ (hgb j) (hgb j)) T t ht
  have hi2 := coefficient_interval_integrable023 (fun s => g j s * (αf j s*R j s) * ρ j s)
    (((hgm j).mul hkm).mul hρm) (bound_mul023 _ _ (bound_mul023 _ _ (hgb j) hkb) hρb) T t ht
  have hi3 := coefficient_interval_integrable023 (fun s => (αf j s*R j s)^2) (hkm.pow_const 2)
    (by simpa only [pow_two] using bound_mul023 _ _ hkb hkb) T t ht
  convert (hi1.add (hi2.const_mul 2)).add hi3 using 1
  funext u
  unfold Standalone.StochasticMeetingVariance.F
  ring

lemma E_constant023 (θ a u : ℝ) :
    Standalone.StochasticMeetingVariance.E (fun _ => θ) a u = Real.exp (-θ * (u-a)) := by
  simp only [Standalone.StochasticMeetingVariance.E, intervalIntegral.integral_const, smul_eq_mul]
  congr 1
  ring


lemma fieldsConditionalMean : fieldsConditionalMeanStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi a b hab j
  exact fieldsConditionalMean023 S k θ αf X x0 h hp hi a b hab j

lemma fieldsWeightedIntegral : fieldsWeightedIntegralStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi a b hab j K hK
  exact fieldsWeightedIntegral023 S k θ αf X x0 h hp hi a b hab j K hK

lemma fieldsMomentAssembly : fieldsMomentAssemblyStatement := by
  intro m d Ω mΩ S k θ αf X x0 h hp hi hsq kw g R ρ hgm hRm hgb hRb
    hcww hcwu hcWW hcWU T t ht Y hcen
  have hiso (n : Fin m) := fieldsKernelIsometry d Ω mΩ S k θ αf X x0 h hp hi hsq
    kw (g n) (R n) ρ (hgm n) (hRm n) (hgb n) (hRb n) hcww hcwu hcWW hcWU (T n) t (ht n)
  have hK (n : Fin m) (j : Fin d) := kernel_integrable023 S k kw αf (g n) (R n) ρ
    h.2.2.2.2.1 (hgm n) (hRm n) h.2.2.2.2.2.1 (hgb n) (hRb n) hcwu (T n) t (ht n) j
  refine ⟨fun n => (hiso n).2.1, hcen, fun n => (hiso n).2.2.1,
    fun n => (hiso n).2.2.2, ?_, hK, ?_⟩
  · intro n j
    have he := (fieldsWeightedIntegral023 S k θ αf X x0 h hp hi t (T n) (ht n) j
      (fun u => Standalone.StochasticMeetingVariance.F
        (g n j (Real.toNNReal u)) (ρ j (Real.toNNReal u))
        (αf j (Real.toNNReal u)) (R n j (Real.toNNReal u))) (hK n j)).2
    change S.μ[fun ω => ∫ u in (t : ℝ)..T n,
      Standalone.StochasticMeetingVariance.F (g n j (Real.toNNReal u)) (ρ j (Real.toNNReal u))
        (αf j (Real.toNNReal u)) (R n j (Real.toNNReal u)) * (X (Real.toNNReal u) ω j : ℝ) | S.ℱ t]
        =ᵐ[S.μ] _
    simpa only [stateR, lflow, E_constant023] using he
  · intro n j
    simp only [E_constant023]
    exact (hK n j).mul_continuousOn (by fun_prop)

end IntegralMoments

/-! ### Centering the constructed meeting jumps -/

section Centered023
open Standalone.ZeroMeanReversionUpstreamBridge
open Novel.ZeroMeanReversionUpstreamBridgeProof
open scoped NNReal ENNReal Topology
variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)

noncomputable def f02313 (θ : ℝ) (j : Fin d) (p : ℝ × (Fin (d+1) → ℝ)) : ℝ :=
  Real.exp (θ*p.1) * fpair j p

lemma f02313_contDiff (θ : ℝ) (j : Fin d) : ContDiff ℝ 2 (f02313 θ j) := by
  unfold f02313 fpair
  fun_prop

lemma f02313_dT (θ : ℝ) (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) :
    dT (f02313 θ j) (s,z) = θ * Real.exp (θ*s) * z (Fin.castSucc j) * z (Fin.last d) := by
  rw [dT_general (f02313 θ j) (f02313_contDiff θ j)]
  change deriv (fun u => Real.exp (θ*u) * (z (Fin.castSucc j)*z (Fin.last d))) s = _
  simpa only [id_eq, mul_assoc, mul_comm, mul_left_comm, one_mul] using
    (((hasDerivAt_id s).const_mul θ).exp.mul_const
      (z (Fin.castSucc j)*z (Fin.last d))).deriv

lemma f02313_deriv (θ : ℝ) (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    deriv (fun u => f02313 θ j (s, Function.update z i u)) =
      fun _ => Real.exp (θ*s) * (if i = Fin.castSucc j then z (Fin.last d)
        else if i = Fin.last d then z (Fin.castSucc j) else 0) := by
  funext u
  unfold f02313
  dsimp only
  rw [deriv_const_mul _ (by
    unfold fpair
    simp only [Function.update_apply]
    split_ifs <;> fun_prop), fpair_deriv]

lemma f02313_dX (θ : ℝ) (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    dX (f02313 θ j) (s,z) i = Real.exp (θ*s) * (if i = Fin.castSucc j then z (Fin.last d)
      else if i = Fin.last d then z (Fin.castSucc j) else 0) := by
  rw [dX_general (f02313 θ j) (f02313_contDiff θ j), f02313_deriv]

lemma f02313_dXX (θ : ℝ) (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    dXX (f02313 θ j) (s,z) i i = 0 := by
  rw [dXX_general (f02313 θ j) (f02313_contDiff θ j), f02313_deriv]
  exact deriv_const _ _

noncomputable def H02313 (k : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) : Fin (d+1) → Fin S.m → ℝ≥0 → Ω → ℝ :=
  Fin.snoc (fun a => Hpw k αf X a) (fun _ _ _ => 0)
noncomputable def K02313 (θ : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (β : ℝ → ℝ) :
    Fin (d+1) → ℝ≥0 → Ω → ℝ := Fin.snoc (Kdrv θ X) (fun s _ => -(β s))

lemma H02313_U4 (k : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin d → ℝ≥0)
    (hU : ∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) (i : Fin (d+1)) (k' : Fin S.m) :
    U4 S.ℱ S.μ (H02313 S k αf X i k') := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa only [H02313, Fin.snoc_last] using U4_zero S
  · simpa only [H02313, Fin.snoc_castSucc] using Hpw_U4 S k αf X hU a k'

lemma K02313_drift (θ : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (β : ℝ → ℝ)
    (hK : ∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) (hβm : Measurable β)
    (hβi : ∀ t, IntervalIntegrable β volume 0 t) (i : Fin (d+1)) :
    LocallyIntegrableDrift S.ℱ S.μ (K02313 θ X β i) := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa only [K02313, Fin.snoc_last, Kext, Fin.snoc_last] using Kext_drift S β hβm hβi (Fin.last d)
  · simpa only [K02313, Fin.snoc_castSucc] using hK a

lemma driverForm02313 (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0) (h : H0237 S k θ αf X x0)
    (β : ℝ → ℝ) (R0 : ℝ) :
    ∀ᵐ ω ∂S.μ, ∀ t, driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) t ω =
      Fin.snoc (fun j => (X t ω j : ℝ)) (weightAC β R0 t) := by
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hdf := driverForm_eq_pw S k θ αf X x0 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2
  filter_upwards [hz,hdf] with ω hz hdf
  intro t
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [driverForm, xext, H02313, K02313, Fin.snoc_last]
    have hI0 : (∑ k', S.I k' (fun _ _ => (0 : ℝ)) t ω) = 0 :=
      Finset.sum_eq_zero fun k' _ => hz k' t
    rw [hI0, add_zero, weightAC, sub_eq_add_neg, ← intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    simp only [Real.coe_toNNReal u hu.1]
  · simpa only [driverForm, xext, H02313, K02313, Fin.snoc_castSucc] using congrFun (hdf t) a

lemma quad02313 (k : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (hc : ∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0)
    (θ : ℝ) (j : Fin d) (s : ℝ) (z : Fin (d+1) → ℝ) (u : ℝ≥0) (ω : Ω) :
    (∑ i, ∑ i', ∑ k', ∑ l', dXX (f02313 θ j) (s,z) i i' * H02313 S k αf X i k' u ω *
      H02313 S k αf X i' l' u ω * S.c k' l' u) = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
  refine Fin.lastCases ?_ (fun a' => ?_) i'
  · simp [H02313]
  · refine Fin.lastCases ?_ (fun a => ?_) i
    · simp [H02313]
    · simp only [H02313, Fin.snoc_castSucc]
      rw [quad_sum_pw S k αf X (fun a a' => dXX (f02313 θ j) (s,z) (Fin.castSucc a) (Fin.castSucc a'))
        a a' u ω, hc]
      split_ifs with haa
      · subst haa
        rw [f02313_dXX]
        ring
      · simp

lemma R_eq02313 (θ : ℝ) (b : ℝ → ℝ) (T s : ℝ)
    (hb : ∀ a c, IntervalIntegrable b volume a c) :
    Standalone.StochasticMeetingVariance.R (fun _ => θ) b T s =
      Real.exp (θ*s) * weightAC (fun u => b u * Real.exp (-θ*u))
        (∫ u in (0 : ℝ)..T, b u * Real.exp (-θ*u)) s := by
  have hβ : ∀ t : ℝ, IntervalIntegrable (fun u => b u * Real.exp (-θ*u)) volume 0 t :=
    fun t => (hb 0 t).mul_continuousOn (by fun_prop)
  rw [← backward_eq_weightAC _ hβ T]
  rw [Novel.StochasticMeetingVarianceProof.R_integrating_factor _ b T s
    (fun _ _ => intervalIntegrable_const)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg, mul_comm]

lemma productTerminal023 (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0) (h : H0237 S k θ αf X x0)
    (hp : H02311 αf) (hi : ∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (j : Fin d) (b : ℝ → ℝ) (hb : Measurable b)
    (hbi : ∀ a c, IntervalIntegrable b volume a c) (T : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, (∫ u in (0 : ℝ)..T, b u * (X (Real.toNNReal u) ω j : ℝ)) =
      Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T 0 * (x0 j : ℝ) +
      (∫ u in (0 : ℝ)..T, θ j * Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T u) +
      S.I (k j) (fun s ω => (αf j s * Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T s) *
        Real.sqrt (X s ω j)) T ω := by
  classical
  let R := Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T
  let β := fun u => b u * Real.exp (-θ j*u)
  let R0 := ∫ u in (0 : ℝ)..T, β u
  have hβm : Measurable β := hb.mul (by fun_prop)
  have hβi : ∀ t : ℝ, IntervalIntegrable β volume 0 t := fun t =>
    (hbi 0 t).mul_continuousOn (by fun_prop)
  have hR (s : ℝ) : R s = Real.exp (θ j*s) * weightAC β R0 s := R_eq02313 (θ j) b T s hbi
  have hRreg := backwardWeightRegularity (θ j) b T hbi
  have hU : U4 S.ℱ S.μ (fun s ω => (αf j s * R s) * Real.sqrt (X s ω j)) :=
    (fieldsCoefficient d Ω mΩ S k θ αf X x0 h hp hi hsq j _
      ((h.2.2.2.2.1 j).mul hRreg.2.1)
      (bound_mul023 _ _ (h.2.2.2.2.2.1 j) hRreg.2.2) T).1
  obtain ⟨hU4,hae⟩ := S.ito_formula (d+1) (xext x0 R0) (H02313 S k αf X) (K02313 θ X β)
    (f02313 (θ j) j) (H02313_U4 S k αf X h.2.2.2.2.2.2.2.2.1)
    (K02313_drift S θ X β h.2.2.2.2.2.2.2.2.2.1 hβm hβi) (f02313_contDiff _ _)
  have hdfae := driverForm02313 S k θ αf X x0 h β R0
  have hz : ∀ᵐ ω ∂S.μ, ∀ k' : Fin S.m, ∀ t, S.I k' (fun _ _ => (0 : ℝ)) t ω = 0 :=
    ae_all_iff.2 fun k' => zero_integral S k'
  have hint : ∀ᵐ ω ∂S.μ, ∀ t, S.I (k j) (fun (s : ℝ≥0) ω => dX (f02313 (θ j) j)
      ((s : ℝ), driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) s ω)
        (Fin.castSucc j) * H02313 S k αf X (Fin.castSucc j) (k j) s ω) t ω =
      S.I (k j) (fun s ω => (αf j s * R s) * Real.sqrt (X s ω j)) t ω := by
    refine int_congr_ae S (k j) _ _ (hU4 (Fin.castSucc j) (k j)) hU ?_
    filter_upwards [hdfae] with ω hdf s
    rw [f02313_dX, hdf s, ite_eq_left rfl, Fin.snoc_last, hR]
    simp only [H02313, Fin.snoc_castSucc, Hpw, ite_true]
    ring
  filter_upwards [hae,hdfae,hz,hint] with ω hω hdf hz hint
  have hIto := hω T
  have hsum : (∑ i, ∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (f02313 (θ j) j)
      ((s : ℝ), driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) s ω) i *
        H02313 S k αf X i k' s ω) T ω) =
      S.I (k j) (fun s ω => (αf j s * R s) * Real.sqrt (X s ω j)) T ω := by
    rw [Fin.sum_univ_castSucc]
    have hlast : (∑ k', S.I k' (fun (s : ℝ≥0) ω => dX (f02313 (θ j) j)
        ((s : ℝ), driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) s ω)
          (Fin.last d) * H02313 S k αf X (Fin.last d) k' s ω) T ω) = 0 := by
      simp only [H02313, Fin.snoc_last, mul_zero]
      exact Finset.sum_eq_zero fun k' _ => hz k' T
    rw [hlast, add_zero, Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single (k j)]
      · exact hint T
      · intro k' _ hk'
        simp only [H02313, Fin.snoc_castSucc, Hpw, ite_eq_right hk', mul_zero]
        exact hz k' T
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro a _ haj
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp only [f02313_dX, ite_eq_right (Fin.castSucc_inj.not.mpr haj), ite_eq_right (Fin.castSucc_ne_last a),
        mul_zero, zero_mul]
      exact hz k' T
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [hsum] at hIto
  have hdrift : (∫ s in (0 : ℝ)..T, (dT (f02313 (θ j) j)
      (s, driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) (Real.toNNReal s) ω) +
      ∑ i, dX (f02313 (θ j) j)
        (s, driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) (Real.toNNReal s) ω) i *
          K02313 θ X β i (Real.toNNReal s) ω +
      (1/2 : ℝ) * ∑ i, ∑ i', ∑ k', ∑ l', dXX (f02313 (θ j) j)
        (s, driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) (Real.toNNReal s) ω) i i' *
          H02313 S k αf X i k' (Real.toNNReal s) ω *
          H02313 S k αf X i' l' (Real.toNNReal s) ω * S.c k' l' (Real.toNNReal s))) =
      (∫ u in (0 : ℝ)..T, θ j * R u) - (∫ u in (0 : ℝ)..T, b u * (X (Real.toNNReal u) ω j : ℝ)) := by
    have hiR : IntervalIntegrable (fun u => θ j * R u) volume 0 T :=
      (hRreg.1.const_mul (θ j)).intervalIntegrable 0 T
    have hiX : IntervalIntegrable (fun u => b u * (X (Real.toNNReal u) ω j : ℝ)) volume 0 T :=
      (hbi 0 T).mul_continuousOn ((h.2.2.1 ω j).comp continuous_real_toNNReal).continuousOn
    rw [← intervalIntegral.integral_sub hiR hiX]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le T.coe_nonneg] at hs
    dsimp only
    rw [hdf, f02313_dT, quad02313 S k αf X h.1, Fin.sum_univ_castSucc]
    simp only [f02313_dX, K02313, Fin.snoc_castSucc, Fin.snoc_last]
    have hsum' : (∑ i : Fin d, (Real.exp (θ j*s) *
        (if Fin.castSucc i = Fin.castSucc j then weightAC β R0 (Real.toNNReal s)
        else if Fin.castSucc i = Fin.last d then (X (Real.toNNReal s) ω j : ℝ) else 0)) *
          Kdrv θ X i (Real.toNNReal s) ω) =
      Real.exp (θ j*s) * weightAC β R0 (Real.toNNReal s) * Kdrv θ X j (Real.toNNReal s) ω := by
      simp only [Fin.castSucc_ne_last, ite_false, Fin.castSucc_inj]
      simp [Finset.sum_ite_eq', mul_ite]
    rw [hsum']
    simp only [(Fin.castSucc_ne_last j).symm, ite_false, ite_true, Kdrv]
    rw [hR s, Real.coe_toNNReal s hs.1]
    have hexp : Real.exp (θ j*s) * Real.exp (-θ j*s) = 1 := by
      rw [← Real.exp_add, show θ j*s + -θ j*s = 0 by ring, Real.exp_zero]
    dsimp only [β]
    nlinarith [congrArg (fun z => z * (b s * (X (Real.toNNReal s) ω j : ℝ))) hexp]
  rw [hdrift] at hIto
  have hL : f02313 (θ j) j ((T : ℝ),
      driverForm S.I (xext x0 R0) (H02313 S k αf X) (K02313 θ X β) T ω) = 0 := by
    rw [hdf]
    simp only [f02313, fpair, Fin.snoc_castSucc, Fin.snoc_last]
    calc Real.exp (θ j*T) * ((X T ω j : ℝ) * weightAC β R0 T) = R T * (X T ω j : ℝ) := by rw [hR]; ring
      _ = 0 := by simp [R, Standalone.StochasticMeetingVariance.R]
  have h0 : f02313 (θ j) j (0, xext x0 R0) = R 0 * (x0 j : ℝ) := by
    simp [f02313, fpair, xext, hR, weightAC, mul_comm]
  rw [hL,h0] at hIto
  change _ = R 0 * (x0 j : ℝ) + (∫ u in (0 : ℝ)..T, θ j*R u) + _
  linarith

lemma fieldsCentered023 {m : ℕ} (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ)
    (αf : Fin d → ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0)
    (h : H0237 S k θ αf X x0) (hp : H02311 αf)
    (hi : ∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ≥0) (n : Fin m)
    (hg : ∀ j, Measurable (g n j))
    (hgb : ∀ j (U : ℝ≥0), ∃ C, ∀ s : ℝ≥0, s ≤ U → |g n j s| ≤ C)
    (hb : ∀ j, Measurable (b n j)) (hbi : ∀ j a c, IntervalIntegrable (b n j) volume a c)
    (t : ℝ≥0) (htT : t ≤ T n) :
    Integrable (Yactual S kw X g b (fun n => (T n : ℝ)) n) S.μ ∧
    Yactual S kw X g b (fun n => (T n : ℝ)) n -
      S.μ[Yactual S kw X g b (fun n => (T n : ℝ)) n | S.ℱ t] =ᵐ[S.μ]
      fun ω => ∑ j, Z02312 S k kw αf X (fun j s => g n j s)
        (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
        (T n) t j ω := by
  let R := fun j => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n)
  let D := fun j => R j 0 * (x0 j : ℝ) + ∫ u in (0 : ℝ)..T n, θ j * R j u
  set Hw : Fin d → ℝ≥0 → Ω → ℝ := fun j s ω => g n j s * Real.sqrt (X s ω j) with hHw
  set Hu : Fin d → ℝ≥0 → Ω → ℝ := fun j s ω => (αf j s * R j s) * Real.sqrt (X s ω j) with hHu
  have hU5w : ∀ j, U5 S.ℱ S.μ (Hw j) (T n) := fun j =>
    fieldsCoefficient d Ω mΩ S k θ αf X x0 h hp hi hsq j (fun s => g n j s)
      ((hg j).comp NNReal.continuous_coe.measurable) (hgb j) (T n)
  have hU5u : ∀ j, U5 S.ℱ S.μ (Hu j) (T n) := by
    intro j
    have hRreg := backwardWeightRegularity (θ j) (b n j) (T n) (hbi j)
    exact fieldsCoefficient d Ω mΩ S k θ αf X x0 h hp hi hsq j (fun s => αf j s * R j s)
      ((h.2.2.2.2.1 j).mul hRreg.2.1) (bound_mul023 _ _ (h.2.2.2.2.2.1 j) hRreg.2.2) (T n)
  have hprod : ∀ j, ∀ᵐ ω ∂S.μ, (∫ u in (0 : ℝ)..T n, b n j u * (X (Real.toNNReal u) ω j : ℝ)) =
      D j + S.I (k j) (Hu j) (T n) ω := fun j =>
    productTerminal023 S k θ αf X x0 h hp hi hsq j (b n j) (hb j) (hbi j) (T n)
  have hall : ∀ᵐ ω ∂S.μ, ∀ j, (∫ u in (0 : ℝ)..T n, b n j u * (X (Real.toNNReal u) ω j : ℝ)) =
      D j + S.I (k j) (Hu j) (T n) ω := ae_all_iff.2 hprod
  -- decomposition Y = A + Z
  set A : Fin d → Ω → ℝ := fun j ω => D j + S.I (k j) (Hu j) t ω +
    S.I (kw j) (Hw j) t ω with hA
  set Z : Fin d → Ω → ℝ := fun j => twoDriverIncrement S (kw j) (k j) (Hw j) (Hu j)
    (T n) t with hZ
  have hY : Yactual S kw X g b (fun n => (T n : ℝ)) n =ᵐ[S.μ] fun ω => ∑ j, (A j ω + Z j ω) := by
    filter_upwards [hall] with ω hω
    simp only [Yactual, hA, hZ, twoDriverIncrement, Real.toNNReal_coe, hHw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω j]
    ring
  have hL2 : ∀ (k' : Fin S.m) (H : ℝ≥0 → Ω → ℝ), U5 S.ℱ S.μ H (T n) →
      ∀ u, u ≤ (T n) → Integrable (S.I k' H u) S.μ := fun k' H hH u hu =>
    ((S.int_martingale k' H _ hH).2 u hu).integrable one_le_two
  have hAint : ∀ j, Integrable (A j) S.μ := fun j =>
    ((integrable_const _).add (hL2 (k j) (Hu j) (hU5u j) _ htT)).add (hL2 (kw j) (Hw j) (hU5w j) _ htT)
  have hZint : ∀ j, Integrable (Z j) S.μ := fun j =>
    ((hL2 (kw j) (Hw j) (hU5w j) _ le_rfl).sub (hL2 (kw j) (Hw j) (hU5w j) _ htT)).add
      ((hL2 (k j) (Hu j) (hU5u j) _ le_rfl).sub (hL2 (k j) (Hu j) (hU5u j) _ htT))
  have hYint : Integrable (Yactual S kw X g b (fun n => (T n : ℝ)) n) S.μ :=
    (integrable_finsetSum Finset.univ fun j _ => (hAint j).add (hZint j)).congr hY.symm
  refine ⟨hYint, ?_⟩
  -- conditional expectations
  have hAcond : ∀ j, S.μ[A j | S.ℱ t] = A j := fun j =>
    condExp_of_stronglyMeasurable (S.ℱ.le _)
      ((stronglyMeasurable_const.add (S.int_adapted _ _ (hU5u j).1 _).stronglyMeasurable).add
        (S.int_adapted _ _ (hU5w j).1 _).stronglyMeasurable) (hAint j)
  have hZcond : ∀ j, S.μ[Z j | S.ℱ t] =ᵐ[S.μ] 0 := by
    intro j
    have h1 := increment_condExp_zero S (kw j) (Hw j) _ _ htT (hU5w j)
    have h2 := increment_condExp_zero S (k j) (Hu j) _ _ htT (hU5u j)
    have h := condExp_add (μ := S.μ) ((hL2 (kw j) (Hw j) (hU5w j) _ le_rfl).sub (hL2 (kw j) (Hw j) (hU5w j) _ htT))
      ((hL2 (k j) (Hu j) (hU5u j) _ le_rfl).sub (hL2 (k j) (Hu j) (hU5u j) _ htT)) (S.ℱ t)
    have h' : S.μ[Z j | S.ℱ t] =ᵐ[S.μ]
        S.μ[fun ω => S.I (kw j) (Hw j) (T n) ω - S.I (kw j) (Hw j) t ω
          | S.ℱ t] +
        S.μ[fun ω => S.I (k j) (Hu j) (T n) ω - S.I (k j) (Hu j) t ω
          | S.ℱ t] := h
    filter_upwards [h', h1, h2] with ω h' h1 h2
    rw [h', Pi.add_apply]
    have h1' : (S.μ[fun ω => S.I (kw j) (Hw j) (T n) ω -
        S.I (kw j) (Hw j) t ω | S.ℱ t]) ω = 0 := h1
    have h2' : (S.μ[fun ω => S.I (k j) (Hu j) (T n) ω -
        S.I (k j) (Hu j) t ω | S.ℱ t]) ω = 0 := h2
    rw [h1', h2', add_zero]
    rfl
  have hsum := condExp_finsum S (fun j ω => A j ω + Z j ω) t
    fun j => (hAint j).add (hZint j)
  have hterm : ∀ j, S.μ[fun ω => A j ω + Z j ω | S.ℱ t] =ᵐ[S.μ] A j := by
    intro j
    have h := condExp_add (μ := S.μ) (hAint j) (hZint j) (S.ℱ t)
    have h' : S.μ[fun ω => A j ω + Z j ω | S.ℱ t] =ᵐ[S.μ]
        S.μ[A j | S.ℱ t] + S.μ[Z j | S.ℱ t] := h
    filter_upwards [h', hZcond j] with ω h' hz
    rw [h', Pi.add_apply, hAcond j]
    have hz' : (S.μ[Z j | S.ℱ t]) ω = 0 := hz
    rw [hz', add_zero]
  have hterms : ∀ᵐ ω ∂S.μ, ∀ j, (S.μ[fun ω => A j ω + Z j ω | S.ℱ t]) ω = A j ω :=
    ae_all_iff.2 hterm
  have hcondY : S.μ[Yactual S kw X g b (fun n => (T n : ℝ)) n | S.ℱ t] =ᵐ[S.μ] fun ω => ∑ j, A j ω := by
    refine (condExp_congr_ae hY).trans ?_
    filter_upwards [hsum, hterms] with ω h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  filter_upwards [hY, hcondY] with ω hY hcondY
  rw [Pi.sub_apply, hY, hcondY, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    change (A j ω + Z j ω) - A j ω = Z j ω
    ring


lemma productTerminal : productTerminalStatement := by
  intro d Ω mΩ S k θ αf X x0 h hp hi hsq j b hb hbi T
  exact productTerminal023 S k θ αf X x0 h hp hi hsq j b hb hbi T

lemma fieldsCentered : fieldsCenteredStatement := by
  intro m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b T n hg hgb hb hbi t ht
  exact fieldsCentered023 S k kw θ αf X x0 h hp hi hsq g b T n hg hgb hb hbi t ht

lemma fieldsConstructedMoments : fieldsConstructedMomentsStatement := by
  intro m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc T t ht
  let R := fun n j => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n)
  have hRreg (n : Fin m) (j : Fin d) := backwardWeightRegularity (θ j) (b n j) (T n) (hc.2.2.2.1 n j)
  have hcen (n : Fin m) := (fieldsCentered m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b T n
    (hc.1 n) (hc.2.1 n) (hc.2.2.1 n) (hc.2.2.2.1 n) t (ht n)).2
  have hm := fieldsMomentAssembly m d Ω mΩ S k θ αf X x0 h hp hi hsq kw
    (fun n j s => g n j s) (fun n j s => R n j s) (fun j s => ρ j s)
    (fun n j => (hc.1 n j).comp NNReal.continuous_coe.measurable)
    (fun n j => (hRreg n j).2.1) hc.2.1 (fun n j => (hRreg n j).2.2)
    hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 T t ht
    (fun n => Yactual S kw X g b (fun n => (T n : ℝ)) n) hcen
  let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
    (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) (fun n => (T n : ℝ))
  have he (n : Fin m) (j : Fin d) (u : ℝ) (hu : 0 ≤ u) :
      Standalone.StochasticMeetingVariance.F (g n j (Real.toNNReal u)) (ρ j (Real.toNNReal u))
        (αf j (Real.toNNReal u)) (R n j (Real.toNNReal u)) = K n j u := by
    simp only [K, R, Standalone.StochasticMeetingVariance.kernel0136, Real.coe_toNNReal u hu]
  have hu0 (n : Fin m) (u : ℝ) (hu : u ∈ Set.uIcc (t : ℝ) (T n)) : 0 ≤ u := by
    rw [Set.uIcc_of_le (show (t : ℝ) ≤ T n from by exact_mod_cast ht n)] at hu
    exact t.coe_nonneg.trans hu.1
  refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_, ?_, ?_⟩
  · intro n j
    refine (hm.2.2.2.2.1 n j).trans (ae_of_all _ fun ω => ?_)
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [he n j u (hu0 n u hu)]
  · intro n j
    exact (hm.2.2.2.2.2.1 n j).congr_uIoo fun u hu => he n j u (hu0 n u ⟨hu.1.le,hu.2.le⟩)
  · intro n j
    apply (hm.2.2.2.2.2.2 n j).congr_uIoo
    intro u hu
    dsimp only
    rw [he n j u (hu0 n u ⟨hu.1.le,hu.2.le⟩)]

lemma fieldsConstructedVariance : fieldsConstructedVarianceStatement := by
  intro m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc T t ht ps hps hs hcoef
  have hm := fieldsConstructedMoments m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc T t ht
  have hK := Novel.StochasticMeetingVarianceProof.full_kernel_nonneg g b ρ
    (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) (fun n => (T n : ℝ))
    hc.2.2.2.2.2.2.2.2
  have hv := fieldsMeetingVariance d Ω mΩ S k θ αf X x0 h t ps hps hs hcoef m
    (fun n => Yactual S kw X g b (fun n => (T n : ℝ)) n)
    (fun n j => Z02312 S k kw αf X (fun j s => g n j s)
      (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s) (T n) t j)
    (fun n j => I02312 αf X (fun j s => g n j s)
      (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
      (fun j s => ρ j s) (T n) t j)
    (Standalone.StochasticMeetingVariance.kernel0136 g b ρ (fun j s => αf j (Real.toNNReal s))
      (fun j _ => θ j) (fun n => (T n : ℝ))) (fun n => (T n : ℝ))
    (fun n => by exact_mod_cast ht n) hK (by simpa only [filtR, stateR, Real.toNNReal_coe] using hm)
  simpa only [filtR, stateR, Real.toNNReal_coe] using hv

lemma fieldsConstructedConditionalVariance : fieldsConstructedConditionalVarianceStatement := by
  intro m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc T t ht ps hps hs hcoef
  have hm := fieldsConstructedMoments m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc T t ht
  have hK := Novel.StochasticMeetingVarianceProof.full_kernel_nonneg g b ρ
    (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) (fun n => (T n : ℝ))
    hc.2.2.2.2.2.2.2.2
  have hv := fieldsConditionalMeetingVariance d Ω mΩ S k θ αf X x0 h t ps hps hs hcoef m
    (fun n => Yactual S kw X g b (fun n => (T n : ℝ)) n)
    (fun n j => Z02312 S k kw αf X (fun j s => g n j s)
      (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s) (T n) t j)
    (fun n j => I02312 αf X (fun j s => g n j s)
      (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
      (fun j s => ρ j s) (T n) t j)
    (Standalone.StochasticMeetingVariance.kernel0136 g b ρ (fun j s => αf j (Real.toNNReal s))
      (fun j _ => θ j) (fun n => (T n : ℝ))) (fun n => (T n : ℝ))
    (fun n => by exact_mod_cast ht n) hK (by simpa only [filtR, stateR, Real.toNNReal_coe] using hm)
  simpa only [filtR, stateR, Real.toNNReal_coe] using hv

end Centered023

/-! ### The variance of the source short-rate jumps -/

section Source023
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.ZeroMeanReversionVarianceSupport
open Novel.ZeroMeanReversionUpstreamBridgeProof
open scoped NNReal ENNReal Topology

lemma fieldsShortRateJump : fieldsShortRateJumpStatement := by
  intro N d Ω mΩ S k kw θ αf X x0 h hp hi hsq T a lam γ c hc
  have hT : StrictMono (fun n => (T n : ℝ)) := fun i j hij => by exact_mod_cast hc.1 hij
  have hTpos : ∀ n, 0 < (T n : ℝ) := fun n => by exact_mod_cast hc.2.1 n
  have hU4 : ∀ j (q : ℕ), U4 S.ℱ S.μ (loadInt (fun n => (T n : ℝ)) a lam γ X j q) := by
    intro j q
    obtain ⟨hKm,hKb⟩ := loadInt_coefficient (fun n => (T n : ℝ)) a lam γ
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 j q
    exact (fieldsCoefficient d Ω mΩ S k θ αf X x0 h hp hi hsq j _ hKm hKb 0).1
  have hout := shortRateJump_core S kw X (fun j => ae_of_all _ fun ω => h.2.2.1 ω j)
    (fun n => (T n : ℝ)) a lam γ c hT hTpos hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 hU4
  simpa only [Real.toNNReal_coe] using hout

lemma sourceCoefficients023 {N m d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (hc : H02315 T a lam) (ρ : Fin d → ℝ → ℝ)
    (hρ : ∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1)
    (hcww : ∀ j s, S.c (kw j) (kw j) s = 1) (hcwu : ∀ j s, S.c (kw j) (k j) s = ρ j s)
    (hcross1 : ∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0)
    (hcross2 : ∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) (rows : Fin m → Fin N) :
    H02314 S k kw (fun n => gJump (fun n => (T n : ℝ)) a lam γ (rows n))
      (fun n => bJump (fun n => (T n : ℝ)) a lam γ (rows n)) ρ := by
  refine ⟨?_, ?_, ?_, ?_, hcww, hcwu, hcross1, hcross2, hρ⟩
  · intro n j
    exact gJump_measurable _ a lam γ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2.1 (rows n) j
  · intro n j U
    obtain ⟨C,hC⟩ := gJump_bound (fun n => (T n : ℝ)) a lam γ hc.2.2.2.2.1 hc.2.2.2.2.2.2 (rows n) j 0 U
    exact ⟨C, fun s hs => hC s ⟨s.coe_nonneg, by exact_mod_cast hs⟩⟩
  · intro n j
    exact bJump_measurable _ a lam γ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2.1 (rows n) j
  · intro n j l r
    have hb := bJump_intInt_all (fun n => (T n : ℝ)) a lam γ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 (rows n) j
    exact (hb l).symm.trans (hb r)

lemma sourceJumps023 {N m d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal) (h : H0237 S k θ αf X x0)
    (hp : H02311 αf) (hi : ∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ)
    (hsq : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ)
    (hc : H02315 T a lam) (rows : Fin m → Fin N) :
    ∀ n, jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n) =ᵐ[S.μ]
      Yactual S kw X (fun n => gJump (fun n => (T n : ℝ)) a lam γ (rows n))
        (fun n => bJump (fun n => (T n : ℝ)) a lam γ (rows n)) (fun n => (T (rows n) : ℝ)) n := by
  have hsr := (fieldsShortRateJump N d Ω mΩ S k kw θ αf X x0 h hp hi hsq T a lam γ c hc).2
  intro n
  filter_upwards [hsr (rows n)] with ω hω
  obtain ⟨L,hL,hjump⟩ := hω
  unfold jumpSrc
  rw [hL.limUnder_eq, Real.toNNReal_coe]
  exact hjump

lemma fieldsSourceVariance : fieldsSourceVarianceStatement := by
  intro N m d Ω mΩ S k kw θ αf X x0 h hp hi hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V
  have hc' := sourceCoefficients023 S k kw T a lam γ hc ρ hρ hcww hcwu hc1 hc2 rows
  have hv := fieldsConstructedVariance m d Ω mΩ S k kw θ αf X x0 h hp hi hsq g b ρ hc'
    (fun n => T (rows n)) t ht ps hps hs hcoef
  have hj := sourceJumps023 S k kw θ αf X x0 h hp hi hsq T a lam γ c hc rows
  have hV : V =ᵐ[S.μ] V0150 (S.ℱ t) S.μ (fun n => Yactual S kw X g b Tr n) :=
    V0150_congr_ae (S.ℱ t) S.μ _ _ hj
  refine ⟨hj, hV.trans hv.1, ?_, ?_⟩
  · rw [Measure.map_congr hV]
    exact hv.2.1
  · rw [Measure.map_congr hV]
    exact hv.2.2

lemma fieldsSourceConditionalVariance : fieldsSourceConditionalVarianceStatement := by
  intro N m d Ω mΩ S k kw θ αf X x0 h hp hi hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V
  have hc' := sourceCoefficients023 S k kw T a lam γ hc ρ hρ hcww hcwu hc1 hc2 rows
  obtain ⟨κ,hκ,hκm,hκD,hκp⟩ := fieldsConstructedConditionalVariance m d Ω mΩ S k kw θ αf X x0
    h hp hi hsq g b ρ hc' (fun n => T (rows n)) t ht ps hps hs hcoef
  have hj := sourceJumps023 S k kw θ αf X x0 h hp hi hsq T a lam γ c hc rows
  have hV : V =ᵐ[S.μ] V0150 (S.ℱ t) S.μ (fun n => Yactual S kw X g b Tr n) :=
    V0150_congr_ae (S.ℱ t) S.μ _ _ hj
  refine ⟨κ,hκ,hκm,fun D hD => ?_,hκp⟩
  rw [Measure.map_congr (ae_restrict_of_ae hV)]
  exact hκD D hD


lemma fieldsSourceColumn : fieldsSourceColumnStatement := by
  intro N m Ω mΩ S k kw αf X h hp hi hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef hlast g b Tr K A C Y V
  have hv := fieldsSourceVariance N m 3 Ω mΩ S k kw θ0235 αf X (fun _ => 1)
    h hp hi hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef
  have hA : ∀ i j, 0 ≤ A i j := Novel.StochasticMeetingVarianceProof.A_nonneg
    (fun n => by exact_mod_cast ht n)
    (Novel.StochasticMeetingVarianceProof.full_kernel_nonneg g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr hρ)
  have hlaw : S.μ.map V = (Measure.pi (fun j => L023 (θ0235 j)
      (ps.map fun p => (p.1 j,p.2)) 1)).map (fun y => C + A.mulVec y) := hv.2.2.1
  rw [hlaw]
  apply sourcePiecewiseSupport m A C hA (fun j : Fin 3 => ps.map fun p : (Fin 3 → ℝ) × ℝ => (p.1 j,p.2))
  · intro j p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
    exact ⟨(hps q hq).1 j,(hps q hq).2⟩
  · intro j
    obtain ⟨a,h,qs,rfl,ha,hh⟩ := hlast
    exact ⟨a j,h,qs.map (fun p => (p.1 j,p.2)),rfl,ha j,hh⟩

lemma fieldsUnconditionalTransform023 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (x0 : Fin d → ℝ≥0) (h : H0237 S k θ αf X x0)
    (t : ℝ≥0) (ps : List ((Fin d → ℝ) × ℝ))
    (hps : ∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2)
    (hs : leftEnd t ps = 0) (hcoef : H0238 αf t ps)
    (l : Fin d → ℝ) (hl : ∀ j, 0 ≤ l j) :
    (∫ ω, Real.exp (-(∑ j, l j * (X t ω j : ℝ))) ∂S.μ) =
      Real.exp (-(∑ j, (piFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j) * x0 j +
        rhoFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j)))) := by
  have he := fieldsTransform d Ω mΩ S k θ αf X x0 h t ps hps (by rw [hs]) hcoef l hl
  rw [hs] at he
  have he' : S.μ[fun ω => Real.exp (-(∑ j, l j * (X t ω j : ℝ))) | S.ℱ 0] =ᵐ[S.μ]
      fun _ => Real.exp (-(∑ j, (piFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j) * x0 j +
        rhoFlow (θ j) (ps.map fun p => (p.1 j,p.2)) (l j)))) := by
    filter_upwards [he, h.2.2.2.2.2.2.1] with ω hω hxω
    simpa only [stateR, filtR, Real.toNNReal_zero, Real.toNNReal_coe, hxω] using hω
  rw [← integral_condExp (S.ℱ.le 0), integral_congr_ae he']
  simp

lemma covariance_congr023 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g f' g' : Ω → ℝ} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    ProbabilityTheory.covariance f g μ = ProbabilityTheory.covariance f' g' μ := by
  unfold ProbabilityTheory.covariance
  rw [integral_congr_ae hf, integral_congr_ae hg]
  exact integral_congr_ae (by filter_upwards [hf, hg] with ω hf hg; rw [hf,hg])

lemma stochasticPiece_map023 {d : ℕ} (ps : List ((Fin d → ℝ) × ℝ)) (j : Fin d) :
    (∃ p ∈ ps.map (fun p => (p.1 j,p.2)), 0 < p.1 ∧ 0 < p.2) ↔
      ∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2 := by
  constructor
  · rintro ⟨p,hp,h1,h2⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.1 hp
    exact ⟨r,hr,h1,h2⟩
  · rintro ⟨p,hp,h1,h2⟩
    exact ⟨(p.1 j,p.2), List.mem_map.2 ⟨p,hp,rfl⟩, h1,h2⟩

lemma stateMoments : stateMomentsStatement := by
  intro d Ω mΩ μ hμ X hm hc hi t j
  have hmj : Measurable (fun ω => (X t ω j : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (hm t))
  have h2 : MemLp (fun ω => (X t ω j : ℝ)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hmj.aestronglyMeasurable).2
    apply (hi t j).mono' (hmj.pow_const 2).aestronglyMeasurable
    filter_upwards [hc j] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb : BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => (X s ω j : ℝ)^2)) := by
      simpa using (isCompact_univ.image ((hω.comp continuous_subtype_val).pow 2)).bddAbove
    exact le_ciSup hb (⟨t, bot_le, le_rfl⟩ : Set.Icc (0 : ℝ≥0) t)
  exact ⟨h2, h2.integrable one_le_two⟩

lemma fieldsSourceCovariance : fieldsSourceCovarianceStatement := by
  classical
  intro N m d Ω mΩ S k kw θ αf X x0 h hp hsup hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V q J
  have hmom := stateMoments d Ω mΩ S.μ inferInstance X
    (fun s => (h.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h.2.2.1 ω j) hsup
  have hi := fun s j => (hmom s j).2
  have h2 := fun j => (hmom t j).1
  have hv := (fieldsSourceVariance N m d Ω mΩ S k kw θ αf X x0 h hp hi hsq
    T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef).2.1
  have hm : Measurable (X t) := (h.2.2.2.1 t).mono (S.ℱ.le t) le_rfl
  have hmR : Measurable (fun ω j => (X t ω j : ℝ)) := measurable_pi_iff.mpr fun j =>
    NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp hm)
  have hpsj (j : Fin d) (p : ℝ × ℝ) (hp : p ∈ ps.map fun p => (p.1 j,p.2)) :
      0 ≤ p.1 ∧ 0 ≤ p.2 := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.1 hp
    exact ⟨(hps r hr).1 j,(hps r hr).2⟩
  have hq (j : Fin d) : 0 ≤ q j ∧ (0 < q j ↔ j ∈ J) := by
    refine ⟨varianceFlow_nonneg _ _ _ (h.2.1 j) (x0 j).coe_nonneg (hpsj j), ?_⟩
    simpa only [J, q, Finset.mem_filter, Finset.mem_univ, true_and, stochasticPiece_map023] using
      varianceFlow_pos_iff (θ j) (x0 j) (ps.map fun p => (p.1 j,p.2))
        (h.2.1 j) (x0 j).coe_nonneg (hpsj j)
  refine ⟨hq, ?_, covariance_active A q (fun j => (hq j).1) J (fun j => (hq j).2)⟩
  have hcov := piecewise_covariance S.μ (fun ω j => (X t ω j : ℝ)) hmR
    (ae_of_all _ fun ω j => (X t ω j).coe_nonneg) h2 θ (fun j => (x0 j : ℝ))
    (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2)) h.2.1 hpsj
    (fieldsUnconditionalTransform023 S k θ αf X x0 h t ps hps hs hcoef) A C
  intro i k'
  refine (covariance_congr023 S.μ ?_ ?_).trans (hcov i k')
  · filter_upwards [hv] with ω hω
    exact congrFun hω i
  · filter_upwards [hv] with ω hω
    exact congrFun hω k'

lemma fieldsSourceConditionalCovariance : fieldsSourceConditionalCovarianceStatement := by
  classical
  intro N m d Ω mΩ S k kw θ αf X x0 h hp hsup hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V
  have hmom := stateMoments d Ω mΩ S.μ inferInstance X
    (fun s => (h.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h.2.2.1 ω j) hsup
  have hi := fun s j => (hmom s j).2
  have h2 := fun j => (hmom t j).1
  obtain ⟨ps0,hps0,hs0,hcoef0⟩ := hp t
  have hv := (fieldsSourceVariance N m d Ω mΩ S k kw θ αf X x0 h hp hi hsq
    T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht ps0 hps0 hs0 hcoef0).2.1
  have hm : Measurable (X t) := (h.2.2.2.1 t).mono (S.ℱ.le t) le_rfl
  have hpsj (j : Fin d) (p : ℝ × ℝ) (hp : p ∈ ps.map fun p => (p.1 j,p.2)) :
      0 ≤ p.1 ∧ 0 ≤ p.2 := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.1 hp
    exact ⟨(hps r hr).1 j,(hps r hr).2⟩
  have htr := fieldsTransform d Ω mΩ S k θ αf X x0 h t ps hps hs hcoef
  simp only [stateR, Real.toNNReal_coe] at htr
  obtain ⟨κ,hκ,hκm,hκD,hκcov⟩ := conditional_piecewise_covariance
    (filtR S.ℱ (leftEnd t ps)) S.μ ((filtR S.ℱ).le _) (X t) hm h2 θ
    (fun j : Fin d => ps.map fun p : (Fin d → ℝ) × ℝ => (p.1 j,p.2))
    (fun ω j => (stateR X (leftEnd t ps) ω j : ℝ))
    (fun ω j => (stateR X _ ω j).coe_nonneg) h.2.1 hpsj htr
  let := hκ
  let f : (Fin d → ℝ≥0) → Fin m → ℝ := fun y => C + A.mulVec (fun j => (y j : ℝ))
  have hf : Measurable f := by fun_prop
  refine ⟨κ.map f, ProbabilityTheory.Kernel.IsMarkovKernel.map κ hf, ?_, ?_, ?_⟩
  · intro B hB
    have he : (fun ω => (κ.map f) ω B) = fun ω => κ ω (f ⁻¹' B) :=
      funext fun ω => ProbabilityTheory.Kernel.map_apply' κ hf ω hB
    rw [he]
    exact hκm _ (hf hB)
  · intro D hD
    rw [Measure.map_congr (ae_restrict_of_ae hv)]
    change (S.μ.restrict D).map (f ∘ X t) = _
    rw [← Measure.map_map hf hm, hκD D hD, Measure.map_comp _ _ hf]
  · filter_upwards [hκcov] with ω hω
    dsimp only
    have hq (j : Fin d) :
        0 ≤ varianceFlow (θ j) (stateR X (leftEnd t ps) ω j) (ps.map fun p => (p.1 j,p.2)) ∧
        (0 < varianceFlow (θ j) (stateR X (leftEnd t ps) ω j) (ps.map fun p => (p.1 j,p.2)) ↔
          j ∈ Finset.univ.filter fun j => (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
            (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))) := by
      refine ⟨varianceFlow_nonneg _ _ _ (h.2.1 j) (stateR X _ ω j).coe_nonneg (hpsj j), ?_⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, stochasticPiece_map023] using varianceFlow_pos_iff (θ j) (stateR X (leftEnd t ps) ω j)
        (ps.map fun p => (p.1 j,p.2)) (h.2.1 j) (stateR X _ ω j).coe_nonneg (hpsj j)
    refine ⟨hq, ?_, covariance_active A _ (fun j => (hq j).1) _ (fun j => (hq j).2)⟩
    intro i k'
    rw [ProbabilityTheory.Kernel.map_apply κ hf ω,
      ProbabilityTheory.covariance_map_fun
        (measurable_pi_apply i).aestronglyMeasurable
        (measurable_pi_apply k').aestronglyMeasurable hf.aemeasurable]
    exact (hω m A C).1 i k'

lemma fieldsSourceColumnCovariance : fieldsSourceColumnCovarianceStatement := by
  classical
  intro N m Ω mΩ S k kw αf X h hp hsup hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef hlast g b Tr K A C Y V q
  have hv := fieldsSourceCovariance N m 3 Ω mΩ S k kw θ0235 αf X (fun _ => 1)
    h hp hsup hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef
  have hq (j : Fin 3) : 0 < q j := by
    apply (hv.1 j).2.2
    change j ∈ Finset.univ.filter (fun j =>
      (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧ (0 < θ0235 j ∨ 0 < (1 : ℝ)))
    obtain ⟨a,h,qs,rfl,ha,hh⟩ := hlast
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨(a,h), by simp, ha j, hh⟩, Or.inr zero_lt_one⟩
  exact ⟨hq, hv.2.1, Novel.ZeroMeanReversionVarianceSupportProof.covariance_kernel A q hq,
    Novel.ZeroMeanReversionVarianceSupportProof.covariance_rank A q hq,
    A.rank_le_width, Novel.ZeroMeanReversionVarianceSupportProof.nullity A⟩

lemma fieldsSourceMean : fieldsSourceMeanStatement := by
  intro N m d Ω mΩ S k kw θ αf X x0 h hp hsup hsq T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht
    g b Tr K A C Y V
  have hmom := stateMoments d Ω mΩ S.μ inferInstance X
    (fun s => (h.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h.2.2.1 ω j) hsup
  have hi := fun s j => (hmom s j).2
  obtain ⟨ps,hps,hs,hcoef⟩ := hp t
  have hv := (fieldsSourceVariance N m d Ω mΩ S k kw θ αf X x0 h hp hi hsq
    T a lam γ c hc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef).2.1
  have hVi (n : Fin m) : (fun ω => V ω n) =ᵐ[S.μ]
      fun ω => C n + ∑ j, A n j * (X t ω j : ℝ) := by
    filter_upwards [hv] with ω hω
    exact congrFun hω n
  have hsumint (n : Fin m) : Integrable (fun ω => ∑ j, A n j * (X t ω j : ℝ)) S.μ :=
    integrable_finsetSum Finset.univ fun j _ => (hi t j).const_mul _
  refine ⟨fun n => ((integrable_const _).add (hsumint n)).congr (hVi n).symm, ?_, ?_⟩
  · intro s hst n
    refine (condExp_congr_ae (hVi n)).trans ?_
    have hsum := condExp_finsum S (fun j ω => A n j * (X t ω j : ℝ)) s
      fun j => (hi t j).const_mul _
    have hterm (j : Fin d) : S.μ[fun ω => A n j * (X t ω j : ℝ) | S.ℱ s] =ᵐ[S.μ]
        fun ω => A n j * lflow (θ j) (X s ω j) ((t : ℝ)-s) := by
      have hmul := condExp_smul (μ := S.μ) (A n j) (fun ω => (X t ω j : ℝ)) (S.ℱ s)
      have hmean := fieldsConditionalMean d Ω mΩ S k θ αf X x0 h hp hi s t hst j
      filter_upwards [hmul,hmean] with ω hm he
      change (S.μ[(A n j) • (fun ω => (X t ω j : ℝ)) | S.ℱ s]) ω = _
      rw [hm, Pi.smul_apply, smul_eq_mul, he]
    have hadd := condExp_add (μ := S.μ) (integrable_const (C n)) (hsumint n) (S.ℱ s)
    have hcst : S.μ[fun _ : Ω => C n | S.ℱ s] = fun _ => C n :=
      condExp_of_stronglyMeasurable (S.ℱ.le s) stronglyMeasurable_const (integrable_const _)
    filter_upwards [hadd,hsum,ae_all_iff.2 hterm] with ω ha hs hj
    change (S.μ[(fun _ : Ω => C n) + (fun ω => ∑ j, A n j * (X t ω j : ℝ)) | S.ℱ s]) ω = _
    rw [ha,Pi.add_apply,hcst,hs]
    exact congrArg (fun z => C n + z) (Finset.sum_congr rfl fun j _ => hj j)
  · intro n
    rw [integral_congr_ae (hVi n), integral_add (integrable_const _) (hsumint n), integral_const]
    simp only [probReal_univ, one_smul, Matrix.mulVec, dotProduct]
    rw [integral_finsetSum Finset.univ (fun j _ => (hi t j).const_mul _)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, (fieldsStateMean d Ω mΩ S k θ αf X x0 h hp hi t j).1]

lemma coefficientU4_from_paths023 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (j : Fin d)
    (hc : ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ))
    (hsq : IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)))
    (K : ℝ≥0 → ℝ) (hm : Measurable K)
    (hb : ∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) :
    U4 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) := by
  refine ⟨Upstream.ItoCalculus.predictable_const_mul S.ℱ K hm _ hsq, ?_⟩
  intro T
  obtain ⟨C,hC⟩ := hb T
  filter_upwards [hc] with ω hω
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hω.comp continuous_real_toNNReal).continuousOn
  calc ∫⁻ s in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal ((K (Real.toNNReal s) * Real.sqrt (X (Real.toNNReal s) ω j))^2)
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (C^2) * ENNReal.ofReal M := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        refine (sq_integrand_bound K C T hC X j s hs ω).trans ?_
        apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Function.comp_apply] using hM s hs)
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top

lemma drift_from_paths023 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (θ : Fin d → ℝ) (j : Fin d)
    (hc : ∀ ω, Continuous fun t => (X t ω j : ℝ))
    (ha : ∀ t, Measurable[S.ℱ t] (X t)) :
    LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j) := by
  have hcont (ω) : Continuous (fun s => Kdrv θ X j s ω) :=
    continuous_const.mul (continuous_const.sub (hc ω))
  have hadapt : StronglyAdapted S.ℱ (Kdrv θ X j) := by
    intro t
    let : MeasurableSpace Ω := S.ℱ t
    exact (measurable_const.mul (measurable_const.sub
      (NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (ha t))))).stronglyMeasurable
  refine ⟨hadapt.isStronglyProgressive_of_continuous hcont, ?_⟩
  intro T
  apply ae_of_all
  intro ω
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    ((hcont ω).comp continuous_real_toNNReal).continuousOn
  calc ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal |Kdrv θ X j (Real.toNNReal s) ω|
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal M := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs, Function.comp_apply] using hM s hs)
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma fieldsPremises : fieldsPremisesStatement := by
  intro d Ω mΩ S k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hsq hsde
  exact ⟨hc,hθ,hcont,hadapt,hαm,hαb,hx0,hx0le,
    fun j => coefficientU4_from_paths023 S X j (ae_of_all _ fun ω => hcont ω j)
      (hsq j) (αf j) (hαm j) (hαb j),
    fun j => drift_from_paths023 S X θ j (fun ω => hcont ω j) hadapt, hsde⟩

/-- The standalone AX-09 interface is the audited field, without additional premises. -/
theorem ofUpstreamPredictability {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (P : Upstream.Predictability ℱ) : Standalone.PositiveMeanReversionSupport.Predictability ℱ :=
  ⟨P.continuous_predictable⟩

lemma continuousVersion : continuousVersionStatement := by
  intro d Ω mΩ S P X x0 hc ha
  obtain ⟨N,X',hN0,hNnull,hX'N,hX'nN,hc',ha'⟩ := continuousVersionData S X x0 hc ha
  have hae : ∀ᵐ ω ∂S.μ, ∀ t, X' t ω = X t ω := by
    filter_upwards [compl_mem_ae_iff.2 hNnull] with ω hω t
    exact hX'nN t ω hω
  refine ⟨X',hae,hc',ha',fun j => ?_⟩
  apply P.continuous_predictable
  · intro t
    let : MeasurableSpace Ω := S.ℱ t
    exact Real.continuous_sqrt.measurable.comp
      (NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (ha' t)))
  · intro ω
    exact Real.continuous_sqrt.comp (hc' ω j)

lemma fieldsVersion : fieldsVersionStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  obtain ⟨X',he,hc',ha',hsq'⟩ := continuousVersion d Ω mΩ S P X x0 hcont hadapt
  have hU' (j) := coefficientU4_from_paths023 S X' j (ae_of_all _ fun ω => hc' ω j)
    (hsq' j) (αf j) (hαm j) (hαb j)
  have hx0' : X' 0 =ᵐ[S.μ] fun _ => x0 := by
    filter_upwards [he,hx0] with ω he hx0
    exact (he 0).trans hx0
  have hsde' (j) : ∀ᵐ ω ∂S.μ, ∀ t, (X' t ω j : ℝ) =
      X' 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X' s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X' j (Real.toNNReal s) ω := by
    have hI := int_congr_ae S (k j) _ _ (hU' j) (hU j)
      (by filter_upwards [he] with ω hω s; rw [hω s])
    filter_upwards [he,hI,hsde j] with ω hω hI hsde t
    have hd : (fun s : ℝ => Kdrv θ X' j (Real.toNNReal s) ω) =
        fun s : ℝ => Kdrv θ X j (Real.toNNReal s) ω := by
      funext s
      simp only [Kdrv,hω]
    rw [hω t,hω 0,hI t,hd]
    exact hsde t
  refine ⟨X',he,fieldsPremises d Ω mΩ S k θ αf X' x0 hc hθ hc' ha' hαm hαb hx0' hx0le hsq' hsde',hsq',?_⟩
  intro t j
  apply (hsup t j).congr
  filter_upwards [he] with ω hω
  exact iSup_congr fun s => by rw [hω s]

lemma fieldsAeLaw : fieldsAeLawStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    b ps hps hb hcoef
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hlaw := fieldsLaw d Ω mΩ S k θ αf X' x0 h' b ps hps hb hcoef
  have heR (s : ℝ) : stateR X' s =ᵐ[S.μ] stateR X s := by
    filter_upwards [he] with ω hω
    exact hω (Real.toNNReal s)
  refine ⟨?_,fun hs => ?_⟩
  · obtain ⟨κ,hκ,hκm,hκD,hκlaw⟩ := hlaw.1
    refine ⟨κ,hκ,hκm,fun D hD => ?_,?_⟩
    · rw [← Measure.map_congr (ae_restrict_of_ae (heR b))]
      exact hκD D hD
    · filter_upwards [hκlaw,heR (leftEnd b ps)] with ω hω heω
      simpa only [heω] using hω
  · have heReal : (fun ω j => (stateR X' b ω j : ℝ)) =ᵐ[S.μ]
        fun ω j => (stateR X b ω j : ℝ) := by
      filter_upwards [heR b] with ω hω
      rw [hω]
    rw [← Measure.map_congr heReal]
    exact hlaw.2 hs

lemma sourceVersion : sourceVersionStatement := by
  intro N d Ω mΩ S kw T a lam γ c X X' he hU hU'
  have hI : ∀ j q, ∀ᵐ ω ∂S.μ, ∀ t,
      S.I (kw j) (loadInt T a lam γ X j q) t ω =
        S.I (kw j) (loadInt T a lam γ X' j q) t ω := by
    intro j q
    apply int_congr_ae S (kw j) _ _ (hU j q) (hU' j q)
    filter_upwards [he] with ω hω s
    simp only [loadInt,hω s]
  have hf : ∀ᵐ ω ∂S.μ, ∀ t u, forwardSrc S kw T a lam γ X c t u ω =
      forwardSrc S kw T a lam γ X' c t u ω := by
    filter_upwards [he,ae_all_iff.2 (fun j => ae_all_iff.2 (hI j))] with ω hω hI t u
    have hd : (fun s : ℝ => driftSrc T a lam γ X s u ω) =
        fun s : ℝ => driftSrc T a lam γ X' s u ω := by
      funext s
      simp only [driftSrc,hω]
    simp only [forwardSrc,hd,hI]
  have hj : ∀ᵐ ω ∂S.μ, ∀ n, jumpSrc S kw T a lam γ X c n ω =
      jumpSrc S kw T a lam γ X' c n ω := by
    filter_upwards [hf] with ω hω n
    simp only [jumpSrc,shortSrc,hω]
  refine ⟨hf,hj,fun m rows t => ?_⟩
  apply V0150_congr_ae (S.ℱ t) S.μ
  intro n
  filter_upwards [hj] with ω hω
  exact hω (rows n)

lemma fieldsSourceVersion023 {N d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : ItoCalculus Ω) (kw : Fin d → Fin S.m)
    (X X' : ℝ≥0 → Ω → Fin d → NNReal)
    (he : ∀ᵐ ω ∂S.μ, ∀ t, X t ω = X' t ω)
    (hc' : ∀ ω j, Continuous fun t => (X' t ω j : ℝ))
    (hsq' : ∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X' s ω j)))
    (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ)
    (hc : H02315 T a lam)
    (hU : ∀ j q, U4 S.ℱ S.μ (loadInt (fun n => (T n : ℝ)) a lam γ X j q)) :
    ∀ (m : ℕ) (rows : Fin m → Fin N) (t : ℝ≥0),
      V0150 (S.ℱ t) S.μ (fun n => jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)) =ᵐ[S.μ]
      V0150 (S.ℱ t) S.μ (fun n => jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X' c (rows n)) := by
  have hU' : ∀ j q, U4 S.ℱ S.μ (loadInt (fun n => (T n : ℝ)) a lam γ X' j q) := by
    intro j q
    obtain ⟨hKm,hKb⟩ := loadInt_coefficient (fun n => (T n : ℝ)) a lam γ
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 j q
    exact coefficientU4_from_paths023 S X' j (ae_of_all _ fun ω => hc' ω j)
      (hsq' j) _ hKm hKb
  exact (sourceVersion N d Ω mΩ S kw (fun n => (T n : ℝ)) a lam γ c X X' he hU hU').2.2

lemma fieldsSourceAeVariance : fieldsSourceAeVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef g b Tr K A C Y V
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hmom := stateMoments d Ω mΩ S.μ inferInstance X'
    (fun s => (h'.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h'.2.2.1 ω j) hsup'
  have hv := fieldsSourceVariance N m d Ω mΩ S k kw θ αf X' x0 h' hp
    (fun s j => (hmom s j).2) hsq' T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2
    rows t ht ps hps hs hcoef
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  refine ⟨hV.trans (hv.2.1.trans ?_),?_,?_⟩
  · filter_upwards [he] with ω hω
    rw [hω t]
  · rw [Measure.map_congr hV]
    exact hv.2.2.1
  · rw [Measure.map_congr hV]
    exact hv.2.2.2

lemma fieldsSourceAeConditionalVariance : fieldsSourceAeConditionalVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef g b Tr K A C Y V
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hmom := stateMoments d Ω mΩ S.μ inferInstance X'
    (fun s => (h'.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h'.2.2.1 ω j) hsup'
  obtain ⟨κ,hκ,hκm,hκD,hκp⟩ := fieldsSourceConditionalVariance N m d Ω mΩ S k kw θ αf X' x0 h' hp
    (fun s j => (hmom s j).2) hsq' T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2
    rows t ht ps hps hs hcoef
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  refine ⟨κ,hκ,hκm,fun D hD => ?_,?_⟩
  · rw [Measure.map_congr (ae_restrict_of_ae hV)]
    exact hκD D hD
  · filter_upwards [hκp,he] with ω hω heω
    simpa only [stateR,heω] using hω

lemma fieldsSourceAeCovariance : fieldsSourceAeCovarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V q J
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hout := fieldsSourceCovariance N m d Ω mΩ S k kw θ αf X' x0 h' hp hsup' hsq'
    T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  refine ⟨hout.1,fun i j => ?_,hout.2.2⟩
  exact (covariance_congr023 S.μ
    (by filter_upwards [hV] with ω hω; exact congrFun hω i)
    (by filter_upwards [hV] with ω hω; exact congrFun hω j)).trans (hout.2.1 i j)

lemma fieldsSourceAeConditionalCovariance : fieldsSourceAeConditionalCovarianceStatement := by
  classical
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef g b Tr K A C Y V
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  obtain ⟨κ,hκ,hκm,hκD,hκp⟩ := fieldsSourceConditionalCovariance N m d Ω mΩ S k kw θ αf X' x0 h' hp hsup' hsq'
    T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  refine ⟨κ,hκ,hκm,fun D hD => ?_,?_⟩
  · rw [Measure.map_congr (ae_restrict_of_ae hV)]
    exact hκD D hD
  · filter_upwards [hκp,he] with ω hω heω
    have hJ : (Finset.univ.filter fun j =>
        (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
          (0 < θ j ∨ 0 < (stateR X' (leftEnd t ps) ω j : ℝ))) =
        Finset.univ.filter (fun j =>
        (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
          (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))) := by
      apply Finset.filter_congr
      intro j _
      simp only [stateR, heω]
    dsimp only at hω ⊢
    rw [hJ] at hω
    simpa only [stateR,heω] using hω

lemma fieldsSourceAeMean : fieldsSourceAeMeanStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
    g b Tr K A C Y V
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hout := fieldsSourceMean N m d Ω mΩ S k kw θ αf X' x0 h' hp hsup' hsq'
    T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2 rows t ht
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  have hVn (n : Fin m) : (fun ω => V ω n) =ᵐ[S.μ]
      fun ω => V0150 (S.ℱ t) S.μ
        (fun n => jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X' c (rows n)) ω n := by
    filter_upwards [hV] with ω hω
    exact congrFun hω n
  refine ⟨fun n => (hout.1 n).congr (hVn n).symm,fun s hst n => ?_,fun n => ?_⟩
  · refine (condExp_congr_ae (hVn n)).trans ((hout.2.1 s hst n).trans ?_)
    filter_upwards [he] with ω hω
    rw [hω s]
  · exact (integral_congr_ae (hVn n)).trans (hout.2.2 n)

lemma fieldsSourceAeColumn : fieldsSourceAeColumnStatement := by
  intro N m Ω mΩ S P k kw αf X hc hcont hadapt hαm hαb hx0 hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef hlast g b Tr K A C Y V
  have hθ : ∀ j, 0 ≤ θ0235 j := by intro j; fin_cases j <;> norm_num [θ0235]
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion 3 Ω mΩ S P k θ0235 αf X (fun _ => 1)
    hc hθ hcont hadapt hαm hαb hx0 (fun _ => le_rfl) hU hsde hsup
  have hmom := stateMoments 3 Ω mΩ S.μ inferInstance X'
    (fun s => (h'.2.2.2.1 s).mono (S.ℱ.le s) le_rfl)
    (fun j => ae_of_all _ fun ω => h'.2.2.1 ω j) hsup'
  have hout := fieldsSourceColumn N m Ω mΩ S k kw αf X' h' hp (fun s j => (hmom s j).2) hsq'
    T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef hlast
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  rw [Measure.map_congr hV]
  exact hout

lemma fieldsSourceAeColumnCovariance : fieldsSourceAeColumnCovarianceStatement := by
  intro N m Ω mΩ S P k kw αf X hc hcont hadapt hαm hαb hx0 hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
    ps hps hs hcoef hlast g b Tr K A C Y V q
  have hθ : ∀ j, 0 ≤ θ0235 j := by intro j; fin_cases j <;> norm_num [θ0235]
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion 3 Ω mΩ S P k θ0235 αf X (fun _ => 1)
    hc hθ hcont hadapt hαm hαb hx0 (fun _ => le_rfl) hU hsde hsup
  have hout := fieldsSourceColumnCovariance N m Ω mΩ S k kw αf X' h' hp hsup' hsq'
    T a lam γ c hcoefSrc ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps hs hcoef hlast
  have hV := fieldsSourceVersion023 S kw X X'
    (by filter_upwards [he] with ω hω s; exact (hω s).symm)
    h'.2.2.1 hsq' T a lam γ c hcoefSrc hload m rows t
  refine ⟨hout.1,fun i j => ?_,hout.2.2⟩
  exact (covariance_congr023 S.μ
    (by filter_upwards [hV] with ω hω; exact congrFun hω i)
    (by filter_upwards [hV] with ω hω; exact congrFun hω j)).trans (hout.2.1 i j)


lemma fieldsAeTransform : fieldsAeTransformStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    b ps hps hb hcoef l hl
  obtain ⟨X',he,h',hsq',hsup'⟩ := fieldsVersion d Ω mΩ S P k θ αf X x0
    hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
  have hout := fieldsTransform d Ω mΩ S k θ αf X' x0 h' b ps hps hb hcoef l hl
  have heexp : (fun ω => Real.exp (-(∑ j, l j * stateR X b ω j))) =ᵐ[S.μ]
      fun ω => Real.exp (-(∑ j, l j * stateR X' b ω j)) := by
    filter_upwards [he] with ω hω
    simp only [stateR,hω]
  refine (condExp_congr_ae heexp).trans (hout.trans ?_)
  filter_upwards [he] with ω hω
  simp only [stateR,hω]

lemma partition_of_breakpoints023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ) (S : Finset ℝ) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ u ∈ S, u ∈ Set.Ioo a b) →
    (∀ l r : ℝ, a ≤ l → r ≤ b → l < r → (∀ u ∈ S, u ∉ Set.Ioo l r) →
      ∃ c : Fin d → ℝ, (∀ j, 0 ≤ c j) ∧
        ∀ j (s : ℝ≥0), l < s → (s : ℝ) < r → αf j s = c j) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 < p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro a b ha hab hS hc
    by_cases he : a = b
    · subst b
      exact ⟨[],by simp,by simp [leftEnd],by trivial⟩
    · obtain ⟨c,hc0,hcα⟩ := hc a b le_rfl le_rfl (lt_of_le_of_ne hab he) (by simp)
      refine ⟨[(c,b-a)],?_,?_,?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst p
        exact ⟨hc0,sub_pos.2 (lt_of_le_of_ne hab he)⟩
      · simp [leftEnd]
      · simpa only [H0238,sub_sub_cancel,true_and,and_true] using hcα
  | insert x S hx ih =>
    intro a b ha hab hS hc
    have hax : a < x := (hS x (Finset.mem_insert_self _ _)).1
    have hxb : x < b := (hS x (Finset.mem_insert_self _ _)).2
    obtain ⟨ps,hps,he,hα⟩ := ih a x ha hax.le
      (fun u hu => ⟨(hS u (Finset.mem_insert_of_mem hu)).1,hx u hu⟩) (by
        intro l r hal hrx hlr hnone
        apply hc l r hal (hrx.trans hxb.le) hlr
        intro u hu huu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · linarith [huu.2]
        · exact hnone u hu huu)
    obtain ⟨c,hc0,hcα⟩ := hc x b hax.le le_rfl hxb (by
      intro u hu huu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact (lt_irrefl _) huu.1
      · exact (not_lt_of_gt (hx u hu)) huu.1)
    refine ⟨(c,b-x)::ps,?_,?_,?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hc0,sub_pos.2 hxb⟩
      · exact hps p hp
    · rw [leftEnd_cons]
      simpa only [sub_sub_cancel] using he
    · simpa only [H0238,sub_sub_cancel] using And.intro hcα hα

lemma commonPartition023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (hα0 : ∀ j t, 0 ≤ αf j t) (hf : H02316 αf)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 < p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  choose B hB using fun j => hf j b.toNNReal
  let S := (Finset.univ.biUnion B).filter fun u => a < u ∧ u < b
  apply partition_of_breakpoints023 αf S a b ha hab
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro l r hal hrb hlr hn
    have hc : ∀ j, ∃ c : ℝ, ∀ s : ℝ≥0, l < s → (s : ℝ) < r → αf j s = c := by
      intro j
      apply hB j l r (ha.trans hal) (by simpa only [Real.coe_toNNReal b hb] using hrb) hlr
      intro u hu huu
      apply hn u
      · exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨j,Finset.mem_univ _,hu⟩,
          lt_of_le_of_lt hal huu.1,lt_of_lt_of_le huu.2 hrb⟩
      · exact huu
    choose c hc using hc
    refine ⟨c,fun j => ?_,hc⟩
    let s : ℝ≥0 := ⟨(l+r)/2,by linarith⟩
    have hs1 : l < (s : ℝ) := by change l < (l+r)/2; linarith
    have hs2 : (s : ℝ) < r := by change (l+r)/2 < r; linarith
    rw [← hc j s hs1 hs2]
    exact hα0 j s

lemma finitePieces023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (hα0 : ∀ j t, 0 ≤ αf j t) (hf : H02316 αf) : H02311 αf := by
  intro t
  obtain ⟨ps,hps,he,hc⟩ := commonPartition023 αf hα0 hf 0 t le_rfl t.coe_nonneg
  exact ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hc⟩

lemma finiteLastPiece023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (hα0 : ∀ j t, 0 ≤ αf j t) (hf : H02316 αf) (t : ℝ≥0) (ht : 0 < t)
    (hlast : ∀ j, ∃ a : ℝ, a < t ∧
      ∀ s : ℝ≥0, a < s → (s : ℝ) < t → 0 < αf j s) :
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
      ∃ c h qs, ps = (c,h)::qs ∧ (∀ j, 0 < c j) ∧ 0 < h := by
  obtain ⟨ps,hps,he,hc⟩ := commonPartition023 αf hα0 hf 0 t le_rfl t.coe_nonneg
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  cases ps with
  | nil => simp only [leftEnd,List.map_nil,List.sum_nil,sub_zero] at he; linarith
  | cons p ps =>
    have hp := hps p List.mem_cons_self
    refine ⟨p::ps,fun q hq => ⟨(hps q hq).1,(hps q hq).2.le⟩,he,hc,
      p.1,p.2,ps,rfl,fun j => ?_,hp.2⟩
    obtain ⟨a,hat,ha⟩ := hlast j
    let l := max 0 (max a ((t : ℝ)-p.2))
    have hlt : l < (t : ℝ) := max_lt htR (max_lt hat (by linarith [hp.2]))
    let s : ℝ≥0 := ⟨(l+t)/2,by have := le_max_left 0 (max a ((t : ℝ)-p.2)); dsimp [l] at *; linarith⟩
    have hls : l < (s : ℝ) := by change l < (l+t)/2; linarith
    have hst : (s : ℝ) < t := by change (l+t)/2 < t; linarith
    have has : a < (s : ℝ) := lt_of_le_of_lt ((le_max_left a _).trans (le_max_right 0 _)) hls
    have hbs : (t : ℝ)-p.2 < (s : ℝ) := lt_of_le_of_lt ((le_max_right a _).trans (le_max_right 0 _)) hls
    rw [← hc.1 j s hbs hst]
    exact ha s has hst

lemma commonPartition : commonPartitionStatement := by
  intro d αf hα0 hf a b ha hab
  exact commonPartition023 αf hα0 hf a b ha hab

lemma finitePieces : finitePiecesStatement := by
  intro d αf hα0 hf
  exact finitePieces023 αf hα0 hf

lemma finiteLastPiece : finiteLastPieceStatement := by
  intro d αf hα0 hf t ht hlast
  exact finiteLastPiece023 αf hα0 hf t ht hlast

lemma coefficient_extension023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (ps : List ((Fin d → ℝ) × ℝ)) :
    ∀ (b : ℝ) (j : Fin d), H0238 αf b ps →
    ∃ g : ℝ≥0 → ℝ, Measurable g ∧ (∃ C : ℝ, ∀ s, |g s| ≤ C) ∧
      ∀ s : ℝ≥0, leftEnd b ps ≤ s → (s : ℝ) ≤ b → g s = αf j s := by
  classical
  induction ps with
  | nil =>
    intro b j hc
    refine ⟨fun _ => αf j b.toNNReal, measurable_const, ⟨|αf j b.toNNReal|,fun _ => le_rfl⟩,?_⟩
    intro s hs hb
    have he : (s : ℝ) = b := le_antisymm hb (by simpa only [leftEnd,List.map_nil,List.sum_nil,sub_zero] using hs)
    rw [← he,Real.toNNReal_coe]
  | cons p ps ih =>
    intro b j hc
    obtain ⟨g,hgm,⟨C,hC⟩,hg⟩ := ih (b-p.2) j hc.2
    let g' := fun s : ℝ≥0 => if (s : ℝ) = b then αf j b.toNNReal else
      if b-p.2 < (s : ℝ) then p.1 j else g s
    have hme : MeasurableSet {s : ℝ≥0 | (s : ℝ) = b} :=
      measurableSet_eq_fun NNReal.continuous_coe.measurable measurable_const
    have hml : MeasurableSet {s : ℝ≥0 | b-p.2 < (s : ℝ)} :=
      measurableSet_lt measurable_const NNReal.continuous_coe.measurable
    refine ⟨g',Measurable.ite hme measurable_const (Measurable.ite hml measurable_const hgm),
      ⟨max |αf j b.toNNReal| (max |p.1 j| C),?_⟩,?_⟩
    · intro s
      dsimp only [g']
      split_ifs
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (hC s).trans ((le_max_right _ _).trans (le_max_right _ _))
    · intro s hs hb
      dsimp only [g']
      split_ifs with he hl
      · rw [← he,Real.toNNReal_coe]
      · exact (hc.1 j s hl (lt_of_le_of_ne hb he)).symm
      · apply hg s
        · simpa only [leftEnd_cons] using hs
        · exact le_of_not_gt hl

lemma coefficient_regularity023 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ)
    (hα0 : ∀ j t, 0 ≤ αf j t) (hf : H02316 αf) :
    (∀ j, Measurable (αf j)) ∧
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) := by
  classical
  have hext (j) (T : ℝ≥0) : ∃ g : ℝ≥0 → ℝ, Measurable g ∧
      (∃ C : ℝ, ∀ s, |g s| ≤ C) ∧ ∀ s, s ≤ T → g s = αf j s := by
    obtain ⟨ps,hps,he,hc⟩ := finitePieces023 αf hα0 hf T
    obtain ⟨g,hgm,hgb,hg⟩ := coefficient_extension023 αf ps T j hc
    refine ⟨g,hgm,hgb,fun s hs => hg s ?_ (by exact_mod_cast hs)⟩
    rw [he]
    exact s.coe_nonneg
  refine ⟨fun j => ?_,fun j T => ?_⟩
  · choose g hgm hgb hg using fun n : ℕ => hext j n
    intro B hB
    have he : αf j ⁻¹' B = ⋃ n : ℕ, {s : ℝ≥0 | s ≤ n} ∩ g n ⁻¹' B := by
      ext s
      simp only [Set.mem_preimage,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
      constructor
      · intro hs
        obtain ⟨n,hn⟩ := exists_nat_ge s
        exact ⟨n,hn,by rw [hg n s hn]; exact hs⟩
      · rintro ⟨n,hn,hs⟩
        rwa [hg n s hn] at hs
    rw [he]
    exact MeasurableSet.iUnion fun n => measurableSet_Iic.inter (hgm n hB)
  · obtain ⟨g,hgm,⟨C,hC⟩,hg⟩ := hext j T
    exact ⟨C,fun s hs => by rw [← hg s hs]; exact hC s⟩

lemma coefficientRegularity : coefficientRegularityStatement := by
  intro d αf hα0 hf
  exact coefficient_regularity023 αf hα0 hf

lemma fieldsFiniteSourceVariance : fieldsFiniteSourceVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf 0 t le_rfl t.coe_nonneg
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsSourceAeVariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    (finitePieces023 αf hα0 hf) T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) he hcoef

lemma fieldsFiniteSourceConditionalVariance : fieldsFiniteSourceConditionalVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht a0 ha0 hat
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a0 t ha0 hat
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsSourceAeConditionalVariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    (finitePieces023 αf hα0 hf) T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha0) hcoef

lemma fieldsFiniteSourceColumn : fieldsFiniteSourceColumnStatement := by
  intro N m Ω mΩ S P k kw αf X hc hcont hadapt hx0 hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ht0 hlast
    g b Tr K A C Y V
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef,hlastps⟩ := finiteLastPiece023 αf hα0 hf t ht0 hlast
  have hp := finitePieces023 αf hα0 hf
  have hs := fieldsSourceAeColumn N m Ω mΩ S P k kw αf X hc hcont hadapt hαm hαb hx0 hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps he hcoef hlastps
  have hv := fieldsSourceAeColumnCovariance N m Ω mΩ S P k kw αf X hc hcont hadapt hαm hαb hx0 hU hsde hsup
    hp T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps hps he hcoef hlastps
  exact ⟨hs,(fun j => varianceFlow (θ0235 j) 1 (ps.map fun p => (p.1 j,p.2))),hv⟩


lemma fieldsFiniteSourceMean : fieldsFiniteSourceMeanStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  exact fieldsSourceAeMean N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    (finitePieces023 αf hα0 hf) T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht

lemma fieldsFiniteSourceCovariance : fieldsFiniteSourceCovarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf 0 t le_rfl t.coe_nonneg
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsSourceAeCovariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    (finitePieces023 αf hα0 hf) T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) he hcoef

lemma fieldsFiniteSourceConditionalCovariance : fieldsFiniteSourceConditionalCovarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup
    hf hα0 T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht a0 ha0 hat
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a0 t ha0 hat
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsSourceAeConditionalCovariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup
    (finitePieces023 αf hα0 hf) T a lam γ c hcoefSrc hload ρ hρ hcww hcwu hc1 hc2 rows t ht ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha0) hcoef



lemma continuousDomains : continuousDomainsStatement := by
  intro d Ω mΩ S P X hc ha
  have hsq (j) : IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j)) := by
    apply P.continuous_predictable
    · intro t
      let : MeasurableSpace Ω := S.ℱ t
      exact Real.continuous_sqrt.measurable.comp
        (NNReal.continuous_coe.measurable.comp ((measurable_pi_apply j).comp (ha t)))
    · intro ω
      exact Real.continuous_sqrt.comp (hc ω j)
  have hK (j) (K : ℝ≥0 → ℝ) (hm : Measurable K)
      (hb : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ s, s ≤ T → |K s| ≤ C) :
      U4 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) :=
    coefficientU4_from_paths023 S X j (ae_of_all _ fun ω => hc ω j) (hsq j) K hm hb
  refine ⟨hsq,hK,fun N T a lam γ hsrc j q => ?_⟩
  obtain ⟨hKm,hKb⟩ := loadInt_coefficient (fun n => (T n : ℝ)) a lam γ
    hsrc.2.2.1 hsrc.2.2.2.1 hsrc.2.2.2.2.2.1 hsrc.2.2.2.2.2.2 j q
  exact hK j _ hKm hKb

lemma fieldsContinuousSourceVariance : fieldsContinuousSourceVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceVariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0 hx0le
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)

lemma fieldsContinuousSourceConditionalVariance : fieldsContinuousSourceConditionalVarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceConditionalVariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0 hx0le
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)

lemma fieldsContinuousSourceColumn : fieldsContinuousSourceColumnStatement := by
  intro N m Ω mΩ S P k kw αf X hc hcont hadapt hx0 hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains 3 Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceColumn N m Ω mΩ S P k kw αf X hc
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)

lemma fieldsContinuousSourceMean : fieldsContinuousSourceMeanStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceMean N m d Ω mΩ S P k kw θ αf X x0 hc hθ
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0 hx0le
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)

lemma fieldsContinuousSourceCovariance : fieldsContinuousSourceCovarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceCovariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0 hx0le
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)

lemma fieldsContinuousSourceConditionalCovariance : fieldsContinuousSourceConditionalCovarianceStatement := by
  intro N m d Ω mΩ S P k kw θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup
    hf hα0 T a lam γ c hcoefSrc
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  exact fieldsFiniteSourceConditionalCovariance N m d Ω mΩ S P k kw θ αf X x0 hc hθ
    (fun j => ae_of_all _ fun ω => hcont ω j) hadapt hx0 hx0le
    (fun j => hD.2.1 j (αf j) (hαm j) (hαb j)) hsde hsup hf hα0 T a lam γ c hcoefSrc
    (hD.2.2 N T a lam γ hcoefSrc)


lemma fieldsContinuousTransform : fieldsContinuousTransformStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup hf hα0 a b ha hab
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  have h := fieldsPremises d Ω mΩ S k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hD.1 hsde
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a b ha hab
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsTransform d Ω mΩ S k θ αf X x0 h b ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha) hcoef

lemma fieldsContinuousLaw : fieldsContinuousLawStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hx0 hx0le hsde hsup hf hα0 a b ha hab
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  have hD := continuousDomains d Ω mΩ S P X hcont hadapt
  have h := fieldsPremises d Ω mΩ S k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hD.1 hsde
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a b ha hab
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsLaw d Ω mΩ S k θ αf X x0 h b ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha) hcoef

lemma fieldsFiniteTransform : fieldsFiniteTransformStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup hf hα0 a b ha hab
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a b ha hab
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsAeTransform d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup b ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha) hcoef

lemma fieldsFiniteLaw : fieldsFiniteLawStatement := by
  intro d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hx0 hx0le hU hsde hsup hf hα0 a b ha hab
  obtain ⟨hαm,hαb⟩ := coefficient_regularity023 αf hα0 hf
  obtain ⟨ps,hps,he,hcoef⟩ := commonPartition023 αf hα0 hf a b ha hab
  refine ⟨ps,fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩,he,hcoef,?_⟩
  exact fieldsAeLaw d Ω mΩ S P k θ αf X x0 hc hθ hcont hadapt hαm hαb hx0 hx0le hU hsde hsup b ps
    (fun p hp => ⟨(hps p hp).1,(hps p hp).2.le⟩) (by rw [he]; exact ha) hcoef

end Source023

theorem positiveMeanReversionSupport : Standalone.PositiveMeanReversionSupport.statement :=
  ⟨riccati, translatedCone, chiSquareParameter, sourceColumn, composition, atom, variance,
    generator, extension, ito023, localization023, conditionalTransform, pieceComposition,
    itoIncrement, onePiece_of_fields, independence, atomMass, mean, secondMoment, conditionalLaw, conditionalMean, conditionalVariance,
    piecewiseVariance, conditionalPiecewiseVariance, piecewiseCovariance, conditionalPiecewiseCovariance, sourceCovariance, coordinateLaw, piecewiseJointLaw,
    piecewiseImageLaw, conditionalPiecewiseLaw, sourcePiecewiseSupport, lowerEndpoint, fieldsTransform, fieldsLaw, fieldsMeetingVariance, fieldsConditionalMeetingVariance, fieldsStateMean, fieldsCoefficient,
    fieldsIncrement, fieldsKernelIsometry, backwardWeightRegularity, kernelIdentification,
    fieldsConditionalMean, fieldsWeightedIntegral, fieldsMomentAssembly, productTerminal, fieldsCentered,
    fieldsConstructedMoments, fieldsConstructedVariance, fieldsConstructedConditionalVariance,
    fieldsShortRateJump, fieldsSourceVariance, fieldsSourceConditionalVariance, fieldsSourceColumn,
    stateMoments, fieldsSourceCovariance, fieldsSourceConditionalCovariance, fieldsSourceColumnCovariance, fieldsSourceMean, fieldsPremises, continuousVersion, fieldsVersion, fieldsAeLaw, sourceVersion, fieldsSourceAeVariance, fieldsSourceAeConditionalVariance, fieldsSourceAeCovariance, fieldsSourceAeConditionalCovariance, fieldsSourceAeMean, fieldsSourceAeColumn, fieldsSourceAeColumnCovariance, fieldsAeTransform,
    commonPartition, finitePieces, finiteLastPiece, fieldsFiniteSourceVariance, fieldsFiniteSourceConditionalVariance, fieldsFiniteSourceColumn, fieldsFiniteSourceMean, fieldsFiniteSourceCovariance, fieldsFiniteSourceConditionalCovariance,
    continuousDomains, fieldsContinuousSourceVariance, fieldsContinuousSourceConditionalVariance, fieldsContinuousSourceColumn, fieldsContinuousSourceMean, fieldsContinuousSourceCovariance, fieldsContinuousSourceConditionalCovariance,
    coefficientRegularity, fieldsContinuousTransform, fieldsContinuousLaw, fieldsFiniteTransform, fieldsFiniteLaw⟩

end Novel.PositiveMeanReversionSupportProof

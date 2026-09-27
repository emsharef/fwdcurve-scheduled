import Standalone.StochasticMeetingVariance

/-! # Claim 013: full-kernel algebra and conditional variance assembly -/

open MeasureTheory ProbabilityTheory Matrix Set
open Standalone.StochasticMeetingVariance

namespace Novel.StochasticMeetingVarianceProof

lemma F_square (g ρ α r : ℝ) :
    F g ρ α r = (g + ρ * α * r) ^ 2 + (1 - ρ ^ 2) * (α * r) ^ 2 := by
  unfold F
  ring

lemma F_nonneg (g ρ α r : ℝ) (hlo : -1 ≤ ρ) (hhi : ρ ≤ 1) : 0 ≤ F g ρ α r := by
  rw [F_square]
  have hr : 0 ≤ 1 - ρ ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ρ) (by linarith : 0 ≤ 1 + ρ)]
  positivity

lemma E_pos (θ : ℝ → ℝ) (t u : ℝ) : 0 < E θ t u := Real.exp_pos _

lemma E_le_one (θ : ℝ → ℝ) {t u : ℝ} (htu : t ≤ u) (hθ : ∀ s, 0 ≤ θ s) : E θ t u ≤ 1 := by
  apply Real.exp_le_one_iff.2
  exact neg_nonpos.2 (intervalIntegral.integral_nonneg_of_forall htu hθ)

lemma R_terminal (θ b : ℝ → ℝ) (T : ℝ) : R θ b T T = 0 := by simp [R]

lemma product_drift (θ r b v : ℝ) : (θ * r - b) * v + r * (θ * (1 - v)) = θ * r - b * v := by
  ring

lemma gaussian_kernel (g ρ r : ℝ) : F g ρ 0 r = g ^ 2 := by simp [F]

section Affine

variable {m d : ℕ} {K : Fin m → Fin d → ℝ → ℝ} {θ : Fin d → ℝ → ℝ}
variable {T : Fin m → ℝ} {t : ℝ}

lemma integral_affine (n : Fin m) (j : Fin d) (v : ℝ)
    (hK : IntervalIntegrable (K n j) volume t (T n))
    (hKE : IntervalIntegrable (fun u => K n j u * E (θ j) t u) volume t (T n)) :
    ∫ u in t..T n, K n j u * (1 + (v - 1) * E (θ j) t u) =
      (∫ u in t..T n, K n j u * (1 - E (θ j) t u)) + A K θ T t n j * v := by
  have hi : IntervalIntegrable (fun u => K n j u * (1 - E (θ j) t u)) volume t (T n) := by
    convert hK.sub hKE using 1
    funext u
    ring
  have heq : (fun u => K n j u * (1 + (v - 1) * E (θ j) t u)) =
      fun u => K n j u * (1 - E (θ j) t u) + (K n j u * E (θ j) t u) * v := by
    funext u
    ring
  rw [heq, intervalIntegral.integral_add hi (hKE.mul_const v), intervalIntegral.integral_mul_const]
  rfl

lemma A_nonneg (hT : ∀ n, t ≤ T n) (hK : ∀ n j u, 0 ≤ K n j u) (n : Fin m) (j : Fin d) :
    0 ≤ A K θ T t n j :=
  intervalIntegral.integral_nonneg_of_forall (hT n) fun u => mul_nonneg (hK n j u) (E_pos _ _ _).le

lemma C_nonneg (hT : ∀ n, t ≤ T n) (hK : ∀ n j u, 0 ≤ K n j u)
    (hθ : ∀ j u, 0 ≤ θ j u) (n : Fin m) : 0 ≤ C K θ T t n := by
  apply Finset.sum_nonneg
  intro j _
  exact intervalIntegral.integral_nonneg (hT n) fun u hu =>
    mul_nonneg (hK n j u) (sub_nonneg.2 (E_le_one _ hu.1 (hθ j)))

end Affine

lemma affine_equalities {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (C V : Fin m → ℝ)
    (v : Fin d → ℝ) (hV : V = C + A.mulVec v) (w : Fin m → ℝ)
    (hw : A.transpose.mulVec w = 0) : dotProduct w (V - C) = 0 := by
  rw [hV, add_sub_cancel_left, dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]

lemma nullity {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) :
    m - d ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin) := by
  have h := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := A.rank_le_width
  change A.transpose.rank + _ = _ at h
  rw [Matrix.rank_transpose, Module.finrank_pi, Fintype.card_fin] at h
  omega

theorem affine_variance : Standalone.StochasticMeetingVariance.affineStatement := by
  intro m d K θ T t v V hT hK hθ hv hKi hKE hV
  have heq : V = C K θ T t + (A K θ T t).mulVec v := by
    funext n
    rw [hV]
    simp_rw [integral_affine _ _ _ (hKi _ _) (hKE _ _)]
    rw [Finset.sum_add_distrib]
    rfl
  exact ⟨heq, A_nonneg hT hK, C_nonneg hT hK hθ, ⟨v, hv, heq⟩,
    affine_equalities _ _ _ _ heq, Matrix.rank_le_width _, nullity _⟩

lemma sum_functions {ι Ω : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    (∑ i, f i) = fun ω => ∑ i, f i ω := by
  funext ω
  simp

theorem conditional_variance : Standalone.StochasticMeetingVariance.momentStatement := by
  intro Ω m₀ μ hμ G hG d Y Z I01314 K θ v t T hprod hcenter hisometry hcross hmean
  let L : Fin d → Ω → ℝ := fun j ω =>
    ∫ u in t..T, K j u * (1 + (v j ω - 1) * E (θ j) t u)
  have hc : (Y - μ[Y | G]) ^ 2 =ᵐ[μ] fun ω => ∑ i, ∑ j, Z i ω * Z j ω := by
    filter_upwards [hcenter] with ω hω
    change ((Y - μ[Y | G]) ω) ^ 2 = _
    rw [hω, pow_two, Finset.sum_mul_sum]
  have houter : μ[fun ω => ∑ i, ∑ j, Z i ω * Z j ω | G] =ᵐ[μ]
      fun ω => ∑ i, (μ[fun ω => ∑ j, Z i ω * Z j ω | G]) ω := by
    simpa only [sum_functions] using
      condExp_finsetSum (s := Finset.univ) (f := fun i ω => ∑ j, Z i ω * Z j ω)
        (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j)) G
  have hinner (i : Fin d) : μ[fun ω => ∑ j, Z i ω * Z j ω | G] =ᵐ[μ]
      fun ω => ∑ j, (μ[fun ω => Z i ω * Z j ω | G]) ω := by
    simpa only [sum_functions] using
      condExp_finsetSum (s := Finset.univ) (f := fun j ω => Z i ω * Z j ω)
        (fun j _ => hprod i j) G
  have hij (i j : Fin d) : μ[fun ω => Z i ω * Z j ω | G] =ᵐ[μ]
      fun ω => if i = j then L i ω else 0 := by
    by_cases h : i = j
    · subst j
      filter_upwards [(hisometry i).trans (hmean i)] with ω hω
      simpa [L, pow_two] using hω
    · filter_upwards [hcross i j h] with ω hω
      simpa [h] using hω
  have hinner_all : ∀ᵐ ω ∂μ, ∀ i, (μ[fun ω => ∑ j, Z i ω * Z j ω | G]) ω =
      ∑ j, (μ[fun ω => Z i ω * Z j ω | G]) ω := ae_all_iff.2 hinner
  have hij_all : ∀ᵐ ω ∂μ, ∀ i j, (μ[fun ω => Z i ω * Z j ω | G]) ω =
      if i = j then L i ω else 0 := ae_all_iff.2 fun i => ae_all_iff.2 (hij i)
  refine (condExp_congr_ae hc).trans (houter.trans ?_)
  filter_upwards [hinner_all, hij_all] with ω hi hp
  simp only [hi, hp]
  simp [L]

lemma R_integrating_factor (θ b : ℝ → ℝ) (T t : ℝ)
    (hθ : ∀ a c, IntervalIntegrable θ volume a c) :
    R θ b T t = Real.exp (∫ u in (0 : ℝ)..t, θ u) *
      ∫ s in t..T, b s * Real.exp (-(∫ u in (0 : ℝ)..s, θ u)) := by
  rw [R, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  have hi := intervalIntegral.integral_add_adjacent_intervals (hθ 0 t) (hθ t s)
  have he : -(∫ u in t..s, θ u) = (∫ u in (0 : ℝ)..t, θ u) + -(∫ u in (0 : ℝ)..s, θ u) := by
    linarith
  change b s * Real.exp (-(∫ u in t..s, θ u)) = _
  rw [he, Real.exp_add]
  ring

theorem backward_equation : Standalone.StochasticMeetingVariance.backwardStatement := by
  intro θ b T t hθm hbm hθi hbi hθc hbc
  have hp : Continuous (fun x => ∫ u in (0 : ℝ)..x, θ u) :=
    intervalIntegral.continuous_primitive hθi 0
  have hdθ := intervalIntegral.integral_hasDerivAt_right (hθi 0 t)
    hθm.stronglyMeasurable.stronglyMeasurableAtFilter hθc
  have hgm : Measurable (fun s => b s * Real.exp (-(∫ u in (0 : ℝ)..s, θ u))) :=
    hbm.mul hp.measurable.neg.exp
  have hgc : ContinuousAt (fun s => b s * Real.exp (-(∫ u in (0 : ℝ)..s, θ u))) t :=
    hbc.mul (Real.continuous_exp.comp hp.neg).continuousAt
  have hdg := intervalIntegral.integral_hasDerivAt_left (hbi t T)
    hgm.stronglyMeasurable.stronglyMeasurableAtFilter hgc
  have hf : R θ b T = fun t => Real.exp (∫ u in (0 : ℝ)..t, θ u) *
      ∫ s in t..T, b s * Real.exp (-(∫ u in (0 : ℝ)..s, θ u)) :=
    funext fun t => R_integrating_factor θ b T t hθi
  rw [hf]
  convert hdθ.exp.mul hdg using 1
  have he : Real.exp (∫ u in (0 : ℝ)..t, θ u) * Real.exp (-(∫ u in (0 : ℝ)..t, θ u)) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [congrArg (fun x : ℝ => b t * x) he]

lemma full_kernel_nonneg {m d : ℕ} (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ α θ : Fin d → ℝ → ℝ) (T : Fin m → ℝ)
    (hρ : ∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) (n : Fin m) (j : Fin d) (u : ℝ) :
    0 ≤ kernel0136 g b ρ α θ T n j u :=
  F_nonneg _ _ _ _ (hρ j u).1 (hρ j u).2

theorem stochasticMeetingVariance : Standalone.StochasticMeetingVariance.statement :=
  ⟨conditional_variance, affine_variance, backward_equation, F_square, F_nonneg,
    fun _ _ => full_kernel_nonneg, R_terminal, product_drift⟩

end Novel.StochasticMeetingVarianceProof

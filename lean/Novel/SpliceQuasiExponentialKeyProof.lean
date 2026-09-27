import Standalone.SpliceQuasiExponentialKey
import Novel.SpliceQuasiExponentialAlgebraProof
import Novel.SpliceCrossTermAnalyticProof
import Novel.SpliceCrossTermConsistencyProof

open Matrix NormedSpace MeasureTheory Set Filter Topology
open Standalone.SpliceQuasiExponentialKey
namespace Novel.SpliceQuasiExponentialKeyProof

variable {r : ℕ}

/-- A vector annihilated by `M` through every test vector is annihilated as a row. -/
lemma row_zero (x : Fin r → ℝ) (M : Matrix (Fin r) (Fin r) ℝ)
    (h : ∀ v, x ⬝ᵥ (M *ᵥ v) = 0) : x ᵥ* M = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
  exact this

/-- If `c e^{AT} (T I + B) = 0` on an open interval, then `c = 0`. -/
lemma final (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det) (c : Fin r → ℝ) (Tm d₁ d₂ : ℝ)
    (hd : d₁ < d₂) (h : ∀ T ∈ Ioo d₁ d₂, ∀ v, c ⬝ᵥ (exp (T • A) *ᵥ
      ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - Tm • 1)) *ᵥ v)) = 0) : c = 0 := by
  set B := A⁻¹ - Tm • (1 : Matrix (Fin r) (Fin r) ℝ)
  set T₀ := (d₁ + d₂) / 2
  have hT₀ : T₀ ∈ Ioo d₁ d₂ := ⟨by simp only [T₀]; linarith, by simp only [T₀]; linarith⟩
  set E := exp (T₀ • A)
  set c' := c ᵥ* E
  have hform : ∀ v, (fun T => c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + B) *ᵥ v))) =
      fun T => T * c ⬝ᵥ ((A ^ 0 * exp (T • A)) *ᵥ v) + c ⬝ᵥ ((A ^ 0 * exp (T • A)) *ᵥ (B *ᵥ v)) := by
    intro v
    funext T
    simp only [pow_zero, one_mul, add_mulVec, smul_mulVec, one_mulVec, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hder : ∀ v, c ⬝ᵥ (E *ᵥ v) + T₀ * c ⬝ᵥ ((A * E) *ᵥ v) + c ⬝ᵥ ((A * E) *ᵥ (B *ᵥ v)) = 0 := by
    intro v
    have hd1 := Novel.RecurrenceNecessityReductionProof.deriv_g A c v 0 T₀
    have hd2 := Novel.RecurrenceNecessityReductionProof.deriv_g A c (B *ᵥ v) 0 T₀
    have hF : HasDerivAt (fun T => c ⬝ᵥ (exp (T • A) *ᵥ
        ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + B) *ᵥ v)))
        (1 * c ⬝ᵥ ((A ^ 0 * E) *ᵥ v) + T₀ * c ⬝ᵥ ((A ^ (0 + 1) * E) *ᵥ v) +
          c ⬝ᵥ ((A ^ (0 + 1) * E) *ᵥ (B *ᵥ v))) T₀ := by
      rw [hform v]
      exact ((hasDerivAt_id T₀).mul hd1).add hd2
    have h0 : HasDerivAt (fun T => c ⬝ᵥ (exp (T • A) *ᵥ
        ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + B) *ᵥ v))) 0 T₀ :=
      (hasDerivAt_const T₀ (0:ℝ)).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioo.mem_nhds hT₀] with T hT
        exact h T hT v)
    have := hF.unique h0
    simp only [pow_zero, one_mul, zero_add, pow_one] at this
    linarith
  have hcomm : A * E = E * A := (Commute.exp_right ((Commute.refl A).smul_right T₀)).eq
  have h1 : c' ᵥ* (A⁻¹ - (Tm - T₀) • (1 : Matrix (Fin r) (Fin r) ℝ)) = 0 := by
    have e : A⁻¹ - (Tm - T₀) • (1 : Matrix (Fin r) (Fin r) ℝ) = T₀ • 1 + B := by
      simp only [B, sub_smul]; abel
    rw [e]
    refine row_zero c' _ fun v => ?_
    rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, ← mulVec_mulVec]
    exact h T₀ hT₀ v
  have h2 : c' ᵥ* (A * (A⁻¹ - (Tm - T₀) • (1 : Matrix (Fin r) (Fin r) ℝ)) + 1) = 0 := by
    refine row_zero c' _ fun v => ?_
    have := hder v
    rw [hcomm] at this
    have e : A⁻¹ - (Tm - T₀) • (1 : Matrix (Fin r) (Fin r) ℝ) = T₀ • 1 + B := by
      simp only [B, sub_smul]; abel
    rw [e, add_mulVec, one_mulVec, ← mulVec_mulVec, add_mulVec, smul_mulVec, one_mulVec,
      mulVec_add, mulVec_smul, dotProduct_add, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [c', dotProduct_mulVec, vecMul_vecMul] at this ⊢
    simp only [← dotProduct_mulVec, ← mulVec_mulVec] at this ⊢
    linarith
  have hc' : c' = 0 :=
    Novel.SpliceQuasiExponentialAlgebraProof.vanishing r A hA c' (Tm - T₀) h1 h2
  have hinv : E * exp ((-T₀) • A) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left _).smul_right _),
      ← add_smul, add_neg_cancel, zero_smul, exp_zero]
  calc c = c ᵥ* (E * exp ((-T₀) • A)) := by rw [hinv, vecMul_one]
    _ = c' ᵥ* exp ((-T₀) • A) := by rw [← vecMul_vecMul]
    _ = 0 := by rw [hc', zero_vecMul]

open scoped Matrix.Norms.Operator in
/-- `u ↦ w e^{uC} b` is real-analytic. -/
lemma analytic_g (C : Matrix (Fin r) (Fin r) ℝ) (w b : Fin r → ℝ) :
    AnalyticOnNhd ℝ (fun u : ℝ => w ⬝ᵥ (exp (u • C) *ᵥ b)) univ := by
  intro t _
  have he : AnalyticAt ℝ (fun u : ℝ => exp (u • C)) t := by
    have h0 : AnalyticAt ℝ (exp : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (t • C) :=
      analyticAt_exp_of_mem_ball (𝕂 := ℝ) _ (by
        rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
    have hl : AnalyticAt ℝ (fun u : ℝ => u • C) t := analyticAt_id.smul analyticAt_const
    exact AnalyticAt.comp (f := fun u : ℝ => u • C) (x := t) h0 hl
  let L : Matrix (Fin r) (Fin r) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => w ⬝ᵥ (X *ᵥ b)
        map_add' := fun X Y => by simp [add_mulVec, dotProduct_add]
        map_smul' := fun a X => by simp [smul_mulVec, dotProduct_smul] }
  exact (L.analyticAt _).comp he

lemma key : keyStatement := by
  intro r A hA b c hc hctrl L Tm d₁ d₂ Δ hd hΔ hK
  set B := A⁻¹ - Tm • (1 : Matrix (Fin r) (Fin r) ℝ)
  -- the row vector `c e^{AT} (T I + B)`
  let row : ℝ → Fin r → ℝ := fun T => (c ᵥ* exp (T • A)) ᵥ* (T • (1 : Matrix (Fin r) (Fin r) ℝ) + B)
  have hrow : ∀ T v, c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + B) *ᵥ v)) =
      row T ⬝ᵥ v := fun T v => by
    simp only [row]
    rw [dotProduct_mulVec, dotProduct_mulVec]
  let g : ℝ → Fin r → ℝ := fun u => exp (u • (-A)) *ᵥ b
  have hgc : ∀ w, Continuous fun u => w ⬝ᵥ g u := fun w =>
    continuousOn_univ.1 (analytic_g (-A) w b).continuousOn
  -- `w v(t) = ∫_0^t Δ(u) w e^{−Au} b du`
  have hint : ∀ w t, w ⬝ᵥ vvec A b Δ t = ∫ u in (0:ℝ)..t, Δ u * (w ⬝ᵥ g u) := by
    intro w t
    have hi : ∀ i, IntervalIntegrable (fun u => w i * (Δ u * g u i)) volume 0 t := fun i =>
      ((hΔ.integrableOn_isCompact isCompact_uIcc).intervalIntegrable.mul_continuousOn
        (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i).continuousOn).const_mul _
    simp only [vvec, dotProduct]
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum fun i _ => hi i]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hloc : ∀ w, LocallyIntegrable (fun u => Δ u * (w ⬝ᵥ g u)) volume := fun w =>
    locallyIntegrableOn_univ.1 ((locallyIntegrableOn_univ.2 hΔ).mul_continuousOn
      (hgc w).continuousOn isClosed_univ.isLocallyClosed)
  -- Lebesgue: `Δ(u) row(T) e^{−Au} b = 0` for almost every `u`, for each `T`
  have hae : ∀ T ∈ Ioo d₁ d₂, ∀ᵐ u ∂volume, u ∈ Ico 0 L → Δ u * (row T ⬝ᵥ g u) = 0 := by
    intro T hT
    refine Novel.SpliceCrossTermAnalyticProof.lebesgue 0 L _ (hloc (row T)) fun t ht => ?_
    simp only [zero_mul, Real.exp_zero, one_mul]
    rw [← hint (row T) t, ← hrow]
    exact hK t ht T hT
  have haeQ : ∀ᵐ u ∂volume, ∀ q : ℚ, (q : ℝ) ∈ Ioo d₁ d₂ → u ∈ Ico 0 L →
      Δ u * (row q ⬝ᵥ g u) = 0 :=
    ae_all_iff.2 fun q => by
      by_cases hq : (q : ℝ) ∈ Ioo d₁ d₂
      · filter_upwards [hae q hq] with u hu _ using hu
      · exact Eventually.of_forall fun u h => absurd h hq
  -- `T ↦ row(T) x` is continuous
  have hrowc : ∀ x, Continuous fun T => row T ⬝ᵥ x := by
    intro x
    have e : (fun T => row T ⬝ᵥ x) = fun T => T * c ⬝ᵥ ((A ^ 0 * exp (T • A)) *ᵥ x) +
        c ⬝ᵥ ((A ^ 0 * exp (T • A)) *ᵥ (B *ᵥ x)) := by
      funext T
      rw [← hrow]
      simp only [pow_zero, one_mul, add_mulVec, smul_mulVec, one_mulVec, mulVec_add,
        mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [e]
    exact continuous_iff_continuousAt.2 fun T =>
      (((hasDerivAt_id T).mul (Novel.RecurrenceNecessityReductionProof.deriv_g A c x 0 T)).add
        (Novel.RecurrenceNecessityReductionProof.deriv_g A c (B *ᵥ x) 0 T)).continuousAt
  by_contra hne
  -- the set where `Δ ≠ 0` and the rational conditions hold has positive measure
  set S := {u | u ∈ Ico 0 L ∧ Δ u ≠ 0 ∧ ∀ q : ℚ, (q : ℝ) ∈ Ioo d₁ d₂ → u ∈ Ico 0 L →
    Δ u * (row q ⬝ᵥ g u) = 0}
  have hSpos : volume S ≠ 0 := by
    intro h0
    apply hne
    rw [ae_iff] at haeQ ⊢
    refine measure_mono_null (fun u hu => ?_) (measure_union_null h0 haeQ)
    simp only [Set.mem_ofPred_eq, not_imp] at hu
    by_cases hq : ∀ q : ℚ, (q : ℝ) ∈ Ioo d₁ d₂ → u ∈ Ico 0 L → Δ u * (row q ⬝ᵥ g u) = 0
    · exact Or.inl ⟨hu.1, hu.2, hq⟩
    · exact Or.inr hq
  have hSinf : S.Infinite := fun hfin => hSpos (hfin.measure_zero volume)
  obtain ⟨z₀, -, hacc⟩ := hSinf.exists_accPt_of_subset_isCompact (isCompact_Icc (a := 0) (b := L))
    (fun u hu => Ico_subset_Icc_self hu.1)
  -- on `S`, `row(T) e^{−Au} b = 0` for every `T` of the interval
  have hS : ∀ u ∈ S, ∀ T ∈ Ioo d₁ d₂, row T ⬝ᵥ g u = 0 := by
    intro u hu T hT
    refine Novel.SpliceCrossTermConsistencyProof.zero_of_rat (fun T => row T ⬝ᵥ g u) (hrowc _) T
      (d₂ - T) (sub_pos.2 hT.2) fun q hq => ?_
    have := hu.2.2 q ⟨hT.1.trans hq.1, by linarith [hq.2]⟩ hu.1
    exact (mul_eq_zero.1 this).resolve_left hu.2.1
  -- analytic continuation in `u`
  have hall : ∀ T ∈ Ioo d₁ d₂, ∀ u, row T ⬝ᵥ g u = 0 := by
    intro T hT u
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, row T ⬝ᵥ g z = 0 := by
      rw [frequently_nhdsWithin_iff]
      exact (accPt_iff_frequently.1 hacc).mono fun y hy => ⟨hS y hy.2 T hT, hy.1⟩
    exact (analytic_g (-A) (row T) b).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (mem_univ z₀) hfreq (mem_univ u)
  -- derivatives at `0` and controllability
  have hrow0 : ∀ T ∈ Ioo d₁ d₂, row T = 0 := by
    intro T hT
    apply hctrl
    intro k
    have hk : ∀ k : ℕ, ∀ u : ℝ, row T ⬝ᵥ (((-A) ^ k * exp (u • (-A))) *ᵥ b) = 0 := by
      intro k
      induction k with
      | zero => intro u; rw [pow_zero, one_mul]; exact hall T hT u
      | succ k ih =>
        intro u
        have hd' := Novel.RecurrenceNecessityReductionProof.deriv_g (-A) (row T) b k u
        have h0 : HasDerivAt (fun u : ℝ => row T ⬝ᵥ (((-A) ^ k * exp (u • (-A))) *ᵥ b)) 0 u := by
          have e : (fun u : ℝ => row T ⬝ᵥ (((-A) ^ k * exp (u • (-A))) *ᵥ b)) = fun _ => (0:ℝ) :=
            funext ih
          rw [e]
          exact hasDerivAt_const u 0
        exact hd'.unique h0
    have := hk k 0
    rw [zero_smul, exp_zero, mul_one] at this
    rcases Nat.even_or_odd k with he | ho
    · rwa [he.neg_pow] at this
    · rw [ho.neg_pow, neg_mulVec, dotProduct_neg, neg_eq_zero] at this
      exact this
  exact hc (final A hA c Tm d₁ d₂ hd fun T hT v => by rw [hrow, hrow0 T hT, zero_dotProduct])

theorem spliceQuasiExponentialKey : Standalone.SpliceQuasiExponentialKey.statement := key

end Novel.SpliceQuasiExponentialKeyProof

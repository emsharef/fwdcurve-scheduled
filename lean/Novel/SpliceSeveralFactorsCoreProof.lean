import Standalone.SpliceSeveralFactorsCore
import Novel.SpliceStateBlockAX01Proof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceStateBlockCross Standalone.SpliceSeveralFactorsCore
namespace Novel.SpliceSeveralFactorsCoreProof
open Novel.SpliceStateBlockAX01Proof

variable {r n : ℕ}

/-- `∫_0^t e^{−Au} W(u) du = 0` for every `t ∈ [0, L)` forces `W = 0` a.e. on `[0, L)`. -/
lemma zero_of_int (A : Matrix (Fin r) (Fin r) ℝ) (W : ℝ → Fin r → ℝ)
    (hW : ∀ i, Measurable fun u => W u i) (C : ℝ) (hC : ∀ u i, |W u i| ≤ C) (L : ℝ)
    (hv : ∀ t ∈ Ico 0 L, ∀ i, ∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ W u) i = 0) :
    ∀ᵐ u ∂volume, u ∈ Ico 0 L → W u = 0 := by
  let f : Fin r → ℝ → ℝ := fun i u => (exp (u • (-A)) *ᵥ W u) i
  have hloc : ∀ i, LocallyIntegrable (f i) volume := fun i => by
    have e : f i = fun u => ∑ j, W u j * (exp (u • (-A)) *ᵥ Pi.single j 1) i := by
      funext u; exact pexp A W u i
    rw [e]
    refine locallyIntegrable_finsetSum _ fun j _ => ?_
    have hWj : LocallyIntegrable (fun u => W u j) volume :=
      (locallyIntegrable_const C).mono (hW j).aestronglyMeasurable
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          exact (hC u j).trans (le_abs_self _))
    exact locallyIntegrableOn_univ.1 ((locallyIntegrableOn_univ.2 hWj).mul_continuousOn
      (econt A i j).continuousOn isClosed_univ.isLocallyClosed)
  have hk : ∀ i, ∀ᵐ u ∂volume, u ∈ Ico 0 L → f i u = 0 := fun i =>
    Novel.SpliceCrossTermAnalyticProof.lebesgue 0 L (f i) (hloc i) fun t ht => by
      simp only [zero_mul, Real.exp_zero, one_mul]
      exact hv t ht i
  filter_upwards [ae_all_iff.2 hk] with u hu hu'
  have hf : exp (u • (-A)) *ᵥ W u = 0 := funext fun i => hu i hu'
  have hinv : exp (u • A) * exp (u • (-A)) = 1 := by
    rw [smul_neg, ← neg_smul, ← Novel.SpliceQuasiExponentialBlockProof.exp_add'', add_neg_cancel,
      zero_smul, NormedSpace.exp_zero]
  calc W u = exp (u • A) *ᵥ (exp (u • (-A)) *ᵥ W u) := by
        rw [mulVec_mulVec, hinv, one_mulVec]
    _ = 0 := by rw [hf, mulVec_zero]

/-- A Claim 040 cross term is interval integrable. -/
lemma ii_cross {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun u => cross040 s Tm c A w u T) volume 0 t := by
  have hc := fun i => Novel.SpliceStateBlockCrossProof.sw_data h i
  refine (ii_sum fun i => (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm
    (Novel.SpliceStateBlockCrossProof.sw s w i) (hc i).1 (hc i).2.choose
    (hc i).2.choose_spec c A (Pi.single i 1) 1 t T ht htT).2).congr fun u _ => ?_
  exact (Novel.SpliceStateBlockCrossProof.cross_sum s Tm c A _ u T).symm

lemma cexp_sumq (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T : ℝ) (y z : Fin n → Fin r → ℝ) :
    c ⬝ᵥ (exp (T • A) *ᵥ ((∑ q, y q) + T • ∑ q, z q)) =
      ∑ q, c ⬝ᵥ (exp (T • A) *ᵥ (y q + T • z q)) := by
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, mulVec_sum, dotProduct_sum]

lemma core : Standalone.SpliceSeveralFactorsCore.coreStatement := by
  intro r n A hA c hobs s w h Tm τ H hτ hτH hdec
  obtain ⟨h1, τl, hl, hidxl⟩ := Novel.SpliceCrossTermConsistencyProof.idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm τ
  set m := idx033 Tm τ - 1
  have hm : m + 1 = idx033 Tm τ := by omega
  have hidxr' : ∀ v ∈ Ico τ (τ + ε), idx033 Tm v = m + 1 := fun v hv => by
    rw [hm]; exact hidxr v hv
  set Δ : Fin n → ℝ → ℝ := fun q u => s q (m + 1) u - s q m u
  -- the summed jump vector vanishes at every `t < τ`
  have hv : ∀ t ∈ Ico 0 τ, ∑ q, vvec040 A (Δ q) (w q) t = 0 := by
    intro t ht
    obtain ⟨p, G, hGa, hp, hX⟩ := hdec t ht
    have hE := fun q => Novel.SpliceStateBlockCrossProof.explicit r (s q) (w q) (h q) Tm A hA c t
      ht.1 m τ τl (τ + ε) hl (by linarith) hidxl hidxr' ht.2
    choose k₀ k₁ y₀ z₀ y₁ z₁ hL hR hy hz using hE
    have hsumL : ∀ T ∈ Ioo τl τ, t ≤ T → ∫ u in (0:ℝ)..t, ∑ q, cross040 (s q) Tm c A (w q) u T =
        ∑ q, k₀ q + c ⬝ᵥ (exp (T • A) *ᵥ ((∑ q, y₀ q) + T • ∑ q, z₀ q)) := by
      intro T hT htT
      rw [intervalIntegral.integral_finsetSum fun q _ => ii_cross (h q) Tm c A t T ht.1 htT,
        Finset.sum_congr rfl fun q _ => hL q T hT htT, Finset.sum_add_distrib, cexp_sumq]
    have hsumR : ∀ T ∈ Ico τ (τ + ε), ∫ u in (0:ℝ)..t, ∑ q, cross040 (s q) Tm c A (w q) u T =
        ∑ q, k₁ q + c ⬝ᵥ (exp (T • A) *ᵥ ((∑ q, y₁ q) + T • ∑ q, z₁ q)) := by
      intro T hT
      have htT : t ≤ T := ht.2.le.trans hT.1
      rw [intervalIntegral.integral_finsetSum fun q _ => ii_cross (h q) Tm c A t T ht.1 htT,
        Finset.sum_congr rfl fun q _ => hR q T hT, Finset.sum_add_distrib, cexp_sumq]
    set τl' := max τl t
    have hτl' : τl' < τ := max_lt hl ht.2
    set τr' := min (τ + ε) H
    have hτr' : τ < τr' := lt_min (by linarith) hτH
    obtain ⟨κ₀, κ₁, hκ⟩ := hp m
    obtain ⟨l₀, l₁, hl'⟩ := hp (m + 1)
    have hmatch := Novel.SpliceQuasiExponentialConsistencyProof.match035 c A G hGa
      (∑ q, y₀ q) (∑ q, z₀ q) (∑ q, y₁ q) (∑ q, z₁ q)
      ((∑ q, k₀ q) - κ₀) (-κ₁) ((∑ q, k₁ q) - l₀) (-l₁) τl' τ τ τr' hτl' hτr'
      (fun T hT => by
        have hTt : t < T := lt_of_le_of_lt (le_max_right _ _) hT.1
        have hTI : T ∈ Ioo t H := ⟨hTt, by linarith [hT.2]⟩
        have hTl : T ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left _ _) hT.1, hT.2⟩
        have := hX T hTI
        rw [hsumL T hTl hTt.le, hκ T hTI (hidxl T hTl)] at this
        linarith)
      (fun T hT => by
        have hTI : T ∈ Ioo t H := ⟨lt_of_le_of_lt ht.2.le hT.1,
          lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
        have hTr : T ∈ Ico τ (τ + ε) := ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
        have := hX T hTI
        rw [hsumR T hTr, hl' T hTI (hidxr' T hTr)] at this
        linarith)
    have hyS : (∑ q, y₁ q) - ∑ q, y₀ q = (A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        ∑ q, vvec040 A (Δ q) (w q) t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun q _ => hy q, mulVec_sum]
    have hzS : (∑ q, z₁ q) - ∑ q, z₀ q = ∑ q, vvec040 A (Δ q) (w q) t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun q _ => hz q]
    rw [hyS, hzS] at hmatch
    set v := ∑ q, vvec040 A (Δ q) (w q) t
    refine Novel.SpliceStateBlockObservabilityProof.observability r A hA c hobs τ 0 1 v one_pos
      fun T hT => ?_
    have haff := Novel.SpliceQuasiExponentialAlgebraProof.affine r A hA c
      ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ v) v 0 1 _ _ one_pos
      (fun T _ => hmatch T) T hT
    have e : c ⬝ᵥ (exp (T • A) *ᵥ ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ v + T • v)) =
        c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ v)) := by
      simp only [add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [← e]
    exact haff
  -- the weighted jumps' sum `W`, and the Lebesgue step
  choose C hC using fun q => (h q).2.2
  let W : ℝ → Fin r → ℝ := fun u => ∑ q, Δ q u • w q u
  have hΔm : ∀ q, Measurable (Δ q) := fun q => ((h q).1 (m + 1)).sub ((h q).1 m)
  have hΔC : ∀ q u, |Δ q u| ≤ C q + C q := fun q u =>
    (abs_sub _ _).trans (add_le_add ((hC q).1 _ _) ((hC q).1 _ _))
  have hWm : ∀ i, Measurable fun u => W u i := fun i => by
    simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun q _ => (hΔm q).mul ((h q).2.1 i)
  have hWC : ∀ u i, |W u i| ≤ ∑ q, (C q + C q) * C q := fun u i => by
    simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hΔC q u) ((hC q).2 u i) (abs_nonneg _)
      (by linarith [(abs_nonneg _).trans ((hC q).1 0 0)])
  have hint : ∀ t ∈ Ico 0 τ, ∀ i, ∫ u in (0:ℝ)..t, (exp (u • (-A)) *ᵥ W u) i = 0 := by
    intro t ht i
    have hq : ∀ q, IntervalIntegrable (fun u => Δ q u * (exp (u • (-A)) *ᵥ w q u) i) volume 0 t :=
      fun q => by
        have e : (fun u => Δ q u * (exp (u • (-A)) *ᵥ w q u) i) =
            fun u => ∑ j, (Δ q u * w q u j) * (exp (u • (-A)) *ᵥ Pi.single j 1) i := by
          funext u
          rw [pexp A (w q) u i, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e]
        refine ii_sum fun j => ii_bc ((hΔm q).mul ((h q).2.1 j)) ((C q + C q) * C q)
          (fun u => ?_) (econt A i j) 0 t
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul (hΔC q u) ((hC q).2 u j) (abs_nonneg _)
          (by linarith [(abs_nonneg _).trans ((hC q).1 0 0)])
    have := congrFun (hv t ht) i
    simp only [Finset.sum_apply, vvec040, Pi.zero_apply] at this
    rw [← intervalIntegral.integral_finsetSum fun q _ => hq q] at this
    refine Eq.trans (intervalIntegral.integral_congr fun u _ => ?_) this
    simp only [W, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  filter_upwards [zero_of_int A W hWm _ hWC τ hint] with u hu hu'
  rw [← hm]
  exact hu hu'

theorem spliceSeveralFactorsCore : Standalone.SpliceSeveralFactorsCore.statement := core

end Novel.SpliceSeveralFactorsCoreProof

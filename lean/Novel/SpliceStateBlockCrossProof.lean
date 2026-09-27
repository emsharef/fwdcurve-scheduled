import Standalone.SpliceStateBlockCross
import Standalone.SpliceStateBlockObservability
import Novel.SpliceRandomScalesNecessityProof
import Novel.SpliceStateBlockObservabilityProof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceQuasiExponentialKey Standalone.SpliceStateBlockCross
namespace Novel.SpliceStateBlockCrossProof

variable {r : ℕ}

/-- `(M v)_k = ∑_i v_i (M e_i)_k`. -/
lemma mv_sum (M : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (k : Fin r) :
    (M *ᵥ v) k = ∑ i, v i * (M *ᵥ Pi.single i 1) k := by
  have h : ∀ i, (M *ᵥ Pi.single i 1) k = M k i := fun i => by
    rw [mulVec_single_one]; rfl
  rw [Finset.sum_congr rfl fun i _ => by rw [h i]]
  simp only [mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_sum (c : Fin r → ℝ) (M : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) :
    c ⬝ᵥ (M *ᵥ v) = ∑ i, v i * c ⬝ᵥ (M *ᵥ Pi.single i 1) := by
  simp only [dotProduct, mv_sum M v, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- The `i`-th component's step scales `w_i(u) s_j(u)`. -/
def sw (s : ℕ → ℝ → ℝ) (w : ℝ → Fin r → ℝ) (i : Fin r) : ℕ → ℝ → ℝ := fun j u => w u i * s j u

lemma cross_sum (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (w : ℝ → Fin r → ℝ) (u T : ℝ) :
    cross040 s Tm c A w u T = ∑ i, cross035 1 (sw s w i) Tm c A (Pi.single i 1) u T := by
  have hsig : ∀ i, sigS033 (sw s w i) Tm u T = w u i * sigS033 s Tm u T := fun i => rfl
  have hSS : ∀ i, SS033 (sw s w i) Tm u T = w u i * SS033 s Tm u T := fun i => by
    unfold SS033
    rw [← intervalIntegral.integral_const_mul]
    rfl
  simp only [cross035, hsig, hSS, Lam035, lam035, one_mul]
  rw [cross040, dot_sum c _ (w u), dot_sum c (exp ((T - u) • A)) (w u), Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sw_data {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w) (i : Fin r) :
    (∀ j, Measurable (sw s w i j)) ∧ ∃ C : ℝ, ∀ j u, |sw s w i j u| ≤ C := by
  obtain ⟨hs, hw, C, hsC, hwC⟩ := h
  refine ⟨fun j => (hw i).mul (hs j), C * C, fun j u => ?_⟩
  simp only [sw, abs_mul]
  exact mul_le_mul (hwC u i) (hsC j u) (abs_nonneg _) ((abs_nonneg _).trans (hwC u i))

/-- The integrated cross term is the sum of the components' integrated cross terms. -/
lemma int_sum {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ u in (0:ℝ)..t, cross040 s Tm c A w u T =
      ∑ i, ∫ u in (0:ℝ)..t, cross035 1 (sw s w i) Tm c A (Pi.single i 1) u T := by
  simp_rw [cross_sum]
  refine intervalIntegral.integral_finsetSum fun i _ => ?_
  obtain ⟨hm, C, hC⟩ := sw_data h i
  exact (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm (sw s w i) hm C hC c A
    (Pi.single i 1) 1 t T ht htT).2

/-- `∑_i v_i(t)` of the components is `v(t)`. -/
lemma vvec_sum {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w)
    (A : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) (t : ℝ) :
    ∑ i, vvec A (Pi.single i 1) (fun u => sw s w i (m + 1) u - sw s w i m u) t =
      vvec040 A (fun u => s (m + 1) u - s m u) w t := by
  obtain ⟨hs, hw, C, hsC, hwC⟩ := h
  funext k
  simp only [Finset.sum_apply, vvec, vvec040]
  have hgc : ∀ i, Continuous fun u : ℝ => (exp (u • (-A)) *ᵥ Pi.single i 1) k := fun i =>
    Novel.RecurrenceNecessityReductionProof.phi_cont (-A) _ k
  rw [← intervalIntegral.integral_finsetSum fun i _ => ?_]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [sw]
    rw [mv_sum _ (w u) k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine (Novel.SpliceCrossTermDriftProof.ii_bdd (((hw i).mul (hs (m + 1))).sub
      ((hw i).mul (hs m))) (C * C + C * C) (fun u => ?_) 0 t).mul_continuousOn
      (hgc i).continuousOn
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> simp only [Pi.mul_apply] <;> rw [abs_mul] <;>
      exact mul_le_mul (hwC u i) (hsC _ u) (abs_nonneg _) ((abs_nonneg _).trans (hwC u i))

lemma cexp_sum (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T : ℝ) (y z : Fin r → Fin r → ℝ) :
    c ⬝ᵥ (exp (T • A) *ᵥ ((∑ i, y i) + T • ∑ i, z i)) =
      ∑ i, c ⬝ᵥ (exp (T • A) *ᵥ (y i + T • z i)) := by
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, mulVec_sum, dotProduct_sum]

lemma explicit : Standalone.SpliceStateBlockCross.explicitStatement := by
  intro r s w h Tm A hA c t ht m τ τl τr hl hr hidxl hidxr htτ
  set τl' := max τl t
  have hτl' : τl' < τ := max_lt hl htτ
  set T0 := (τl' + τ) / 2
  have hT0 : T0 ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left τl t) (by simp only [T0]; linarith),
    by simp only [T0]; linarith⟩
  have htT0 : t ≤ T0 := by simp only [T0]; linarith [le_max_right τl t]
  have hE : ∀ (i : Fin r) (j : ℕ) (Ta : ℝ), idx033 Tm Ta = j → t ≤ Ta → ∀ T, idx033 Tm T = j →
      t ≤ T → ∫ u in (0:ℝ)..t, cross035 1 (sw s w i) Tm c A (Pi.single i 1) u T =
        -(1 * (c ⬝ᵥ (A⁻¹ *ᵥ Pi.single i 1))) * (∫ u in (0:ℝ)..t, sw s w i j u) +
          c ⬝ᵥ (exp (T • A) *ᵥ (yCoef035 1 (sw s w i) Tm A (Pi.single i 1) j Ta t +
            T • zCoef035 1 (sw s w i) A (Pi.single i 1) j t)) :=
    fun i j Ta hTa htTa T hT htT => by
      obtain ⟨hm, C, hC⟩ := sw_data h i
      exact Novel.SpliceQuasiExponentialCrossProof.explicit Tm (sw s w i) hm C hC r A hA
        (Pi.single i 1) c 1 j t Ta ht hTa htTa T hT htT
  have hJ : ∀ i : Fin r,
      yCoef035 1 (sw s w i) Tm A (Pi.single i 1) (m + 1) τ t -
          yCoef035 1 (sw s w i) Tm A (Pi.single i 1) m T0 t =
        (1:ℝ) • ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
          vvec A (Pi.single i 1) (fun u => sw s w i (m + 1) u - sw s w i m u) t) ∧
      zCoef035 1 (sw s w i) A (Pi.single i 1) (m + 1) t -
          zCoef035 1 (sw s w i) A (Pi.single i 1) m t =
        (1:ℝ) • vvec A (Pi.single i 1) (fun u => sw s w i (m + 1) u - sw s w i m u) t :=
    fun i => by
    obtain ⟨hm, C, hC⟩ := sw_data h i
    exact Novel.SpliceQuasiExponentialCrossProof.jump Tm (sw s w i) hm C hC r A (Pi.single i 1) 1
      m τ τl τr T0 τ t hl hr hidxl hidxr hT0 ⟨le_rfl, hr⟩ ht htT0
  refine ⟨∑ i, -(1 * (c ⬝ᵥ (A⁻¹ *ᵥ Pi.single i 1))) * (∫ u in (0:ℝ)..t, sw s w i m u),
    ∑ i, -(1 * (c ⬝ᵥ (A⁻¹ *ᵥ Pi.single i 1))) * (∫ u in (0:ℝ)..t, sw s w i (m + 1) u),
    ∑ i, yCoef035 1 (sw s w i) Tm A (Pi.single i 1) m T0 t,
    ∑ i, zCoef035 1 (sw s w i) A (Pi.single i 1) m t,
    ∑ i, yCoef035 1 (sw s w i) Tm A (Pi.single i 1) (m + 1) τ t,
    ∑ i, zCoef035 1 (sw s w i) A (Pi.single i 1) (m + 1) t, ?_, ?_, ?_, ?_⟩
  · intro T hT htT
    rw [int_sum h Tm c A t T ht htT, Finset.sum_congr rfl fun i _ =>
      hE i m T0 (hidxl T0 hT0) htT0 T (hidxl T hT) htT, Finset.sum_add_distrib, cexp_sum]
  · intro T hT
    have htT : t ≤ T := htτ.le.trans hT.1
    rw [int_sum h Tm c A t T ht htT, Finset.sum_congr rfl fun i _ =>
      hE i (m + 1) τ (hidxr τ ⟨le_rfl, hr⟩) htτ.le T (hidxr T hT) htT, Finset.sum_add_distrib,
      cexp_sum]
  · rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => (hJ i).1]
    simp only [one_smul]
    rw [← mulVec_sum, vvec_sum h A m t]
  · rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => (hJ i).2]
    simp only [one_smul]
    exact vvec_sum h A m t

/-- `v(t) = 0` for every `t ∈ [0, L)` forces `Δ(u) w(u) = 0` for almost every `u ∈ [0, L)`. -/
lemma zero_of_vvec {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w)
    (A : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) (L : ℝ)
    (hv : ∀ t ∈ Ico 0 L, vvec040 A (fun u => s (m + 1) u - s m u) w t = 0) :
    ∀ᵐ u ∂volume, u ∈ Ico 0 L → (s (m + 1) u - s m u) • w u = 0 := by
  obtain ⟨hs, hw, C, hsC, hwC⟩ := h
  set Δ : ℝ → ℝ := fun u => s (m + 1) u - s m u
  let f : Fin r → ℝ → ℝ := fun k u => Δ u * (exp (u • (-A)) *ᵥ w u) k
  have hΔw : ∀ i, LocallyIntegrable (fun u => Δ u * w u i) volume := fun i => by
    refine (locallyIntegrable_const ((C + C) * C)).mono
      (((hs (m + 1)).sub (hs m)).mul (hw i)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    rw [abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hsC _ _) (hsC _ _))) (hwC u i)
      (abs_nonneg _) (by linarith [(abs_nonneg _).trans (hsC 0 0)])
  have hloc : ∀ k, LocallyIntegrable (f k) volume := fun k => by
    have e : f k = fun u => ∑ i, (Δ u * w u i) * (exp (u • (-A)) *ᵥ Pi.single i 1) k := by
      funext u
      simp only [f]
      rw [mv_sum _ (w u) k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    refine locallyIntegrable_finsetSum _ fun i _ => ?_
    exact locallyIntegrableOn_univ.1 ((locallyIntegrableOn_univ.2 (hΔw i)).mul_continuousOn
      (Novel.RecurrenceNecessityReductionProof.phi_cont (-A) _ k).continuousOn
      isClosed_univ.isLocallyClosed)
  have hk : ∀ k, ∀ᵐ u ∂volume, u ∈ Ico 0 L → f k u = 0 := fun k =>
    Novel.SpliceCrossTermAnalyticProof.lebesgue 0 L (f k) (hloc k) fun t ht => by
      have := congrFun (hv t ht) k
      simp only [zero_mul, Real.exp_zero, one_mul]
      exact this
  filter_upwards [ae_all_iff.2 hk] with u hu hu'
  have hf : Δ u • (exp (u • (-A)) *ᵥ w u) = 0 := funext fun k => by
    simpa [f, smul_eq_mul] using hu k hu'
  have hinv : exp (u • A) * exp (u • (-A)) = 1 := by
    rw [smul_neg, ← neg_smul, ← Novel.SpliceQuasiExponentialBlockProof.exp_add'', add_neg_cancel,
      zero_smul, NormedSpace.exp_zero]
  calc Δ u • w u = exp (u • A) *ᵥ (Δ u • (exp (u • (-A)) *ᵥ w u)) := by
        rw [mulVec_smul, mulVec_mulVec, hinv, one_mulVec]
    _ = 0 := by rw [hf, mulVec_zero]

lemma core : Standalone.SpliceStateBlockCross.coreStatement := by
  intro r A hA c hobs s w h Tm τ H hτ hτH hdec
  obtain ⟨h1, τl, hl, hidxl⟩ := Novel.SpliceCrossTermConsistencyProof.idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm τ
  set m := idx033 Tm τ - 1
  have hm : m + 1 = idx033 Tm τ := by omega
  have hidxr' : ∀ v ∈ Ico τ (τ + ε), idx033 Tm v = m + 1 := fun v hv => by
    rw [hm]; exact hidxr v hv
  have hv : ∀ t ∈ Ico 0 τ, vvec040 A (fun u => s (m + 1) u - s m u) w t = 0 := by
    intro t ht
    obtain ⟨p, G, hGa, hp, hX⟩ := hdec t ht
    obtain ⟨k₀, k₁, y₀, z₀, y₁, z₁, hL, hR, hy, hz⟩ := explicit r s w h Tm A hA c t ht.1 m τ τl
      (τ + ε) hl (by linarith) hidxl hidxr' ht.2
    set τl' := max τl t
    have hτl' : τl' < τ := max_lt hl ht.2
    set τr' := min (τ + ε) H
    have hτr' : τ < τr' := lt_min (by linarith) hτH
    obtain ⟨κ₀, κ₁, hκ⟩ := hp m
    obtain ⟨l₀, l₁, hl'⟩ := hp (m + 1)
    have hmatch := Novel.SpliceQuasiExponentialConsistencyProof.match035 c A G hGa y₀ z₀ y₁ z₁
      (k₀ - κ₀) (-κ₁) (k₁ - l₀) (-l₁) τl' τ τ τr' hτl' hτr'
      (fun T hT => by
        have hTt : t < T := lt_of_le_of_lt (le_max_right _ _) hT.1
        have hTI : T ∈ Ioo t H := ⟨hTt, by linarith [hT.2]⟩
        have hTl : T ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left _ _) hT.1, hT.2⟩
        have := hX T hTI
        rw [hL T hTl hTt.le, hκ T hTI (hidxl T hTl)] at this
        linarith)
      (fun T hT => by
        have hTI : T ∈ Ioo t H := ⟨lt_of_le_of_lt ht.2.le hT.1,
          lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
        have hTr : T ∈ Ico τ (τ + ε) := ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
        have := hX T hTI
        rw [hR T hTr, hl' T hTI (hidxr' T hTr)] at this
        linarith)
    rw [hy, hz] at hmatch
    set v := vvec040 A (fun u => s (m + 1) u - s m u) w t
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
  filter_upwards [zero_of_vvec h A m τ hv] with u hu hu'
  rw [← hm]
  exact hu hu'

theorem spliceStateBlockCross : Standalone.SpliceStateBlockCross.statement := ⟨explicit, core⟩

end Novel.SpliceStateBlockCrossProof

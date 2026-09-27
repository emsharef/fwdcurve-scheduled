import Standalone.SpliceSeveralFactorsSufficiency
import Novel.SpliceSeveralFactorsAX01Proof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceStateBlockCross Standalone.SpliceStateBlockAX01
open Standalone.SpliceSeveralFactorsAX01 Standalone.SpliceSeveralFactorsSufficiency
namespace Novel.SpliceSeveralFactorsSufficiencyProof
open Novel.SpliceStateBlockAX01Proof Novel.SpliceSeveralFactorsAX01Proof

variable {r k L : ℕ}

/-- The regrouped step scales `R_{i,j}(u) = ∑_l H^Z_{il}(u) S_{l,j}(u)` of block component `i`. -/
def Rcomp (s : Fin L → ℕ → ℝ → ℝ) (HS : Fin L → ℝ → Fin k → ℝ) (HZ : ℝ → Fin r → Fin k → ℝ)
    (i : Fin r) : ℕ → ℝ → ℝ :=
  fun j u => ∑ l, HZ u i l * Scomb s HS l j u

section Main
variable {s : Fin L → ℕ → ℝ → ℝ} {HS : Fin L → ℝ → Fin k → ℝ} {HZ : ℝ → Fin r → Fin k → ℝ}
  {dL dC : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ} {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ}
  {A : Matrix (Fin r) (Fin r) ℝ}

lemma R_data (h : PathData041 s HS HZ dL dC bZ z H) (i : Fin r) :
    (∀ j, Measurable (Rcomp s HS HZ i j)) ∧ ∃ C, ∀ j u, |Rcomp s HS HZ i j u| ≤ C := by
  have hd := data041 h
  obtain ⟨-, -, hHZ, -, ⟨C, -, -, hHZC, -⟩, -⟩ := h
  choose C' hC' using fun l => (hd l).2.2
  refine ⟨fun j => Finset.measurable_sum _ fun l _ => (hHZ i l).mul ((hd l).1 j),
    ∑ l, |C| * C' l, fun j u => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  exact mul_le_mul ((hHZC u i l).trans (le_abs_self C)) ((hC' l).1 j u) (abs_nonneg _)
    (abs_nonneg _)

/-- The drivers' cross terms, regrouped by block component. -/
lemma regroup (h : PathData041 s HS HZ dL dC bZ z H) (u T : ℝ) :
    ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T =
      ∑ i, cross035 1 (Rcomp s HS HZ i) Tm c A (Pi.single i 1) u T := by
  have hd := data041 h
  simp_rw [Novel.SpliceStateBlockCrossProof.cross_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- linearity of the cross integrand in the step scales
  have hSS : SS033 (Rcomp s HS HZ i) Tm u T =
      ∑ l, SS033 (Novel.SpliceStateBlockCrossProof.sw (Scomb s HS l) (fun u i => HZ u i l) i)
        Tm u T := by
    unfold SS033
    rw [← intervalIntegral.integral_finsetSum fun l _ => ?_]
    · rfl
    obtain ⟨hm, C', hC'⟩ := Novel.SpliceStateBlockCrossProof.sw_data (hd l) i
    exact Novel.SpliceCrossTermDriftProof.ii_bdd
      ((Novel.SpliceCrossTermDriftProof.sigS_meas2 _ hm Tm).comp
        (measurable_const.prodMk measurable_id)) C' (fun v => hC' _ _) u T
  simp only [cross035, one_mul]
  rw [hSS, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rfl

lemma ii_R (h : PathData041 s HS HZ dL dC bZ z H) (i : Fin r) (t T : ℝ) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    IntervalIntegrable (fun u => cross035 1 (Rcomp s HS HZ i) Tm c A (Pi.single i 1) u T)
      volume 0 t :=
  (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm (Rcomp s HS HZ i) (R_data h i).1
    (R_data h i).2.choose (R_data h i).2.choose_spec c A (Pi.single i 1) 1 t T ht htT).2

end Main

lemma jumpFree : Standalone.SpliceSeveralFactorsSufficiency.jumpFreeStatement := by
  intro r k L A hA c s HS HZ dL dC bZ z Tm H h hjump t ht
  have hcase : ∀ i : Fin r, (1:ℝ) = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 t → ∀ v, t ≤ v →
      Rcomp s HS HZ i (idx033 Tm v) u = Rcomp s HS HZ i (idx033 Tm t) u := fun i => by
    right
    filter_upwards [(eventually_all_finset Tm).2 hjump] with u hu hu0
    exact Novel.SpliceCrossTermSufficiencyProof.chain Tm _ u t hu0.2 fun τ hτ huτ => by
      have := congrFun (hu τ hτ ⟨hu0.1, huτ⟩) i
      simp only [W041, Pi.zero_apply] at this
      rw [← sub_eq_zero, ← this]
      simp only [Rcomp, Scomb]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  have hX := fun i => Novel.SpliceQuasiExponentialCrossProof.uncorrelated Tm (Rcomp s HS HZ i)
    (R_data h i).1 (R_data h i).2.choose (R_data h i).2.choose_spec r A hA (Pi.single i 1) c 1 t ht
    (hcase i)
  choose K y z' hX using hX
  refine ⟨∑ i, K i, ∑ i, y i, ∑ i, z' i, fun T hT => ?_⟩
  rw [intervalIntegral.integral_congr fun u _ => regroup (Tm := Tm) (c := c) (A := A) h u T,
    intervalIntegral.integral_finsetSum fun i _ => ii_R h i t T ht hT,
    Finset.sum_congr rfl fun i _ => hX i T hT, Finset.sum_add_distrib,
    Novel.SpliceStateBlockCrossProof.cexp_sum]

lemma affine : Standalone.SpliceSeveralFactorsSufficiency.affineStatement := by
  intro r k L A hA c s HS HZ dL dC bZ z Tm H h hAX hjump t ht htH
  obtain ⟨K, y, z', hX⟩ := jumpFree r k L A hA c s HS HZ dL dC bZ z Tm H h hjump t ht
  obtain ⟨-, -, -, -, -, hG⟩ := parts_ii041 (c := c) (A := A) (Tm := Tm) h t t ht le_rfl htH.le
  let Φ : ℝ → ℝ := fun T => (∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) -
    (K + c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z')))
  have hΦa : AnalyticOnNhd ℝ Φ univ := fun T _ =>
    (hG T (mem_univ _)).sub (analyticAt_const.add
      (Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A y z' T (mem_univ _)))
  have hΦ : ∀ T ∈ Ioo t H, blockPart041 s HS HZ bZ z Tm c A t T = Φ T := by
    intro T hT
    obtain ⟨-, iD, -, iB, iX, -⟩ := parts_ii041 (c := c) (A := A) (Tm := Tm) h t T ht hT.1.le
      htH.le
    show ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T -
      ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T) = Φ T
    rw [intervalIntegral.integral_sub (iD.sub iB) iX, hX T hT.1.le]
  set T₁ := (t + H) / 2
  have hT₁ : T₁ ∈ Ioo t H := ⟨by simp only [T₁]; linarith, by simp only [T₁]; linarith⟩
  obtain ⟨ε, hε, hidx⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm T₁
  obtain ⟨k₀, k₁, hk⟩ := front_affine041 (Tm := Tm) h t ht htH.le (idx033 Tm T₁)
  set T₂ := min (T₁ + ε) H
  have hT₂ : T₁ < T₂ := lt_min (by linarith) hT₁.2
  have hI : ∀ T ∈ Ioo T₁ T₂, Φ T = -(k₀ + k₁ * T) := by
    intro T hT
    have hTI : T ∈ Ioo t H := ⟨hT₁.1.trans hT.1, lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
    have hTj : idx033 Tm T = idx033 Tm T₁ :=
      hidx T ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
    have hd := decomp041 h hA hAX t ht htH.le T hTI
    have := hk T hTj hTI.1.le
    rw [hX T hTI.1.le] at hd
    simp only [Φ]
    linarith
  have hall : ∀ T, Φ T = -(k₀ + k₁ * T) := by
    have hF : AnalyticOnNhd ℝ (fun T => Φ T + (k₀ + k₁ * T)) univ := fun T hT =>
      (hΦa T hT).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    have hmid : (T₁ + T₂) / 2 ∈ Ioo T₁ T₂ := ⟨by linarith, by linarith⟩
    intro T
    have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [hI x hx]) (mem_univ T)
    simp only [Pi.zero_apply] at this
    linarith
  exact ⟨-k₀, -k₁, fun T hT => by rw [hΦ T hT, hall T]; ring⟩

lemma converse : Standalone.SpliceSeveralFactorsSufficiency.converseStatement := by
  intro r k L A hA c s HS HZ dL dC bZ z Tm H h t T ht htT hTH hdrift
  obtain ⟨iS, iD, iP, iB, iX, -⟩ := parts_ii041 (c := c) (A := A) (Tm := Tm) h t T ht htT
    (htT.trans hTH)
  have e : ∫ u in (0:ℝ)..t, sigma041 s HS HZ Tm c A u T ⬝ᵥ
      (fun l => ∫ v in u..T, sigma041 s HS HZ Tm c A u v l) =
      ∫ u in (0:ℝ)..t, ((∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T) +
        bbS c A HZ u T + ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T) :=
    intervalIntegral.integral_congr fun u _ => expand041 h hA u T
  rw [e, intervalIntegral.integral_add iS iD, intervalIntegral.integral_add (iP.add iB) iX,
    intervalIntegral.integral_add iP iB]
  have hb : blockPart041 s HS HZ bZ z Tm c A t T =
      (∫ u in (0:ℝ)..t, driftB c A bZ z u T) - (∫ u in (0:ℝ)..t, bbS c A HZ u T) -
        ∫ u in (0:ℝ)..t, ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T := by
    show ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T -
      ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T) = _
    rw [intervalIntegral.integral_sub (iD.sub iB) iX, intervalIntegral.integral_sub iD iB]
  rw [hb] at hdrift
  have hsp : ∫ u in (0:ℝ)..t, stepPart041 s HS Tm u T =
      ∫ u in (0:ℝ)..t, ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T := rfl
  rw [hsp] at hdrift
  linarith

theorem spliceSeveralFactorsSufficiency : Standalone.SpliceSeveralFactorsSufficiency.statement :=
  ⟨jumpFree, affine, converse⟩

end Novel.SpliceSeveralFactorsSufficiencyProof

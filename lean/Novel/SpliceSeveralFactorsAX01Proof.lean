import Standalone.SpliceSeveralFactorsAX01
import Novel.SpliceSeveralFactorsCoreProof

open Matrix NormedSpace MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceStateBlockCross Standalone.SpliceStateBlockAX01
open Standalone.SpliceSeveralFactorsAX01
namespace Novel.SpliceSeveralFactorsAX01Proof
open Novel.SpliceStateBlockAX01Proof

variable {r k L : ℕ}

section Main
variable {s : Fin L → ℕ → ℝ → ℝ} {HS : Fin L → ℝ → Fin k → ℝ} {HZ : ℝ → Fin r → Fin k → ℝ}
  {dL dC : ℕ → ℝ → ℝ} {bZ z : ℝ → Fin r → ℝ} {H : ℝ} {Tm : Finset ℝ} {c : Fin r → ℝ}
  {A : Matrix (Fin r) (Fin r) ℝ}

/-- Each driver's pair (combined scales, block column) is measurable and bounded. -/
lemma data041 (h : PathData041 s HS HZ dL dC bZ z H) (l : Fin k) :
    PathData (Scomb s HS l) (fun u i => HZ u i l) := by
  obtain ⟨hs, hHS, hHZ, -, ⟨C, hsC, hHSC, hHZC, -⟩, -⟩ := h
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hB0 : 0 ≤ ∑ ℓ : Fin L, |C| * |C| := Finset.sum_nonneg fun _ _ => mul_nonneg hC0 hC0
  refine ⟨fun j => Finset.measurable_sum _ fun ℓ _ => (hs ℓ j).mul (hHS ℓ l),
    fun i => hHZ i l, (∑ ℓ : Fin L, |C| * |C|) + |C|, fun j u => ?_,
    fun u i => ((hHZC u i l).trans (le_abs_self C)).trans (le_add_of_nonneg_left hB0)⟩
  refine le_trans ?_ (le_add_of_nonneg_right hC0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [abs_mul]
  exact mul_le_mul ((hsC ℓ j u).trans (le_abs_self C)) ((hHSC ℓ u l).trans (le_abs_self C))
    (abs_nonneg _) hC0

/-- `∫_u^T σ_l(u, v) dv = S^S_l(u, T) + c A^{−1}(e^{A(T−u)} − I) H^Z_{·l}(u)`. -/
lemma sigma_int041 (h : PathData041 s HS HZ dL dC bZ z H) (hA : IsUnit A.det) (u T : ℝ)
    (l : Fin k) :
    ∫ v in u..T, sigma041 s HS HZ Tm c A u v l =
      SS033 (Scomb s HS l) Tm u T +
        c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ fun i => HZ u i l) := by
  obtain ⟨hm, -, C, hsC, -⟩ := data041 h l
  show ∫ v in u..T, (sigS033 (Scomb s HS l) Tm u v +
      c ⬝ᵥ (exp ((v - u) • A) *ᵥ fun i => HZ u i l)) = _
  generalize Scomb s HS l = S at hm hsC ⊢
  have hmv : Measurable fun v => sigS033 S Tm u v :=
    (Novel.SpliceCrossTermDriftProof.sigS_meas2 S hm Tm).comp
      (measurable_const.prodMk measurable_id)
  have i1 : IntervalIntegrable (fun v => sigS033 S Tm u v) volume u T :=
    Novel.SpliceCrossTermDriftProof.ii_bdd hmv C (fun v => hsC _ _) u T
  have i2 : IntervalIntegrable (fun v => c ⬝ᵥ (exp ((v - u) • A) *ᵥ fun i => HZ u i l))
      volume u T := (cexp_cont c A u _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, int_cexp A hA]
  rfl

/-- `σ·∫σ = ∑_l σ^S_l ∫σ^S_l + σ^B·∫σ^B + ∑_l cross_l`. -/
lemma expand041 (h : PathData041 s HS HZ dL dC bZ z H) (hA : IsUnit A.det) (u T : ℝ) :
    (sigma041 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma041 s HS HZ Tm c A u v l) =
      (∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T) + bbS c A HZ u T +
      ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T := by
  have e : (sigma041 s HS HZ Tm c A u T ⬝ᵥ fun l => ∫ v in u..T, sigma041 s HS HZ Tm c A u v l) =
      ∑ l, (sigS033 (Scomb s HS l) Tm u T + c ⬝ᵥ (exp ((T - u) • A) *ᵥ fun i => HZ u i l)) *
        (SS033 (Scomb s HS l) Tm u T +
          c ⬝ᵥ ((A⁻¹ * (exp ((T - u) • A) - 1)) *ᵥ fun i => HZ u i l)) := by
    simp only [sigma_int041 (Tm := Tm) (c := c) h hA u T]
    rfl
  rw [e]
  have alg2 : ∀ (a β S B : Fin k → ℝ), ∑ l, (a l + β l) * (S l + B l) =
      ∑ l, a l * S l + ∑ l, β l * B l + ∑ l, (a l * B l + β l * S l) := fun a β S B => by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [alg2]
  rfl

/-- The integrands of AX-01 are interval integrable on `[0, t]`, `0 ≤ t ≤ T`, `t ≤ H`. -/
lemma parts_ii041 (h : PathData041 s HS HZ dL dC bZ z H) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (htH : t ≤ H) :
    IntervalIntegrable (fun u => driftS dL dC Tm u T) volume 0 t ∧
    IntervalIntegrable (fun u => driftB c A bZ z u T) volume 0 t ∧
    IntervalIntegrable (fun u => ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T)
      volume 0 t ∧
    IntervalIntegrable (fun u => bbS c A HZ u T) volume 0 t ∧
    IntervalIntegrable (fun u => ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T)
      volume 0 t ∧
    AnalyticOnNhd ℝ (fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T)) univ := by
  have hd := data041 h
  obtain ⟨-, -, hHZ, hz, ⟨C, -, -, hHZC, hzC⟩, hdL, hdC, hbZ⟩ := h
  have hsub : uIcc 0 t ⊆ uIcc 0 H := by
    rw [uIcc_of_le ht, uIcc_of_le (ht.trans htH)]
    exact Icc_subset_Icc le_rfl htH
  obtain ⟨iD, iB, hG⟩ := block_analytic (c := c) (A := A) hHZ hz C hHZC hzC t
    fun i => (hbZ i).mono_set hsub
  refine ⟨((hdL _).mono_set hsub).add (((hdC _).mono_set hsub).mul_const T), iD T,
    ii_sum fun l => ?_, iB T,
    ii_sum fun l => Novel.SpliceSeveralFactorsCoreProof.ii_cross (hd l) Tm c A t T ht htT, hG⟩
  obtain ⟨hm, -, C', hC', -⟩ := hd l
  exact (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm (Scomb s HS l) hm C' hC' c A
    (fun _ => 0) 0 t T ht htT).1

/-- Integrating AX-01 over `[0, t]`: the summed cross term is the front end's part plus the
block's. -/
lemma decomp041 (h : PathData041 s HS HZ dL dC bZ z H) (hA : IsUnit A.det)
    (hAX : AX01Path041 s HS HZ dL dC bZ z Tm c A H) (t : ℝ) (ht : 0 ≤ t) (htH : t ≤ H) :
    ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t,
        ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T =
      ((∫ u in (0:ℝ)..t, driftS dL dC Tm u T) -
        ∫ u in (0:ℝ)..t, ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T) +
        ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T) := by
  intro T hT
  obtain ⟨iS, iD, iP, iB, iX, -⟩ := parts_ii041 (c := c) (A := A) (Tm := Tm) h t T ht hT.1.le htH
  have hae : ∫ u in (0:ℝ)..t, (driftS dL dC Tm u T + driftB c A bZ z u T) =
      ∫ u in (0:ℝ)..t, ((∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T) +
        bbS c A HZ u T + ∑ l, cross040 (Scomb s HS l) Tm c A (fun u i => HZ u i l) u T) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hAX] with u hu hu'
    rw [uIoc_of_le ht] at hu'
    rw [hu ⟨hu'.1.le, hu'.2.trans htH⟩ T ⟨hu'.2.trans hT.1.le, hT.2.le⟩, expand041 h hA u T]
  rw [intervalIntegral.integral_add iS iD, intervalIntegral.integral_add (iP.add iB) iX,
    intervalIntegral.integral_add iP iB] at hae
  rw [intervalIntegral.integral_sub iD iB]
  linarith

/-- The front end's part is affine on each maturity interval. -/
lemma front_affine041 (h : PathData041 s HS HZ dL dC bZ z H) (t : ℝ) (ht : 0 ≤ t) (htH : t ≤ H)
    (j : ℕ) : ∃ k₀ k₁ : ℝ, ∀ T, idx033 Tm T = j → t ≤ T →
      (∫ u in (0:ℝ)..t, driftS dL dC Tm u T) -
        (∫ u in (0:ℝ)..t, ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T) =
        k₀ + k₁ * T := by
  have hd := data041 h
  obtain ⟨-, -, -, -, -, hdL, hdC, -⟩ := h
  have hsub : uIcc 0 t ⊆ uIcc 0 H := by
    rw [uIcc_of_le ht, uIcc_of_le (ht.trans htH)]
    exact Icc_subset_Icc le_rfl htH
  have hstep : ∀ l : Fin k, ∃ c₀ c₁ : ℝ, ∀ T, idx033 Tm T = j → t ≤ T →
      ∫ u in (0:ℝ)..t, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T =
        c₀ + c₁ * T := fun l => by
    obtain ⟨hm, -, C', hC', -⟩ := hd l
    exact Novel.SpliceCrossTermCurveProof.step Tm (Scomb s HS l) hm C' hC' j t ht
  choose c₀ c₁ hc using hstep
  refine ⟨(∫ u in (0:ℝ)..t, dL j u) - ∑ l, c₀ l, (∫ u in (0:ℝ)..t, dC j u) - ∑ l, c₁ l,
    fun T hT htT => ?_⟩
  have e1 : ∫ u in (0:ℝ)..t, driftS dL dC Tm u T =
      (∫ u in (0:ℝ)..t, dL j u) + (∫ u in (0:ℝ)..t, dC j u) * T := by
    simp only [driftS, hT]
    rw [intervalIntegral.integral_add ((hdL j).mono_set hsub)
      (((hdC j).mono_set hsub).mul_const T), intervalIntegral.integral_mul_const]
  have e2 : ∫ u in (0:ℝ)..t, ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T =
      ∑ l, (c₀ l + c₁ l * T) := by
    rw [intervalIntegral.integral_finsetSum fun l _ => by
      obtain ⟨hm, -, C', hC', -⟩ := hd l
      exact (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm (Scomb s HS l) hm C' hC'
        (0 : Fin 1 → ℝ) 0 (fun _ => 0) 0 t T ht htT).1]
    exact Finset.sum_congr rfl fun l _ => hc l T hT htT
  rw [e1, e2, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

end Main

lemma necessity : Standalone.SpliceSeveralFactorsAX01.necessityStatement := by
  intro r k L A hA c hobs s HS HZ dL dC bZ z Tm H h hAX τ hτ hτH
  have hcore := Novel.SpliceSeveralFactorsCoreProof.core r k A hA c hobs (fun l => Scomb s HS l)
    (fun l u i => HZ u i l) (data041 h) Tm τ H hτ hτH fun t ht => by
      have htH : t ≤ H := ht.2.le.trans hτH.le
      obtain ⟨-, -, -, -, -, hG⟩ := parts_ii041 (c := c) (A := A) (Tm := Tm) h t t ht.1 le_rfl htH
      refine ⟨fun T => (∫ u in (0:ℝ)..t, driftS dL dC Tm u T) -
          ∫ u in (0:ℝ)..t, ∑ l, sigS033 (Scomb s HS l) Tm u T * SS033 (Scomb s HS l) Tm u T,
        fun T => ∫ u in (0:ℝ)..t, (driftB c A bZ z u T - bbS c A HZ u T), hG, fun j => ?_,
        decomp041 h hA hAX t ht.1 htH⟩
      obtain ⟨k₀, k₁, hk⟩ := front_affine041 (Tm := Tm) h t ht.1 htH j
      exact ⟨k₀, k₁, fun T hT hTj => hk T hTj hT.1.le⟩
  filter_upwards [hcore] with u hu hu'
  have := hu hu'
  funext i
  have hi := congrFun this i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Scomb] at hi
  simp only [W041, Pi.zero_apply]
  rw [← hi]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

lemma noThirdWay : Standalone.SpliceSeveralFactorsAX01.noThirdWayStatement := by
  intro r k L A hA c hobs s HS HZ bZ z Tm H τ hτ hτH hne dL dC h hAX
  exact hne (necessity r k L A hA c hobs s HS HZ dL dC bZ z Tm H h hAX τ hτ hτH)

theorem spliceSeveralFactorsAX01 : Standalone.SpliceSeveralFactorsAX01.statement :=
  ⟨necessity, noThirdWay⟩

end Novel.SpliceSeveralFactorsAX01Proof

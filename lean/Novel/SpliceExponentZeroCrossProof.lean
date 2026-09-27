import Standalone.SpliceExponentZeroCross
import Novel.SpliceExponentZeroQuasiPolyProof
import Novel.SpliceStateBlockCrossProof
import Novel.SpliceQuasiExponentialCrossProof
import Mathlib.Analysis.Analytic.Polynomial

open Matrix NormedSpace MeasureTheory Set Filter Polynomial
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermAlpha
open Standalone.SpliceStateBlockCross Standalone.SpliceExponentZeroCross
namespace Novel.SpliceExponentZeroCrossProof

variable {r : ℕ}

/-! ### Moments as polynomials in `T` -/

/-- `∑_{i ≤ n} binom(n, i) (∫_0^t f(u) (−u)^{n−i} du) X^i`, whose value at `T` is
`∫_0^t f(u) (T − u)^n du`. -/
noncomputable def mom (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (n + 1),
    C ((n.choose i : ℝ) * ∫ u in (0:ℝ)..t, f u * (-u) ^ (n - i)) * X ^ i

lemma mom_eval {f : ℝ → ℝ} {t : ℝ} (hf : IntervalIntegrable f volume 0 t) (n : ℕ) (T : ℝ) :
    (mom f n t).eval T = ∫ u in (0:ℝ)..t, f u * (T - u) ^ n := by
  have hi : ∀ i ∈ Finset.range (n + 1), IntervalIntegrable
      (fun u => (n.choose i : ℝ) * T ^ i * (f u * (-u) ^ (n - i))) volume 0 t := fun i _ =>
    (hf.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => (-u) ^ (n - i)).continuousOn).const_mul _
  have e : ∀ u, f u * (T - u) ^ n = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * T ^ i * (f u * (-u) ^ (n - i)) := fun u => by
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum hi]
  simp only [mom, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    intervalIntegral.integral_const_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma mom_coeff (f : ℝ → ℝ) (n : ℕ) (t : ℝ) (i : ℕ) :
    (mom f n t).coeff i =
      if i ≤ n then (n.choose i : ℝ) * ∫ u in (0:ℝ)..t, f u * (-u) ^ (n - i) else 0 := by
  simp only [mom, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma mom_top (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : (mom f n t).coeff n = ∫ u in (0:ℝ)..t, f u := by
  simp [mom_coeff]

lemma mom_hi (f : ℝ → ℝ) (n : ℕ) (t : ℝ) (i : ℕ) (hi : n < i) : (mom f n t).coeff i = 0 := by
  simp [mom_coeff, not_le.2 hi]

lemma mom_sub {f g : ℝ → ℝ} {t : ℝ} (hf : IntervalIntegrable f volume 0 t)
    (hg : IntervalIntegrable g volume 0 t) (n : ℕ) :
    mom (fun u => f u - g u) n t = mom f n t - mom g n t := by
  unfold mom
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ContinuousOn (fun u : ℝ => (-u) ^ (n - i)) (uIcc 0 t) := by fun_prop
  rw [← sub_mul, ← C_sub, ← mul_sub, ← intervalIntegral.integral_sub (hf.mul_continuousOn hc)
    (hg.mul_continuousOn hc)]
  simp only [sub_mul]

lemma mom_smul (a : ℝ) (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    mom (fun u => a * f u) n t = C a * mom f n t := by
  unfold mom
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, intervalIntegral.integral_const_mul, ← mul_assoc (C a), ← C_mul]
  ring_nf

lemma mom_zero {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : ∀ᵐ u ∂volume, u ∈ Ioc 0 t → f u = 0)
    (n : ℕ) : mom f n t = 0 := by
  unfold mom
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [intervalIntegral.integral_congr_ae (g := fun _ => 0) ?_]
  · simp
  · filter_upwards [hf] with u hu hmem
    rw [uIoc_of_le ht] at hmem
    simp [hu hmem]

/-! ### The polynomial cross term on one maturity interval -/

section
variable {s : ℕ → ℝ → ℝ} {w : ℝ → ℝ} (hs : ∀ j, Measurable (s j)) (hw : Measurable w)
  {Cs Cw : ℝ} (hsC : ∀ j u, |s j u| ≤ Cs) (hwC : ∀ u, |w u| ≤ Cw)
include hs hw hsC hwC

lemma ws_ii (j : ℕ) (t : ℝ) : IntervalIntegrable (fun u => w u * s j u) volume 0 t :=
  Novel.SpliceCrossTermDriftProof.ii_bdd (hw.mul (hs j)) (Cw * Cs) (fun u => by
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hwC u) (hsC j u) (abs_nonneg _) ((abs_nonneg _).trans (hwC u))) 0 t

lemma wk_ii (Tm : Finset ℝ) (j : ℕ) (T0 t : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0) :
    IntervalIntegrable (fun u => w u * kappa033 s Tm j T0 u) volume 0 t := by
  obtain ⟨G, hGm, hG⟩ := Novel.SpliceCrossTermDriftProof.SS_measurable s hs Tm T0
  have hT0 : 0 ≤ T0 := ht.trans htT0
  have hGb : ∀ u ∈ uIcc 0 t, |G u| ≤ Cs * T0 := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    rw [← hG u (hu.2.trans htT0), SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T0) (C := Cs)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by rw [Real.norm_eq_abs]; exact hsC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ T0 - u)] at hb
    nlinarith [hu.1, (abs_nonneg _).trans (hsC 0 0)]
  refine (Novel.SpliceCrossTermCurveProof.ii_on (hw.mul (hGm.sub ((hs j).mul_const T0)))
    (Cw * (Cs * T0 + Cs * T0)) fun u hu => ?_).congr fun u hu => ?_
  · show |w u * (G u - s j u * T0)| ≤ _
    rw [abs_mul]
    refine mul_le_mul (hwC u) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hwC u))
    refine (abs_sub _ _).trans (add_le_add (hGb u hu) ?_)
    rw [abs_mul, abs_of_nonneg hT0]
    exact mul_le_mul_of_nonneg_right (hsC j u) hT0
  · rw [uIoc_of_le ht] at hu
    show w u * (G u - s j u * T0) = w u * kappa033 s Tm j T0 u
    rw [kappa033, hG u (hu.2.trans htT0)]
end

/-- The integrated cross term of `z_{0,μ}` on `I_j`, as a polynomial in `T`, from the anchor
`T₀ ∈ I_j`. -/
noncomputable def PJ (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (w : ℝ → ℝ) (μ j : ℕ) (T0 t : ℝ) : ℝ[X] :=
  C (1 / ((μ : ℝ) + 1)) * mom (fun u => w u * s j u) (μ + 1) t +
    X * mom (fun u => w u * s j u) μ t + mom (fun u => w u * kappa033 s Tm j T0 u) μ t

/-- The jump `J_μ`. -/
noncomputable def Jpoly (Δ w : ℝ → ℝ) (μ : ℕ) (τ t : ℝ) : ℝ[X] :=
  C (1 / ((μ : ℝ) + 1)) * mom (fun u => Δ u * w u) (μ + 1) t +
    (X - C τ) * mom (fun u => Δ u * w u) μ t

section
variable {s : ℕ → ℝ → ℝ} {w : ℝ → ℝ} (hs : ∀ j, Measurable (s j)) (hw : Measurable w)
  {Cs Cw : ℝ} (hsC : ∀ j u, |s j u| ≤ Cs) (hwC : ∀ u, |w u| ≤ Cw)
include hs hw hsC hwC

omit hw hwC in
lemma crossPoly_eq (Tm : Finset ℝ) (μ j : ℕ) (T0 T u : ℝ) (hT : idx033 Tm T = j)
    (hseg : ∀ v ∈ Ioo (min T0 T) (max T0 T), idx033 Tm v = j) :
    crossPoly044 s Tm μ w u T = 1 / ((μ : ℝ) + 1) * (w u * s j u * (T - u) ^ (μ + 1)) +
      (T * (w u * s j u * (T - u) ^ μ) + w u * kappa033 s Tm j T0 u * (T - u) ^ μ) := by
  have hSS := Novel.SpliceCrossTermAlphaProof.SS_shift Tm s hs Cs hsC j u T0 T hseg
  simp only [crossPoly044, sigS033, hT, hSS, kappa033]
  ring

/-- The integral of `crossPoly_eq`'s right side is `PJ` at `T`. -/
lemma int_rhs (Tm : Finset ℝ) (μ j : ℕ) (T0 t T : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0) :
    IntervalIntegrable (fun u => 1 / ((μ : ℝ) + 1) * (w u * s j u * (T - u) ^ (μ + 1)) +
      (T * (w u * s j u * (T - u) ^ μ) + w u * kappa033 s Tm j T0 u * (T - u) ^ μ)) volume 0 t ∧
    ∫ u in (0:ℝ)..t, (1 / ((μ : ℝ) + 1) * (w u * s j u * (T - u) ^ (μ + 1)) +
      (T * (w u * s j u * (T - u) ^ μ) + w u * kappa033 s Tm j T0 u * (T - u) ^ μ)) =
        (PJ s Tm w μ j T0 t).eval T := by
  have h1 := ws_ii hs hw hsC hwC j t
  have h2 := wk_ii hs hw hsC hwC Tm j T0 t ht htT0
  have hc : ∀ n, ContinuousOn (fun u : ℝ => (T - u) ^ n) (uIcc 0 t) := fun n => by fun_prop
  have i1 := (h1.mul_continuousOn (hc (μ + 1))).const_mul (1 / ((μ : ℝ) + 1))
  have i2 := (h1.mul_continuousOn (hc μ)).const_mul T
  have i3 := h2.mul_continuousOn (hc μ)
  refine ⟨i1.add (i2.add i3), ?_⟩
  rw [intervalIntegral.integral_add i1 (i2.add i3), intervalIntegral.integral_add i2 i3,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [PJ, eval_add, eval_mul, eval_C, eval_X, mom_eval h1, mom_eval h2]
  ring

lemma int_PJ (Tm : Finset ℝ) (μ j : ℕ) (T0 t T : ℝ) (ht : 0 ≤ t) (htT0 : t ≤ T0)
    (hT : idx033 Tm T = j) (hseg : ∀ v ∈ Ioo (min T0 T) (max T0 T), idx033 Tm v = j) :
    IntervalIntegrable (fun u => crossPoly044 s Tm μ w u T) volume 0 t ∧
    ∫ u in (0:ℝ)..t, crossPoly044 s Tm μ w u T = (PJ s Tm w μ j T0 t).eval T := by
  have e : (fun u => crossPoly044 s Tm μ w u T) = fun u =>
      1 / ((μ : ℝ) + 1) * (w u * s j u * (T - u) ^ (μ + 1)) +
        (T * (w u * s j u * (T - u) ^ μ) + w u * kappa033 s Tm j T0 u * (T - u) ^ μ) :=
    funext fun u => crossPoly_eq hs hsC Tm μ j T0 T u hT hseg
  rw [e]
  exact int_rhs hs hw hsC hwC Tm μ j T0 t T ht htT0

lemma PJ_jump (Tm : Finset ℝ) (μ m : ℕ) (τ τl τr T0 T1 t : ℝ)
    (hidxl : ∀ v ∈ Ioo τl τ, idx033 Tm v = m) (hidxr : ∀ v ∈ Ico τ τr, idx033 Tm v = m + 1)
    (hT0 : T0 ∈ Ioo τl τ) (hT1 : T1 ∈ Ico τ τr) (ht : 0 ≤ t) (htT0 : t ≤ T0) :
    PJ s Tm w μ (m + 1) T1 t - PJ s Tm w μ m T0 t =
      Jpoly (fun u => s (m + 1) u - s m u) w μ τ t := by
  have htT1 : t ≤ T1 := htT0.trans (hT0.2.le.trans hT1.1)
  have e1 : ∀ n, mom (fun u => w u * s (m + 1) u) n t - mom (fun u => w u * s m u) n t =
      mom (fun u => (s (m + 1) u - s m u) * w u) n t := fun n => by
    rw [← mom_sub (ws_ii hs hw hsC hwC _ t) (ws_ii hs hw hsC hwC _ t)]
    congr 1
    funext u
    ring
  have e2 : mom (fun u => w u * kappa033 s Tm (m + 1) T1 u) μ t -
      mom (fun u => w u * kappa033 s Tm m T0 u) μ t =
        -(C τ * mom (fun u => (s (m + 1) u - s m u) * w u) μ t) := by
    rw [← mom_sub (wk_ii hs hw hsC hwC Tm _ T1 t ht htT1) (wk_ii hs hw hsC hwC Tm _ T0 t ht htT0),
      ← neg_mul, ← map_neg, ← mom_smul]
    congr 1
    funext u
    rw [Novel.SpliceQuasiExponentialCrossProof.kappa_jump Tm s hs Cs hsC m τ τl τr T0 T1 hidxl
      hidxr hT0 hT1 u]
    ring
  simp only [PJ, Jpoly]
  linear_combination C (1 / ((μ : ℝ) + 1)) * e1 (μ + 1) + X * e1 μ + e2
end

lemma Jpoly_top (Δ w : ℝ → ℝ) (μ : ℕ) (τ t : ℝ) :
    (Jpoly Δ w μ τ t).coeff (μ + 1) =
      ((μ : ℝ) + 2) / ((μ : ℝ) + 1) * ∫ u in (0:ℝ)..t, Δ u * w u := by
  simp only [Jpoly, coeff_add, coeff_C_mul, sub_mul, coeff_sub, coeff_X_mul, mom_top,
    mom_hi _ μ t (μ + 1) (Nat.lt_succ_self μ)]
  field_simp
  ring

lemma Jpoly_hi (Δ w : ℝ → ℝ) (μ : ℕ) (τ t : ℝ) (i : ℕ) (hi : μ + 1 < i) :
    (Jpoly Δ w μ τ t).coeff i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Jpoly, coeff_add, coeff_C_mul, sub_mul, coeff_sub, coeff_X_mul,
    mom_hi _ (μ + 1) t (k + 1) hi, mom_hi _ μ t k (by omega), mom_hi _ μ t (k + 1) (by omega)]
  ring

lemma Jpoly_deg (Δ w : ℝ → ℝ) (μ : ℕ) (τ t : ℝ) : (Jpoly Δ w μ τ t).natDegree ≤ μ + 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun i hi => Jpoly_hi Δ w μ τ t i (by exact_mod_cast hi)

lemma Jpoly_eval {Δ w : ℝ → ℝ} {t : ℝ} (hf : IntervalIntegrable (fun u => Δ u * w u) volume 0 t)
    (μ : ℕ) (τ T : ℝ) :
    (Jpoly Δ w μ τ t).eval T = ∫ u in (0:ℝ)..t, Δ u * w u *
      ((T - u) ^ (μ + 1) / ((μ : ℝ) + 1) + (T - u) ^ μ * (T - τ)) := by
  have hc : ∀ n, ContinuousOn (fun u : ℝ => (T - u) ^ n) (uIcc 0 t) := fun n => by fun_prop
  simp only [Jpoly, eval_add, eval_mul, eval_C, eval_sub, eval_X, mom_eval hf]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hf.mul_continuousOn (hc _)).const_mul _)
      ((hf.mul_continuousOn (hc _)).const_mul _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  ring

lemma Jpoly_zero {Δ w : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ᵐ u ∂volume, u ∈ Ioc 0 t → Δ u * w u = 0) (μ : ℕ) (τ : ℝ) : Jpoly Δ w μ τ t = 0 := by
  simp [Jpoly, mom_zero ht h]


lemma dw_ii {s : ℕ → ℝ → ℝ} {w : ℝ → ℝ} (hs : ∀ j, Measurable (s j)) (hw : Measurable w)
    {Cs Cw : ℝ} (hsC : ∀ j u, |s j u| ≤ Cs) (hwC : ∀ u, |w u| ≤ Cw) (m : ℕ) (t : ℝ) :
    IntervalIntegrable (fun u => (s (m + 1) u - s m u) * w u) volume 0 t :=
  Novel.SpliceCrossTermDriftProof.ii_bdd (((hs _).sub (hs _)).mul hw) ((Cs + Cs) * Cw) (fun u => by
    rw [Pi.mul_apply, Pi.sub_apply, abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hsC _ _) (hsC _ _))) (hwC u) (abs_nonneg _)
      (by linarith [(abs_nonneg _).trans (hsC 0 0)])) 0 t

lemma jump : Standalone.SpliceExponentZeroCross.jumpStatement := by
  intro s w hs hw ⟨C, hsC, hwC⟩ Tm μ m t τ τl τr ht hl hr hidxl hidxr htτ
  have hτl' : max τl t < τ := max_lt hl htτ
  set T0 := (max τl t + τ) / 2
  have hT0 : T0 ∈ Ioo τl τ :=
    ⟨lt_of_le_of_lt (le_max_left τl t) (by simp only [T0]; linarith), by simp only [T0]; linarith⟩
  have htT0 : t ≤ T0 := by simp only [T0]; linarith [le_max_right τl t]
  have hτ1 : τ ∈ Ico τ τr := ⟨le_rfl, hr⟩
  refine ⟨PJ s Tm w μ m T0 t, PJ s Tm w μ (m + 1) τ t, fun T hT htT => ?_, fun T hT => ?_, ?_⟩
  · exact (int_PJ hs hw hsC hwC Tm μ m T0 t T ht htT0 (hidxl T hT) fun v hv =>
      hidxl v ⟨(lt_min hT0.1 hT.1).trans hv.1, hv.2.trans (max_lt hT0.2 hT.2)⟩).2
  · exact (int_PJ hs hw hsC hwC Tm μ (m + 1) τ t T ht htτ.le (hidxr T hT) fun v hv =>
      hidxr v ⟨(le_min le_rfl hT.1).trans hv.1.le, hv.2.trans (max_lt hr hT.2)⟩).2
  rw [PJ_jump hs hw hsC hwC Tm μ m τ τl τr T0 τ t hidxl hidxr hT0 hτ1 ht htT0]
  exact ⟨fun T => Jpoly_eval (dw_ii hs hw hsC hwC m t) μ τ T, Jpoly_deg _ _ μ τ t,
    Jpoly_top _ _ μ τ t⟩

/-! ### The argument on one path -/

lemma cross040_ii {s : ℕ → ℝ → ℝ} {w : ℝ → Fin r → ℝ} (h : PathData s w) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun u => cross040 s Tm c A w u T) volume 0 t := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin r)), IntervalIntegrable (fun u =>
      Standalone.SpliceQuasiExponentialCross.cross035 1 (Novel.SpliceStateBlockCrossProof.sw s w i)
        Tm c A (Pi.single i 1) u T) volume 0 t := fun i _ => by
    obtain ⟨hm, C, hC⟩ := Novel.SpliceStateBlockCrossProof.sw_data h i
    exact (Novel.SpliceRandomScalesNecessityProof.ii_parts Tm _ hm C hC c A (Pi.single i 1) 1 t T
      ht htT).2
  convert IntervalIntegrable.sum _ hi using 1
  funext u
  rw [Finset.sum_apply, Novel.SpliceStateBlockCrossProof.cross_sum]

/-- A real-analytic `G` equal to `c e^{AT}(y + T z) + P(T)` on an interval equals it everywhere. -/
lemma ext_all (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (G : ℝ → ℝ)
    (hG : AnalyticOnNhd ℝ G univ) (y z : Fin r → ℝ) (P : ℝ[X]) (d e : ℝ) (hde : d < e)
    (h : ∀ T ∈ Ioo d e, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + P.eval T) :
    ∀ T, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + P.eval T := by
  intro T
  have hF : AnalyticOnNhd ℝ (fun T => G T - (c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + P.eval T))
      univ := fun x hx => (hG x hx).sub
        ((Novel.SpliceQuasiExponentialConsistencyProof.quasi_analytic c A y z x hx).add
          (AnalyticOnNhd.eval_polynomial P x hx))
  have hmid : (d + e) / 2 ∈ Ioo d e := ⟨by linarith, by linarith⟩
  have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
    (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [h x hx]) (mem_univ T)
  simp only [Pi.zero_apply] at this
  linarith

lemma core : Standalone.SpliceExponentZeroCross.coreStatement := by
  intro r A hA c hobs s wζ d wP h Tm τ H hτ hτH hdec
  obtain ⟨hPD, hwm, Cw, hwC⟩ := h
  obtain ⟨hs, -, Cs, hsC, -⟩ := id hPD
  obtain ⟨h1, τl, hl, hidxl⟩ := Novel.SpliceCrossTermConsistencyProof.idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm τ
  set m := idx033 Tm τ - 1
  have hm : m + 1 = idx033 Tm τ := by omega
  have hidxr' : ∀ v ∈ Ico τ (τ + ε), idx033 Tm v = m + 1 := fun v hv => by
    rw [hm]; exact hidxr v hv
  set Δ : ℝ → ℝ := fun u => s (m + 1) u - s m u
  have key : ∀ t ∈ Ico 0 τ, vvec040 A Δ wζ t = 0 ∧
      ∀ i, 2 ≤ i → (∑ μ ∈ Finset.range (d + 1), Jpoly Δ (wP μ) μ τ t).coeff i = 0 := by
    intro t ht
    obtain ⟨p, G, hGa, hp, hX⟩ := hdec t ht
    obtain ⟨k₀, k₁, y₀, z₀, y₁, z₁, hL, hR, hy, hz⟩ := Novel.SpliceStateBlockCrossProof.explicit r
      s wζ hPD Tm A hA c t ht.1 m τ τl (τ + ε) hl (by linarith) hidxl hidxr' ht.2
    have hτl' : max τl t < τ := max_lt hl ht.2
    set τr' := min (τ + ε) H
    have hτr' : τ < τr' := lt_min (by linarith) hτH
    set T0 := (max τl t + τ) / 2
    have hT0 : T0 ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left τl t) (by simp only [T0]; linarith),
      by simp only [T0]; linarith⟩
    have htT0 : t ≤ T0 := by simp only [T0]; linarith [le_max_right τl t]
    have hτ1 : τ ∈ Ico τ (τ + ε) := ⟨le_rfl, by linarith⟩
    set S₀ := ∑ μ ∈ Finset.range (d + 1), PJ s Tm (wP μ) μ m T0 t
    set S₁ := ∑ μ ∈ Finset.range (d + 1), PJ s Tm (wP μ) μ (m + 1) τ t
    have hsplit : ∀ T, t ≤ T → (∀ μ ∈ Finset.range (d + 1),
        IntervalIntegrable (fun u => crossPoly044 s Tm μ (wP μ) u T) volume 0 t) →
        ∫ u in (0:ℝ)..t, cross044 s Tm c A wζ d wP u T = (∫ u in (0:ℝ)..t, cross040 s Tm c A wζ u T) +
          ∑ μ ∈ Finset.range (d + 1), ∫ u in (0:ℝ)..t, crossPoly044 s Tm μ (wP μ) u T := by
      intro T htT hi
      have hsum : IntervalIntegrable (fun u => ∑ μ ∈ Finset.range (d + 1),
          crossPoly044 s Tm μ (wP μ) u T) volume 0 t := by
        convert IntervalIntegrable.sum _ hi using 1
        funext u
        rw [Finset.sum_apply]
      unfold cross044
      rw [intervalIntegral.integral_add (cross040_ii hPD Tm c A t T ht.1 htT) hsum,
        intervalIntegral.integral_finsetSum hi]
    -- `G` on the left and on the right of `τ`
    obtain ⟨κ₀, κ₁, hκ⟩ := hp m
    obtain ⟨l₀, l₁, hl'⟩ := hp (m + 1)
    have hGL := ext_all c A G hGa y₀ z₀ (C (k₀ - κ₀) - C κ₁ * X + S₀) (max τl t) τ hτl'
      fun T hT => by
        have hTt : t < T := lt_of_le_of_lt (le_max_right _ _) hT.1
        have hTI : T ∈ Ioo t H := ⟨hTt, by linarith [hT.2]⟩
        have hTl : T ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left _ _) hT.1, hT.2⟩
        have hPJ := fun μ (_ : μ ∈ Finset.range (d + 1)) => int_PJ hs (hwm μ) hsC (hwC μ) Tm μ m T0
          t T ht.1 htT0 (hidxl T hTl) fun v hv =>
            hidxl v ⟨(lt_min hT0.1 hTl.1).trans hv.1, hv.2.trans (max_lt hT0.2 hTl.2)⟩
        have := hX T hTI
        rw [hsplit T hTt.le fun μ hμ => (hPJ μ hμ).1, hL T hTl hTt.le, hκ T hTI (hidxl T hTl),
          Finset.sum_congr rfl fun μ hμ => (hPJ μ hμ).2] at this
        simp only [S₀, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_finsetSum]
        linarith
    have hGR := ext_all c A G hGa y₁ z₁ (C (k₁ - l₀) - C l₁ * X + S₁) τ τr' hτr'
      fun T hT => by
        have hTI : T ∈ Ioo t H := ⟨lt_of_le_of_lt ht.2.le hT.1,
          lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
        have hTr : T ∈ Ico τ (τ + ε) := ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
        have hPJ := fun μ (_ : μ ∈ Finset.range (d + 1)) => int_PJ hs (hwm μ) hsC (hwC μ) Tm μ
          (m + 1) τ t T ht.1 ht.2.le (hidxr' T hTr) fun v hv =>
            hidxr' v ⟨(le_min le_rfl hTr.1).trans hv.1.le, hv.2.trans (max_lt hτ1.2 hTr.2)⟩
        have := hX T hTI
        rw [hsplit T (ht.2.le.trans hTr.1) fun μ hμ => (hPJ μ hμ).1, hR T hTr,
          hl' T hTI (hidxr' T hTr), Finset.sum_congr rfl fun μ hμ => (hPJ μ hμ).2] at this
        simp only [S₁, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_finsetSum]
        linarith
    set Q := (C (k₀ - κ₀) - C κ₁ * X + S₀) - (C (k₁ - l₀) - C l₁ * X + S₁)
    have hdiff : ∀ T : ℝ, c ⬝ᵥ (exp (T • A) *ᵥ ((y₁ - y₀) + T • (z₁ - z₀))) = Q.eval T := by
      intro T
      have e1 := hGL T
      have e2 := hGR T
      have : c ⬝ᵥ (exp (T • A) *ᵥ ((y₁ - y₀) + T • (z₁ - z₀))) =
          c ⬝ᵥ (exp (T • A) *ᵥ (y₁ + T • z₁)) - c ⬝ᵥ (exp (T • A) *ᵥ (y₀ + T • z₀)) := by
        simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
        ring
      rw [this, eval_sub]
      linarith
    obtain ⟨hQ, hq⟩ := Novel.SpliceExponentZeroQuasiPolyProof.quasiPoly r A hA c (y₁ - y₀)
      (z₁ - z₀) Q 0 1 one_pos fun T _ => hdiff T
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hy, hz] at hq
      set v := vvec040 A Δ wζ t
      refine Novel.SpliceStateBlockObservabilityProof.observability r A hA c hobs τ 0 1 v one_pos
        fun T _ => ?_
      have e : c ⬝ᵥ (exp (T • A) *ᵥ ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ v + T • v)) =
          c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ v)) := by
        simp only [add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
          dotProduct_smul, smul_eq_mul]
        ring
      rw [← e]
      exact hq T
    · have hJ : S₁ - S₀ = ∑ μ ∈ Finset.range (d + 1), Jpoly Δ (wP μ) μ τ t := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun μ _ => PJ_jump hs (hwm μ) hsC (hwC μ) Tm μ m τ τl
          (τ + ε) T0 τ t hidxl hidxr' hT0 hτ1 ht.1 htT0
      have hS : S₁ - S₀ = C (k₀ - κ₀) - C (k₁ - l₀) + (C l₁ - C κ₁) * X := by
        linear_combination -hQ
      rw [← hJ, hS]
      simp [coeff_C, coeff_X, sub_mul, show i ≠ 0 by omega, show 1 ≠ i by omega]
  refine ⟨?_, ?_⟩
  · filter_upwards [Novel.SpliceStateBlockCrossProof.zero_of_vvec hPD A m τ fun t ht => (key t ht).1] with u hu hu'
    rw [← hm]
    exact hu hu'
  -- the polynomial coefficients, from `μ = d` down
  have hloc : ∀ μ, LocallyIntegrable (fun u => Δ u * wP μ u) volume := fun μ => by
    refine (locallyIntegrable_const ((Cs + Cs) * Cw)).mono
      (((hs (m + 1)).sub (hs m)).mul (hwm μ)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    rw [abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hsC _ _) (hsC _ _))) (hwC μ u)
      (abs_nonneg _) (by linarith [(abs_nonneg _).trans (hsC 0 0)])
  have hpoly : ∀ n μ, d - μ = n → 1 ≤ μ → μ ≤ d →
      ∀ᵐ u ∂volume, u ∈ Ico 0 τ → Δ u * wP μ u = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro μ hn hμ1 hμd
      have hIH : ∀ ν, μ < ν → ν ≤ d → ∀ᵐ u ∂volume, u ∈ Ico 0 τ → Δ u * wP ν u = 0 :=
        fun ν h1' h2' => ih (d - ν) (by omega) ν rfl (by omega) h2'
      refine Novel.SpliceCrossTermAnalyticProof.lebesgue 0 τ _ (hloc μ) fun t ht => ?_
      simp only [zero_mul, Real.exp_zero, one_mul]
      have hc := (key t ht).2 (μ + 1) (by omega)
      rw [finsetSum_coeff, Finset.sum_eq_single μ (fun ν hν hne => ?_)
        (fun h => absurd (Finset.mem_range.2 (by omega)) h), Jpoly_top] at hc
      · have hpos : (0:ℝ) < ((μ : ℝ) + 2) / ((μ : ℝ) + 1) := by positivity
        exact (mul_eq_zero.1 hc).resolve_left hpos.ne'
      · rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Jpoly_hi _ _ ν τ t (μ + 1) (by omega)
        · have hz := hIH ν hgt (by simpa [Nat.lt_succ_iff] using hν)
          rw [Jpoly_zero ht.1 (by
            filter_upwards [hz] with u hu hmem
            exact hu ⟨hmem.1.le, hmem.2.trans_lt ht.2⟩), coeff_zero]
  intro μ hμ1 hμd
  filter_upwards [hpoly (d - μ) μ rfl hμ1 hμd] with u hu hu'
  rw [← hm]
  exact hu hu'

theorem spliceExponentZeroCross : Standalone.SpliceExponentZeroCross.statement := ⟨jump, core⟩

end Novel.SpliceExponentZeroCrossProof

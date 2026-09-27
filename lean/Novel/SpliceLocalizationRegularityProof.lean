import Standalone.SpliceLocalizationRegularity
import Novel.SpliceLocalizationConverseProof
import Novel.SpliceStateBlockAX01Proof

open Matrix NormedSpace MeasureTheory Set
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse Standalone.SpliceLocalizationRegularity
namespace Novel.SpliceLocalizationRegularityProof

variable {k r : ℕ}

lemma abs_sum_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {C : ℝ}
    (hf : ∀ i ∈ s, |f i| ≤ C) : |∑ i ∈ s, f i * g i| ≤ C * ∑ i ∈ s, |g i| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hf i hi) (abs_nonneg _)

/-- A bound for `c e^{xA}` on `[0, H]`. -/
lemma ephi_bound (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (H : ℝ) :
    ∃ Ce, 0 ≤ Ce ∧ ∀ x ∈ Icc 0 H, ∀ i, |ephi c A x i| ≤ Ce := by
  have hc : Continuous fun x => ephi c A x := continuous_pi fun i =>
    continuousOn_univ.1 (Novel.SpliceStateBlockAX01Proof.row_analytic c A i).continuousOn
  obtain ⟨Ce, hCe⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn (s := Icc 0 H)
  refine ⟨max Ce 0, le_max_right _ _, fun x hx i => ?_⟩
  exact ((norm_le_pi_norm (ephi c A x) i).trans (hCe x hx)).trans (le_max_left _ _)

/-- `|x^μ| ≤ B^d` on `[0, H]` for `μ ≤ d`, `B = max 1 |H|`. -/
lemma pow_bound {H x : ℝ} (hx : x ∈ Icc 0 H) {μ d : ℕ} (hμ : μ ≤ d) :
    |x ^ μ| ≤ (max 1 |H|) ^ d := by
  have hB : 1 ≤ max 1 |H| := le_max_left _ _
  have hxB : |x| ≤ max 1 |H| := by
    rw [abs_of_nonneg hx.1]; exact hx.2.trans ((le_abs_self H).trans (le_max_right _ _))
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) hxB μ).trans (pow_le_pow_right₀ hB hμ)

lemma sigEnvS : sigEnvStatement := by
  intro k r d c A S H
  obtain ⟨Ce, hCe0, hCe⟩ := ephi_bound c A H
  set B := max 1 |H|
  refine ⟨B ^ d + Ce, fun p u T hu huT hTH l => ?_⟩
  have hx : T - u ∈ Icc 0 H := ⟨by linarith, by linarith⟩
  have hBd : 0 ≤ B ^ d := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  simp only [sig049, Pi.add_apply, sigB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct]
  have h1 : |p.V (nS S T) l| ≤ ∑ m ∈ Finset.range (S.card + 1), |p.V m l| :=
    Finset.single_le_sum (f := fun m => |p.V m l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_filter_le _ _)))
  have h2 := abs_sum_mul_le (Finset.range (d + 1)) (fun μ => (T - u) ^ μ) (fun μ => p.Hp μ l)
    (C := B ^ d) fun μ hμ => pow_bound hx (by simpa [Nat.lt_succ_iff] using hμ)
  have h3 := abs_sum_mul_le Finset.univ (fun i => ephi c A (T - u) i) (fun i => p.Hz i l)
    (C := Ce) fun i _ => hCe _ hx i
  have hS1 : 0 ≤ ∑ μ ∈ Finset.range (d + 1), |p.Hp μ l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ i, |p.Hz i l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc _ ≤ |p.V (nS S T) l| + (|∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * p.Hp μ l| +
        |∑ i, ephi c A (T - u) i * p.Hz i l|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ _ := by nlinarith [mul_nonneg hCe0 hS1, mul_nonneg hBd hS2]

lemma alphaEnvS : alphaEnvStatement := by
  intro k r d c A S H
  obtain ⟨Ce, hCe0, hCe⟩ := ephi_bound c A H
  set B := max 1 |H|
  set NA := ∑ i, ∑ j, |A i j|
  have hNA : 0 ≤ NA := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBd : 0 ≤ B ^ d := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  refine ⟨B ^ d + Ce + d * B ^ d + Ce * NA, fun p u T hu huT hTH => ?_⟩
  have hx : T - u ∈ Icc 0 H := ⟨by linarith, by linarith⟩
  have hT : |T| ≤ |H| := by rw [abs_of_nonneg (hu.trans huT)]; exact hTH.trans (le_abs_self H)
  simp only [alpha049, driftB049, dotProduct, mulVec]
  -- the front end
  have h1 : |p.dL (nS S T)| + |p.dC (nS S T) * T| ≤
      ∑ m ∈ Finset.range (S.card + 1), (|p.dL m| + |H| * |p.dC m|) := by
    rw [abs_mul]
    have hmem : nS S T ∈ Finset.range (S.card + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_filter_le S fun τ => τ ≤ T))
    refine le_trans ?_ (Finset.single_le_sum (f := fun m => |p.dL m| + |H| * |p.dC m|)
      (fun _ _ => by positivity) hmem)
    have := mul_le_mul_of_nonneg_left hT (abs_nonneg (p.dC (nS S T)))
    linarith
  -- the block
  have h2 := abs_sum_mul_le (Finset.range (d + 1)) (fun μ => (T - u) ^ μ) (fun μ => p.bP μ)
    (C := B ^ d) fun μ hμ => pow_bound hx (by simpa [Nat.lt_succ_iff] using hμ)
  have h3 := abs_sum_mul_le Finset.univ (fun i => ephi c A (T - u) i) (fun i => p.bZ i)
    (C := Ce) fun i _ => hCe _ hx i
  have h4 := abs_sum_mul_le (Finset.range (d + 1)) (fun μ => (μ : ℝ) * (T - u) ^ (μ - 1))
    (fun μ => p.zP μ) (C := d * B ^ d) fun μ hμ => by
      have hμd : μ ≤ d := by simpa [Nat.lt_succ_iff] using hμ
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul (by exact_mod_cast hμd) (pow_bound hx (by omega)) (abs_nonneg _)
        (Nat.cast_nonneg _)
  have h5 : |∑ i, ephi c A (T - u) i * ∑ j, A i j * p.z j| ≤ Ce * NA * ∑ j, |p.z j| := by
    refine (abs_sum_mul_le Finset.univ _ _ (C := Ce) fun i _ => hCe _ hx i).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCe0
    calc ∑ i, |∑ j, A i j * p.z j| ≤ ∑ i, ∑ j, |A i j| * |p.z j| :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (le_of_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _))
      _ ≤ ∑ i, ∑ j, |A i j| * ∑ j', |p.z j'| := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun j => |p.z j|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)) (abs_nonneg _)
      _ = NA * ∑ j, |p.z j| := by simp only [← Finset.sum_mul, NA]
  have hs1 : 0 ≤ ∑ μ ∈ Finset.range (d + 1), |p.bP μ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs2 : 0 ≤ ∑ μ ∈ Finset.range (d + 1), |p.zP μ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs3 : 0 ≤ ∑ i, |p.bZ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs4 : 0 ≤ ∑ i, |p.z i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsplit : (∑ μ ∈ Finset.range (d + 1), (|p.bP μ| + |p.zP μ|)) + ∑ i, (|p.bZ i| + |p.z i|) =
      (∑ μ ∈ Finset.range (d + 1), |p.bP μ|) + (∑ μ ∈ Finset.range (d + 1), |p.zP μ|) +
        ((∑ i, |p.bZ i|) + ∑ i, |p.z i|) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit]
  have htri : |p.dL (nS S T) + p.dC (nS S T) * T +
      ((∑ μ ∈ Finset.range (d + 1), p.bP μ * (T - u) ^ μ) + ∑ i, ephi c A (T - u) i * p.bZ i -
        ((∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * p.zP μ * (T - u) ^ (μ - 1)) +
          ∑ i, ephi c A (T - u) i * ∑ j, A i j * p.z j))| ≤
      (|p.dL (nS S T)| + |p.dC (nS S T) * T|) +
        (|∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * p.bP μ| +
          |∑ i, ephi c A (T - u) i * p.bZ i| +
          |∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * (T - u) ^ (μ - 1) * p.zP μ| +
          |∑ i, ephi c A (T - u) i * ∑ j, A i j * p.z j|) := by
    have e1 : ∑ μ ∈ Finset.range (d + 1), p.bP μ * (T - u) ^ μ =
        ∑ μ ∈ Finset.range (d + 1), (T - u) ^ μ * p.bP μ := Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * p.zP μ * (T - u) ^ (μ - 1) =
        ∑ μ ∈ Finset.range (d + 1), (μ : ℝ) * (T - u) ^ (μ - 1) * p.zP μ :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _)) ?_)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _)) ((abs_add_le _ _))) |>.trans ?_
    linarith
  refine htri.trans ?_
  nlinarith [mul_nonneg hCe0 hs1, mul_nonneg hCe0 hs2, mul_nonneg hBd hs3, mul_nonneg hBd hs4,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hBd) hs1, mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hBd) hs3,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hBd) hs4, mul_nonneg (mul_nonneg hCe0 hNA) hs1,
    mul_nonneg (mul_nonneg hCe0 hNA) hs2, mul_nonneg (mul_nonneg hCe0 hNA) hs3, mul_nonneg hBd hs2,
    mul_nonneg hCe0 hs4, mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hBd) hs2, mul_nonneg hBd hs1,
    mul_nonneg hCe0 hs3, mul_nonneg (mul_nonneg hCe0 hNA) hs4]

lemma envelopeS : envelopeStatement := by
  intro k r d c A S H D hV hHp hHz hbP hbZ hzP hz C
  have hr : ∀ {n m : ℕ}, m ∈ Finset.range (n + 1) → m ≤ n := fun h => by
    simpa [Nat.lt_succ_iff] using h
  have habs : ∀ {f : ℝ → ℝ}, MemLp f 2 (volume.restrict (Icc 0 H)) →
      MemLp (fun u => |f u|) 2 (volume.restrict (Icc 0 H)) := fun h => by
    simpa only [Real.norm_eq_abs] using h.norm
  have hI := Novel.SpliceLocalizationConverseProof.integrabilityS k r d c A S H D hV hHp hHz hbP
    hbZ hzP hz
  refine ⟨fun l => ?_, ?_⟩
  · exact (memLp_finsetSum _ fun m hm => habs (hV m (hr hm) l)).add
      (((memLp_finsetSum _ fun μ hμ => habs (hHp μ (hr hμ) l)).add
        (memLp_finsetSum _ fun i _ => habs (hHz i l))).const_mul C)
  · exact (integrable_finsetSum _ fun m hm => ((hI m (hr hm)).1.abs).add
      (((hI m (hr hm)).2.abs).const_mul |H|)).add
      (((integrable_finsetSum _ fun μ hμ => (hbP μ (hr hμ)).abs.add (hzP μ (hr hμ)).abs).add
        (integrable_finsetSum _ fun i _ => (hbZ i).abs.add (hz i).abs)).const_mul C)

theorem spliceLocalizationRegularity : Standalone.SpliceLocalizationRegularity.statement := ⟨sigEnvS, alphaEnvS, envelopeS⟩

end Novel.SpliceLocalizationRegularityProof

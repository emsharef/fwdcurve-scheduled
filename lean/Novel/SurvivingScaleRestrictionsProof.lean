import Standalone.SurvivingScaleRestrictions
import Novel.GaussianMeetingVarianceConeProof
import Novel.ZeroMeanReversionVarianceSupportProof
import Mathlib.Analysis.LocallyConvex.Separation

open MeasureTheory Matrix Set
open Standalone.GaussianMeetingVarianceCone
open Standalone.SurvivingScaleRestrictions

namespace Novel.SurvivingScaleRestrictionsProof

/-! ### (a) the fixed direction of the kernel on a meeting interval -/

lemma fixedDirection : fixedDirectionStatement := by
  intro lam α β a hαβ ha hint
  have hpos : 0 < ∫ s in α..β, Real.exp (2 * lam * s) :=
    intervalIntegral.integral_pos hαβ (by fun_prop) (fun _ _ => (Real.exp_pos _).le)
      ⟨α, ⟨le_rfl, hαβ.le⟩, Real.exp_pos _⟩
  have hint' : IntervalIntegrable (fun s => a s ^ 2 * Real.exp (2 * lam * s)) volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ.le]
    exact hint
  have hnum : 0 ≤ ∫ s in α..β, a s ^ 2 * Real.exp (2 * lam * s) :=
    intervalIntegral.integral_nonneg hαβ.le fun s _ => by positivity
  refine ⟨(∫ s in α..β, a s ^ 2 * Real.exp (2 * lam * s)) / ∫ s in α..β, Real.exp (2 * lam * s),
    div_nonneg hnum hpos.le, fun T => ?_⟩
  have hsplit : (fun s => a s ^ 2 * Real.exp (-2 * lam * (T - s))) =
      fun s => Real.exp (-2 * lam * T) * (a s ^ 2 * Real.exp (2 * lam * s)) := by
    funext s
    rw [show -2 * lam * (T - s) = -2 * lam * T + 2 * lam * s by ring, Real.exp_add]
    ring
  have hH : H lam T α β = Real.exp (-2 * lam * T) * ∫ s in α..β, Real.exp (2 * lam * s) := by
    rw [← GaussianMeetingVarianceConeProof.integral_H, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show Real.exp (-2 * lam * (T - s)) = Real.exp (-2 * lam * T) * Real.exp (2 * lam * s)
    rw [show -2 * lam * (T - s) = -2 * lam * T + 2 * lam * s by ring, Real.exp_add]
  rw [hsplit, intervalIntegral.integral_const_mul, hH]
  field_simp

/-! ### (b) the dual cone and Farkas' lemma -/

lemma cone_eq_cone0154 {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℝ) :
    cone M = Standalone.ZeroMeanReversionVarianceSupport.cone0154 M 0 := by
  ext V
  simp only [cone, Standalone.ZeroMeanReversionVarianceSupport.cone0154, mem_ofPred_eq, zero_add]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

lemma cone_convex {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℝ) : Convex ℝ (cone M) := by
  intro V hV W hW s r hs hr hsr
  obtain ⟨q, hq, rfl⟩ := hV
  obtain ⟨p, hp, rfl⟩ := hW
  refine ⟨s • q + r • p, fun j => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hq j; have := hp j; positivity, ?_⟩
  rw [mulVec_add, mulVec_smul, mulVec_smul]

lemma cone_smul_mem {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℝ) {V : Fin m → ℝ} (hV : V ∈ cone M)
    {c : ℝ} (hc : 0 ≤ c) : c • V ∈ cone M := by
  obtain ⟨q, hq, rfl⟩ := hV
  exact ⟨c • q, fun j => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hq j),
    mulVec_smul _ _ _⟩

lemma zero_mem_cone {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℝ) : (0 : Fin m → ℝ) ∈ cone M :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma dual : dualStatement := by
  intro m d M hM
  have hclosed : IsClosed (cone M) := by
    rw [cone_eq_cone0154]
    exact ZeroMeanReversionVarianceSupportProof.closed_translate M 0 hM
  have hgen : ∀ w : Fin m → ℝ, (∀ V ∈ cone M, 0 ≤ dotProduct w V) ↔
      ∀ j, 0 ≤ M.transpose.mulVec w j := by
    intro w
    constructor
    · intro h j
      have he := h (M.mulVec (Pi.single j 1)) ⟨Pi.single j 1, fun k => by
        by_cases hk : k = j <;> simp [hk], rfl⟩
      rw [GaussianMeetingVarianceConeProof.dot_mulVec] at he
      simpa using he
    · rintro hw V ⟨q, hq, rfl⟩
      rw [GaussianMeetingVarianceConeProof.dot_mulVec]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hq j)
  refine ⟨hgen, fun V => ⟨fun hV w hw => (hgen w).2 hw V hV, fun h => ?_⟩,
    fun w => GaussianMeetingVarianceConeProof.annihilates_cone M w⟩
  -- Farkas: separate a point outside the closed convex cone
  by_contra hV
  obtain ⟨f, u, hfV, hf⟩ := geometric_hahn_banach_point_closed (cone_convex M) hclosed hV
  have hu : u < 0 := by simpa using hf 0 (zero_mem_cone M)
  -- `f` is nonnegative on the cone, else scaling would push it below `u`
  have hfnn : ∀ W ∈ cone M, 0 ≤ f W := by
    intro W hW
    by_contra hneg
    have hneg' : f W < 0 := lt_of_not_ge hneg
    obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ c * f W < u := by
      refine ⟨(u - 1) / f W, div_nonneg_of_nonpos (by linarith) hneg'.le, ?_⟩
      rw [div_mul_cancel₀ _ hneg'.ne]
      linarith
    have := hf (c • W) (cone_smul_mem M hW hc0)
    rw [map_smul, smul_eq_mul] at this
    linarith
  -- read `f` as a dot product
  set w : Fin m → ℝ := fun i => f (Pi.single i 1) with hw
  have hfw : ∀ x, f x = dotProduct w x := fun x =>
    GaussianMeetingVarianceConeProof.functional_dot (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) x
  have hwA : ∀ j, 0 ≤ M.transpose.mulVec w j :=
    (hgen w).1 fun W hW => by rw [← hfw]; exact hfnn W hW
  have := h w hwA
  rw [← hfw] at this
  linarith

/-! ### (c) the consecutive-meeting ratio bounds -/

lemma H_shift (lam T Δ a b : ℝ) :
    H lam (T + Δ) a b = Real.exp (-2 * lam * Δ) * H lam T a b := by
  unfold H
  by_cases hl : lam = 0
  · subst hl; simp
  · simp only [hl, if_false]
    rw [show -2 * lam * (T + Δ - b) = -2 * lam * Δ + -2 * lam * (T - b) by ring,
      show -2 * lam * (T + Δ - a) = -2 * lam * Δ + -2 * lam * (T - a) by ring,
      Real.exp_add, Real.exp_add]
    ring

lemma ratioBound : ratioBoundStatement := by
  intro m d k₀ τ γ' lam t hτ hkt htk hlam
  intro A
  have hAdef : A = Standalone.GaussianMeetingVarianceCone.A (m := m) τ (fun _ => γ') lam t k₀ :=
    rfl
  clear_value A
  subst hAdef
  -- monotonicity of the dates on the relevant range
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr hb) hab
  have hentry : ∀ (n : Fin m) (j : Fin d) (k : ℕ), k ∈ Finset.Ico k₀ (k₀ + n.val + 1) →
      max t (τ k) ≤ τ (k + 1) := by
    intro n j k hk
    rw [Finset.mem_Ico] at hk
    refine max_le ?_ (hmono k (k+1) (by omega) (by omega))
    exact htk.trans (hmono (k₀ + 1) (k + 1) (by omega) (by omega))
  have hnonneg : ∀ (n : Fin m) (j : Fin d),
      0 ≤ Standalone.GaussianMeetingVarianceCone.A (m := m) τ (fun _ => γ') lam t k₀ n j := by
    intro n j
    unfold Standalone.GaussianMeetingVarianceCone.A
    refine Finset.sum_nonneg fun k hk => ?_
    exact mul_nonneg (sq_nonneg _)
      (GaussianMeetingVarianceConeProof.H_nonneg (hentry n j k hk) _ _)
  have hrow : ∀ (n : Fin m) (j : Fin d) (hn : 0 < n.val),
      Standalone.GaussianMeetingVarianceCone.A (m := m) τ (fun _ => γ') lam t k₀ n j =
        Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
          Standalone.GaussianMeetingVarianceCone.A (m := m) τ (fun _ => γ') lam t k₀
            ⟨n.val - 1, by omega⟩ j +
        γ' j ^ 2 * H (lam j) (τ (k₀ + n.val + 1)) (max t (τ (k₀ + n.val))) (τ (k₀ + n.val + 1)) := by
    intro n j hn
    unfold Standalone.GaussianMeetingVarianceCone.A
    simp only
    have hidx : k₀ + (n.val - 1) + 1 = k₀ + n.val := by omega
    rw [hidx, Finset.mul_sum]
    rw [Finset.sum_Ico_succ_top (by omega : k₀ ≤ k₀ + n.val)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hT : τ (k₀ + n.val + 1) = τ (k₀ + n.val) + (τ (k₀ + n.val + 1) - τ (k₀ + n.val)) := by ring
    rw [hT, H_shift]
    ring
  refine ⟨hnonneg, hrow, fun lamMax hmax V hV => ⟨fun n => ?_, fun n hn => ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := hV
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hnonneg n j) (hq j)
  · obtain ⟨q, hq, rfl⟩ := hV
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hrow n j hn]
    have hΔ : 0 ≤ τ (k₀ + n.val + 1) - τ (k₀ + n.val) :=
      sub_nonneg.2 (hmono _ _ (by omega) (by omega))
    have he : Real.exp (-2 * lamMax * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) ≤
        Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) := by
      apply Real.exp_le_exp.2
      have := hmax j
      nlinarith
    have hA := hnonneg ⟨n.val - 1, by omega⟩ j
    have hH : 0 ≤ γ' j ^ 2 * H (lam j) (τ (k₀ + n.val + 1)) (max t (τ (k₀ + n.val)))
        (τ (k₀ + n.val + 1)) :=
      mul_nonneg (sq_nonneg _) (GaussianMeetingVarianceConeProof.H_nonneg
        (max_le (htk.trans (hmono (k₀+1) (k₀ + n.val + 1) (by omega) (by omega)))
          (hmono _ _ (by omega) (by omega))) _ _)
    have hq' := hq j
    nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hA hq')]

/-! ### The one-factor matrix: triangular structure, recursion, attainment, diagonal case -/

section OneFactor
open Novel.GaussianMeetingVarianceConeProof (A0127_diag A0127_det_pos H_pos H_nonneg)

variable {N : ℕ} {τ γ : ℕ → ℝ} {lam : ℝ}

lemma A0127_zero_of_lt (n k : Fin N) (hnk : n < k) : A0127 τ γ lam n k = 0 := by
  simp [A0127, not_le_of_gt hnk]

lemma A0127_diag_pos (hτ : StrictMonoOn τ (Iic N)) (hγ : γ 1 ≠ 0) (n : Fin N) :
    0 < A0127 τ γ lam n n := by
  rw [A0127_diag]
  exact mul_pos (sq_pos_of_ne_zero hγ) (H_pos (hτ (by simp) (by simp) (Nat.lt_succ_self n.val)) lam _)

lemma A0127_nonneg (hτ : StrictMonoOn τ (Iic N)) (n k : Fin N) : 0 ≤ A0127 τ γ lam n k := by
  unfold A0127
  split_ifs with h
  · refine mul_nonneg (sq_nonneg _) (H_nonneg ?_ lam _)
    exact hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) (Nat.le_succ k.val)
  · exact le_rfl

/-- A lower triangular matrix applied to `q`, at row `p`, is the sum over the columns `l ≤ p`. -/
lemma mulVec_lower {M : Matrix (Fin N) (Fin N) ℝ} (hlow : ∀ n k : Fin N, n < k → M n k = 0)
    (q : Fin N → ℝ) (p : Fin N) :
    M.mulVec q p = ∑ l ∈ Finset.univ.filter (· ≤ p), M p l * q l := by
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ p)]
  have : ∑ l ∈ Finset.univ.filter (fun l => ¬ l ≤ p), M p l * q l = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [Finset.mem_filter] at hl
      rw [hlow p l (lt_of_not_ge hl.2), zero_mul]
  rw [this, add_zero]

/-- The split of the row sum into the strict part and the diagonal term. -/
lemma mulVec_split {M : Matrix (Fin N) (Fin N) ℝ} (hlow : ∀ n k : Fin N, n < k → M n k = 0)
    (q : Fin N → ℝ) (k : Fin N) :
    M.mulVec q k = (∑ l ∈ Finset.univ.filter (· < k), M k l * q l) + M k k * q k := by
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < k)]
  congr 1
  rw [Finset.sum_eq_single k]
  · intro l hl hlk
    rw [Finset.mem_filter] at hl
    rw [hlow k l (lt_of_le_of_ne (not_lt.mp hl.2) (Ne.symm hlk)), zero_mul]
  · intro h
    exact (h (by simp)).elim

lemma recursion : recursionStatement := by
  intro N τ γ lam hτ hγ M
  have hMdef : M = A0127 (N := N) τ γ lam := rfl
  clear_value M
  subst hMdef
  have hlow : ∀ n k : Fin N, n < k → A0127 τ γ lam n k = 0 := A0127_zero_of_lt
  have hdiag := A0127_diag_pos (lam := lam) hτ hγ
  have hdet : IsUnit (A0127 (N := N) τ γ lam).det :=
    isUnit_iff_ne_zero.mpr (A0127_det_pos hτ hγ).ne'
  have hinj : ∀ q q' : Fin N → ℝ, (A0127 τ γ lam).mulVec q = (A0127 τ γ lam).mulVec q' → q = q' := by
    intro q q' h
    have h2 := congrArg (fun v => (A0127 (N := N) τ γ lam)⁻¹.mulVec v) h
    simpa [mulVec_mulVec, nonsing_inv_mul _ hdet] using h2
  refine ⟨hlow, hdiag, fun V => ⟨(A0127 τ γ lam)⁻¹.mulVec V, ?_, fun q hq => ?_⟩,
    fun V q hq => ⟨fun k => ?_, ?_⟩, ?_, fun w => ?_⟩
  · beta_reduce
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  · rw [← hq, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · have h := mulVec_split hlow q k
    rw [hq] at h
    rw [eq_div_iff (hdiag k).ne']
    linarith
  · constructor
    · rintro ⟨q', hq', hq'V⟩
      have : q' = q := hinj q' q (hq'V.trans hq.symm)
      subst this
      exact hq'
    · intro hqn
      exact ⟨q, hqn, hq⟩
  · exact linearIndependent_rows_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hdet))
  · rw [(dual N N (A0127 τ γ lam) (A0127_nonneg hτ)).1 w]
    constructor
    · intro h
      refine ⟨(A0127 τ γ lam).transpose.mulVec w, h, ?_⟩
      rw [mulVec_mulVec, ← transpose_mul, mul_nonsing_inv _ hdet, transpose_one, one_mulVec]
    · rintro ⟨c, hc, rfl⟩
      intro j
      rw [mulVec_mulVec, ← transpose_mul, nonsing_inv_mul _ hdet, transpose_one, one_mulVec]
      exact hc j

/-- With a constant loading, each row of the one-factor matrix below the diagonal is the previous
row scaled by `e^{−2λ Δ_n}`. -/
lemma A0127_rel (τ : ℕ → ℝ) (γ' lam : ℝ) (n k : Fin N) (hk : k < n) :
    A0127 τ (fun _ => γ') lam n k =
      Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) *
        A0127 τ (fun _ => γ') lam ⟨n.val - 1, by omega⟩ k := by
  have hk' : k.val < n.val := Fin.lt_def.mp hk
  have h1 : k ≤ n := hk.le
  have h2 : k ≤ (⟨n.val - 1, by omega⟩ : Fin N) := by
    rw [Fin.le_def]; show k.val ≤ n.val - 1; omega
  simp only [A0127, h1, h2, ite_true]
  have hidx : n.val - 1 + 1 = n.val := by omega
  simp only [Fin.val_mk, hidx]
  have hs := H_shift lam (τ n.val) (τ (n.val + 1) - τ n.val) (τ k.val) (τ (k.val + 1))
  rw [show τ n.val + (τ (n.val + 1) - τ n.val) = τ (n.val + 1) by ring] at hs
  rw [hs]
  ring

lemma filter_lt_eq (n : Fin N) (hn : 0 < n.val) :
    Finset.univ.filter (fun l : Fin N => l < n) =
      Finset.univ.filter (· ≤ (⟨n.val - 1, by omega⟩ : Fin N)) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
  show l.val < n.val ↔ l.val ≤ n.val - 1
  omega

/-- On the cone of the one-factor matrix with a constant loading, each entry dominates the
previous one scaled by `e^{−2λ Δ_n}`. -/
lemma cone_ratio (τ : ℕ → ℝ) (γ' lam : ℝ) (q : Fin N → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hτ : StrictMonoOn τ (Iic N)) (n : Fin N) (hn : 0 < n.val) :
    Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) *
        (A0127 τ (fun _ => γ') lam).mulVec q ⟨n.val - 1, by omega⟩ ≤
      (A0127 τ (fun _ => γ') lam).mulVec q n := by
  have hlow : ∀ n k : Fin N, n < k → A0127 τ (fun _ => γ') lam n k = 0 := A0127_zero_of_lt
  rw [mulVec_split hlow q n, mulVec_lower hlow q, ← filter_lt_eq n hn, Finset.mul_sum]
  have hdiag : 0 ≤ A0127 τ (fun _ => γ') lam n n * q n :=
    mul_nonneg (A0127_nonneg hτ n n) (hq n)
  have : ∑ l ∈ Finset.univ.filter (· < n),
      Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) * (A0127 τ (fun _ => γ') lam
        ⟨n.val - 1, by omega⟩ l * q l) =
      ∑ l ∈ Finset.univ.filter (· < n), A0127 τ (fun _ => γ') lam n l * q l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_filter] at hl
    rw [A0127_rel τ γ' lam n l hl.2]
    ring
  rw [this]
  linarith

lemma attainment : attainmentStatement := by
  intro N τ γ' lam hτ hγ M
  have hMdef : M = A0127 (N := N) τ (fun _ => γ') lam := rfl
  clear_value M
  subst hMdef
  have hlow : ∀ n k : Fin N, n < k → A0127 τ (fun _ => γ') lam n k = 0 := A0127_zero_of_lt
  have hdiag := A0127_diag_pos (γ := fun _ => γ') (lam := lam) hτ hγ
  have hdet : IsUnit (A0127 (N := N) τ (fun _ => γ') lam).det :=
    isUnit_iff_ne_zero.mpr (A0127_det_pos (γ := fun _ => γ') hτ hγ).ne'
  have hrel := A0127_rel (N := N) τ γ' lam
  have hfilt := filter_lt_eq (N := N)
  have key : ∀ V q : Fin N → ℝ, (A0127 τ (fun _ => γ') lam).mulVec q = V →
      (∀ n : Fin N, n.val = 0 → q n = V n / A0127 τ (fun _ => γ') lam n n) ∧
      ∀ (n : Fin N), 0 < n.val →
        q n = (V n - Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) *
          V ⟨n.val - 1, by omega⟩) / A0127 τ (fun _ => γ') lam n n := by
    intro V q hq
    constructor
    · intro n hn
      have h := mulVec_split hlow q n
      rw [hq] at h
      have hempty : ∑ l ∈ Finset.univ.filter (· < n), A0127 τ (fun _ => γ') lam n l * q l = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [Finset.mem_filter] at hl
        have := Fin.lt_def.mp hl.2
        omega
      rw [eq_div_iff (hdiag n).ne']
      linarith
    · intro n hn
      have h := mulVec_split hlow q n
      rw [hq] at h
      have hprev : ∑ l ∈ Finset.univ.filter (· < n), A0127 τ (fun _ => γ') lam n l * q l =
          Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) * V ⟨n.val - 1, by omega⟩ := by
        rw [← hq, mulVec_lower hlow, ← hfilt n hn, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Finset.mem_filter] at hl
        rw [hrel n l hl.2]
        ring
      rw [eq_div_iff (hdiag n).ne']
      linarith
  refine ⟨hrel, fun V hV0 hV => ⟨?_, key V⟩⟩
  set q := (A0127 (N := N) τ (fun _ => γ') lam)⁻¹.mulVec V with hqdef
  have hq : (A0127 τ (fun _ => γ') lam).mulVec q = V := by
    rw [hqdef, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  obtain ⟨k0, kpos⟩ := key V q hq
  refine ⟨q, fun n => ?_, hq⟩
  by_cases hn : 0 < n.val
  · rw [kpos n hn]
    exact div_nonneg (sub_nonneg.2 (hV n hn)) (hdiag n).le
  · have hn0 : n.val = 0 := by omega
    rw [k0 n hn0]
    exact div_nonneg (hV0 n hn0) (hdiag n).le

lemma diagonal : diagonalStatement := by
  intro N τ γ lam hτ hγ hγ2 M
  have hMdef : M = A0127 (N := N) τ γ lam := rfl
  clear_value M
  subst hMdef
  have hdiag := A0127_diag_pos (lam := lam) hτ hγ
  have hoff : ∀ n k : Fin N, n ≠ k → A0127 τ γ lam n k = 0 := by
    intro n k hnk
    rcases lt_or_gt_of_ne hnk with h | h
    · exact A0127_zero_of_lt n k h
    · have hk : k ≤ n := h.le
      have hkn : k.val < n.val := Fin.lt_def.mp h
      simp only [A0127, hk, ite_true]
      rw [hγ2 (n.val + 1 - k.val) (by omega)]
      ring
  refine ⟨hoff, hdiag, fun V hV => ⟨fun n => V n / A0127 τ γ lam n n,
    fun n => div_nonneg (hV n) (hdiag n).le, ?_⟩⟩
  funext n
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single n]
  · field_simp [(hdiag n).ne']
  · intro l _ hln
    rw [hoff n l (Ne.symm hln), zero_mul]
  · intro h; exact absurd (Finset.mem_univ n) h

end OneFactor

/-- (d), the decay cases. -/
lemma closureCase : closureStatement := by
  intro N τ γ' hτ hγ
  have hsub : ∀ lam : ℝ, cone (A0127 (N := N) τ (fun _ => γ') lam) ⊆ orthant N := by
    rintro lam V ⟨q, hq, rfl⟩ n
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (A0127_nonneg hτ n l) (hq l)
  have hΔ : ∀ n : Fin N, 0 < n.val → 0 < τ (n.val + 1) - τ n.val := fun n hn =>
    sub_pos.2 (hτ (by simp) (by simp) (Nat.lt_succ_self n.val))
  refine ⟨hsub, ?_, fun Λ hΛ => ⟨fun lam hlam hlamΛ V hV => ⟨fun n _ => hsub lam hV n, ?_⟩,
    fun V hV0 hV => ((attainment N τ γ' Λ hτ hγ).2 V hV0 hV).1⟩⟩
  · apply le_antisymm
    · refine closure_minimal ?_ ?_
      · exact Set.iUnion₂_subset fun lam _ => hsub lam
      · rw [orthant, Set.setOf_forall]
        exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
    · intro V hV
      rw [Metric.mem_closure_iff]
      intro ε hε
      set δ := ε / 2 with hδ
      have hδpos : 0 < δ := by positivity
      -- a bound on the entries of `V`
      have hMb : ∀ n, V n ≤ ∑ m, V m := fun n =>
        Finset.single_le_sum (fun m _ => hV m) (Finset.mem_univ n)
      have hMb0 : 0 ≤ ∑ m, V m := Finset.sum_nonneg fun m _ => hV m
      set Mb := ∑ m, V m with hMbdef
      have hr : 0 < δ / (Mb + δ) := by positivity
      -- a decay large enough that every ratio constant is below `δ / (Mb + δ)`
      have hev : ∀ᶠ lam : ℝ in Filter.atTop, ∀ n : Fin N, 0 < n.val →
          Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) < δ / (Mb + δ) := by
        rw [Filter.eventually_all]
        intro n
        by_cases hn : 0 < n.val
        · have ht : Filter.Tendsto
              (fun lam : ℝ => Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)))
              Filter.atTop (nhds 0) := by
            refine Real.tendsto_exp_atBot.comp ?_
            have h1 : Filter.Tendsto (fun lam : ℝ => (-2 * (τ (n.val + 1) - τ n.val)) * lam)
                Filter.atTop Filter.atBot :=
              Filter.Tendsto.const_mul_atTop_of_neg (by nlinarith [hΔ n hn]) Filter.tendsto_id
            refine h1.congr fun lam => ?_
            ring
          exact ((tendsto_order.1 ht).2 _ hr).mono fun lam h _ => h
        · exact Filter.Eventually.of_forall fun lam h => absurd h hn
      obtain ⟨lam, hlam, hlam0⟩ := (hev.and (Filter.eventually_ge_atTop 0)).exists
      refine ⟨fun n => V n + δ, ?_, ?_⟩
      · refine Set.mem_iUnion₂.2 ⟨lam, hlam0, ?_⟩
        refine ((attainment N τ γ' lam hτ hγ).2 (fun n => V n + δ)
          (fun n _ => by have := hV n; linarith) fun n hn => ?_).1
        have hlt := hlam n hn
        have hVn := hV ⟨n.val - 1, by omega⟩
        have hMn := hMb ⟨n.val - 1, by omega⟩
        calc Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) * (V ⟨n.val - 1, by omega⟩ + δ)
            ≤ δ / (Mb + δ) * (Mb + δ) :=
              mul_le_mul hlt.le (by linarith) (by linarith) hr.le
          _ = δ := by field_simp
          _ ≤ V n + δ := by linarith [hV n]
      · rw [dist_pi_lt_iff hε]
        intro n
        rw [Real.dist_eq, show V n - (V n + δ) = -δ by ring, abs_neg, abs_of_pos hδpos]
        linarith
  · obtain ⟨q, hq, rfl⟩ := hV
    intro n hn
    have h1 := cone_ratio τ γ' lam q hq hτ n hn
    have hprev : 0 ≤ (A0127 τ (fun _ => γ') lam).mulVec q ⟨n.val - 1, by omega⟩ :=
      hsub lam ⟨q, hq, rfl⟩ _
    have he : Real.exp (-2 * Λ * (τ (n.val + 1) - τ n.val)) ≤
        Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) := by
      apply Real.exp_le_exp.2
      have := hΔ n hn
      nlinarith
    calc Real.exp (-2 * Λ * (τ (n.val + 1) - τ n.val)) *
          (A0127 τ (fun _ => γ') lam).mulVec q ⟨n.val - 1, by omega⟩
        ≤ Real.exp (-2 * lam * (τ (n.val + 1) - τ n.val)) *
          (A0127 τ (fun _ => γ') lam).mulVec q ⟨n.val - 1, by omega⟩ :=
          mul_le_mul_of_nonneg_right he hprev
      _ ≤ _ := h1

/-! ### The piecewise cone of (24.2) -/

section Piecewise

variable {m d : ℕ}

/-- Claim 012's per-factor entry is the sum of the piecewise entries over the pieces. -/
lemma A_eq_sum_Apw (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (n : Fin m) (j : Fin d) :
    A (m := m) τ γ lam t k₀ n j = ∑ k : Fin m, Apw (m := m) τ γ lam t k₀ n (j, k) := by
  set F : ℕ → ℝ := fun k => if k ≤ n.val then γ (n.val + 1 - k) j ^ 2 *
    H (lam j) (τ (k₀ + n.val + 1)) (max t (τ (k₀ + k))) (τ (k₀ + k + 1)) else 0 with hF
  have h1 : ∑ k : Fin m, Apw (m := m) τ γ lam t k₀ n (j, k) = ∑ k : Fin m, F k.val := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Apw, hF, Fin.le_def]
  have h2 : ∑ k : Fin m, F k.val = ∑ i ∈ Finset.range m, F i := Fin.sum_univ_eq_sum_range F m
  have h3 : ∑ i ∈ Finset.range m, F i = ∑ i ∈ Finset.range (n.val + 1), F i := by
    symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro i _ hi
      rw [Finset.mem_range] at hi
      simp only [hF]
      rw [if_neg (by omega)]
  rw [h1, h2, h3]
  unfold A
  rw [Finset.sum_Ico_eq_sum_range, show k₀ + n.val + 1 - k₀ = n.val + 1 by omega]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp only [hF]
  rw [if_pos (by omega), show k₀ + n.val + 1 - (k₀ + k) = n.val + 1 - k by omega]

lemma A_mulVec_eq (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (q : Fin d → ℝ) :
    (A (m := m) τ γ lam t k₀).mulVec q = (Apw (m := m) τ γ lam t k₀).mulVec (fun p => q p.1) := by
  funext n
  simp only [mulVec, dotProduct, A_eq_sum_Apw, Finset.sum_mul, Fintype.sum_prod_type]

lemma Apw_nonneg (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (hτ : StrictMonoOn τ (Iic (k₀ + m))) (hkt : τ k₀ ≤ t) (htk : t ≤ τ (k₀ + 1))
    (n : Fin m) (p : Fin d × Fin m) : 0 ≤ Apw (m := m) τ γ lam t k₀ n p := by
  unfold Apw
  split_ifs with h
  · refine mul_nonneg (sq_nonneg _) (GaussianMeetingVarianceConeProof.H_nonneg ?_ _ _)
    have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
      hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
    have hp := p.2.isLt
    refine max_le ?_ (hmono _ _ (by omega) (by omega))
    exact htk.trans (hmono (k₀ + 1) (k₀ + p.2.val + 1) (by omega) (by omega))
  · exact le_rfl

/-- With a constant loading, each piecewise entry below the diagonal is the previous row's entry
scaled by `e^{−2λ_j Δ_n}`. -/
lemma Apw_rel (τ : ℕ → ℝ) (γ' : Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (n : Fin m) (p : Fin d × Fin m) (hk : p.2 < n) :
    Apw (m := m) τ (fun _ => γ') lam t k₀ n p =
      Real.exp (-2 * lam p.1 * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) *
        Apw (m := m) τ (fun _ => γ') lam t k₀ ⟨n.val - 1, by omega⟩ p := by
  have hk' : p.2.val < n.val := Fin.lt_def.mp hk
  have h1 : p.2 ≤ n := hk.le
  have h2 : p.2 ≤ (⟨n.val - 1, by omega⟩ : Fin m) := by
    rw [Fin.le_def]; show p.2.val ≤ n.val - 1; omega
  simp only [Apw, h1, h2, ite_true]
  have hidx : k₀ + (n.val - 1) + 1 = k₀ + n.val := by omega
  simp only [Fin.val_mk, hidx]
  have hs := H_shift (lam p.1) (τ (k₀ + n.val)) (τ (k₀ + n.val + 1) - τ (k₀ + n.val))
    (max t (τ (k₀ + p.2.val))) (τ (k₀ + p.2.val + 1))
  rw [show τ (k₀ + n.val) + (τ (k₀ + n.val + 1) - τ (k₀ + n.val)) = τ (k₀ + n.val + 1) by ring]
    at hs
  rw [hs]
  ring

/-- The shifted date sequence of the one-factor block: `t` first, then the meeting dates. -/
noncomputable def shiftedDates (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) : ℕ → ℝ :=
  fun k => if k = 0 then t else τ (k₀ + k)

lemma shiftedDates_strictMono (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ)
    (hτ : StrictMonoOn τ (Iic (k₀ + m))) (htk : t < τ (k₀ + 1)) :
    StrictMonoOn (shiftedDates τ t k₀) (Iic m) := by
  intro a ha b hb hab
  rw [mem_Iic] at ha hb
  unfold shiftedDates
  have hmono : ∀ a b : ℕ, a < b → b ≤ k₀ + m → τ a < τ b := fun a b hab hb =>
    hτ (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := by omega
    rw [if_pos rfl, if_neg hb0]
    rcases Nat.lt_or_ge 1 b with h | h
    · exact htk.trans (hmono (k₀ + 1) (k₀ + b) (by omega) (by omega))
    · have : b = 1 := by omega
      subst this; exact htk
  · have hb0 : b ≠ 0 := by omega
    rw [if_neg ha0, if_neg hb0]
    exact hmono _ _ (by omega) (by omega)

/-- The block of the factor `j` of the piecewise matrix is the one-factor matrix (12.7) on the
shifted dates. -/
lemma Apw_block (τ : ℕ → ℝ) (γ' : Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (hτ : StrictMonoOn τ (Iic (k₀ + m))) (hkt : τ k₀ ≤ t) (htk : t ≤ τ (k₀ + 1))
    (j : Fin d) (n k : Fin m) :
    Apw (m := m) τ (fun _ => γ') lam t k₀ n (j, k) =
      A0127 (shiftedDates τ t k₀) (fun _ => γ' j) (lam j) n k := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  by_cases hkn : k ≤ n
  · simp only [Apw, A0127, shiftedDates, hkn, ite_true, Nat.add_one_ne_zero, ite_false,
      ← Nat.add_assoc]
    congr 2
    by_cases hk0 : k.val = 0
    · rw [if_pos hk0, hk0, add_zero, max_eq_left hkt]
    · rw [if_neg hk0]
      exact max_eq_right (htk.trans (hmono (k₀ + 1) (k₀ + k.val) (by omega)
        (by have := k.isLt; omega)))
  · simp only [Apw, A0127, shiftedDates, hkn, ite_false]

/-- The one-factor cone of the factor `j` on the shifted dates embeds in the piecewise cone by
setting the other factors' scales to zero. -/
lemma block_cone_subset (τ : ℕ → ℝ) (γ' : Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (hτ : StrictMonoOn τ (Iic (k₀ + m))) (hkt : τ k₀ ≤ t) (htk : t ≤ τ (k₀ + 1)) (j : Fin d) :
    cone (A0127 (shiftedDates τ t k₀) (fun _ => γ' j) (lam j)) ⊆
      cone (Apw (m := m) τ (fun _ => γ') lam t k₀) := by
  rintro V ⟨q, hq, hqV⟩
  refine ⟨fun p => if p.1 = j then q p.2 else 0, fun p => ?_, ?_⟩
  · show 0 ≤ (if p.1 = j then q p.2 else 0)
    split_ifs
    · exact hq _
    · exact le_rfl
  · rw [← hqV]
    funext n
    simp only [mulVec, dotProduct, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_pos rfl, Apw_block τ γ' lam t k₀ hτ hkt htk j n k]
    · intro i _ hij
      exact Finset.sum_eq_zero fun k _ => by rw [if_neg hij, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h

lemma piecewiseCone : piecewiseConeStatement := by
  intro m d k₀ τ lam t hτ hkt htk hlam
  refine ⟨fun γ q => A_mulVec_eq τ γ lam t k₀ q, fun γ V hV => ?_, fun γ' lamMax hmax => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hV
    exact ⟨fun p => q p.1, fun p => hq p.1, (A_mulVec_eq τ γ lam t k₀ q).symm⟩
  intro B
  have hBdef : B = Apw (m := m) τ (fun _ => γ') lam t k₀ := rfl
  clear_value B
  subst hBdef
  have hnn := Apw_nonneg (m := m) τ (fun _ => γ') lam t k₀ hτ hkt htk.le
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  refine ⟨fun V hV => ⟨fun n => ?_, fun n hn => ?_⟩, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hV
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hnn n p) (hq p)
  · obtain ⟨q, hq, rfl⟩ := hV
    set n' : Fin m := ⟨n.val - 1, by omega⟩ with hn'
    have hΔ : 0 ≤ τ (k₀ + n.val + 1) - τ (k₀ + n.val) :=
      sub_nonneg.2 (hmono _ _ (by omega) (by omega))
    -- termwise: each column's contribution to row `n` dominates `e^{−2λ_max Δ}` times its
    -- contribution to row `n − 1`
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have he : Real.exp (-2 * lamMax * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) ≤
        Real.exp (-2 * lam p.1 * (τ (k₀ + n.val + 1) - τ (k₀ + n.val))) := by
      apply Real.exp_le_exp.2
      have := hmax p.1
      nlinarith
    have hprev := mul_nonneg (hnn n' p) (hq p)
    by_cases hk : p.2 < n
    · rw [Apw_rel τ γ' lam t k₀ n p hk]
      have := mul_le_mul_of_nonneg_right he hprev
      rw [hn'] at this ⊢
      nlinarith
    · -- the previous row's entry vanishes
      have hzero : Apw (m := m) τ (fun _ => γ') lam t k₀ n' p = 0 := by
        unfold Apw
        rw [if_neg]
        rw [hn', Fin.le_def]
        show ¬ p.2.val ≤ n.val - 1
        have := Fin.lt_def.not.mp hk
        omega
      rw [hzero, zero_mul, mul_zero]
      exact mul_nonneg (hnn n p) (hq p)
  · rintro ⟨j, hj, hγj⟩ V hV0 hV
    have hsm := shiftedDates_strictMono (m := m) τ t k₀ hτ htk
    have hatt := (attainment m (shiftedDates τ t k₀) (γ' j) lamMax hsm hγj).2 V hV0 ?_
    · refine block_cone_subset τ γ' lam t k₀ hτ hkt htk.le j ?_
      rw [hj]; exact hatt.1
    · intro n hn
      have h := hV n hn
      unfold shiftedDates
      rw [if_neg (by omega : n.val + 1 ≠ 0), if_neg (by omega : n.val ≠ 0)]
      exact h

end Piecewise

/-! ### (a) assembled: the attainable set over measurable scales -/

section Assembly

variable {m d : ℕ}

lemma measurableSet_piece (τ : ℕ → ℝ) (t : ℝ) (k₀ k : ℕ) : MeasurableSet (piece τ t k₀ k) :=
  measurableSet_Ioc

lemma piece_lo_le_hi (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) (hτ : StrictMonoOn τ (Iic (k₀ + m)))
    (htk : t ≤ τ (k₀ + 1)) (k : Fin m) : max t (τ (k₀ + k.val)) ≤ τ (k₀ + k.val + 1) := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  have hk := k.isLt
  exact max_le (htk.trans (hmono _ _ (by omega) (by omega))) (hmono _ _ (by omega) (by omega))

lemma piece_lo_lt_hi (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) (hτ : StrictMonoOn τ (Iic (k₀ + m)))
    (htk : t < τ (k₀ + 1)) (k : Fin m) : max t (τ (k₀ + k.val)) < τ (k₀ + k.val + 1) := by
  have hk := k.isLt
  have hmono : ∀ a b : ℕ, a < b → b ≤ k₀ + m → τ a < τ b := fun a b hab hb =>
    hτ (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  refine max_lt ?_ (hmono _ _ (by omega) (by omega))
  rcases Nat.eq_zero_or_pos k.val with h0 | h0
  · rw [h0, add_zero]; exact htk
  · exact htk.trans_le ((hmono _ _ (by omega) (by omega)).le)

lemma piece_subset_row (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) (hτ : StrictMonoOn τ (Iic (k₀ + m)))
    (n k : Fin m) (hk : k ≤ n) : piece τ t k₀ k.val ⊆ Ioc t (τ (k₀ + n.val + 1)) := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  have hk' : k.val ≤ n.val := hk
  have hn := n.isLt
  exact Ioc_subset_Ioc (le_max_left _ _) (hmono _ _ (by omega) (by omega))

lemma piece_inter_row (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) (hτ : StrictMonoOn τ (Iic (k₀ + m)))
    (n k : Fin m) (hk : ¬ k ≤ n) : piece τ t k₀ k.val ∩ Ioc t (τ (k₀ + n.val + 1)) = ∅ := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  have hk' : n.val < k.val := by
    have := Fin.le_def.not.mp hk
    omega
  have hkm := k.isLt
  apply Set.eq_empty_iff_forall_notMem.2
  intro s hs
  have h1 : τ (k₀ + n.val + 1) ≤ τ (k₀ + k.val) := hmono _ _ (by omega) (by omega)
  have h2 := hs.1.1
  have h3 := hs.2.2
  have := le_max_right t (τ (k₀ + k.val))
  linarith

lemma piece_pairwise (τ : ℕ → ℝ) (t : ℝ) (k₀ : ℕ) (hτ : StrictMonoOn τ (Iic (k₀ + m)))
    (k k' : Fin m) (hkk : k ≠ k') (s : ℝ) (hs : s ∈ piece τ t k₀ k.val)
    (hs' : s ∈ piece τ t k₀ k'.val) : False := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ k₀ + m → τ a ≤ τ b := fun a b hab hb =>
    hτ.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr hb) hab
  have hk := k.isLt
  have hk' := k'.isLt
  rcases lt_or_gt_of_ne (fun e => hkk (Fin.ext e) : k.val ≠ k'.val) with h | h
  · have h1 : τ (k₀ + k.val + 1) ≤ τ (k₀ + k'.val) := hmono _ _ (by omega) (by omega)
    have := le_max_right t (τ (k₀ + k'.val))
    have := hs.2; have := hs'.1
    linarith
  · have h1 : τ (k₀ + k'.val + 1) ≤ τ (k₀ + k.val) := hmono _ _ (by omega) (by omega)
    have := le_max_right t (τ (k₀ + k.val))
    have := hs'.2; have := hs.1
    linarith

/-- The kernel integrand on a piece, rewritten through the exponential weight. -/
lemma kernel_term_integrable (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (a : Fin d → ℝ → ℝ) (ha : Admissible m τ lam t k₀ a) (n : Fin m) (j : Fin d) (k : Fin m) :
    IntegrableOn (fun s => a j s ^ 2 *
      (γ (n.val + 1 - k.val) j ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s))))
      (piece τ t k₀ k.val) := by
  have h : IntegrableOn (fun s => (γ (n.val + 1 - k.val) j ^ 2 *
      Real.exp (-2 * lam j * τ (k₀ + n.val + 1))) * (a j s ^ 2 * Real.exp (2 * lam j * s)))
      (piece τ t k₀ k.val) :=
    (ha.2 j k).const_mul _
  refine IntegrableOn.congr_fun h (fun s _ => ?_) (measurableSet_piece τ t k₀ k.val)
  have he : Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s)) =
      Real.exp (-2 * lam j * τ (k₀ + n.val + 1)) * Real.exp (2 * lam j * s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  ring

/-- The variance vector of admissible scales, piece by piece. -/
lemma scaledVariance_eq (τ : ℕ → ℝ) (γ : ℕ → Fin d → ℝ) (lam : Fin d → ℝ) (t : ℝ) (k₀ : ℕ)
    (hτ : StrictMonoOn τ (Iic (k₀ + m))) (htk : t ≤ τ (k₀ + 1))
    (a : Fin d → ℝ → ℝ) (ha : Admissible m τ lam t k₀ a) (n : Fin m) :
    scaledVariance (m := m) τ γ lam t k₀ a n = ∑ j, ∑ k : Fin m, if k ≤ n then
      γ (n.val + 1 - k.val) j ^ 2 * ∫ s in max t (τ (k₀ + k.val))..τ (k₀ + k.val + 1),
        a j s ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s)) else 0 := by
  unfold scaledVariance kernel
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm : ∀ k : Fin m, (fun s => a j s ^ 2 * (piece τ t k₀ k.val).indicator
      (fun s => γ (n.val + 1 - k.val) j ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s))) s)
      = (piece τ t k₀ k.val).indicator (fun s => a j s ^ 2 *
        (γ (n.val + 1 - k.val) j ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s)))) := by
    intro k
    funext s
    exact (Set.indicator_mul_right (piece τ t k₀ k.val) (fun s => a j s ^ 2)
      (fun s => γ (n.val + 1 - k.val) j ^ 2 *
        Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s)))).symm
  have hint : ∀ k : Fin m, Integrable (fun s => a j s ^ 2 * (piece τ t k₀ k.val).indicator
      (fun s => γ (n.val + 1 - k.val) j ^ 2 * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s))) s)
      (volume.restrict (Ioc t (τ (k₀ + n.val + 1)))) := by
    intro k
    rw [hterm k, integrable_indicator_iff (measurableSet_piece τ t k₀ k.val)]
    unfold IntegrableOn
    rw [Measure.restrict_restrict (measurableSet_piece τ t k₀ k.val)]
    exact (kernel_term_integrable τ γ lam t k₀ a ha n j k).mono_set inter_subset_left
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => hint k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hterm k, integral_indicator (measurableSet_piece τ t k₀ k.val),
    Measure.restrict_restrict (measurableSet_piece τ t k₀ k.val)]
  by_cases hk : k ≤ n
  · rw [if_pos hk, inter_eq_left.2 (piece_subset_row τ t k₀ hτ n k hk)]
    unfold piece
    rw [← intervalIntegral.integral_of_le (piece_lo_le_hi τ t k₀ hτ htk k),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  · rw [if_neg hk, piece_inter_row τ t k₀ hτ n k hk]
    simp

lemma attainable : attainableStatement := by
  intro m d k₀ τ γ lam t hτ hkt htk
  have hlt := piece_lo_lt_hi (m := m) τ t k₀ hτ htk
  constructor
  · intro a ha
    choose c hc using fun p : Fin d × Fin m =>
      fixedDirection (lam p.1) (max t (τ (k₀ + p.2.val))) (τ (k₀ + p.2.val + 1)) (a p.1)
        (hlt p.2) (ha.1 p.1) (ha.2 p.1 p.2)
    refine ⟨c, fun p => (hc p).1, ?_⟩
    funext n
    rw [scaledVariance_eq τ γ lam t k₀ hτ htk.le a ha n]
    simp only [mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    unfold Apw
    simp only
    split_ifs with hk
    · rw [(hc (j, k)).2 (τ (k₀ + n.val + 1))]
      ring
    · simp
  · rintro V ⟨q, hq, rfl⟩
    let a : Fin d → ℝ → ℝ := fun j s =>
      Real.sqrt (∑ k : Fin m, (piece τ t k₀ k.val).indicator (fun _ => q (j, k)) s)
    have hsq : ∀ j s, a j s ^ 2 = ∑ k : Fin m, (piece τ t k₀ k.val).indicator (fun _ => q (j, k)) s :=
      fun j s => Real.sq_sqrt (Finset.sum_nonneg fun k _ =>
        Set.indicator_nonneg (fun _ _ => hq (j, k)) s)
    have hon : ∀ (j : Fin d) (k : Fin m), ∀ s ∈ piece τ t k₀ k.val, a j s ^ 2 = q (j, k) := by
      intro j k s hs
      rw [hsq, Finset.sum_eq_single k]
      · rw [Set.indicator_of_mem hs]
      · intro k' _ hk'
        rw [Set.indicator_of_notMem]
        exact fun hs' => piece_pairwise τ t k₀ hτ k k' (Ne.symm hk') s hs hs'
      · intro h; exact absurd (Finset.mem_univ k) h
    have ha : Admissible m τ lam t k₀ a := by
      refine ⟨fun j => ?_, fun j k => ?_⟩
      · exact Real.continuous_sqrt.measurable.comp
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.indicator (measurableSet_piece τ t k₀ k.val))
      · have hc : Continuous fun s => q (j, k) * Real.exp (2 * lam j * s) := by fun_prop
        refine (hc.integrableOn_Ioc).congr_fun (fun s hs => ?_) (measurableSet_piece τ t k₀ k.val)
        simp only
        rw [hon j k s hs]
    refine ⟨a, ha, ?_⟩
    funext n
    rw [scaledVariance_eq τ γ lam t k₀ hτ htk.le a ha n]
    simp only [mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    unfold Apw
    simp only
    split_ifs with hk
    · rw [intervalIntegral.integral_congr_Ioo_of_le (hlt k).le
        (g := fun s => q (j, k) * Real.exp (-2 * lam j * (τ (k₀ + n.val + 1) - s)))
        (fun s hs => by simp only; rw [hon j k s (Ioo_subset_Ioc_self hs)]),
        intervalIntegral.integral_const_mul, GaussianMeetingVarianceConeProof.integral_H]
      ring
    · simp

end Assembly

/-! ### (d) on the piecewise cone -/

section PiecewiseClosure

variable {m d : ℕ}

lemma piecewiseClosure : piecewiseClosureStatement := by
  intro m d k₀ τ γ' t hτ hkt htk hγ
  have hnn : ∀ lam : Fin d → ℝ, cone (Apw (m := m) τ (fun _ => γ') lam t k₀) ⊆ orthant m := by
    rintro lam V ⟨q, hq, rfl⟩ n
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (Apw_nonneg τ (fun _ => γ') lam t k₀ hτ hkt htk.le n p) (hq p)
  refine ⟨hnn, le_antisymm ?_ ?_⟩
  · refine closure_minimal (Set.iUnion₂_subset fun lam _ => hnn lam) ?_
    rw [orthant, Set.setOf_forall]
    exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
  · obtain ⟨j, hγj⟩ := hγ
    have hsm := shiftedDates_strictMono (m := m) τ t k₀ hτ htk
    have hcl := (closureCase m (shiftedDates τ t k₀) (γ' j) hsm hγj).2.1
    rw [← hcl]
    apply closure_mono
    refine Set.iUnion₂_subset fun Λ hΛ => ?_
    have h1 := block_cone_subset (m := m) τ γ' (fun _ => Λ) t k₀ hτ hkt htk.le j
    refine h1.trans (Set.subset_iUnion₂_of_subset (fun _ => Λ) (fun _ => hΛ) le_rfl)

end PiecewiseClosure

theorem survivingScaleRestrictions : Standalone.SurvivingScaleRestrictions.statement :=
  ⟨fixedDirection, dual, ratioBound, recursion, attainment, diagonal, closureCase, piecewiseCone,
    attainable, piecewiseClosure⟩

end Novel.SurvivingScaleRestrictionsProof

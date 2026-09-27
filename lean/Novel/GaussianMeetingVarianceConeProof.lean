import Standalone.GaussianMeetingVarianceCone
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Claim 012: deterministic integral and matrix proofs -/

open MeasureTheory Matrix Set
open Standalone.GaussianMeetingVarianceCone

namespace Novel.GaussianMeetingVarianceConeProof

lemma integral_H (lam T a b : ℝ) :
    ∫ s in a..b, Real.exp (-2 * lam * (T - s)) = H lam T a b := by
  by_cases hlam : lam = 0
  · simp [H, hlam]
  · have hd (s : ℝ) : HasDerivAt (fun u => Real.exp (-2 * lam * (T - u)) / (2 * lam))
        (Real.exp (-2 * lam * (T - s))) s := by
      have hlin : HasDerivAt (fun u : ℝ => -2 * lam * (T - u)) (2 * lam) s := by
        convert ((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul (-2 * lam) using 1 <;>
          simp [Pi.sub_apply]
      simpa [hlam] using hlin.exp.div_const (2 * lam)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((by fun_prop : Continuous (fun s => Real.exp (-2 * lam * (T - s)))).intervalIntegrable _ _)]
    simp [H, hlam, sub_div]

lemma H_pos {a b : ℝ} (hab : a < b) (lam T : ℝ) : 0 < H lam T a b := by
  rw [← integral_H]
  exact intervalIntegral.integral_pos hab (by fun_prop)
    (fun _ _ => (Real.exp_pos _).le) ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩

lemma H_nonneg {a b : ℝ} (hab : a ≤ b) (lam T : ℝ) : 0 ≤ H lam T a b := by
  rw [← integral_H]
  exact intervalIntegral.integral_nonneg_of_forall hab fun _ => (Real.exp_pos _).le

section Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (M : Matrix ι κ ℝ)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma scale_range :
    Set.range (fun a : κ → NNReal => M.mulVec (fun j => (a j : ℝ) ^ 2)) = cone M := by
  ext V
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun j => (a j : ℝ) ^ 2, fun j => sq_nonneg _, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨fun j => ⟨Real.sqrt (q j), Real.sqrt_nonneg _⟩, ?_⟩
    apply congrArg M.mulVec
    funext j
    exact Real.sq_sqrt (hq j)

omit [DecidableEq ι] [DecidableEq κ] in
lemma dot_mulVec (w : ι → ℝ) (q : κ → ℝ) :
    dotProduct w (M.mulVec q) = dotProduct (M.transpose.mulVec w) q := by
  rw [dotProduct_mulVec, mulVec_transpose]

omit [DecidableEq ι] in
lemma annihilates_cone (w : ι → ℝ) :
    (∀ V ∈ cone M, dotProduct w V = 0) ↔ M.transpose.mulVec w = 0 := by
  constructor
  · intro h
    funext j
    have he := h (M.mulVec (Pi.single j 1)) ⟨Pi.single j 1, fun k => by
      by_cases hk : k = j <;> simp [hk], rfl⟩
    rw [dot_mulVec] at he
    simpa using he
  · intro hw V hV
    obtain ⟨q, _, rfl⟩ := hV
    rw [dot_mulVec, hw, zero_dotProduct]

lemma functional_dot (l : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    l x = dotProduct (fun i => l (Pi.single i 1)) x := by
  rw [l.pi_apply_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun j : ι => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  simp [hi, smul_eq_mul, mul_comm]

lemma column_space (V : ι → ℝ) :
    (∀ w, M.transpose.mulVec w = 0 → dotProduct w V = 0) ↔
      V ∈ LinearMap.range M.mulVecLin := by
  constructor
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ V).1
    intro l hl
    rw [functional_dot]
    apply h
    funext j
    have he := ((Submodule.mem_dualAnnihilator l).1 hl) (M.mulVec (Pi.single j 1))
      (LinearMap.mem_range_self _ _)
    rw [functional_dot, dot_mulVec] at he
    simpa using he
  · rintro ⟨q, rfl⟩ w hw
    change dotProduct w (M.mulVec q) = 0
    rw [dot_mulVec, hw, zero_dotProduct]

omit [DecidableEq ι] [DecidableEq κ] in
lemma nullity :
    Fintype.card ι - Fintype.card κ ≤ Module.finrank ℝ (LinearMap.ker M.transpose.mulVecLin) := by
  have h := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := M.rank_le_card_width
  have ht : M.transpose.rank = M.rank := Matrix.rank_transpose _
  change M.transpose.rank + _ = _ at h
  rw [Module.finrank_pi, ht] at h
  omega

end Matrix

section Triangular

variable {N : ℕ} {τ γ : ℕ → ℝ} {lam : ℝ}

lemma A0127_lower : (A0127 (N := N) τ γ lam).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [A0127, not_le_of_gt hij]

lemma A0127_diag (n : Fin N) : A0127 τ γ lam n n =
    γ 1 ^ 2 * H lam (τ (n.val + 1)) (τ n.val) (τ (n.val + 1)) := by
  simp [A0127]

lemma A0127_det : (A0127 (N := N) τ γ lam).det =
    ∏ n : Fin N, γ 1 ^ 2 * H lam (τ (n.val + 1)) (τ n.val) (τ (n.val + 1)) := by
  rw [Matrix.det_of_isLowerTriangular _ A0127_lower]
  simp_rw [A0127_diag]

lemma A0127_det_pos (hτ : StrictMonoOn τ (Iic N)) (hγ : γ 1 ≠ 0) :
    0 < (A0127 (N := N) τ γ lam).det := by
  rw [A0127_det]
  refine Finset.prod_pos fun n _ => mul_pos (sq_pos_of_ne_zero hγ) ?_
  exact H_pos (hτ (by simp) (by simp) (Nat.lt_succ_self n.val)) lam _

lemma integral0127_eq (hτ : StrictMonoOn τ (Iic N)) : integral0127 (N := N) τ γ lam = A0127 τ γ lam := by
  funext n k
  have hk0 : τ 0 ≤ τ k.val := hτ.monotoneOn (by simp) (by simp) (Nat.zero_le _)
  have hkk : τ k.val ≤ τ (k.val + 1) := hτ.monotoneOn (by simp) (by simp) (by omega)
  by_cases hkn : k ≤ n
  · have hkn' : τ (k.val + 1) ≤ τ (n.val + 1) :=
      hτ.monotoneOn (by simp) (by simp) (by exact Nat.add_le_add_right hkn 1)
    have heq : Ioc (τ 0) (τ (n.val + 1)) ∩ Ioc (τ k.val) (τ (k.val + 1)) =
        Ioc (τ k.val) (τ (k.val + 1)) := by
      apply inter_eq_right.2
      exact Ioc_subset_Ioc hk0 hkn'
    rw [integral0127, heq, ← intervalIntegral.integral_of_le hkk,
      intervalIntegral.integral_const_mul, integral_H]
    simp [A0127, hkn]
  · have hnk : τ (n.val + 1) ≤ τ k.val :=
      hτ.monotoneOn (by simp) (by simp) (by exact Nat.succ_le_of_lt (not_le.1 hkn))
    have heq : Ioc (τ 0) (τ (n.val + 1)) ∩ Ioc (τ k.val) (τ (k.val + 1)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro s hs
      exact (not_lt_of_ge (hs.1.2.trans hnk)) hs.2.1
    simp [integral0127, heq, A0127, hkn]

end Triangular

section Interior

variable {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)

lemma cone_interior (hM : M.det ≠ 0) : (interior (cone M)).Nonempty := by
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)
  have hs : Function.Surjective M.mulVecLin := Matrix.mulVec_surjective_iff_isUnit.2 hu
  have hop := M.mulVecLin.isOpenMap_of_finiteDimensional hs
  let U : Set (Fin N → ℝ) := {q | ∀ i, 0 < q i}
  have hU : IsOpen U := by
    have heq : U = ⋂ i : Fin N, {q : Fin N → ℝ | 0 < q i} := by ext q; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hsub : M.mulVecLin '' U ⊆ cone M := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, fun i => (hq i).le, rfl⟩
  have hi := (hop U hU).subset_interior_iff.2 hsub
  exact ⟨M.mulVec (fun _ => 1), hi ⟨fun _ => 1, by intro i; norm_num, rfl⟩⟩

lemma no_equality (hM : M.det ≠ 0) (w : Fin N → ℝ)
    (hw : ∀ V ∈ cone M, dotProduct w V = 0) : w = 0 := by
  have h := (annihilates_cone M w).1 hw
  have hu : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 (by simpa using hM))
  apply Matrix.mulVec_injective_iff_isUnit.2 hu
  simpa using h

end Interior

lemma integral_pieces {n k₀ : ℕ} (τ γ : ℕ → ℝ) (lam t q : ℝ) (g : ℝ → ℝ)
    (hkn : k₀ < n) (hτ : StrictMonoOn τ (Iic n)) (hlo : τ k₀ ≤ t) (hhi : t ≤ τ (k₀ + 1))
    (hg : ∀ k ∈ Finset.Ico k₀ n, ∀ s ∈ Ioo (max t (τ k)) (τ (k + 1)),
      g s = (q * γ (n - k) ^ 2) * Real.exp (-2 * lam * (τ n - s))) :
    ∫ s in t..τ n, g s = ∑ k ∈ Finset.Ico k₀ n,
      (q * γ (n - k) ^ 2) * H lam (τ n) (max t (τ k)) (τ (k + 1)) := by
  let b := fun k => max t (τ k)
  have hmono {a c : ℕ} (hac : a ≤ c) (hc : c ≤ n) : τ a ≤ τ c :=
    hτ.monotoneOn (by simp; omega) hc hac
  have hnext (k : ℕ) (hk : k ∈ Finset.Ico k₀ n) : b (k + 1) = τ (k + 1) := by
    exact max_eq_right (hhi.trans (hmono (by have := Finset.mem_Ico.1 hk; omega)
      (by have := Finset.mem_Ico.1 hk; omega)))
  have hle (k : ℕ) (hk : k ∈ Finset.Ico k₀ n) : max t (τ k) ≤ τ (k + 1) := by
    apply max_le
    · exact hhi.trans (hmono (by have := Finset.mem_Ico.1 hk; omega)
        (by have := Finset.mem_Ico.1 hk; omega))
    · exact hmono (by omega) (by have := Finset.mem_Ico.1 hk; omega)
  have hint (k : ℕ) (hk : k ∈ Finset.Ico k₀ n) : IntervalIntegrable g volume (b k) (b (k + 1)) := by
    rw [hnext k hk]
    have hc : Continuous (fun s => (q * γ (n - k) ^ 2) * Real.exp (-2 * lam * (τ n - s))) := by fun_prop
    apply (hc.intervalIntegrable (b k) (τ (k + 1))).congr_uIoo
    intro s hs
    rw [Set.uIoo_of_le (hle k hk)] at hs
    exact (hg k hk s hs).symm
  have hb0 : b k₀ = t := max_eq_left hlo
  have hbn : b n = τ n := max_eq_right (hhi.trans (hmono hkn le_rfl))
  calc
    ∫ s in t..τ n, g s = ∫ s in b k₀..b n, g s := by rw [hb0, hbn]
    _ = ∑ k ∈ Finset.Ico k₀ n, ∫ s in b k..b (k + 1), g s :=
      (intervalIntegral.sum_integral_adjacent_intervals_Ico (a := b) (f := g) hkn.le
        (fun k hk => hint k (Finset.mem_Ico.2 hk))).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hnext k hk, intervalIntegral.integral_congr_Ioo_of_le (hle k hk) (hg k hk),
        intervalIntegral.integral_const_mul, integral_H]

theorem variance_eq_matrix : Standalone.GaussianMeetingVarianceCone.integralStatement := by
  intro m d k₀ τ γ lam t q g V hτ hlo hhi hg hV
  funext n
  rw [hV]
  change (∑ j, ∫ s in t..τ (k₀ + n.val + 1), g n j s) =
    ∑ j, A τ γ lam t k₀ n j * q j
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_pieces τ (fun k => γ k j) (lam j) t (q j) (g n j)
    (by omega) (hτ.mono (by intro k hk; simp only [mem_Iic] at hk ⊢; omega)) hlo hhi (hg n j)]
  unfold A
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem partition_variance_eq_matrix : Standalone.GaussianMeetingVarianceCone.partitionStatement := by
  intro m d K t T b g q V hT hg hV
  constructor
  · funext n
    rw [hV]
    change (∑ j, ∫ s in t..T n,
      ∑ l : Fin K, q (j, l) * (Ioc (b l.val) (b (l.val + 1))).indicator (g n j) s) =
        ∑ p : Fin d × Fin K, A0126 t T b g n p * q p
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_of_le (hT n)]
    have hi (l : Fin K) : Integrable (fun s =>
        q (j, l) * (Ioc (b l.val) (b (l.val + 1))).indicator (g n j) s)
        (volume.restrict (Ioc t (T n))) :=
      ((hg n j).indicator measurableSet_Ioc).const_mul _
    rw [integral_finsetSum _ (fun l _ => hi l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_comm]
    exact mul_comm _ _
  · simpa using (A0126 (K := K) t T b g).rank_le_card_width

theorem gaussianMeetingVarianceCone : Standalone.GaussianMeetingVarianceCone.statement := by
  refine ⟨variance_eq_matrix, partition_variance_eq_matrix, integral_H, ?_, ?_⟩
  · intro m d M
    exact ⟨scale_range M, annihilates_cone M, column_space M, M.rank_le_width,
      by simpa using nullity M⟩
  · intro N τ γ lam hτ hγ
    have hp := A0127_det_pos (lam := lam) hτ hγ
    exact ⟨integral0127_eq hτ, A0127_det, hp, cone_interior _ (ne_of_gt hp),
      no_equality _ (ne_of_gt hp)⟩

end Novel.GaussianMeetingVarianceConeProof

import Standalone.SeparableMeetingMarkovCoefficients
import Novel.SeparableMeetingShapesProof
import Mathlib.Analysis.Calculus.FDeriv.Const

open MeasureTheory Filter Topology
open scoped NNReal
open Standalone.BoundedVarianceExistence Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingMarkovCoefficients
namespace Novel.SeparableMeetingMarkovCoefficientsProof

variable {p d N : ℕ}

lemma zpart_sub (x y : Fin (dim028 p d N) → ℝ) : zpart x - zpart y = zpart (x - y) := rfl

lemma norm_zpart_le (x : Fin (dim028 p d N) → ℝ) : ‖zpart x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => norm_le_pi_norm x _

lemma measurable_zpart : Measurable (zpart : (Fin (dim028 p d N) → ℝ) → Fin p → ℝ) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

lemma sq_sub_le {a b K L D : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) (hab : |a - b| ≤ L * D)
    (hL : 0 ≤ L) (hD : 0 ≤ D) : |a ^ 2 - b ^ 2| ≤ 2 * K * L * D := by
  have he : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  have h1 : |a + b| ≤ 2 * K := (abs_add_le a b).trans (by linarith)
  have hK : 0 ≤ K := (abs_nonneg a).trans ha
  rw [he, abs_mul]
  calc |a + b| * |a - b| ≤ (2 * K) * (L * D) :=
        mul_le_mul h1 hab (abs_nonneg _) (by linarith)
    _ = 2 * K * L * D := by ring

lemma abs_unit_mul {I E w : ℝ} (hI : |I| ≤ 1) (hE : |E| ≤ 1) : |I * E * w| ≤ |w| := by
  rw [abs_mul, abs_mul]
  have : |I| * |E| ≤ 1 := by
    calc |I| * |E| ≤ 1 * 1 := mul_le_mul hI hE (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc |I| * |E| * |w| ≤ 1 * |w| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = |w| := one_mul _

lemma coord_le {n : ℕ} {v : Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |v i| ≤ C) :
    ‖v‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun i => by rw [Real.norm_eq_abs]; exact h i

lemma coord2_le {n m : ℕ} {v : Fin n → Fin m → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i l, |v i l| ≤ C) : ‖v‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun i => coord_le hC (h i)

lemma abs_coord2_le {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (l : Fin m) :
    |v i l| ≤ ‖v‖ := by
  have h1 : ‖v i l‖ ≤ ‖v i‖ := norm_le_pi_norm (v i) l
  have h2 : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

lemma lipschitz : lipschitzStatement := by
  intro p d N m beta Sigma psi ind eH G drv LZ Kψ Lψ Gbar hLZ hK hL hG hZ hψ hψL hind heH hGb
    t x y
  set D := ‖x - y‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have hzD : ‖zpart x - zpart y‖ ≤ D := by rw [zpart_sub]; exact norm_zpart_le _
  set K := LZ + (1 + 2 * Kψ * (1 + Gbar)) * Lψ with hKdef
  have hexp : K * D = LZ * D + Lψ * D + 2 * Kψ * Lψ * D + Gbar * (2 * Kψ * Lψ * D) := by
    rw [hKdef]; ring
  have h1 : 0 ≤ LZ * D := mul_nonneg hLZ hD0
  have h2 : 0 ≤ Lψ * D := mul_nonneg hL hD0
  have h3 : 0 ≤ 2 * Kψ * Lψ * D := by positivity
  have h4 : 0 ≤ Gbar * (2 * Kψ * Lψ * D) := by positivity
  have hKD : 0 ≤ K * D := by rw [hexp]; linarith
  have hpsi (j : Fin d) : |psi j (t, zpart x) - psi j (t, zpart y)| ≤ Lψ * D :=
    (hψL j t _ _).trans (mul_le_mul_of_nonneg_left hzD hL)
  have hsq (j : Fin d) : |psi j (t, zpart x) ^ 2 - psi j (t, zpart y) ^ 2| ≤ 2 * Kψ * Lψ * D :=
    sq_sub_le (hψ j _) (hψ j _) (hpsi j) hL hD0
  have hbeta : ‖beta (t, zpart x) - beta (t, zpart y)‖ ≤ LZ * D :=
    (hZ t _ _).1.trans (mul_le_mul_of_nonneg_left hzD hLZ)
  have hSigma : ‖Sigma (t, zpart x) - Sigma (t, zpart y)‖ ≤ LZ * D :=
    (hZ t _ _).2.trans (mul_le_mul_of_nonneg_left hzD hLZ)
  constructor
  · apply coord_le hKD
    intro i
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [Pi.sub_apply, drift028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · simp only [Sum.elim_inl]
      rw [← mul_sub]
      have hc : |beta (t, zpart x) i' - beta (t, zpart y) i'| ≤ LZ * D := by
        have := norm_le_pi_norm (beta (t, zpart x) - beta (t, zpart y)) i'
        rw [Real.norm_eq_abs, Pi.sub_apply] at this
        exact this.trans hbeta
      calc |eH t * (beta (t, zpart x) i' - beta (t, zpart y) i')|
          = |1 * eH t * (beta (t, zpart x) i' - beta (t, zpart y) i')| := by rw [one_mul]
        _ ≤ |beta (t, zpart x) i' - beta (t, zpart y) i'| :=
            abs_unit_mul (by norm_num) (heH t)
        _ ≤ K * D := by rw [hexp]; linarith
    · simp only [Sum.elim_inr, Sum.elim_inl]
      have he : -(ind jk.2 t * eH t * psi jk.1 (t, zpart x) ^ 2 * G jk.1 jk.2 t) -
          -(ind jk.2 t * eH t * psi jk.1 (t, zpart y) ^ 2 * G jk.1 jk.2 t) =
          -(ind jk.2 t * eH t * (G jk.1 jk.2 t *
            (psi jk.1 (t, zpart x) ^ 2 - psi jk.1 (t, zpart y) ^ 2))) := by ring
      rw [he, abs_neg]
      calc _ ≤ |G jk.1 jk.2 t * (psi jk.1 (t, zpart x) ^ 2 - psi jk.1 (t, zpart y) ^ 2)| :=
            abs_unit_mul (hind _ _) (heH t)
        _ = |G jk.1 jk.2 t| * |psi jk.1 (t, zpart x) ^ 2 - psi jk.1 (t, zpart y) ^ 2| :=
            abs_mul _ _
        _ ≤ Gbar * (2 * Kψ * Lψ * D) := mul_le_mul (hGb _ _ _) (hsq _) (abs_nonneg _) hG
        _ ≤ K * D := by rw [hexp]; linarith
    · simp only [Sum.elim_inr]
      rw [← mul_sub]
      calc _ ≤ |psi jk.1 (t, zpart x) ^ 2 - psi jk.1 (t, zpart y) ^ 2| :=
            abs_unit_mul (hind _ _) (heH t)
        _ ≤ 2 * Kψ * Lψ * D := hsq _
        _ ≤ K * D := by rw [hexp]; linarith
  · apply coord2_le hKD
    intro i l
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [Pi.sub_apply, diffusion028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · simp only [Sum.elim_inl]
      rw [← mul_sub]
      have hc : |Sigma (t, zpart x) i' l - Sigma (t, zpart y) i' l| ≤ LZ * D :=
        (abs_coord2_le (Sigma (t, zpart x) - Sigma (t, zpart y)) i' l).trans hSigma
      calc |eH t * (Sigma (t, zpart x) i' l - Sigma (t, zpart y) i' l)|
          = |1 * eH t * (Sigma (t, zpart x) i' l - Sigma (t, zpart y) i' l)| := by
            rw [one_mul]
        _ ≤ |Sigma (t, zpart x) i' l - Sigma (t, zpart y) i' l| :=
            abs_unit_mul (by norm_num) (heH t)
        _ ≤ K * D := by rw [hexp]; linarith
    · simp only [Sum.elim_inr, Sum.elim_inl]
      split_ifs
      · rw [← mul_sub]
        calc _ ≤ |psi jk.1 (t, zpart x) - psi jk.1 (t, zpart y)| :=
              abs_unit_mul (hind _ _) (heH t)
          _ ≤ Lψ * D := hpsi _
          _ ≤ K * D := by rw [hexp]; linarith
      · simpa using hKD
    · simpa using hKD

lemma coefficients : coefficientsStatement := by
  intro p d N m beta Sigma psi ind eH G drv Kψ Lψ Gbar hZ hψm hψ hψL hindm hind heHm heH hGm hGb
  obtain ⟨hbm, hSm, ⟨LZ, hLZ, hZL⟩, hZB⟩ := hZ
  have hψ' (j : Fin d) (q) : |psi j q| ≤ |Kψ| := (hψ j q).trans (le_abs_self _)
  have hGb' (j : Fin d) (k : Fin (N+1)) (t) : |G j k t| ≤ |Gbar| :=
    (hGb j k t).trans (le_abs_self _)
  have hψL' (j : Fin d) (t) (z z' : Fin p → ℝ) :
      |psi j (t,z) - psi j (t,z')| ≤ |Lψ| * ‖z - z'‖ :=
    (hψL j t z z').trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hq : Measurable fun q : ℝ≥0 × (Fin (dim028 p d N) → ℝ) => (q.1, zpart q.2) :=
    measurable_fst.prodMk (measurable_zpart.comp measurable_snd)
  refine ⟨?_, ?_, ⟨_, ?_, lipschitz p d N m beta Sigma psi ind eH G drv LZ |Kψ| |Lψ| |Gbar|
    hLZ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hZL hψ' hψL' hind heH hGb'⟩, ?_⟩
  · refine measurable_pi_iff.2 fun i => ?_
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [drift028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · exact (heHm.comp measurable_fst).mul ((measurable_pi_apply i').comp (hbm.comp hq))
    · exact ((((hindm jk.2).comp measurable_fst).mul (heHm.comp measurable_fst)).mul
        (((hψm jk.1).comp hq).pow_const 2)).mul ((hGm jk.1 jk.2).comp measurable_fst) |>.neg
    · exact (((hindm jk.2).comp measurable_fst).mul (heHm.comp measurable_fst)).mul
        (((hψm jk.1).comp hq).pow_const 2)
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l => ?_
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [diffusion028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · exact (heHm.comp measurable_fst).mul
        ((measurable_pi_apply l).comp ((measurable_pi_apply i').comp (hSm.comp hq)))
    · simp only [Sum.elim_inr, Sum.elim_inl]
      split_ifs
      · exact (((hindm jk.2).comp measurable_fst).mul (heHm.comp measurable_fst)).mul
          ((hψm jk.1).comp hq)
      · exact measurable_const
    · exact measurable_const
  · positivity
  · intro T R hR
    obtain ⟨CZ, hCZ, hCZb⟩ := hZB T R hR
    set C := CZ + |Kψ| ^ 2 * (1 + |Gbar|) + |Kψ| with hCdef
    have hC : 0 ≤ C := by positivity
    refine ⟨C, hC, fun t ht x hx => ?_⟩
    have hz : ‖zpart x‖ ≤ R := (norm_zpart_le x).trans hx
    have hb := (hCZb t ht _ hz).1
    have hs := (hCZb t ht _ hz).2
    have hψ2 (j : Fin d) : |psi j (t, zpart x) ^ 2| ≤ |Kψ| ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hψ' j _) 2
    have hK2 : 0 ≤ |Kψ| ^ 2 * |Gbar| := by positivity
    constructor
    · apply coord_le hC
      intro i
      obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
      simp only [drift028, Equiv.symm_apply_apply]
      rcases s with i' | jk | jk
      · simp only [Sum.elim_inl]
        have hc : |beta (t, zpart x) i'| ≤ CZ := by
          have := norm_le_pi_norm (beta (t, zpart x)) i'
          rw [Real.norm_eq_abs] at this
          exact this.trans hb
        calc |eH t * beta (t, zpart x) i'| = |1 * eH t * beta (t, zpart x) i'| := by
              rw [one_mul]
          _ ≤ |beta (t, zpart x) i'| := abs_unit_mul (by norm_num) (heH t)
          _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg Kψ, abs_nonneg Gbar]
      · simp only [Sum.elim_inr, Sum.elim_inl, abs_neg]
        rw [show ind jk.2 t * eH t * psi jk.1 (t, zpart x) ^ 2 * G jk.1 jk.2 t =
          ind jk.2 t * eH t * (psi jk.1 (t, zpart x) ^ 2 * G jk.1 jk.2 t) by ring]
        calc _ ≤ |psi jk.1 (t, zpart x) ^ 2 * G jk.1 jk.2 t| := abs_unit_mul (hind _ _) (heH t)
          _ = |psi jk.1 (t, zpart x) ^ 2| * |G jk.1 jk.2 t| := abs_mul _ _
          _ ≤ |Kψ| ^ 2 * |Gbar| := mul_le_mul (hψ2 _) (hGb' _ _ _) (abs_nonneg _) (by positivity)
          _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg Kψ, abs_nonneg Gbar]
      · simp only [Sum.elim_inr]
        calc _ ≤ |psi jk.1 (t, zpart x) ^ 2| := abs_unit_mul (hind _ _) (heH t)
          _ ≤ |Kψ| ^ 2 := hψ2 _
          _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg Kψ, abs_nonneg Gbar]
    · apply coord2_le hC
      intro i l
      obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
      simp only [diffusion028, Equiv.symm_apply_apply]
      rcases s with i' | jk | jk
      · simp only [Sum.elim_inl]
        calc |eH t * Sigma (t, zpart x) i' l| = |1 * eH t * Sigma (t, zpart x) i' l| := by
              rw [one_mul]
          _ ≤ |Sigma (t, zpart x) i' l| := abs_unit_mul (by norm_num) (heH t)
          _ ≤ CZ := (abs_coord2_le _ i' l).trans hs
          _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg Kψ, abs_nonneg Gbar]
      · simp only [Sum.elim_inr, Sum.elim_inl]
        split_ifs
        · calc _ ≤ |psi jk.1 (t, zpart x)| := abs_unit_mul (hind _ _) (heH t)
            _ ≤ |Kψ| := hψ' _ _
            _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg Kψ, abs_nonneg Gbar]
        · simpa using hC
      · simpa using hC

lemma frozen : frozenStatement := by
  intro p d N m beta Sigma psi ind eH G drv k J c hb hS hψ hk hl heH hG
  refine ⟨fun x i => Sum.elim (fun i' => beta (0, zpart x) i')
      (Sum.elim
        (fun jk : Fin d × Fin (N+1) =>
          if jk.2 = k then -(psi jk.1 (0, zpart x) ^ 2 * c jk.1) else 0)
        (fun jk : Fin d × Fin (N+1) => if jk.2 = k then psi jk.1 (0, zpart x) ^ 2 else 0))
      ((equiv028 p d N).symm i),
    fun x i l => Sum.elim (fun i' => Sigma (0, zpart x) i' l)
      (Sum.elim
        (fun jk : Fin d × Fin (N+1) =>
          if jk.2 = k ∧ l = drv jk.1 then psi jk.1 (0, zpart x) else 0)
        (fun _ => 0))
      ((equiv028 p d N).symm i), fun t ht x => ⟨?_, ?_⟩⟩
  · funext i
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [drift028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · simp [heH t ht, hb t 0]
    · by_cases hjk : jk.2 = k
      · simp [hjk, hk t ht, heH t ht, hG jk.1 t ht, hψ jk.1 t 0]
      · simp [hjk, hl jk.2 hjk t ht]
    · by_cases hjk : jk.2 = k
      · simp [hjk, hk t ht, heH t ht, hψ jk.1 t 0]
      · simp [hjk, hl jk.2 hjk t ht]
  · funext i l
    obtain ⟨s, rfl⟩ := (equiv028 p d N).surjective i
    simp only [diffusion028, Equiv.symm_apply_apply]
    rcases s with i' | jk | jk
    · simp [heH t ht, hS t 0]
    · by_cases hjk : jk.2 = k
      · simp [hjk, hk t ht, heH t ht, hψ jk.1 t 0]
      · simp [hjk, hl jk.2 hjk t ht]
    · simp

lemma constantPrimitive : constantPrimitiveStatement := by
  intro g b t h0 h1 hz
  have h := Novel.SeparableMeetingShapesProof.primitive g (fun _ => 0) 0 b t h0 h1
    (fun u hu => by rw [hz u hu, zero_mul])
  simpa using h

lemma movingPrimitive : movingPrimitiveStatement := by
  intro g phi a b c hbc hg hphi hshape hconst
  have hf : Continuous fun u => a * phi u := continuous_const.mul hphi
  set F : ℝ → ℝ := fun t => ∫ u in b..t, a * phi u with hF
  have hF0 : ∀ t ∈ Set.Icc b c, F t = 0 := by
    intro t ht
    have h1 := intervalIntegral.integral_interval_sub_left (hg 0 t) (hg 0 b)
    have h2 : (∫ u in b..t, g u) = F t := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le ht.1] at hu
      exact hshape u ⟨hu.1, hu.2.trans ht.2⟩
    have h3 := hconst t ht
    simp only [G026] at h3
    rw [← h2, ← h1, h3, sub_self]
  have hopen : ∀ u ∈ Set.Ioo b c, a * phi u = 0 := by
    intro u hu
    have hd : HasDerivAt F (a * phi u) u := (hf.integral_hasStrictDerivAt b u).hasDerivAt
    have hev : F =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      exact hF0 v (Set.Ioo_subset_Icc_self hv)
    have h0 : HasDerivAt F 0 u := (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev
    exact hd.unique h0
  have hclosed : IsClosed {u | a * phi u = 0} := isClosed_eq hf continuous_const
  intro u hu
  have hsub : closure (Set.Ioo b c) ⊆ {u | a * phi u = 0} :=
    closure_minimal (fun v hv => hopen v hv) hclosed
  rw [closure_Ioo hbc.ne] at hsub
  exact hsub hu

theorem separableMeetingMarkovCoefficients : Standalone.SeparableMeetingMarkovCoefficients.statement :=
  ⟨lipschitz, coefficients, frozen, constantPrimitive, movingPrimitive⟩

end Novel.SeparableMeetingMarkovCoefficientsProof

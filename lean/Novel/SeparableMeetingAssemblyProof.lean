import Standalone.SeparableMeetingAssembly
import Novel.SeparableMeetingRepresentationProof

open MeasureTheory ProbabilityTheory Filter
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingAssembly
open scoped NNReal
namespace Novel.SeparableMeetingAssemblyProof

lemma lo_le_hi {N : ℕ} {Td : Fin (N+2) → ℝ≥0} (hTd : Monotone Td) (k : Fin (N+1)) :
    lo026 Td k ≤ hi026 Td k :=
  hTd (Fin.castSucc_le_succ k)

lemma mask_self {Ω : Type*} {N : ℕ} {Td : Fin (N+2) → ℝ≥0} (hTd : Monotone Td)
    (chi : ℝ≥0 → Ω → ℝ) {k : Fin (N+1)} {s : ℝ≥0}
    (hlo : lo026 Td k < s) (hhi : s ≤ hi026 Td k) (ω : Ω) :
    H026 chi (lo026 Td k) (hi026 Td k) s ω = chi s ω := by
  rw [Novel.SeparableMeetingIntegralsProof.mask chi _ _ (lo_le_hi hTd k)]
  simp [hlo, hhi]

lemma mask_other {Ω : Type*} {N : ℕ} {Td : Fin (N+2) → ℝ≥0} (hTd : Monotone Td)
    (chi : ℝ≥0 → Ω → ℝ) {k k' : Fin (N+1)} {s : ℝ≥0}
    (hlo : lo026 Td k < s) (hhi : s ≤ hi026 Td k) (hk : k' ≠ k) (ω : Ω) :
    H026 chi (lo026 Td k') (hi026 Td k') s ω = 0 := by
  rw [Novel.SeparableMeetingIntegralsProof.mask chi _ _ (lo_le_hi hTd k')]
  rcases lt_or_gt_of_ne hk with h | h
  · have hle : hi026 Td k' ≤ lo026 Td k := hTd (by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact h)
    simp [not_le.mpr (hle.trans_lt hlo)]
  · have hle : hi026 Td k ≤ lo026 Td k' := hTd (by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact h)
    simp [not_lt.mpr (hhi.trans hle)]

lemma mask_none {Ω : Type*} {N : ℕ} {Td : Fin (N+2) → ℝ≥0} (hTd : Monotone Td)
    (chi : ℝ≥0 → Ω → ℝ) {s : ℝ≥0}
    (hs : ¬ ∃ k, lo026 Td k < s ∧ s ≤ hi026 Td k) (k : Fin (N+1)) (ω : Ω) :
    H026 chi (lo026 Td k) (hi026 Td k) s ω = 0 := by
  rw [Novel.SeparableMeetingIntegralsProof.mask chi _ _ (lo_le_hi hTd k)]
  simp only [ite_eq_right_iff]
  exact fun h => absurd ⟨k, h⟩ hs

lemma pointwise : pointwiseStatement := by
  intro Ω d N Td hTd chi g k s hlo hhi T ω
  constructor
  · intro j
    rw [sigma026, Finset.sum_eq_single k
      (fun k' _ hk => by rw [mask_other hTd (chi j) hlo hhi hk, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), mask_self hTd (chi j) hlo hhi, mul_comm]
  · simp only [alpha026, Real.toNNReal_coe]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single k
      (fun k' _ hk => by rw [mask_other hTd (chi j) hlo hhi hk]; ring)
      (fun h => absurd (Finset.mem_univ k) h), mask_self hTd (chi j) hlo hhi]
    ring

lemma drift : Standalone.SeparableMeetingAssembly.driftStatement := by
  intro Ω d N Td hTd chi g hg s T ω
  by_cases hs : ∃ k, lo026 Td k < s ∧ s ≤ hi026 Td k
  · obtain ⟨k, hlo, hhi⟩ := hs
    have hp u := pointwise Ω d N Td hTd chi g k s hlo hhi u ω
    have ha : (fun u => alpha026 Td chi g u s ω) = fun u =>
        ∑ j, chi j s ω ^ 2 * g j k u * (∫ v in (s:ℝ)..u, g j k v) := by
      funext u
      rw [(hp u).2]
      apply Finset.sum_congr rfl
      intro j _
      rw [G026, G026, intervalIntegral.integral_interval_sub_left (hg j k 0 u) (hg j k 0 s)]
    have hσ (j) : (fun u => sigma026 Td chi g j u s ω) = fun u => chi j s ω * g j k u := by
      funext u
      exact (hp u).1 j
    simp only [ha, hσ]
    exact Novel.SeparableMeetingShapesProof.hjm d (fun j => g j k) (fun j => chi j s ω)
      s T (fun j => hg j k _ _)
  · simp [alpha026, sigma026, mask_none hTd _ hs]

lemma curve : curveStatement := by
  intro Ω mΩ S N Td hTd chi g hchi hg T
  have hdom (j) (k : Fin (N+1)) : U4 S.ℱ S.μ (H026 (chi j) (lo026 Td k) (hi026 Td k)) :=
    Novel.SeparableMeetingIntegralsProof.domain S (chi j) _ _ (lo_le_hi hTd k) (hchi j)
  have hG (j) (k : Fin (N+1)) : Continuous (G026 (g j k)) :=
    intervalIntegral.continuous_primitive (hg j k) 0
  have hrep (j) := Novel.SeparableMeetingRepresentationProof.representation Ω mΩ S j (N+1)
    (fun k => H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun k => g j k T)
    (fun k => G026 (g j k) T) (fun k => G026 (g j k)) (hdom j) (hG j)
  refine ⟨fun j => (hrep j).1, ?_⟩
  have hsq : ∀ᵐ ω ∂S.μ, ∀ (n : ℕ) j (k : Fin (N+1)), IntervalIntegrable
      (fun s => H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2)
        volume 0 (n:ℝ) := by
    simp only [ae_all_iff]
    exact fun n j k =>
      Novel.SeparableMeetingCoefficientsProof.square_integrable S _ (hdom j k) n
  have hall : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t : ℝ≥0,
      S.I j (sigma026 Td chi g j T) t ω +
        (∫ s in (0:ℝ)..t, ∑ k, g j k T *
          H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2 *
            (G026 (g j k) T - G026 (g j k) s)) =
      ∑ k, (g j k T * (S.I j (H026 (chi j) (lo026 Td k) (hi026 Td k)) t ω -
          D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (G026 (g j k)) t ω) +
        g j k T * G026 (g j k) T *
          D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω) :=
    ae_all_iff.2 fun j => (hrep j).2
  filter_upwards [hall, hsq] with ω hω hq t
  obtain ⟨n, hn⟩ := exists_nat_ge (t:ℝ)
  have hint (j) (k : Fin (N+1)) : IntervalIntegrable (fun s => g j k T *
      H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2 *
        (G026 (g j k) T - G026 (g j k) s)) volume 0 t := by
    have h0 := (hq n j k).mono_set (by
      rw [Set.uIcc_of_le t.coe_nonneg, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ n)]
      exact Set.Icc_subset_Icc le_rfl hn)
    exact (h0.const_mul (g j k T)).mul_continuousOn
      (continuous_const.sub (hG j k)).continuousOn
  have hsum (j) : IntervalIntegrable (fun s => ∑ k, g j k T *
      H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2 *
        (G026 (g j k) T - G026 (g j k) s)) volume 0 t := by
    have h := IntervalIntegrable.sum Finset.univ (fun k _ => hint j k)
    convert h using 1
    funext s
    simp
  simp only [alpha026]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hsum j), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_comm, hω j t]
  apply Finset.sum_congr rfl
  intro k _
  simp only [M0262, J026, Real.toNNReal_coe]

lemma freeze : freezeStatement := by
  intro Ω mΩ S chi lo hi hle hchi G hGc
  have hdom := Novel.SeparableMeetingIntegralsProof.domain S chi lo hi hle hchi
  have ho := Novel.SeparableMeetingCoefficientsProof.ordinary Ω mΩ S _ hdom G hGc
  have hall : ∀ᵐ ω ∂S.μ, ∀ n : ℕ,
      IntervalIntegrable (fun s => H026 chi lo hi (Real.toNNReal s) ω ^ 2 * G s)
        volume 0 (n:ℝ) :=
    ae_all_iff.2 fun n => (ho.2 n).mono fun ω hω => hω.1
  filter_upwards [hall] with ω hω t
  refine ⟨fun ht => Novel.SeparableMeetingCoefficientsProof.ordinary_before chi lo hi t
    hle ht G ω, fun ht => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (t:ℝ)
  exact Novel.SeparableMeetingCoefficientsProof.ordinary_after chi lo hi t hle ht G ω
    ((hω n).mono_set (by
      rw [Set.uIcc_of_le t.coe_nonneg, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ n)]
      exact Set.Icc_subset_Icc le_rfl hn))

lemma shapeCurve : shapeCurveStatement := by
  intro d n g phi a b T M A hg hshape
  have h := Novel.SeparableMeetingShapesProof.shape d n a (fun j k => G026 (g j k) b) M A
    (fun j => phi j T) (fun j => ∫ u in b..T, phi j u) 0
  simp only [zero_add] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [Novel.SeparableMeetingShapesProof.primitive (g j k) (phi j) (a j k) b T
      (hg j k _ _) (hg j k _ _) (hshape j k), hshape j k T Set.right_mem_uIcc]

lemma loading : loadingStatement := by
  intro n I a phi hI hphi
  refine ⟨fun x y => ?_, fun hdis m u hu => ?_⟩
  · have hc (m) : IntervalIntegrable (fun u => a m * phi u) volume x y :=
      (continuous_const.mul hphi).intervalIntegrable x y
    have h := IntervalIntegrable.sum Finset.univ
      (fun m _ => (⟨(hc m).1.indicator (hI m), (hc m).2.indicator (hI m)⟩ :
        IntervalIntegrable ((I m).indicator (fun u => a m * phi u)) volume x y))
    convert h using 1
    funext u
    simp
  · rw [Finset.sum_eq_single m
      (fun m' _ hm => Set.indicator_of_notMem
        (Set.disjoint_left.1 (hdis hm).symm hu) _)
      (fun h => absurd (Finset.mem_univ m) h), Set.indicator_of_mem hu]

/-- (26.4) for the actual audited AX-03/AX-04 input. -/
lemma upstream_curve {Ω : Type} [MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (N : ℕ) (Td : Fin (N+2) → ℝ≥0) (hTd : Monotone Td)
    (chi : Fin S.m → ℝ≥0 → Ω → ℝ) (g : Fin S.m → Fin (N+1) → ℝ → ℝ)
    (hchi : ∀ j, Upstream.U4 S.ℱ S.μ (chi j))
    (hg : ∀ j k x y, IntervalIntegrable (g j k) volume x y) (T : ℝ) :
    (∀ j, Upstream.U4 S.ℱ S.μ (sigma026 Td chi g j T)) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
      (∫ s in (0:ℝ)..t, alpha026 Td chi g T s ω) + ∑ j, S.I j (sigma026 Td chi g j T) t ω =
      ∑ j, ∑ k,
        (g j k T * (S.I j (H026 (chi j) (lo026 Td k) (hi026 Td k)) t ω -
            D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (G026 (g j k)) t ω) +
          g j k T * G026 (g j k) T *
            D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω) := by
  have h := curve Ω _ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) N Td hTd
    chi g hchi hg T
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2] with ω hω t
  have h' := hω t
  simp only [M0262, J026, Real.toNNReal_coe] at h'
  exact h'

theorem separableMeetingAssembly : Standalone.SeparableMeetingAssembly.statement :=
  ⟨pointwise, drift, curve, freeze, shapeCurve, loading⟩
end Novel.SeparableMeetingAssemblyProof

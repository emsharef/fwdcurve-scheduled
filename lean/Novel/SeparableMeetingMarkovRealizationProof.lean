import Standalone.SeparableMeetingMarkovRealization
import Novel.SeparableMeetingAssemblyProof

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SeparableMeetingIntegrals
open Standalone.SeparableMeetingCoefficients Standalone.SeparableMeetingShapes
open Standalone.SeparableMeetingAssembly Standalone.SeparableMeetingMarkovCoefficients
open Standalone.SeparableMeetingMarkovRealization
namespace Novel.SeparableMeetingMarkovRealizationProof

lemma dim : dimStatement := by
  intro p d N
  refine ⟨?_, ?_⟩
  · simp [Index028, dim028, Fintype.card_sum, Fintype.card_prod]
  · simp only [dim028]; ring

lemma lambda : lambdaStatement := by
  intro p d N f0 g G
  refine ⟨fun z M A T => ?_, fun T => ?_⟩
  · simp only [Lambda028, state028, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  · exact continuous_const.add (continuous_finset_sum _ fun j _ =>
      continuous_finset_sum _ fun k _ => continuous_const.mul
        ((continuous_apply _).add (continuous_const.mul (continuous_apply _))))

/-- Claim 026's (26.4) with the factor `j` driven by `drv j`. -/
lemma curve_drv {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω)
    {d N : ℕ} (drv : Fin d → Fin S.m) (Td : Fin (N+2) → ℝ≥0) (hTd : Monotone Td)
    (chi : Fin d → ℝ≥0 → Ω → ℝ) (g : Fin d → Fin (N+1) → ℝ → ℝ)
    (hchi : ∀ j, U4 S.ℱ S.μ (chi j)) (hg : ∀ j k x y, IntervalIntegrable (g j k) volume x y)
    (T : ℝ) :
    (∀ j, U4 S.ℱ S.μ (sigma026 Td chi g j T)) ∧
    ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
      (∫ s in (0:ℝ)..t, alpha026 Td chi g T s ω) + ∑ j, S.I (drv j) (sigma026 Td chi g j T) t ω =
      ∑ j, ∑ k,
        (g j k T * M0262 S (drv j) (chi j) (lo026 Td k) (hi026 Td k) (G026 (g j k)) t ω +
          g j k T * G026 (g j k) T *
            D026 (H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun _ => 1) t ω) := by
  have hdom (j) (k : Fin (N+1)) : U4 S.ℱ S.μ (H026 (chi j) (lo026 Td k) (hi026 Td k)) :=
    Novel.SeparableMeetingIntegralsProof.domain S (chi j) _ _
      (Novel.SeparableMeetingAssemblyProof.lo_le_hi hTd k) (hchi j)
  have hG (j) (k : Fin (N+1)) : Continuous (G026 (g j k)) :=
    intervalIntegral.continuous_primitive (hg j k) 0
  have hrep (j) := Novel.SeparableMeetingRepresentationProof.representation Ω mΩ S (drv j)
    (N+1) (fun k => H026 (chi j) (lo026 Td k) (hi026 Td k)) (fun k => g j k T)
    (fun k => G026 (g j k) T) (fun k => G026 (g j k)) (hdom j) (hG j)
  refine ⟨fun j => (hrep j).1, ?_⟩
  have hsq : ∀ᵐ ω ∂S.μ, ∀ (n : ℕ) j (k : Fin (N+1)), IntervalIntegrable
      (fun s => H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2)
        volume 0 (n:ℝ) := by
    simp only [ae_all_iff]
    exact fun n j k =>
      Novel.SeparableMeetingCoefficientsProof.square_integrable S _ (hdom j k) n
  have hall : ∀ᵐ ω ∂S.μ, ∀ j, ∀ t : ℝ≥0,
      S.I (drv j) (sigma026 Td chi g j T) t ω +
        (∫ s in (0:ℝ)..t, ∑ k, g j k T *
          H026 (chi j) (lo026 Td k) (hi026 Td k) (Real.toNNReal s) ω ^ 2 *
            (G026 (g j k) T - G026 (g j k) s)) =
      ∑ k, (g j k T * (S.I (drv j) (H026 (chi j) (lo026 Td k) (hi026 Td k)) t ω -
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

lemma curve : Standalone.SeparableMeetingMarkovRealization.curveStatement := by
  intro Ω mΩ S p d N drv Td hTd chi g f0 Z hchi hg T
  have h := curve_drv S drv Td hTd chi g hchi hg T
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2] with ω hω t
  rw [(lambda p d N f0 g (fun j k => G026 (g j k))).1, add_assoc, hω t]

theorem separableMeetingMarkovRealization : Standalone.SeparableMeetingMarkovRealization.statement :=
  ⟨dim, lambda, curve⟩

end Novel.SeparableMeetingMarkovRealizationProof

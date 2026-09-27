import Standalone.SharefFilipovicPartA
import Novel.SharefFilipovicSplitProof

open Set MeasureTheory
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicSplit
open Standalone.SharefFilipovicPartA
namespace Novel.SharefFilipovicPartAProof
open Novel.SharefFilipovicSplitProof

lemma partA : partAStatement := by
  intro β hβ n₁ n₂ m Z b sZ DS sS t p q htp hpq hDSi hsSi ⟨d₀, d₁, hD⟩ ⟨s₀, s₁, hs⟩ hdisj hax
  classical
  -- the driver groups are separate, so the squared norm splits
  have hsq : ∀ T, ∑ k, (∫ u in t..T, (sS u k + sB034 β sZ t u k)) ^ 2 =
      ∑ k, (∫ u in t..T, sS u k) ^ 2 + ∑ k, (∫ u in t..T, sB034 β sZ t u k) ^ 2 := by
    intro T
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases hdisj k with h | h
    · have e1 : (fun u => sS u k + sB034 β sZ t u k) = fun u => sB034 β sZ t u k := by
        funext u; rw [h u, zero_add]
      have e2 : (fun u => sS u k) = fun _ => (0:ℝ) := funext h
      rw [e1, e2]
      simp
    · have hz : ∀ u, sB034 β sZ t u k = 0 := fun u => by simp [sB034, h]
      have e1 : (fun u => sS u k + sB034 β sZ t u k) = fun u => sS u k := by
        funext u; rw [hz u, add_zero]
      have e2 : (fun u => sB034 β sZ t u k) = fun _ => (0:ℝ) := funext hz
      rw [e1, e2]
      simp
  have hax' : ∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DB034 β Z b t u) =
      (1/2 : ℝ) * (∑ k, (∫ u in t..T, sS u k) ^ 2 + ∑ l, (∫ u in t..T, sB034 β sZ t u l) ^ 2) :=
    fun T hT => by rw [hax T hT, hsq]
  have hres := split β hβ n₁ n₂ m m Z b sZ DS sS t p q htp hpq hDSi hsSi ⟨d₀, d₁, hD⟩
    ⟨s₀, s₁, hs⟩ hax'
  refine ⟨hres, fun T hT => ?_⟩
  have hDSc : ContinuousOn DS (Ioo p q) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.congr fun T hT => hD T hT
  have hsSc : ∀ k, ContinuousOn (fun u => sS u k) (Ioo p q) := fun k =>
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.congr
      fun T hT => hs T hT k
  have hderiv := deriv_identity β Z b sZ DS sS t p q htp hDSi hsSi hDSc hsSc hax' T hT
  have hblock := block_identity (n₁ := n₁) (n₂ := n₂) β sZ t T
  have h0 := hres (T - t)
  simp only [residual034] at h0
  simp only [DB034] at hderiv
  rw [hblock] at hderiv
  have e : ∑ k, sS T k * ∫ u in t..T, sS u k = ∑ k, (∫ u in t..T, sS u k) * sS T k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e]
  linarith

theorem sharefFilipovicPartA : Standalone.SharefFilipovicPartA.statement := partA

end Novel.SharefFilipovicPartAProof

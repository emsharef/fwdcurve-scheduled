import Standalone.CorrelatedFactorsProcess
import Novel.CorrelatedFactorsSignProof
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set
open Standalone.SharefFilipovicResidual Standalone.CorrelatedFactorsReduction
open Standalone.CorrelatedFactorsProcess
namespace Novel.CorrelatedFactorsProcessProof
open Novel.CorrelatedFactorsReductionProof Novel.CorrelatedFactorsSignProof

lemma point : pointStatement := by
  intro β hβ n₁ z hz0 hz1 b a ha hb hres
  have hK0 : ∀ k : Fin (1 + 1), (k : ℕ) ≤ 2 * (1 / 2) → z (Sum.inr k) = 0 →
      b (Sum.inr k) = 0 := fun k hk _ => by
    have : k = 0 := Fin.ext (by simpa using hk)
    rw [this]; exact hb
  obtain ⟨hsupp, -, -, htk⟩ := (reduction β hβ n₁ 1 z b a ha hK0).1 hres
  have h := htk 0 (by simp) hz0
  have htop := SA_top β hβ.ne' 0 (Nat.zero_le _) a (fun i j hij => by
    obtain ⟨μ, ν, h1, h2, h3, h4⟩ := hsupp i j hij
    exact ⟨μ, ν, h1, h2, by omega, by omega⟩)
  have hnn := ha.diag_nonneg (i := Sum.inl 0)
  have h1 := SA_coeff_zero β a hsupp 1 (by norm_num)
  simp only [mul_zero] at htop
  simp only [tk, Fin.val_zero, Nat.cast_zero, zero_add, htop, h1] at h
  have hc : c2 z 1 = z (Sum.inr 1) := by unfold c2; simp
  have e0 : a (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = a (Sum.inl 0) (Sum.inl 0) := rfl
  rw [hc, e0] at h
  have : 0 ≤ β * (a (Sum.inl 0) (Sum.inl 0) * (1 / β) ^ 2) := by
    have := hβ.le; positivity
  linarith

lemma path : pathStatement := by
  intro β hβ n₁ Z a b t₀ δ hδ hcont hneg hae
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hcont (Iio_mem_nhds hneg))
  have hη : t₀ < min (t₀ + δ) u := lt_min (by linarith) hu
  rw [ae_restrict_iff' measurableSet_Ioo] at hae
  have hzero : volume (Ioo t₀ (min (t₀ + δ) u)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with t ht htI
    obtain ⟨h0, ha, hb, hres⟩ := ht ⟨htI.1, htI.2.trans_le (min_le_left _ _)⟩
    exact point β hβ n₁ (Z t) h0 (hsub ⟨htI.1.le, htI.2.trans_le (min_le_right _ _)⟩)
      (b t) (a t) ha hb hres
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  linarith

theorem correlatedFactorsProcess : Standalone.CorrelatedFactorsProcess.statement := ⟨point, path⟩

end Novel.CorrelatedFactorsProcessProof

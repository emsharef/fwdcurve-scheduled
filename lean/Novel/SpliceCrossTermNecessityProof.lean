import Standalone.SpliceCrossTermNecessity
import Novel.SpliceCrossTermDriftProof
import Novel.SpliceCrossTermAnalyticProof

open MeasureTheory Set Filter
open Standalone.SpliceCrossTermDrift Standalone.SpliceCrossTermNecessity
namespace Novel.SpliceCrossTermNecessityProof

/-- At a time `t < τ` where the cross term is `p + g(· − t)`, the coefficient `β` does not jump. -/
lemma beta_eq_at (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a b ρ : ℝ) (ha : a ≠ 0) (m : ℕ) (τ τl τr H : ℝ)
    (hl : τl < τ) (hr : τ < τr) (hH : τ < H)
    (hidxl : ∀ v ∈ Ioo τl τ, idx033 Tm v = m) (hidxr : ∀ v ∈ Ico τ τr, idx033 Tm v = m + 1)
    (t : ℝ) (ht : t ∈ Ico 0 τ)
    (hform : ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
      (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
      ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T = p T + g (T - t)) :
    beta033 a b ρ s m t = beta033 a b ρ s (m + 1) t := by
  obtain ⟨g, hg, p, hp, hX⟩ := hform
  obtain ⟨c1, α1, hc1⟩ := Novel.SpliceCrossTermDriftProof.cross Tm s hs C hC a b ρ ha m t ht.1
  obtain ⟨c2, α2, hc2⟩ :=
    Novel.SpliceCrossTermDriftProof.cross Tm s hs C hC a b ρ ha (m + 1) t ht.1
  obtain ⟨k0, k1, hk⟩ := hp m
  obtain ⟨l0, l1, hl'⟩ := hp (m + 1)
  have hg' : AnalyticOnNhd ℝ (fun T => g (T - t)) univ := fun x _ =>
    AnalyticAt.comp (g := g) (f := fun T => T - t) (hg _ (mem_univ _)) (by fun_prop)
  have h1 : ∀ T ∈ Ioo (max t τl) τ, g (T - t) =
      Real.exp (-a * T) * (α1 + beta033 a b ρ s m t * T) + ((c1 - k0) + (-k1) * T) := by
    intro T hT
    have hTt : T ∈ Ioo t H := ⟨lt_of_le_of_lt (le_max_left _ _) hT.1, hT.2.trans hH⟩
    have hidx : idx033 Tm T = m :=
      hidxl T ⟨lt_of_le_of_lt (le_max_right _ _) hT.1, hT.2⟩
    have e1 := hX T hTt
    have e2 := hc1 T hidx hTt.1.le
    have e3 := hk T hTt hidx
    linear_combination e2 - e1 - e3
  have h2 : ∀ T ∈ Ioo τ (min τr H), g (T - t) =
      Real.exp (-a * T) * (α2 + beta033 a b ρ s (m + 1) t * T) + ((c2 - l0) + (-l1) * T) := by
    intro T hT
    have hTt : T ∈ Ioo t H := ⟨ht.2.trans hT.1, lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
    have hidx : idx033 Tm T = m + 1 :=
      hidxr T ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
    have e1 := hX T hTt
    have e2 := hc2 T hidx hTt.1.le
    have e3 := hl' T hTt hidx
    linear_combination e2 - e1 - e3
  exact (Novel.SpliceCrossTermAnalyticProof.match_coef a ha _ hg' _ _ _ _
    (max_lt ht.2 hl) (lt_min hr hH) _ _ _ _ _ _ _ _ h1 h2).2

lemma necessity : necessityStatement := by
  intro Tm s hs C hC a b ρ ha hb m τ τl τr H hτ0 hl hr hH hidxl hidxr hcons
  have hβ : ∀ t ∈ Ico 0 τ, beta033 a b ρ s m t = beta033 a b ρ s (m + 1) t := fun t ht =>
    beta_eq_at Tm s hs C hC a b ρ ha m τ τl τr H hl hr hH hidxl hidxr t ht (hcons t ht)
  -- the jump of `β` vanishes before `τ`
  have hint : ∀ t ∈ Ico 0 τ,
      ∫ u in (0:ℝ)..t, Real.exp (a * u) * (ρ * b * (s (m + 1) u - s m u)) = 0 := by
    intro t ht
    have hj := Novel.SpliceCrossTermDriftProof.jump s hs C hC a b ρ m t
    rw [← hβ t ht, sub_self] at hj
    rw [show (fun u => Real.exp (a * u) * (ρ * b * (s (m + 1) u - s m u))) =
      fun u => ρ * b * (Real.exp (a * u) * (s (m + 1) u - s m u)) from by funext u; ring,
      intervalIntegral.integral_const_mul]
    exact hj.symm
  have hloc : LocallyIntegrable (fun u => ρ * b * (s (m + 1) u - s m u)) volume := by
    refine (locallyIntegrable_const (|ρ * b| * (C + C))).mono
      (((hs (m + 1)).sub (hs m)).const_mul _).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (by linarith) : 0 ≤ |ρ * b| * (C + C))]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hC _ _) (hC _ _)))
      (abs_nonneg _)
  filter_upwards [Novel.SpliceCrossTermAnalyticProof.lebesgue a τ _ hloc hint] with u hu hmem
  have h := hu hmem
  have : ρ * (s (m + 1) u - s m u) * b = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_right hb

theorem spliceCrossTermNecessity : Standalone.SpliceCrossTermNecessity.statement := necessity

end Novel.SpliceCrossTermNecessityProof

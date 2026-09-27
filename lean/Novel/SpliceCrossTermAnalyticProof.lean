import Standalone.SpliceCrossTermAnalytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter Topology
open Standalone.SpliceCrossTermAnalytic
namespace Novel.SpliceCrossTermAnalyticProof

/-- Two functions that agree on an open interval have the same derivative there. -/
lemma deriv_agree {f g : ℝ → ℝ} {f' g' : ℝ → ℝ} {c d : ℝ}
    (hf : ∀ T, HasDerivAt f (f' T) T) (hg : ∀ T, HasDerivAt g (g' T) T)
    (hfg : ∀ T ∈ Ioo c d, f T = g T) : ∀ T ∈ Ioo c d, f' T = g' T := by
  intro T hT
  have hev : f =ᶠ[𝓝 T] g := by
    filter_upwards [Ioo_mem_nhds hT.1 hT.2] with x hx
    exact hfg x hx
  exact (hf T).unique ((hg T).congr_of_eventuallyEq hev)

lemma hasDerivAt_expaff (a α β T : ℝ) :
    HasDerivAt (fun T => Real.exp (-a * T) * (α + β * T))
      (Real.exp (-a * T) * (β - a * (α + β * T))) T := by
  have h1 : HasDerivAt (fun T => Real.exp (-a * T)) (Real.exp (-a * T) * (-a)) T := by
    have := ((hasDerivAt_id T).const_mul (-a)).exp
    convert this using 1 <;> simp
  have h2 : HasDerivAt (fun T => α + β * T) β T := by
    simpa using ((hasDerivAt_id T).const_mul β).const_add α
  convert h1.mul h2 using 1
  ring

lemma affine : affineStatement := by
  intro a ha c d hcd α β k₀ k₁ h
  -- first derivative
  have h1 := deriv_agree (fun T => hasDerivAt_expaff a α β T)
    (fun T => ((hasDerivAt_id T).const_mul k₁).const_add k₀) h
  simp only [mul_one] at h1
  -- second derivative
  have h2 := deriv_agree (f' := fun T => Real.exp (-a * T) * ((-a * β) - a * ((β - a * α) + (-a * β) * T)))
    (fun T => by
      have := hasDerivAt_expaff a (β - a * α) (-a * β) T
      convert this using 2 <;> ring_nf)
    (fun T => hasDerivAt_const T k₁) (fun T hT => by rw [← h1 T hT]; ring_nf)
  have key : ∀ T ∈ Ioo c d, a ^ 2 * α - 2 * a * β + a ^ 2 * β * T = 0 := by
    intro T hT
    have := h2 T hT
    have hexp : Real.exp (-a * T) ≠ 0 := (Real.exp_pos _).ne'
    have : Real.exp (-a * T) * (a ^ 2 * α - 2 * a * β + a ^ 2 * β * T) = 0 := by
      rw [← this]; ring
    exact (mul_eq_zero.1 this).resolve_left hexp
  have hT1 : (2 * c + d) / 3 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hT2 : (c + 2 * d) / 3 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have e1 := key _ hT1
  have e2 := key _ hT2
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hβ : β = 0 := by
    have : a ^ 2 * β * ((d - c) / 3) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.1 this with h | h
    · exact (mul_eq_zero.1 h).resolve_left ha2
    · exact absurd h (by linarith)
  refine ⟨?_, hβ⟩
  subst hβ
  have : a ^ 2 * α = 0 := by linear_combination e1
  exact (mul_eq_zero.1 this).resolve_left ha2

lemma analytic_expaff (a α β k₀ k₁ : ℝ) :
    AnalyticOnNhd ℝ (fun T => Real.exp (-a * T) * (α + β * T) + (k₀ + k₁ * T)) univ := by
  intro x _
  have he : AnalyticAt ℝ (fun T => Real.exp (-a * T)) x :=
    (analyticOnNhd_rexp (-a * x) (mem_univ _)).comp (by fun_prop)
  exact (he.mul (by fun_prop)).add (by fun_prop)

lemma match_coef : matchStatement := by
  intro a ha g hg c₁ d₁ c₂ d₂ h₁ h₂ α₁ β₁ α₂ β₂ k₀ k₁ l₀ l₁ hg₁ hg₂
  have hmid : (c₁ + d₁) / 2 ∈ Ioo c₁ d₁ := ⟨by linarith, by linarith⟩
  have hev : g =ᶠ[𝓝 ((c₁ + d₁) / 2)]
      fun T => Real.exp (-a * T) * (α₁ + β₁ * T) + (k₀ + k₁ * T) := by
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with x hx
    exact hg₁ x hx
  have hall := hg.eqOn_of_preconnected_of_eventuallyEq (analytic_expaff a α₁ β₁ k₀ k₁)
    isPreconnected_univ (mem_univ _) hev
  have h := affine a ha c₂ d₂ h₂ (α₁ - α₂) (β₁ - β₂) (l₀ - k₀) (l₁ - k₁) (fun T hT => by
    have e1 := hall (mem_univ T)
    have e2 := hg₂ T hT
    simp only at e1
    linear_combination e2 - e1)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma lebesgue : lebesgueStatement := by
  intro a L Δ hΔ h0
  have hf : LocallyIntegrable (fun u => Real.exp (a * u) * Δ u) volume :=
    hΔ.continuous_mul (by fun_prop)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf, Measure.ae_ne volume 0]
    with x hx hx0 hmem
  have hpos : 0 < x := lt_of_le_of_ne hmem.1 (Ne.symm hx0)
  have hev : (fun y => ∫ u in (0:ℝ)..y, Real.exp (a * u) * Δ u) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hpos hmem.2] with y hy
    exact h0 y ⟨hy.1.le, hy.2⟩
  have hd := (hx 0).unique ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev)
  exact (mul_eq_zero.1 hd).resolve_left (Real.exp_pos _).ne'

lemma open_set : openStatement := by
  intro a L Δ hΔ hne
  have hf : LocallyIntegrable (fun u => Real.exp (a * u) * Δ u) volume :=
    hΔ.continuous_mul (by fun_prop)
  have hφ : Continuous fun t => ∫ u in (0:ℝ)..t, Real.exp (a * u) * Δ u :=
    intervalIntegral.continuous_primitive (fun x y => intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
  refine ⟨isOpen_Ioo.inter (isOpen_ne_fun hφ continuous_const), ?_⟩
  by_contra hN
  apply hne
  apply lebesgue a L Δ hΔ
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0; simp
  · by_contra hφt
    exact hN ⟨t, ⟨hpos, ht.2⟩, hφt⟩

theorem spliceCrossTermAnalytic : Standalone.SpliceCrossTermAnalytic.statement := ⟨affine, match_coef, lebesgue, open_set⟩

end Novel.SpliceCrossTermAnalyticProof

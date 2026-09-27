import Standalone.SpliceCrossTermConsistency
import Novel.SpliceCrossTermCurveProof
import Novel.SpliceCrossTermNecessityProof
import Novel.SpliceCrossTermOpenProof

open MeasureTheory Set Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency
namespace Novel.SpliceCrossTermConsistencyProof

/-- The maturity interval is constant just to the right of every point. -/
lemma idx_right (Tm : Finset ℝ) (T : ℝ) :
    ∃ ε > 0, ∀ T' ∈ Ico T (T + ε), idx033 Tm T' = idx033 Tm T := by
  classical
  have key : ∀ ε > 0, (∀ τ ∈ Tm, T < τ → T + ε ≤ τ) →
      ∃ ε > 0, ∀ T' ∈ Ico T (T + ε), idx033 Tm T' = idx033 Tm T := by
    intro ε hε h
    refine ⟨ε, hε, fun T' hT' => ?_⟩
    unfold idx033
    congr 1
    refine Finset.filter_congr fun τ hτ => ⟨fun h1 => ?_, fun h1 => h1.trans hT'.1⟩
    by_contra h2
    have := h τ hτ (lt_of_not_ge h2)
    linarith [hT'.2]
  by_cases hne : (Tm.filter fun τ => T < τ).Nonempty
  · refine key ((Tm.filter fun τ => T < τ).min' hne - T) ?_ fun τ hτ hTτ => ?_
    · have := (Finset.mem_filter.1 ((Tm.filter fun τ => T < τ).min'_mem hne)).2
      linarith
    · have := (Tm.filter fun τ => T < τ).min'_le τ (Finset.mem_filter.2 ⟨hτ, hTτ⟩)
      linarith
  · refine key 1 one_pos fun τ hτ hTτ => absurd ⟨τ, Finset.mem_filter.2 ⟨hτ, hTτ⟩⟩ hne

/-- Just to the left of a meeting the maturity interval is the one before. -/
lemma idx_left (Tm : Finset ℝ) (τ : ℝ) (hτ : τ ∈ Tm) :
    1 ≤ idx033 Tm τ ∧ ∃ τl < τ, ∀ v ∈ Ioo τl τ, idx033 Tm v = idx033 Tm τ - 1 := by
  classical
  have hmem : τ ∈ Tm.filter fun x => x ≤ τ := Finset.mem_filter.2 ⟨hτ, le_rfl⟩
  refine ⟨Finset.card_pos.2 ⟨τ, hmem⟩, ?_⟩
  have key : ∀ τl < τ, (∀ x ∈ Tm, x < τ → x ≤ τl) →
      ∃ τl < τ, ∀ v ∈ Ioo τl τ, idx033 Tm v = idx033 Tm τ - 1 := by
    intro τl hl h
    refine ⟨τl, hl, fun v hv => ?_⟩
    unfold idx033
    rw [← Finset.card_erase_of_mem hmem]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxv⟩
      exact ⟨by rintro rfl; linarith [hv.2], hx, by linarith [hv.2]⟩
    · rintro ⟨hne, hx, hxτ⟩
      exact ⟨hx, (h x hx (lt_of_le_of_ne hxτ hne)).trans hv.1.le⟩
  by_cases hne : (Tm.filter fun x => x < τ).Nonempty
  · exact key _ (Finset.mem_filter.1 ((Tm.filter fun x => x < τ).max'_mem hne)).2
      fun x hx hxτ => (Tm.filter fun x => x < τ).le_max' x (Finset.mem_filter.2 ⟨hx, hxτ⟩)
  · exact key (τ - 1) (by linarith) fun x hx hxτ =>
      absurd ⟨x, Finset.mem_filter.2 ⟨hx, hxτ⟩⟩ hne

/-- A continuous function vanishing at the rationals just to the right of `T` vanishes at `T`. -/
lemma zero_of_rat (ψ : ℝ → ℝ) (hψ : Continuous ψ) (T ε : ℝ) (hε : 0 < ε)
    (h : ∀ q : ℚ, (q : ℝ) ∈ Ioo T (T + ε) → ψ q = 0) : ψ T = 0 := by
  by_contra hne
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hψ.continuousAt (|ψ T|) (abs_pos.2 hne)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right T (lt_min hδ hε))
  have hq := h q ⟨hq1, by linarith [min_le_right δ ε]⟩
  have hd : dist (q : ℝ) T < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left δ ε]
  have := hball hd
  rw [hq, Real.dist_eq, zero_sub, abs_neg] at this
  exact lt_irrefl _ this

/-- The time integral of the drift (33.1) splits into its three parts. -/
lemma alpha_split (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a b ρ t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ u in (0:ℝ)..t, alpha033 a b ρ s Tm u T =
      (∫ u in (0:ℝ)..t, sigS033 s Tm u T * SS033 s Tm u T) +
      (∫ u in (0:ℝ)..t, b * Real.exp (-a * (T - u)) * (b * (1 - Real.exp (-a * (T - u))) / a)) +
      ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T := by
  obtain ⟨G, hGm, hG⟩ := Novel.SpliceCrossTermDriftProof.SS_measurable s hs Tm T
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  set j := idx033 Tm T
  have hGb : ∀ u ∈ uIcc 0 t, |G u| ≤ C * T := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    rw [← hG u (hu.2.trans htT), SS033]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := T) (C := C)
      (f := fun v => sigS033 s Tm u v) (fun v _ => by rw [Real.norm_eq_abs]; exact hC _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ T - u)] at hb
    nlinarith [hu.1]
  have hGi : IntervalIntegrable G volume 0 t :=
    Novel.SpliceCrossTermCurveProof.ii_on hGm (C * T) hGb
  have hsj : IntervalIntegrable (s j) volume 0 t :=
    Novel.SpliceCrossTermDriftProof.ii_bdd (hs j) C (hC j) 0 t
  have hEq : ∀ u ∈ uIoc 0 t, G u = SS033 s Tm u T := fun u hu => by
    rw [uIoc_of_le ht] at hu
    exact (hG u (hu.2.trans htT)).symm
  have i1 : IntervalIntegrable (fun u => sigS033 s Tm u T * SS033 s Tm u T) volume 0 t := by
    refine (Novel.SpliceCrossTermCurveProof.ii_on ((hs j).mul hGm) (C * (C * T))
      fun u hu => ?_).congr fun u hu => ?_
    · show |s j u * G u| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hC _ _) (hGb u hu) (abs_nonneg _) hC0
    · show s j u * G u = sigS033 s Tm u T * SS033 s Tm u T
      rw [hEq u hu]; rfl
  have i2 : IntervalIntegrable (fun u => b * Real.exp (-a * (T - u)) *
      (b * (1 - Real.exp (-a * (T - u))) / a)) volume 0 t :=
    (by fun_prop : Continuous fun u => b * Real.exp (-a * (T - u)) *
      (b * (1 - Real.exp (-a * (T - u))) / a)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun u => cross033 a b ρ s Tm u T) volume 0 t := by
    have h1 := hsj.continuousOn_mul (g := fun u => b * (1 - Real.exp (-a * (T - u))) / a)
      (by fun_prop)
    have h2 := hGi.continuousOn_mul (g := fun u => b * Real.exp (-a * (T - u))) (by fun_prop)
    refine ((h1.add h2).const_mul ρ).congr fun u hu => ?_
    show ρ * (b * (1 - Real.exp (-a * (T - u))) / a * s j u + b * Real.exp (-a * (T - u)) * G u) =
      cross033 a b ρ s Tm u T
    rw [cross033, ← hEq u hu]
    show _ = ρ * (s j u * _ + _)
    ring
  unfold alpha033
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]

/-- A version agrees with the curve at every rational maturity, almost surely. -/
lemma version_rat {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ → ℝ)
    (F : ℝ → Ω → ℝ) (t H : ℝ) (hv : ∀ T ∈ Icc t H, ∀ᵐ ω ∂μ, g ω T = F T ω) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, (q : ℝ) ∈ Icc t H → g ω q = F q ω :=
  ae_all_iff.2 fun q => by
    by_cases hq : (q : ℝ) ∈ Icc t H
    · filter_upwards [hv q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq

/-- The version of the random part holds at every rational maturity on one event. -/
lemma good {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a b ρ : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, ∀ q : ℚ,
      S.I k₁ (fun u _ => sigS033 s Tm u q + ρ * (b * Real.exp (-a * (q - u)))) t ω +
        S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * (b * Real.exp (-a * (q - u)))) t ω =
      S.I k₁ (fun u _ => s (idx033 Tm q) u) t ω + Real.exp (-a * q) *
        (ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
          Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω) :=
  ae_all_iff.2 fun q =>
    Novel.SpliceCrossTermCurveProof.random Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ q t

/-- The pathwise form of the cross term at `t`, from agreement of an element of `𝓕_t(E)` with
the curve at the rational maturities, on the event of `good`. -/
lemma form_of_rat {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a b ρ H : ℝ) (ha : a ≠ 0) (f0 : ℝ → ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) (hE : Block033 a E) (hf0 : Fam033 Tm H E 0 f0) (t : ℝ≥0) (ω : Ω)
    (hrand : ∀ q : ℚ,
      S.I k₁ (fun u _ => sigS033 s Tm u q + ρ * (b * Real.exp (-a * (q - u)))) t ω +
        S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * (b * Real.exp (-a * (q - u)))) t ω =
      S.I k₁ (fun u _ => s (idx033 Tm q) u) t ω + Real.exp (-a * q) *
        (ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
          Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω))
    (h : ℝ → ℝ) (hh : Fam033 Tm H E t h)
    (hag : ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H → h q = curve033 S k₁ k₂ f0 a b ρ s Tm t q ω) :
    ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
      (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo (t : ℝ) H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
      ∀ T ∈ Ioo (t : ℝ) H, ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T = p T + g (T - t) := by
  obtain ⟨ph, hph, gh, hgh, hh⟩ := hh
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  obtain ⟨γ₁, γ₂, hγ⟩ := Novel.SpliceCrossTermCurveProof.block a b t ha
  let G : ℝ → ℝ := fun x => gh x - g0 (x + t) - γ₁ * Real.exp (-a * (x + t)) -
    γ₂ * Real.exp (-2 * a * (x + t)) - Real.exp (-a * (x + t)) *
      (ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
        Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω)
  have hGa : AnalyticOnNhd ℝ G univ := by
    intro x _
    have e1 : ∀ c : ℝ, AnalyticAt ℝ (fun x : ℝ => Real.exp (c * (x + t))) x := fun c =>
      (analyticOnNhd_rexp _ (mem_univ _)).comp (by fun_prop)
    have g0a : AnalyticAt ℝ (fun x => g0 (x + t)) x :=
      (hE.analytic g0 hg0 _ (mem_univ _)).comp (by fun_prop)
    exact ((((hE.analytic gh hgh x (mem_univ _)).sub g0a).sub
      (analyticAt_const.mul (e1 (-a)))).sub (analyticAt_const.mul (e1 (-2 * a)))).sub
      ((e1 (-a)).mul analyticAt_const)
  have hGc : Continuous G := continuousOn_univ.1 hGa.continuousOn
  refine ⟨G, hGa, fun T => (∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T) - G (T - t),
    fun j => ?_, fun T _ => by ring⟩
  obtain ⟨κ₀, κ₁, hk⟩ := hph j
  obtain ⟨l₀, l₁, hl⟩ := hp0 j
  obtain ⟨c₀, c₁, hc⟩ := Novel.SpliceCrossTermCurveProof.step Tm s hs C hC j t t.2
  obtain ⟨d₀, α, hd⟩ := Novel.SpliceCrossTermDriftProof.cross Tm s hs C hC a b ρ ha j t t.2
  refine ⟨κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω, κ₁ - l₁ - c₁, fun T hT hTj => ?_⟩
  -- at the rational maturities of the interval
  have hrat : ∀ q : ℚ, (q : ℝ) ∈ Ioo (t : ℝ) H → idx033 Tm q = j →
      (∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u q) - G (q - t) =
        (κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω) + (κ₁ - l₁ - c₁) * q := by
    intro q hq hqj
    have hq0 : (0:ℝ) ≤ q := t.2.trans hq.1.le
    have e := hag q (Ioo_subset_Icc_self hq)
    have er := hrand q
    rw [hqj] at er
    rw [hh q (Ioo_subset_Icc_self hq), curve033, alpha_split Tm s hs C hC a b ρ t q t.2 hq.1.le,
      hγ q, hc q hqj hq.1.le, hf0 q ⟨hq0, hq.2.le⟩, hk q ⟨hq0, hq.2.le⟩ hqj,
      hl q ⟨hq0, hq.2.le⟩ hqj] at e
    simp only [G, sub_add_cancel]
    simp only [sub_zero] at e
    linear_combination -e - er
  -- extend to the whole interval by continuity
  obtain ⟨ε, hε, hε'⟩ := idx_right Tm T
  let ψ : ℝ → ℝ := fun T' => (d₀ + Real.exp (-a * T') * (α + beta033 a b ρ s j t * T')) -
    G (T' - t) - ((κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω) + (κ₁ - l₁ - c₁) * T')
  have hψc : Continuous ψ := by
    have := hGc.comp (continuous_id.sub continuous_const : Continuous fun T' : ℝ => T' - t)
    simp only [ψ]
    fun_prop
  have hψ : ψ T = 0 := by
    refine zero_of_rat ψ hψc T (min ε (H - T)) (lt_min hε (sub_pos.2 hT.2)) fun q hq => ?_
    have hqI : (q : ℝ) ∈ Ioo (t : ℝ) H :=
      ⟨hT.1.trans hq.1, by linarith [hq.2, min_le_right ε (H - T)]⟩
    have hqj : idx033 Tm q = j := by
      rw [hε' q ⟨hq.1.le, by linarith [hq.2, min_le_left ε (H - T)]⟩, hTj]
    have := hrat q hqI hqj
    rw [hd q hqj hqI.1.le] at this
    simp only [ψ]
    linarith
  show (∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T) - G (T - t) = _
  rw [hd T hTj hT.1.le]
  simp only [ψ] at hψ
  linarith

lemma necessity : necessityStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ H ha hb hTm f0 E hE hcons τ hτ
  obtain ⟨hf0, hver⟩ := hcons
  have := S.isProbabilityMeasure
  obtain ⟨h1, τl, hl, hidxl⟩ := idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := idx_right Tm τ
  have hm : idx033 Tm τ - 1 + 1 = idx033 Tm τ := by omega
  have hN := Novel.SpliceCrossTermNecessityProof.necessity Tm s hs C hC a b ρ ha hb
    (idx033 Tm τ - 1) τ τl (τ + ε) H (hTm τ hτ).1.le hl (by linarith) (hTm τ hτ).2 hidxl
    (fun v hv => by rw [hm]; exact hidxr v hv) (fun t ht => by
      let t' : ℝ≥0 := ⟨t, ht.1⟩
      obtain ⟨g, hgF, -, hgv⟩ := hver t' (by show t ≤ H; linarith [ht.2, (hTm τ hτ).2])
      obtain ⟨ω, hω1, hω2⟩ := ((version_rat S.μ g
        (fun T ω => curve033 S k₁ k₂ f0 a b ρ s Tm t' T ω) t' H hgv).and
        (good S k₁ k₂ Tm s hs C hC a b ρ t')).exists
      exact form_of_rat S k₁ k₂ Tm s hs C hC a b ρ H ha f0 E hE hf0 t' ω hω2 (g ω) (hgF ω) hω1)
  filter_upwards [hN] with u hu hu'
  have := hu hu'
  rw [hm] at this
  exact this

lemma noThirdWay : noThirdWayStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ H ha hb hTm f0 E hE hf0 τ hτ hne
  have := S.isProbabilityMeasure
  obtain ⟨h1, τl, hl, hidxl⟩ := idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := idx_right Tm τ
  have hm : idx033 Tm τ - 1 + 1 = idx033 Tm τ := by omega
  have hne' : ¬ ∀ᵐ u ∂volume, u ∈ Ico 0 τ →
      ρ * (s (idx033 Tm τ - 1 + 1) u - s (idx033 Tm τ - 1) u) = 0 := by
    rw [hm]; exact hne
  obtain ⟨O, hO, hOne, hOsub, hOnot⟩ := Novel.SpliceCrossTermOpenProof.open_times Tm s hs C hC
    a b ρ ha hb (idx033 Tm τ - 1) τ τl (τ + ε) H hl (by linarith) (hTm τ hτ).2 hidxl
    (fun v hv => by rw [hm]; exact hidxr v hv) hne'
  have key : ∀ t : ℝ≥0, (t : ℝ) ∈ O →
      (∀ᵐ ω ∂S.μ, ¬ ∃ h : ℝ → ℝ, Fam033 Tm H E t h ∧
        ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H → h q = curve033 S k₁ k₂ f0 a b ρ s Tm t q ω) ∧
      ¬ HasVersion033 S k₁ k₂ f0 a b ρ s Tm H E t := by
    intro t ht
    have hae : ∀ᵐ ω ∂S.μ, ¬ ∃ h : ℝ → ℝ, Fam033 Tm H E t h ∧
        ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H → h q = curve033 S k₁ k₂ f0 a b ρ s Tm t q ω := by
      filter_upwards [good S k₁ k₂ Tm s hs C hC a b ρ t] with ω hω
      rintro ⟨h, hh, hag⟩
      exact hOnot t ht (form_of_rat S k₁ k₂ Tm s hs C hC a b ρ H ha f0 E hE hf0 t ω hω h hh hag)
    refine ⟨hae, ?_⟩
    rintro ⟨g, hgF, -, hgv⟩
    obtain ⟨ω, hω1, hω2⟩ := ((version_rat S.μ g
      (fun T ω => curve033 S k₁ k₂ f0 a b ρ s Tm t T ω) t H hgv).and hae).exists
    exact hω2 ⟨g ω, hgF ω, hω1⟩
  refine ⟨?_, O, hO, hOne, hOsub, key⟩
  rintro ⟨-, hver⟩
  obtain ⟨t, ht⟩ := hOne
  have ht0 : 0 ≤ t := (hOsub ht).1.le
  exact (key ⟨t, ht0⟩ ht).2 (hver ⟨t, ht0⟩ (by show t ≤ H; linarith [(hOsub ht).2, (hTm τ hτ).2]))

theorem spliceCrossTermConsistency : Standalone.SpliceCrossTermConsistency.statement := ⟨necessity, noThirdWay⟩

end Novel.SpliceCrossTermConsistencyProof

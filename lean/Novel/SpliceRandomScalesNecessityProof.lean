import Standalone.SpliceRandomScalesNecessity
import Novel.SpliceRandomScalesPathProof
import Novel.SpliceRandomScalesCurveProof
import Novel.SpliceQuasiExponentialConsistencyProof

open Matrix NormedSpace MeasureTheory Set Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermAlpha Standalone.SpliceCrossTermConsistency
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceQuasiExponentialBlock
open Standalone.SpliceQuasiExponentialConsistency Standalone.SpliceRandomScalesPath
open Standalone.SpliceRandomScalesCurve Standalone.SpliceRandomScalesNecessity
namespace Novel.SpliceRandomScalesNecessityProof
open Novel.SpliceQuasiExponentialConsistencyProof

variable {r : ℕ}

/-- The scales on each path. -/
lemma path_scales {Ω : Type} [MeasurableSpace Ω] {S : ItoCalculus Ω} {s : ℕ → ℝ → Ω → ℝ}
    {ρ ψ : ℝ → Ω → ℝ} {C : ℝ} (h : Scales039 S s ρ ψ C) (ω : Ω) :
    PathScales (fun u => ρ u ω) (fun u => ψ u ω) (fun j u => s j u ω) := by
  obtain ⟨-, -, -, hs, hρ, hψ, hsC, hρC, hψC⟩ := h
  refine ⟨fun j => hs j ω, hρ ω, hψ ω, max C 1, fun i u => (hsC i u ω).trans (le_max_left _ _),
    fun u => (hρC u ω).trans (le_max_right _ _), fun u => (hψC u ω).trans (le_max_left _ _)⟩

/-- `σ^S S^S` and the cross part are interval integrable, for measurable bounded scales. -/
lemma ii_parts (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (ρ t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun u => sigS033 s Tm u T * SS033 s Tm u T) volume 0 t ∧
    IntervalIntegrable (fun u => cross035 ρ s Tm c A b u T) volume 0 t := by
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
  have hlc : Continuous fun u => lam035 c A b (T - u) :=
    (cont_of_analytic (lam_analytic c A b)).comp (continuous_const.sub continuous_id)
  have hLc : Continuous fun u => Lam035 c A b (T - u) :=
    (cont_of_analytic (Lam_analytic c A b)).comp (continuous_const.sub continuous_id)
  refine ⟨?_, ?_⟩
  · refine (Novel.SpliceCrossTermCurveProof.ii_on ((hs j).mul hGm) (C * (C * T))
      fun u hu => ?_).congr fun u hu => ?_
    · show |s j u * G u| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hC _ _) (hGb u hu) (abs_nonneg _) hC0
    · show s j u * G u = sigS033 s Tm u T * SS033 s Tm u T
      rw [hEq u hu]; rfl
  · have h1 := hsj.continuousOn_mul (g := fun u => Lam035 c A b (T - u)) hLc.continuousOn
    have h2 := hGi.continuousOn_mul (g := fun u => lam035 c A b (T - u)) hlc.continuousOn
    refine ((h1.add h2).const_mul ρ).congr fun u hu => ?_
    show ρ * (Lam035 c A b (T - u) * s j u + lam035 c A b (T - u) * G u) =
      cross035 ρ s Tm c A b u T
    rw [cross035, ← hEq u hu]
    show _ = ρ * (s j u * _ + _)
    ring

/-- The time integral of the drift splits into its three parts, on one path. -/
lemma alpha_split039 (ρ ψ : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (h : PathScales ρ ψ s) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t T : ℝ) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    ∫ u in (0:ℝ)..t, alpha039 ρ ψ s Tm c A b u T =
      (∫ u in (0:ℝ)..t, sigS033 s Tm u T * SS033 s Tm u T) +
      (∫ u in (0:ℝ)..t, ψ u ^ 2 * (lam035 c A b (T - u) * Lam035 c A b (T - u))) +
      ∫ u in (0:ℝ)..t, cross039 ρ ψ s Tm c A b u T := by
  have h' := h
  obtain ⟨hs, -, hψ, C, hsC, -, hψC⟩ := h
  obtain ⟨hwm, Cw, hwC⟩ := Novel.SpliceRandomScalesPathProof.wS_bounded h'
  have i1 := (ii_parts Tm s hs C hsC c A b 0 t T ht htT).1
  have i3 : IntervalIntegrable (fun u => cross039 ρ ψ s Tm c A b u T) volume 0 t :=
    ((ii_parts Tm (wS ρ ψ s) hwm Cw hwC c A b 1 t T ht htT).2).congr fun u _ =>
      (Novel.SpliceRandomScalesPathProof.cross ρ ψ s Tm r c A b u T).symm
  have hlL : Continuous fun u => lam035 c A b (T - u) * Lam035 c A b (T - u) :=
    ((cont_of_analytic (lam_analytic c A b)).comp (continuous_const.sub continuous_id)).mul
      ((cont_of_analytic (Lam_analytic c A b)).comp (continuous_const.sub continuous_id))
  have i2 : IntervalIntegrable
      (fun u => ψ u ^ 2 * (lam035 c A b (T - u) * Lam035 c A b (T - u))) volume 0 t :=
    (Novel.SpliceCrossTermDriftProof.ii_bdd (hψ.pow_const 2) (C ^ 2) (fun u => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hψC u) 2) 0 t).mul_continuousOn
      hlL.continuousOn
  unfold alpha039
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]

/-- The version of the random part holds at every rational maturity on one event. -/
lemma good039 {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, ∀ q : ℚ,
      S.I k₁ (fun u ω => s (idx033 Tm q) u ω + ρ u ω * ψ u ω * lam035 c A b (q - u)) t ω +
        S.I k₂ (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * lam035 c A b (q - u)) t ω =
      S.I k₁ (fun u ω => s (idx033 Tm q) u ω) t ω +
        c ⬝ᵥ (exp ((q : ℝ) • A) *ᵥ Yv039 S k₁ k₂ ρ ψ A b t ω) :=
  ae_all_iff.2 fun q =>
    Novel.SpliceRandomScalesCurveProof.random Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c q t

/-- On a good path, agreement of an element of `𝓕_t(E)` with the curve at the rational maturities
puts the cross term in the form `p + g(· − t)`, `p` piecewise affine and `g` analytic. -/
lemma form_of_rat039 {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det)
    (b : Fin r → ℝ) (H : ℝ) (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E)
    (hf0 : Fam033 Tm H E 0 f0) (t : ℝ≥0) (ω : Ω)
    (hrand : ∀ q : ℚ,
      S.I k₁ (fun u ω => s (idx033 Tm q) u ω + ρ u ω * ψ u ω * lam035 c A b (q - u)) t ω +
        S.I k₂ (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω * lam035 c A b (q - u)) t ω =
      S.I k₁ (fun u ω => s (idx033 Tm q) u ω) t ω +
        c ⬝ᵥ (exp ((q : ℝ) • A) *ᵥ Yv039 S k₁ k₂ ρ ψ A b t ω))
    (h : ℝ → ℝ) (hh : Fam033 Tm H E t h)
    (hag : ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H →
      h q = curve039 S k₁ k₂ f0 ρ ψ s Tm c A b t q ω) :
    ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
      (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo (t : ℝ) H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
      ∀ T ∈ Ioo (t : ℝ) H, ∫ u in (0:ℝ)..t,
        cross039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm c A b u T =
          p T + g (T - t) := by
  have := hE.finiteDimensional
  set ρω : ℝ → ℝ := fun v => ρ v ω
  set ψω : ℝ → ℝ := fun v => ψ v ω
  set sω : ℕ → ℝ → ℝ := fun j v => s j v ω
  have hP : PathScales ρω ψω sω := path_scales hsc ω
  obtain ⟨hs, -, hψm, C', hsC, -, hψC⟩ := hP
  have hcont : ∀ g ∈ E, Continuous g := fun g hg => cont_of_analytic (hE.analytic g hg)
  obtain ⟨ph, hph, gh, hgh, hh⟩ := hh
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  set Y := Yv039 S k₁ k₂ ρ ψ A b t ω
  let Gb : ℝ → ℝ := fun x => ∫ u in (0:ℝ)..t, (fun u => ψω u ^ 2) u *
    (fun x => lam035 c A b x * Lam035 c A b x) (x + (t - u))
  have hGbE : Gb ∈ E := Novel.SpliceQuasiExponentialBlockProof.int_mem E hcont
    (fun g hg h hh => hE.shift g hg h hh) _ hE.lamLam_mem (fun u => ψω u ^ 2) t t.2
    (Novel.SpliceCrossTermDriftProof.ii_bdd (hψm.pow_const 2) (C' ^ 2) (fun u => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hψC u) 2) 0 t)
  have hbl : ∀ T : ℝ, Gb (T - t) =
      ∫ u in (0:ℝ)..t, ψω u ^ 2 * (lam035 c A b (T - u) * Lam035 c A b (T - u)) :=
    fun T => intervalIntegral.integral_congr fun u _ => by
      simp only
      rw [show (T : ℝ) - t + (t - u) = T - u by ring]
  let G : ℝ → ℝ := fun x => gh x - g0 (x + t) - Gb x -
    c ⬝ᵥ (exp (x • A) *ᵥ (exp ((t : ℝ) • A) *ᵥ Y))
  have hGa : AnalyticOnNhd ℝ G univ := by
    intro x _
    have g0a : AnalyticAt ℝ (fun x => g0 (x + t)) x :=
      (hE.analytic g0 hg0 _ (mem_univ _)).comp (by fun_prop)
    exact (((hE.analytic gh hgh x (mem_univ _)).sub g0a).sub
      (hE.analytic Gb hGbE x (mem_univ _))).sub
      (Novel.SpliceQuasiExponentialKeyProof.analytic_g A c _ x (mem_univ _))
  have hGc : Continuous G := cont_of_analytic hGa
  refine ⟨G, hGa, fun T => (∫ u in (0:ℝ)..t, cross039 ρω ψω sω Tm c A b u T) - G (T - t),
    fun j => ?_, fun T _ => by ring⟩
  obtain ⟨κ₀, κ₁, hk⟩ := hph j
  obtain ⟨l₀, l₁, hl⟩ := hp0 j
  obtain ⟨c₀, c₁, hc⟩ := Novel.SpliceCrossTermCurveProof.step Tm sω hs C' hsC j t t.2
  refine ⟨κ₀ - l₀ - c₀ - S.I k₁ (fun u ω => s j u ω) t ω, κ₁ - l₁ - c₁, fun T hT hTj => ?_⟩
  -- at the rational maturities of the interval
  have hrat : ∀ q : ℚ, (q : ℝ) ∈ Ioo (t : ℝ) H → idx033 Tm q = j →
      (∫ u in (0:ℝ)..t, cross039 ρω ψω sω Tm c A b u q) - G (q - t) =
        (κ₀ - l₀ - c₀ - S.I k₁ (fun u ω => s j u ω) t ω) + (κ₁ - l₁ - c₁) * q := by
    intro q hq hqj
    have hq0 : (0:ℝ) ≤ q := t.2.trans hq.1.le
    have e := hag q (Ioo_subset_Icc_self hq)
    have er := hrand q
    rw [hqj] at er
    rw [hh q (Ioo_subset_Icc_self hq), curve039,
      alpha_split039 ρω ψω sω (path_scales hsc ω) Tm c A b t q t.2 hq.1.le, hc q hqj hq.1.le,
      hf0 q ⟨hq0, hq.2.le⟩, hk q ⟨hq0, hq.2.le⟩ hqj, hl q ⟨hq0, hq.2.le⟩ hqj, hqj] at e
    simp only [G, sub_add_cancel]
    rw [hbl, ← cexp_shift]
    simp only [sub_zero] at e
    linear_combination -e - er
  -- extend to the whole interval by continuity, with the explicit form anchored at `T`
  obtain ⟨ε, hε, hε'⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm T
  have hX := Novel.SpliceRandomScalesPathProof.explicit ρω ψω sω (path_scales hsc ω) Tm r A hA
    b c j t T t.2 hTj hT.1.le
  let φ : ℝ → ℝ := fun T' => (-(c ⬝ᵥ (A⁻¹ *ᵥ b)) * (∫ u in (0:ℝ)..t, ρω u * ψω u * sω j u) +
      c ⬝ᵥ (exp (T' • A) *ᵥ (yCoef035 1 (wS ρω ψω sω) Tm A b j T t +
        T' • zCoef035 1 (wS ρω ψω sω) A b j t))) -
    G (T' - t) - ((κ₀ - l₀ - c₀ - S.I k₁ (fun u ω => s j u ω) t ω) + (κ₁ - l₁ - c₁) * T')
  have hφc : Continuous φ := by
    have h1 := cont_of_analytic (quasi_analytic c A (yCoef035 1 (wS ρω ψω sω) Tm A b j T t)
      (zCoef035 1 (wS ρω ψω sω) A b j t))
    have h2 := hGc.comp (continuous_id.sub continuous_const : Continuous fun T' : ℝ => T' - t)
    exact ((continuous_const.add h1).sub h2).sub (continuous_const.add
      (continuous_const.mul continuous_id))
  have hφ : φ T = 0 := by
    refine Novel.SpliceCrossTermConsistencyProof.zero_of_rat φ hφc T (min ε (H - T))
      (lt_min hε (sub_pos.2 hT.2)) fun q hq => ?_
    have hqI : (q : ℝ) ∈ Ioo (t : ℝ) H :=
      ⟨hT.1.trans hq.1, by linarith [hq.2, min_le_right ε (H - T)]⟩
    have hqj : idx033 Tm q = j := by
      rw [hε' q ⟨hq.1.le, by linarith [hq.2, min_le_left ε (H - T)]⟩, hTj]
    have := hrat q hqI hqj
    rw [hX q hqj hqI.1.le] at this
    simp only [φ]
    linarith
  show (∫ u in (0:ℝ)..t, cross039 ρω ψω sω Tm c A b u T) - G (T - t) = _
  rw [hX T hTj hT.1.le]
  simp only [φ] at hφ
  linarith

/-- `t ↦ v_m(t)` is continuous for a bounded measurable weight. -/
lemma vvec_cont (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (Δ : ℝ → ℝ) (hΔ : Measurable Δ)
    (C : ℝ) (hC : ∀ u, |Δ u| ≤ C) :
    Continuous fun t => Standalone.SpliceQuasiExponentialKey.vvec A b Δ t := by
  refine continuous_pi fun i => intervalIntegral.continuous_primitive (fun a a' => ?_) 0
  have hg : Continuous fun u : ℝ => (exp (u • (-A)) *ᵥ b) i :=
    Novel.RecurrenceNecessityReductionProof.phi_cont (-A) b i
  exact (Novel.SpliceCrossTermDriftProof.ii_bdd hΔ C hC a a').mul_continuousOn hg.continuousOn

/-- (b) at one meeting. -/
lemma necessity_at {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b c : Fin r → ℝ) (hstand : Standing035 A b c) (H : ℝ)
    (hTm : ∀ τ ∈ Tm, 0 < τ ∧ τ < H) (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ))
    (hE : Block035 c A b E) (hcons : Consistent039 S k₁ k₂ f0 ρ ψ s Tm c A b H E)
    (τ : ℝ) (hτ : τ ∈ Tm) :
    ∀ᵐ ω ∂S.μ, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0 := by
  obtain ⟨hA, hc, hctrl⟩ := hstand
  obtain ⟨hf0, hver⟩ := hcons
  obtain ⟨h1, τl, hl, hidxl⟩ := Novel.SpliceCrossTermConsistencyProof.idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm τ
  set m := idx033 Tm τ - 1
  have hm : m + 1 = idx033 Tm τ := by omega
  have hidxr' : ∀ v ∈ Ico τ (τ + ε), idx033 Tm v = m + 1 := fun v hv => by
    rw [hm]; exact hidxr v hv
  have hτH := (hTm τ hτ).2
  -- the weighted jump on a path
  let Δ : Ω → ℝ → ℝ := fun ω u => ρ u ω * ψ u ω * (s (m + 1) u ω - s m u ω)
  let Kc : ℝ → Ω → Prop := fun t ω => ∀ T ∈ Ioo (0:ℝ) 1, c ⬝ᵥ (exp (T • A) *ᵥ
    ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ
      Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t)) = 0
  -- the subspace condition at each `t < τ`, almost surely
  have hKt : ∀ t ∈ Ico 0 τ, ∀ᵐ ω ∂S.μ, Kc t ω := by
    intro t ht
    let t' : ℝ≥0 := ⟨t, ht.1⟩
    obtain ⟨g, hgF, -, hgv⟩ := hver t' (by show t ≤ H; linarith [ht.2])
    filter_upwards [Novel.SpliceCrossTermConsistencyProof.version_rat S.μ g
      (fun T ω => curve039 S k₁ k₂ f0 ρ ψ s Tm c A b t' T ω) t' H hgv,
      good039 S k₁ k₂ s ρ ψ C hsc Tm c A b t'] with ω hω1 hω2
    set ρω : ℝ → ℝ := fun v => ρ v ω
    set ψω : ℝ → ℝ := fun v => ψ v ω
    set sω : ℕ → ℝ → ℝ := fun j v => s j v ω
    have hP : PathScales ρω ψω sω := path_scales hsc ω
    obtain ⟨G, hGa, p, hp0, hX0⟩ := form_of_rat039 S k₁ k₂ s ρ ψ C hsc Tm c A hA b H f0 E hE hf0
      t' ω hω2 (g ω) (hgF ω) hω1
    have hX : ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross039 ρω ψω sω Tm c A b u T = p T + G (T - t) :=
      fun T hT => hX0 T hT
    have hp : ∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T := hp0
    set τl' := max τl t
    have hτl' : τl' < τ := max_lt hl ht.2
    set T0 := (τl' + τ) / 2
    have hT0 : T0 ∈ Ioo τl τ := ⟨lt_of_le_of_lt (le_max_left τl t) (by simp only [T0]; linarith),
      by simp only [T0]; linarith⟩
    have htT0 : t ≤ T0 := by simp only [T0]; linarith [le_max_right τl t]
    set τr' := min (τ + ε) H
    have hτr' : τ < τr' := lt_min (by linarith) hτH
    obtain ⟨κ₀, κ₁, hκ⟩ := hp m
    obtain ⟨l₀, l₁, hl'⟩ := hp (m + 1)
    have hXl := Novel.SpliceRandomScalesPathProof.explicit ρω ψω sω hP Tm r A hA b c m t T0
      ht.1 (hidxl T0 hT0) htT0
    have hXr := Novel.SpliceRandomScalesPathProof.explicit ρω ψω sω hP Tm r A hA b c (m + 1)
      t τ ht.1 (hidxr' τ ⟨le_rfl, by linarith⟩) ht.2.le
    have hmatch := match035 c A (fun T => G (T - t))
      (fun x _ => AnalyticAt.comp (f := fun T : ℝ => T - t) (x := x) (hGa (x - t) (mem_univ _))
        (by fun_prop))
      (yCoef035 1 (wS ρω ψω sω) Tm A b m T0 t) (zCoef035 1 (wS ρω ψω sω) A b m t)
      (yCoef035 1 (wS ρω ψω sω) Tm A b (m + 1) τ t) (zCoef035 1 (wS ρω ψω sω) A b (m + 1) t)
      (-(c ⬝ᵥ (A⁻¹ *ᵥ b)) * (∫ u in (0:ℝ)..t, ρω u * ψω u * sω m u) - κ₀) (-κ₁)
      (-(c ⬝ᵥ (A⁻¹ *ᵥ b)) * (∫ u in (0:ℝ)..t, ρω u * ψω u * sω (m + 1) u) - l₀) (-l₁)
      τl' τ τ τr' hτl' hτr'
      (fun T hT => by
        have hTt : (t:ℝ) < T := lt_of_le_of_lt (le_max_right _ _) hT.1
        have hTI : T ∈ Ioo t H := ⟨hTt, by linarith [hT.2]⟩
        have hidx : idx033 Tm T = m := hidxl T ⟨lt_of_le_of_lt (le_max_left _ _) hT.1, hT.2⟩
        have := hX T hTI
        rw [hXl T hidx hTt.le, hκ T hTI hidx] at this
        show G (T - t) = _
        linarith)
      (fun T hT => by
        have hTI : T ∈ Ioo t H := ⟨lt_of_le_of_lt ht.2.le hT.1,
          lt_of_lt_of_le hT.2 (min_le_right _ _)⟩
        have hidx : idx033 Tm T = m + 1 :=
          hidxr' T ⟨hT.1.le, lt_of_lt_of_le hT.2 (min_le_left _ _)⟩
        have := hX T hTI
        rw [hXr T hidx hTI.1.le, hl' T hTI hidx] at this
        show G (T - t) = _
        linarith)
    obtain ⟨hy, hz⟩ := Novel.SpliceRandomScalesPathProof.jump ρω ψω sω hP Tm r A b m τ τl
      (τ + ε) T0 τ t hl (by linarith) hidxl hidxr' hT0 ⟨le_rfl, by linarith⟩ ht.1 htT0
    rw [hy, hz] at hmatch
    intro T hT
    have haff := Novel.SpliceQuasiExponentialAlgebraProof.affine r A hA c
      ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t)
      (Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t) 0 1 _ _ one_pos
      (fun T _ => hmatch T) T hT
    have e : c ⬝ᵥ (exp (T • A) *ᵥ ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t +
          T • Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t)) =
        c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ
          Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t)) := by
      simp only [add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [← e]
    exact haff
  -- at every rational `t < τ` on one event, then at every `t < τ` by continuity
  have hKq : ∀ᵐ ω ∂S.μ, ∀ q : ℚ, (q : ℝ) ∈ Ico 0 τ → Kc q ω := ae_all_iff.2 fun q => by
    by_cases hq : (q : ℝ) ∈ Ico 0 τ
    · filter_upwards [hKt q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hKq] with ω hω
  obtain ⟨hs, hρm, hψm, C', hsC, hρC, hψC⟩ := path_scales hsc ω
  have hΔm : Measurable (Δ ω) := (hρm.mul hψm).mul ((hs (m + 1)).sub (hs m))
  have hΔC : ∀ u, |Δ ω u| ≤ C' * C' * (C' + C') := fun u => by
    show |ρ u ω * ψ u ω * (s (m + 1) u ω - s m u ω)| ≤ _
    rw [abs_mul, abs_mul]
    have hC0 : 0 ≤ C' := (abs_nonneg _).trans (hρC 0)
    gcongr
    · exact hρC u
    · exact hψC u
    · exact (abs_sub _ _).trans (add_le_add (hsC _ _) (hsC _ _))
  have hvc := vvec_cont A b (Δ ω) hΔm _ hΔC
  have hall : ∀ t ∈ Ico 0 τ, Kc t ω := by
    intro t ht T hT
    let φ : ℝ → ℝ := fun t' => c ⬝ᵥ (exp (T • A) *ᵥ
      ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b (Δ ω) t'))
    have hφc : Continuous φ :=
      continuous_const.dotProduct (continuous_const.matrix_mulVec
        (continuous_const.matrix_mulVec hvc))
    have hτt : 0 < τ - t := sub_pos.2 ht.2
    refine Novel.SpliceCrossTermConsistencyProof.zero_of_rat φ hφc t (τ - t) hτt fun q hq => ?_
    exact hω q ⟨ht.1.trans hq.1.le, by linarith [hq.2]⟩ T hT
  have hkey := Novel.SpliceRandomScalesPathProof.key (fun u => ρ u ω) (fun u => ψ u ω)
    (fun j u => s j u ω) (path_scales hsc ω) r A hA b c hc hctrl m τ τ 0 1 one_pos hall
  filter_upwards [hkey] with u hu hu'
  have := hu hu'
  unfold jumpW jump033
  rw [← hm, Nat.add_sub_cancel]
  exact this

lemma necessity : Standalone.SpliceRandomScalesNecessity.necessityStatement := by
  intro Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c hstand H hTm f0 E hE hcons
  exact (eventually_all_finset Tm).2 fun τ hτ =>
    necessity_at S k₁ k₂ s ρ ψ C hsc Tm A b c hstand H hTm f0 E hE hcons τ hτ

lemma noThirdWay : Standalone.SpliceRandomScalesNecessity.noThirdWayStatement := by
  intro Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c hstand H hTm hne f0 E hE hcons
  exact hne (necessity Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c hstand H hTm f0 E hE hcons)

theorem spliceRandomScalesNecessity : Standalone.SpliceRandomScalesNecessity.statement :=
  ⟨necessity, noThirdWay⟩

end Novel.SpliceRandomScalesNecessityProof

import Standalone.SpliceQuasiExponentialConsistency
import Novel.SpliceQuasiExponentialCurveProof
import Novel.SpliceQuasiExponentialBlockProof
import Novel.SpliceQuasiExponentialAlgebraProof
import Novel.SpliceCrossTermSufficiencyProof

open Matrix NormedSpace MeasureTheory Set Filter Topology
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency Standalone.SpliceQuasiExponentialCross
open Standalone.SpliceQuasiExponentialCurve Standalone.SpliceQuasiExponentialBlock
open Standalone.SpliceQuasiExponentialConsistency
namespace Novel.SpliceQuasiExponentialConsistencyProof

variable {r : ℕ}

lemma lam_analytic (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    AnalyticOnNhd ℝ (lam035 c A b) univ :=
  Novel.SpliceQuasiExponentialKeyProof.analytic_g A c b

lemma Lam_eq' (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (x : ℝ) :
    Lam035 c A b x = (c ᵥ* A⁻¹) ⬝ᵥ (exp (x • A) *ᵥ b) - (c ᵥ* A⁻¹) ⬝ᵥ b := by
  rw [Lam035, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
    dotProduct_mulVec c A⁻¹ (exp (x • A) *ᵥ b), dotProduct_mulVec c A⁻¹ b]

lemma Lam_analytic (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) :
    AnalyticOnNhd ℝ (Lam035 c A b) univ := by
  have e : Lam035 c A b = fun x : ℝ => (c ᵥ* A⁻¹) ⬝ᵥ (exp (x • A) *ᵥ b) - (c ᵥ* A⁻¹) ⬝ᵥ b :=
    funext (Lam_eq' c A b)
  rw [e]
  exact fun x hx => (Novel.SpliceQuasiExponentialKeyProof.analytic_g A _ b x hx).sub analyticAt_const

lemma cont_of_analytic {f : ℝ → ℝ} (h : AnalyticOnNhd ℝ f univ) : Continuous f :=
  continuousOn_univ.1 h.continuousOn

/-- `T ↦ c e^{AT}(y + T z)` is real-analytic. -/
lemma quasi_analytic (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (y z : Fin r → ℝ) :
    AnalyticOnNhd ℝ (fun T : ℝ => c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z))) univ := by
  have e : (fun T : ℝ => c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z))) =
      fun T : ℝ => c ⬝ᵥ (exp (T • A) *ᵥ y) + T * c ⬝ᵥ (exp (T • A) *ᵥ z) := by
    funext T
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e]
  exact fun x hx => (Novel.SpliceQuasiExponentialKeyProof.analytic_g A c y x hx).add
    (analyticAt_id.mul (Novel.SpliceQuasiExponentialKeyProof.analytic_g A c z x hx))

/-- The time integral of the drift (33.1) splits into its three parts. -/
lemma alpha_split (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (ρ t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ u in (0:ℝ)..t, alpha035 ρ s Tm c A b u T =
      (∫ u in (0:ℝ)..t, sigS033 s Tm u T * SS033 s Tm u T) +
      (∫ u in (0:ℝ)..t, lam035 c A b (T - u) * Lam035 c A b (T - u)) +
      ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T := by
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
  have i1 : IntervalIntegrable (fun u => sigS033 s Tm u T * SS033 s Tm u T) volume 0 t := by
    refine (Novel.SpliceCrossTermCurveProof.ii_on ((hs j).mul hGm) (C * (C * T))
      fun u hu => ?_).congr fun u hu => ?_
    · show |s j u * G u| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hC _ _) (hGb u hu) (abs_nonneg _) hC0
    · show s j u * G u = sigS033 s Tm u T * SS033 s Tm u T
      rw [hEq u hu]; rfl
  have i2 : IntervalIntegrable (fun u => lam035 c A b (T - u) * Lam035 c A b (T - u)) volume 0 t :=
    (hlc.mul hLc).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun u => cross035 ρ s Tm c A b u T) volume 0 t := by
    have h1 := hsj.continuousOn_mul (g := fun u => Lam035 c A b (T - u)) hLc.continuousOn
    have h2 := hGi.continuousOn_mul (g := fun u => lam035 c A b (T - u)) hlc.continuousOn
    refine ((h1.add h2).const_mul ρ).congr fun u hu => ?_
    show ρ * (Lam035 c A b (T - u) * s j u + lam035 c A b (T - u) * G u) = cross035 ρ s Tm c A b u T
    rw [cross035, ← hEq u hu]
    show _ = ρ * (s j u * _ + _)
    ring
  unfold alpha035
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]

/-- The random vector `ρ X_1 + √(1 − ρ²) X_2` of the version of the random part. -/
noncomputable def Yv {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (ρ : ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (ω : Ω) : Fin r → ℝ :=
  ρ • (fun i => S.I k₁ (fun u _ => (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω) +
    Real.sqrt (1 - ρ ^ 2) • (fun i => S.I k₂ (fun u _ => (exp ((u : ℝ) • (-A)) *ᵥ b) i) t ω)

/-- The version of `f(t, ·)`: `f(0, ·)`, the drift integral, and the version of the random part. -/
noncomputable def ver {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (ω : Ω) (T : ℝ) : ℝ :=
  f0 T + (∫ u in (0:ℝ)..t, alpha035 ρ s Tm c A b u T) +
    (S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω + c ⬝ᵥ (exp (T • A) *ᵥ Yv S k₁ k₂ ρ A b t ω))

section Version
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
  (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
  (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
  (ρ : ℝ) (f0 : ℝ → ℝ) (t : ℝ≥0)
include hs hC

lemma ver_ae (T : ℝ) : ∀ᵐ ω ∂S.μ, ver S k₁ k₂ f0 ρ s Tm c A b t ω T =
    curve035 S k₁ k₂ f0 ρ s Tm c A b t T ω := by
  filter_upwards [Novel.SpliceQuasiExponentialCurveProof.random Ω mΩ S k₁ k₂ Tm s hs C hC r A b c
    ρ T t] with ω hω
  simp only [ver, curve035, Yv]
  rw [← hω]
  ring

lemma ver_meas (T : ℝ) : Measurable fun ω => ver S k₁ k₂ f0 ρ s Tm c A b t ω T := by
  have hm : ∀ k (H : ℝ≥0 → Ω → ℝ), U4 S.ℱ S.μ H → Measurable fun ω => S.I k H t ω :=
    fun k H hH => (S.int_adapted k H hH t).mono (S.ℱ.le t) le_rfl
  have h1 := hm k₁ _ (Novel.SpliceCrossTermCurveProof.step_U4 S s hs C hC (idx033 Tm T))
  have hv : Measurable fun ω => Yv S k₁ k₂ ρ A b t ω :=
    measurable_pi_iff.2 fun i =>
      (measurable_const.mul (hm k₁ _ (Novel.SpliceQuasiExponentialCurveProof.g_U4 S A b i))).add
        (measurable_const.mul (hm k₂ _ (Novel.SpliceQuasiExponentialCurveProof.g_U4 S A b i)))
  have hd : Measurable fun v : Fin r → ℝ => c ⬝ᵥ (exp (T • A) *ᵥ v) :=
    (continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)).measurable
  unfold ver
  exact measurable_const.add (h1.add (hd.comp hv))

end Version

/-- `c e^{AT} v = c e^{A(T − t)} (e^{At} v)`. -/
lemma cexp_shift (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T t : ℝ) (v : Fin r → ℝ) :
    c ⬝ᵥ (exp (T • A) *ᵥ v) = c ⬝ᵥ (exp ((T - t) • A) *ᵥ (exp (t • A) *ᵥ v)) := by
  rw [mulVec_mulVec, ← Novel.SpliceQuasiExponentialBlockProof.exp_add'', sub_add_cancel]

/-- The version is an element of `S⁺ + E(· − t)` plus the cross term. -/
lemma decomp {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (ρ H : ℝ) (hctrl : ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0)
    (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E) (hf0 : Fam033 Tm H E 0 f0)
    (t : ℝ≥0) (ω : Ω) : ∃ p, SPlus033 Tm H p ∧ ∃ g ∈ E, ∀ T ∈ Icc (t : ℝ) H,
      ver S k₁ k₂ f0 ρ s Tm c A b t ω T = p T + g (T - t) +
        ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T := by
  have := hE.finiteDimensional
  have hcont : ∀ g ∈ E, Continuous g := fun g hg => cont_of_analytic (hE.analytic g hg)
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  choose c₀ c₁ hc using fun j => Novel.SpliceCrossTermCurveProof.step Tm s hs C hC j t t.2
  have hGb := Novel.SpliceQuasiExponentialBlockProof.int_mem E hcont
    (fun g hg h hh => hE.shift g hg h hh) _ hE.lamLam_mem (fun _ => (1:ℝ)) t t.2
    intervalIntegrable_const
  have hGc := Novel.SpliceQuasiExponentialBlockProof.mem_cexp c A b hctrl E hE
    (exp ((t : ℝ) • A) *ᵥ Yv S k₁ k₂ ρ A b t ω)
  refine ⟨fun T => p0 T + ((c₀ (idx033 Tm T) + S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω) +
      c₁ (idx033 Tm T) * T),
    Novel.SpliceCrossTermSufficiencyProof.splus_add Tm H hp0
      (Novel.SpliceCrossTermSufficiencyProof.splus_pw Tm H
        (fun j => c₀ j + S.I k₁ (fun u _ => s j u) t ω) c₁), _,
    E.add_mem (hE.shift g0 hg0 t t.2) (E.add_mem hGb hGc), fun T hT => ?_⟩
  have hT0 : (0:ℝ) ≤ T := t.2.trans hT.1
  have hbl : (∫ u in (0:ℝ)..t, (fun _ => (1:ℝ)) u *
      (fun x => lam035 c A b x * Lam035 c A b x) (T - t + (t - u))) =
      ∫ u in (0:ℝ)..t, lam035 c A b (T - u) * Lam035 c A b (T - u) :=
    intervalIntegral.integral_congr fun u _ => by
      simp only [one_mul]
      rw [show (T : ℝ) - t + (t - u) = T - u by ring]
  simp only [ver, Pi.add_apply]
  rw [alpha_split Tm s hs C hC c A b ρ t T t.2 hT.1, hc _ T rfl hT.1, hf0 T ⟨hT0, hT.2⟩,
    sub_add_cancel, sub_zero, hbl, ← cexp_shift]
  ring

lemma uncorrelatedSplice : uncorrelatedSpliceStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC r A b c hstand ρ H f0 hf0 hjump
  obtain ⟨hA, -, hctrl⟩ := hstand
  obtain ⟨hB, hxE, -⟩ := Novel.SpliceQuasiExponentialBlockProof.e1 r A hA b c
  refine ⟨hf0, fun t _ => ⟨fun ω T => ver S k₁ k₂ f0 ρ s Tm c A b t ω T, fun ω => ?_,
    fun T => ver_meas S k₁ k₂ Tm s hs C hC c A b ρ f0 t T,
    fun T _ => ver_ae S k₁ k₂ Tm s hs C hC c A b ρ f0 t T⟩⟩
  obtain ⟨p, hp, g, hg, hdec⟩ := decomp S k₁ k₂ Tm s hs C hC c A b ρ H hctrl f0 _ hB hf0 t ω
  have hcase : ρ = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 (t : ℝ) →
      ∀ v, (t : ℝ) ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u := by
    by_cases hρ : ρ = 0
    · exact Or.inl hρ
    right
    filter_upwards [(Filter.eventually_all_finset Tm).2 hjump] with u hu hu0
    exact Novel.SpliceCrossTermSufficiencyProof.chain Tm s u t hu0.2 fun τ hτ huτ => by
      have := (mul_eq_zero.1 (hu τ hτ ⟨hu0.1, huτ⟩)).resolve_left hρ
      unfold jump033 at this
      linarith
  obtain ⟨K, y, z, hX⟩ :=
    Novel.SpliceQuasiExponentialCrossProof.uncorrelated Tm s hs C hC r A hA b c ρ t t.2 hcase
  refine ⟨fun T => p T + (K + 0 * T),
    Novel.SpliceCrossTermSufficiencyProof.splus_add Tm H hp
      (Novel.SpliceCrossTermSufficiencyProof.splus_pw Tm H (fun _ => K) fun _ => 0),
    g + ((fun x => c ⬝ᵥ (exp (x • A) *ᵥ (exp ((t : ℝ) • A) *ᵥ (y + (t : ℝ) • z)))) +
      fun x => x * c ⬝ᵥ (exp (x • A) *ᵥ (exp ((t : ℝ) • A) *ᵥ z))),
    (E1 c A b).add_mem hg ((E1 c A b).add_mem
      (Novel.SpliceQuasiExponentialBlockProof.mem_cexp c A b hctrl _ hB _)
      (Novel.SpliceQuasiExponentialBlockProof.mem_xcexp c A b hctrl _ hB hxE _)),
    fun T hT => ?_⟩
  have e : c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) =
      c ⬝ᵥ (exp ((T - t) • A) *ᵥ (exp ((t : ℝ) • A) *ᵥ (y + (t : ℝ) • z))) +
        (T - t) * c ⬝ᵥ (exp ((T - t) • A) *ᵥ (exp ((t : ℝ) • A) *ᵥ z)) := by
    rw [← cexp_shift, ← cexp_shift]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  beta_reduce
  rw [hdec T hT, hX T hT.1, e]
  simp only [Pi.add_apply]
  ring

lemma enlarged : enlargedStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC r A b c hstand ρ H f0 hf0
  classical
  obtain ⟨hA, -, hctrl⟩ := hstand
  obtain ⟨hB, -, -⟩ := Novel.SpliceQuasiExponentialBlockProof.e1 r A hA b c
  have hf0' : FamPlus035 c A Tm H (E1 c A b) 0 f0 := by
    obtain ⟨p0, hp0, g0, hg0, h0⟩ := hf0
    exact ⟨p0, hp0, g0, hg0, 0, 0, fun T hT => by rw [h0 T hT]; simp⟩
  refine ⟨hf0', fun t _ => ⟨fun ω T => ver S k₁ k₂ f0 ρ s Tm c A b t ω T, fun ω => ?_,
    fun T => ver_meas S k₁ k₂ Tm s hs C hC c A b ρ f0 t T,
    fun T _ => ver_ae S k₁ k₂ Tm s hs C hC c A b ρ f0 t T⟩⟩
  obtain ⟨p, hp, g, hg, hdec⟩ := decomp S k₁ k₂ Tm s hs C hC c A b ρ H hctrl f0 _ hB hf0 t ω
  let anchor : ℕ → ℝ := fun j =>
    if h : ∃ T0, idx033 Tm T0 = j ∧ (t : ℝ) ≤ T0 then Classical.choose h else 0
  have hanchor : ∀ T, (t : ℝ) ≤ T →
      idx033 Tm (anchor (idx033 Tm T)) = idx033 Tm T ∧ (t : ℝ) ≤ anchor (idx033 Tm T) := by
    intro T hT
    have h : ∃ T0, idx033 Tm T0 = idx033 Tm T ∧ (t : ℝ) ≤ T0 := ⟨T, rfl, hT⟩
    have hs := Classical.choose_spec h
    simp only [anchor, h, dite_true]
    exact hs
  refine ⟨fun T => p T + ((fun j => -(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * ∫ u in (0:ℝ)..t, s j u)
      (idx033 Tm T) + (fun _ => (0:ℝ)) (idx033 Tm T) * T),
    Novel.SpliceCrossTermSufficiencyProof.splus_add Tm H hp
      (Novel.SpliceCrossTermSufficiencyProof.splus_pw Tm H
        (fun j => -(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * ∫ u in (0:ℝ)..t, s j u) fun _ => 0), g, hg,
    fun j => yCoef035 ρ s Tm A b j (anchor j) t, fun j => zCoef035 ρ s A b j t,
    fun T hT => ?_⟩
  obtain ⟨ha1, ha2⟩ := hanchor T hT.1
  beta_reduce
  rw [hdec T hT, Novel.SpliceQuasiExponentialCrossProof.explicit Tm s hs C hC r A hA b c ρ
    (idx033 Tm T) t (anchor (idx033 Tm T)) t.2 ha1 ha2 T rfl hT.1]
  ring

/-- The version of the random part holds at every rational maturity on one event. -/
lemma good {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (ρ : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂S.μ, ∀ q : ℚ,
      S.I k₁ (fun u _ => sigS033 s Tm u q + ρ * lam035 c A b (q - u)) t ω +
        S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * lam035 c A b (q - u)) t ω =
      S.I k₁ (fun u _ => s (idx033 Tm q) u) t ω + c ⬝ᵥ (exp ((q : ℝ) • A) *ᵥ Yv S k₁ k₂ ρ A b t ω) :=
  ae_all_iff.2 fun q => by
    simp only [Yv]
    exact Novel.SpliceQuasiExponentialCurveProof.random Ω mΩ S k₁ k₂ Tm s hs C hC r A b c ρ q t

/-- The pathwise form of the cross term at `t`, from agreement of an element of `𝓕_t(E)` with
the curve at the rational maturities, on the event of `good`. -/
lemma form_of_rat {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (hA : IsUnit A.det)
    (b : Fin r → ℝ) (ρ H : ℝ) (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E)
    (hf0 : Fam033 Tm H E 0 f0) (t : ℝ≥0) (ω : Ω)
    (hrand : ∀ q : ℚ,
      S.I k₁ (fun u _ => sigS033 s Tm u q + ρ * lam035 c A b (q - u)) t ω +
        S.I k₂ (fun u _ => Real.sqrt (1 - ρ ^ 2) * lam035 c A b (q - u)) t ω =
      S.I k₁ (fun u _ => s (idx033 Tm q) u) t ω + c ⬝ᵥ (exp ((q : ℝ) • A) *ᵥ Yv S k₁ k₂ ρ A b t ω))
    (h : ℝ → ℝ) (hh : Fam033 Tm H E t h)
    (hag : ∀ q : ℚ, (q : ℝ) ∈ Icc (t : ℝ) H → h q = curve035 S k₁ k₂ f0 ρ s Tm c A b t q ω) :
    ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g univ ∧ ∃ p : ℝ → ℝ,
      (∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo (t : ℝ) H, idx033 Tm T = j → p T = k₀ + k₁ * T) ∧
      ∀ T ∈ Ioo (t : ℝ) H, ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T = p T + g (T - t) := by
  have := hE.finiteDimensional
  have hcont : ∀ g ∈ E, Continuous g := fun g hg => cont_of_analytic (hE.analytic g hg)
  obtain ⟨ph, hph, gh, hgh, hh⟩ := hh
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  set Y := Yv S k₁ k₂ ρ A b t ω
  let Gb : ℝ → ℝ := fun x => ∫ u in (0:ℝ)..t, (fun _ => (1:ℝ)) u *
    (fun x => lam035 c A b x * Lam035 c A b x) (x + (t - u))
  have hGbE : Gb ∈ E := Novel.SpliceQuasiExponentialBlockProof.int_mem E hcont
    (fun g hg h hh => hE.shift g hg h hh) _ hE.lamLam_mem (fun _ => (1:ℝ)) t t.2
    intervalIntegrable_const
  have hbl : ∀ T : ℝ, Gb (T - t) = ∫ u in (0:ℝ)..t, lam035 c A b (T - u) * Lam035 c A b (T - u) :=
    fun T => intervalIntegral.integral_congr fun u _ => by
      simp only [one_mul]
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
  refine ⟨G, hGa, fun T => (∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T) - G (T - t),
    fun j => ?_, fun T _ => by ring⟩
  obtain ⟨κ₀, κ₁, hk⟩ := hph j
  obtain ⟨l₀, l₁, hl⟩ := hp0 j
  obtain ⟨c₀, c₁, hc⟩ := Novel.SpliceCrossTermCurveProof.step Tm s hs C hC j t t.2
  refine ⟨κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω, κ₁ - l₁ - c₁, fun T hT hTj => ?_⟩
  -- at the rational maturities of the interval
  have hrat : ∀ q : ℚ, (q : ℝ) ∈ Ioo (t : ℝ) H → idx033 Tm q = j →
      (∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u q) - G (q - t) =
        (κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω) + (κ₁ - l₁ - c₁) * q := by
    intro q hq hqj
    have hq0 : (0:ℝ) ≤ q := t.2.trans hq.1.le
    have e := hag q (Ioo_subset_Icc_self hq)
    have er := hrand q
    rw [hqj] at er
    rw [hh q (Ioo_subset_Icc_self hq), curve035,
      alpha_split Tm s hs C hC c A b ρ t q t.2 hq.1.le, hc q hqj hq.1.le, hf0 q ⟨hq0, hq.2.le⟩,
      hk q ⟨hq0, hq.2.le⟩ hqj, hl q ⟨hq0, hq.2.le⟩ hqj] at e
    simp only [G, sub_add_cancel]
    rw [hbl, ← cexp_shift]
    simp only [sub_zero] at e
    linear_combination -e - er
  -- extend to the whole interval by continuity, with the explicit form anchored at `T`
  obtain ⟨ε, hε, hε'⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm T
  have hX := Novel.SpliceQuasiExponentialCrossProof.explicit Tm s hs C hC r A hA b c ρ j t T t.2
    hTj hT.1.le
  let ψ : ℝ → ℝ := fun T' => (-(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * (∫ u in (0:ℝ)..t, s j u) +
      c ⬝ᵥ (exp (T' • A) *ᵥ (yCoef035 ρ s Tm A b j T t + T' • zCoef035 ρ s A b j t))) -
    G (T' - t) - ((κ₀ - l₀ - c₀ - S.I k₁ (fun u _ => s j u) t ω) + (κ₁ - l₁ - c₁) * T')
  have hψc : Continuous ψ := by
    have h1 := cont_of_analytic (quasi_analytic c A (yCoef035 ρ s Tm A b j T t)
      (zCoef035 ρ s A b j t))
    have h2 := hGc.comp (continuous_id.sub continuous_const : Continuous fun T' : ℝ => T' - t)
    exact ((continuous_const.add h1).sub h2).sub (continuous_const.add
      (continuous_const.mul continuous_id))
  have hψ : ψ T = 0 := by
    refine Novel.SpliceCrossTermConsistencyProof.zero_of_rat ψ hψc T (min ε (H - T))
      (lt_min hε (sub_pos.2 hT.2)) fun q hq => ?_
    have hqI : (q : ℝ) ∈ Ioo (t : ℝ) H :=
      ⟨hT.1.trans hq.1, by linarith [hq.2, min_le_right ε (H - T)]⟩
    have hqj : idx033 Tm q = j := by
      rw [hε' q ⟨hq.1.le, by linarith [hq.2, min_le_left ε (H - T)]⟩, hTj]
    have := hrat q hqI hqj
    rw [hX q hqj hqI.1.le] at this
    simp only [ψ]
    linarith
  show (∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T) - G (T - t) = _
  rw [hX T hTj hT.1.le]
  simp only [ψ] at hψ
  linarith

/-- Matching an analytic function against `c e^{AT}(y + T z)` plus affine on two intervals. -/
lemma match035 (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (G : ℝ → ℝ)
    (hG : AnalyticOnNhd ℝ G univ) (y₁ z₁ y₂ z₂ : Fin r → ℝ) (a₁ b₁ a₂ b₂ d₁ d₂ e₁ e₂ : ℝ)
    (hd : d₁ < d₂) (he : e₁ < e₂)
    (h1 : ∀ T ∈ Ioo d₁ d₂, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y₁ + T • z₁)) + (a₁ + b₁ * T))
    (h2 : ∀ T ∈ Ioo e₁ e₂, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y₂ + T • z₂)) + (a₂ + b₂ * T)) :
    ∀ T : ℝ, c ⬝ᵥ (exp (T • A) *ᵥ ((y₂ - y₁) + T • (z₂ - z₁))) = (a₁ - a₂) + (b₁ - b₂) * T := by
  have hall : ∀ (y z : Fin r → ℝ) (a b' d e : ℝ), d < e →
      (∀ T ∈ Ioo d e, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + (a + b' * T)) →
      ∀ T, G T = c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + (a + b' * T) := by
    intro y z a b' d e hde h T
    have hF : AnalyticOnNhd ℝ (fun T => G T - (c ⬝ᵥ (exp (T • A) *ᵥ (y + T • z)) + (a + b' * T)))
        univ := fun x hx => (hG x hx).sub ((quasi_analytic c A y z x hx).add
          (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))
    have hmid : (d + e) / 2 ∈ Ioo d e := ⟨by linarith, by linarith⟩
    have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
      (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx; simp [h x hx]) (mem_univ T)
    simp only [Pi.zero_apply] at this
    linarith
  intro T
  have e1 := hall y₁ z₁ a₁ b₁ d₁ d₂ hd h1 T
  have e2 := hall y₂ z₂ a₂ b₂ e₁ e₂ he h2 T
  have : c ⬝ᵥ (exp (T • A) *ᵥ ((y₂ - y₁) + T • (z₂ - z₁))) =
      c ⬝ᵥ (exp (T • A) *ᵥ (y₂ + T • z₂)) - c ⬝ᵥ (exp (T • A) *ᵥ (y₁ + T • z₁)) := by
    simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [this]
  linarith

lemma necessity : Standalone.SpliceQuasiExponentialConsistency.necessityStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC r A b c hstand ρ H hTm f0 E hE hcons τ hτ
  obtain ⟨hA, hc, hctrl⟩ := hstand
  obtain ⟨hf0, hver⟩ := hcons
  have := S.isProbabilityMeasure
  obtain ⟨h1, τl, hl, hidxl⟩ := Novel.SpliceCrossTermConsistencyProof.idx_left Tm τ hτ
  obtain ⟨ε, hε, hidxr⟩ := Novel.SpliceCrossTermConsistencyProof.idx_right Tm τ
  set m := idx033 Tm τ - 1
  have hm : m + 1 = idx033 Tm τ := by omega
  have hidxr' : ∀ v ∈ Ico τ (τ + ε), idx033 Tm v = m + 1 := fun v hv => by rw [hm]; exact hidxr v hv
  have hτH := (hTm τ hτ).2
  by_cases hρ : ρ = 0
  · exact Eventually.of_forall fun u _ => by rw [hρ, zero_mul]
  set Δ : ℝ → ℝ := fun u => s (m + 1) u - s m u
  have hloc : MeasureTheory.LocallyIntegrable Δ volume := by
    refine (locallyIntegrable_const (C + C)).mono ((hs (m + 1)).sub (hs m)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ C + C)]
    exact (abs_sub _ _).trans (add_le_add (hC _ _) (hC _ _))
  -- the subspace condition at every `t < τ`
  have hK : ∀ t ∈ Ico 0 τ, ∀ T ∈ Ioo (0:ℝ) 1, c ⬝ᵥ (exp (T • A) *ᵥ
      ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b Δ t)) = 0 := by
    intro t ht T hT
    let t' : ℝ≥0 := ⟨t, ht.1⟩
    obtain ⟨g, hgF, -, hgv⟩ := hver t' (by show t ≤ H; linarith [ht.2])
    obtain ⟨ω, hω1, hω2⟩ := ((Novel.SpliceCrossTermConsistencyProof.version_rat S.μ g
      (fun T ω => curve035 S k₁ k₂ f0 ρ s Tm c A b t' T ω) t' H hgv).and
      (good S k₁ k₂ Tm s hs C hC c A b ρ t')).exists
    obtain ⟨G, hGa, p, hp0, hX0⟩ := form_of_rat S k₁ k₂ Tm s hs C hC c A hA b ρ H f0 E hE hf0 t' ω
      hω2 (g ω) (hgF ω) hω1
    have hX : ∀ T ∈ Ioo t H, ∫ u in (0:ℝ)..t, cross035 ρ s Tm c A b u T = p T + G (T - t) :=
      fun T hT => hX0 T hT
    have hp : ∀ j, ∃ k₀ k₁ : ℝ, ∀ T ∈ Ioo t H, idx033 Tm T = j → p T = k₀ + k₁ * T := hp0
    -- the two sides of `τ`
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
    have hXl := Novel.SpliceQuasiExponentialCrossProof.explicit Tm s hs C hC r A hA b c ρ m t T0
      ht.1 (hidxl T0 hT0) htT0
    have hXr := Novel.SpliceQuasiExponentialCrossProof.explicit Tm s hs C hC r A hA b c ρ (m + 1)
      t τ ht.1 (hidxr' τ ⟨le_rfl, by linarith⟩) ht.2.le
    have hmatch := match035 c A (fun T => G (T - t))
      (fun x _ => AnalyticAt.comp (f := fun T : ℝ => T - t) (x := x) (hGa (x - t) (mem_univ _))
        (by fun_prop))
      (yCoef035 ρ s Tm A b m T0 t) (zCoef035 ρ s A b m t)
      (yCoef035 ρ s Tm A b (m + 1) τ t) (zCoef035 ρ s A b (m + 1) t)
      (-(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * (∫ u in (0:ℝ)..t, s m u) - κ₀) (-κ₁)
      (-(ρ * (c ⬝ᵥ (A⁻¹ *ᵥ b))) * (∫ u in (0:ℝ)..t, s (m + 1) u) - l₀) (-l₁)
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
    obtain ⟨hy, hz⟩ := Novel.SpliceQuasiExponentialCrossProof.jump Tm s hs C hC r A b ρ m τ τl
      (τ + ε) T0 τ t hl (by linarith) hidxl hidxr' hT0 ⟨le_rfl, by linarith⟩ ht.1 htT0
    rw [hy, hz] at hmatch
    have haff := Novel.SpliceQuasiExponentialAlgebraProof.affine r A hA c
      (ρ • ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b Δ t))
      (ρ • Standalone.SpliceQuasiExponentialKey.vvec A b Δ t) 0 1 _ _ one_pos
      (fun T _ => hmatch T) T hT
    have e : c ⬝ᵥ (exp (T • A) *ᵥ (ρ • ((A⁻¹ - τ • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ
        Standalone.SpliceQuasiExponentialKey.vvec A b Δ t) +
          T • ρ • Standalone.SpliceQuasiExponentialKey.vvec A b Δ t)) =
        ρ * c ⬝ᵥ (exp (T • A) *ᵥ ((T • (1 : Matrix (Fin r) (Fin r) ℝ) + (A⁻¹ - τ • 1)) *ᵥ
          Standalone.SpliceQuasiExponentialKey.vvec A b Δ t)) := by
      simp only [add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [e] at haff
    exact (mul_eq_zero.1 haff).resolve_left hρ
  have hkey := Novel.SpliceQuasiExponentialKeyProof.key r A hA b c hc hctrl τ τ 0 1 Δ one_pos
    hloc hK
  filter_upwards [hkey] with u hu hu'
  have := hu hu'
  simp only [Δ] at this
  unfold jump033
  rw [← hm, Nat.add_sub_cancel, this, mul_zero]

lemma noThirdWay : Standalone.SpliceQuasiExponentialConsistency.noThirdWayStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC r A b c hstand ρ H hTm τ hτ hne f0 E hE hcons
  exact hne (necessity Ω mΩ S k₁ k₂ Tm s hs C hC r A b c hstand ρ H hTm f0 E hE hcons τ hτ)

theorem spliceQuasiExponentialConsistency : Standalone.SpliceQuasiExponentialConsistency.statement := ⟨necessity, noThirdWay, uncorrelatedSplice, enlarged⟩

end Novel.SpliceQuasiExponentialConsistencyProof

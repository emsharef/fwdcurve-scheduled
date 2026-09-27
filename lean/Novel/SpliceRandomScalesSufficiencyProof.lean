import Standalone.SpliceRandomScalesSufficiency
import Novel.SpliceRandomScalesNecessityProof

open Matrix NormedSpace MeasureTheory Set Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermAlpha Standalone.SpliceCrossTermConsistency
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceQuasiExponentialBlock
open Standalone.SpliceQuasiExponentialConsistency Standalone.SpliceRandomScalesPath
open Standalone.SpliceRandomScalesCurve Standalone.SpliceRandomScalesNecessity
open Standalone.SpliceRandomScalesSufficiency
namespace Novel.SpliceRandomScalesSufficiencyProof
open Novel.SpliceQuasiExponentialConsistencyProof

variable {r : ℕ}

section Meas
variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The predictable σ-algebra lies inside the product σ-algebra. -/
lemma pred_le_prod (ℱ : Filtration ℝ≥0 mΩ) :
    ℱ.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
  measurableSpace_le_predictable_of_measurableSet
    (fun A hA => (measurableSet_singleton _).prod (ℱ.le _ A hA))
    (fun i A hA => measurableSet_Ioi.prod (ℱ.le i A hA))

/-- A predictable process is jointly measurable in `(u, ω)`, with `u ∈ ℝ` read through
`Real.toNNReal`. -/
lemma joint_meas (ℱ : Filtration ℝ≥0 mΩ) (f : ℝ → Ω → ℝ)
    (h : IsStronglyPredictable ℱ (fun (u : ℝ≥0) ω => f u ω)) :
    Measurable fun q : ℝ × Ω => f (Real.toNNReal q.1) q.2 := by
  have h1 : StronglyMeasurable (Function.uncurry fun (u : ℝ≥0) ω => f u ω) :=
    h.mono (pred_le_prod ℱ)
  exact h1.measurable.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

/-- The pathwise drift integral `∫_0^t α(u, T, ω) du` is measurable in `ω`, for `t ≤ T`. -/
lemma drift_meas (S : ItoCalculus Ω) (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ)
    (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ) (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (b : Fin r → ℝ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    Measurable fun ω => ∫ u in (0:ℝ)..t,
      alpha039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm c A b u T := by
  classical
  obtain ⟨hsP, hρP, hψP, -, -, -, -, -, -⟩ := hsc
  -- the scales read through `Real.toNNReal`, jointly measurable
  let st : ℕ → ℝ → Ω → ℝ := fun j u ω => s j (Real.toNNReal u) ω
  let ρt : ℝ → Ω → ℝ := fun u ω => ρ (Real.toNNReal u) ω
  let ψt : ℝ → Ω → ℝ := fun u ω => ψ (Real.toNNReal u) ω
  have hst : ∀ j, Measurable fun q : ℝ × Ω => st j q.1 q.2 := fun j => joint_meas S.ℱ (s j) (hsP j)
  have hρt : Measurable fun q : ℝ × Ω => ρt q.1 q.2 := joint_meas S.ℱ ρ hρP
  have hψt : Measurable fun q : ℝ × Ω => ψt q.1 q.2 := joint_meas S.ℱ ψ hψP
  -- on `[0, t]` the two readings agree
  have hagree : ∀ ω, ∀ u ∈ uIcc 0 t,
      alpha039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm c A b u T =
      alpha039 (fun v => ρt v ω) (fun v => ψt v ω) (fun j v => st j v ω) Tm c A b u T := by
    intro ω u hu
    rw [uIcc_of_le ht] at hu
    simp only [alpha039, cross039, sigS033, SS033, st, ρt, ψt, Real.coe_toNNReal _ hu.1]
  -- `S^S` as a jointly measurable function
  let F : (ℝ × Ω) × ℝ → ℝ := fun p =>
    if p.1.1 < p.2 ∧ p.2 ≤ T then st (idx033 Tm p.2) p.1.1 p.1.2 else 0
  have hjoint : Measurable fun x : ℕ × (ℝ × Ω) => st x.1 x.2.1 x.2.2 :=
    measurable_from_prod_countable_right hst
  have hFm : Measurable F :=
    Measurable.ite ((measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
      (hjoint.comp (((Novel.SpliceCrossTermDriftProof.idx_meas Tm).comp measurable_snd).prodMk
        measurable_fst)) measurable_const
  let G : ℝ × Ω → ℝ := fun q => ∫ v, F (q, v)
  have hGm : Measurable G :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hSS : ∀ q : ℝ × Ω, q.1 ≤ T → SS033 (fun j v => st j v q.2) Tm q.1 T = G q := by
    intro q hq
    rw [SS033, intervalIntegral.integral_of_le hq, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext v
    simp only [Set.indicator_apply, Set.mem_Ioc, F, sigS033]
  have hlc : Continuous fun u => lam035 c A b (T - u) :=
    (cont_of_analytic (lam_analytic c A b)).comp (continuous_const.sub continuous_id)
  have hLc : Continuous fun u => Lam035 c A b (T - u) :=
    (cont_of_analytic (Lam_analytic c A b)).comp (continuous_const.sub continuous_id)
  have hl : Measurable fun q : ℝ × Ω => lam035 c A b (T - q.1) := hlc.measurable.comp measurable_fst
  have hL : Measurable fun q : ℝ × Ω => Lam035 c A b (T - q.1) := hLc.measurable.comp measurable_fst
  let α : ℝ × Ω → ℝ := fun q =>
    st (idx033 Tm T) q.1 q.2 * G q +
      ψt q.1 q.2 ^ 2 * (lam035 c A b (T - q.1) * Lam035 c A b (T - q.1)) +
      ρt q.1 q.2 * (st (idx033 Tm T) q.1 q.2 * (ψt q.1 q.2 * Lam035 c A b (T - q.1)) +
        ψt q.1 q.2 * lam035 c A b (T - q.1) * G q)
  have hαm : Measurable α :=
    (((hst _).mul hGm).add ((hψt.pow_const 2).mul (hl.mul hL))).add
      (hρt.mul (((hst _).mul (hψt.mul hL)).add ((hψt.mul hl).mul hGm)))
  have hα : ∀ ω, ∀ u ∈ uIcc 0 t,
      alpha039 (fun v => ρt v ω) (fun v => ψt v ω) (fun j v => st j v ω) Tm c A b u T =
        α (u, ω) := by
    intro ω u hu
    rw [uIcc_of_le ht] at hu
    have := hSS (u, ω) (hu.2.trans htT)
    simp only [alpha039, cross039, sigS033, α] at this ⊢
    rw [this]
  have e : (fun ω => ∫ u in (0:ℝ)..t,
      alpha039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm c A b u T) =
      fun ω => ∫ u, α (u, ω) ∂(volume.restrict (Ioc 0 t)) := by
    funext ω
    rw [intervalIntegral.integral_congr (hagree ω), intervalIntegral.integral_congr (hα ω),
      intervalIntegral.integral_of_le ht]
  rw [e]
  exact ((hαm.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 t))).measurable

end Meas

/-- The version of `f(t, ·)` on `[t, ∞)`: `f(0, ·)`, the drift integral, and the version of the
random part. -/
noncomputable def ver039 {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (ρ ψ : ℝ → Ω → ℝ) (s : ℕ → ℝ → Ω → ℝ) (Tm : Finset ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (t : ℝ≥0) (ω : Ω) (T : ℝ) : ℝ :=
  if (t : ℝ) ≤ T then
    f0 T + (∫ u in (0:ℝ)..t, alpha039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm
      c A b u T) + (S.I k₁ (fun u ω => s (idx033 Tm T) u ω) t ω +
        c ⬝ᵥ (exp (T • A) *ᵥ Yv039 S k₁ k₂ ρ ψ A b t ω))
  else 0

section Version
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
  (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ)
  (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (f0 : ℝ → ℝ) (t : ℝ≥0)
include hsc

lemma ver_ae (T : ℝ) (hT : (t : ℝ) ≤ T) : ∀ᵐ ω ∂S.μ, ver039 S k₁ k₂ f0 ρ ψ s Tm c A b t ω T =
    curve039 S k₁ k₂ f0 ρ ψ s Tm c A b t T ω := by
  filter_upwards [Novel.SpliceRandomScalesCurveProof.random Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c
    T t] with ω hω
  simp only [ver039, hT, ite_true, curve039]
  linear_combination -hω

lemma ver_meas (T : ℝ) : Measurable fun ω => ver039 S k₁ k₂ f0 ρ ψ s Tm c A b t ω T := by
  by_cases hT : (t : ℝ) ≤ T
  swap
  · simp only [ver039, hT, ite_false]; exact measurable_const
  have hsc' := hsc
  obtain ⟨hsP, hρP, hψP, -, -, -, hsC, hρC, hψC⟩ := hsc
  have hm : ∀ k (H : ℝ≥0 → Ω → ℝ), U4 S.ℱ S.μ H → Measurable fun ω => S.I k H t ω :=
    fun k H hH => (S.int_adapted k H hH t).mono (S.ℱ.le t) le_rfl
  have hw1C : ∀ u ω, |ρ u ω * ψ u ω| ≤ 1 * C := fun u ω => by
    rw [abs_mul]; exact mul_le_mul (hρC u ω) (hψC u ω) (abs_nonneg _) zero_le_one
  have hw2C : ∀ u ω, |Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω| ≤ 1 * C := fun u ω => by
    rw [abs_mul]
    exact mul_le_mul (Novel.SpliceRandomScalesCurveProof.sqrt_le _) (hψC u ω) (abs_nonneg _)
      zero_le_one
  have h1 := hm k₁ _ (Novel.SpliceRandomScalesCurveProof.U4_proc S (s (idx033 Tm T)) (hsP _) C
    (hsC _))
  have hv : Measurable fun ω => Yv039 S k₁ k₂ ρ ψ A b t ω :=
    measurable_pi_iff.2 fun i =>
      (hm k₁ _ (Novel.SpliceRandomScalesCurveProof.U4_mul S (fun u ω => ρ u ω * ψ u ω)
        (hρP.mul hψP) _ hw1C _ (Novel.SpliceRandomScalesCurveProof.gcont A b i))).add
      (hm k₂ _ (Novel.SpliceRandomScalesCurveProof.U4_mul S
        (fun u ω => Real.sqrt (1 - ρ u ω ^ 2) * ψ u ω)
        ((Novel.SpliceRandomScalesCurveProof.sqrt_pred S ρ hρP).mul hψP) _ hw2C _
        (Novel.SpliceRandomScalesCurveProof.gcont A b i)))
  have hd : Measurable fun v : Fin r → ℝ => c ⬝ᵥ (exp (T • A) *ᵥ v) :=
    (continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)).measurable
  simp only [ver039, hT, ite_true]
  exact (measurable_const.add (drift_meas S s ρ ψ C hsc'
    Tm c A b t T t.2 hT)).add (h1.add (hd.comp hv))

end Version

/-- On every path the version is an element of `S⁺ + E(· − t)` plus the cross term. -/
lemma decomp039 {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (s : ℕ → ℝ → Ω → ℝ) (ρ ψ : ℝ → Ω → ℝ) (C : ℝ) (hsc : Scales039 S s ρ ψ C) (Tm : Finset ℝ)
    (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ) (H : ℝ)
    (hctrl : ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0)
    (f0 : ℝ → ℝ) (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E) (hf0 : Fam033 Tm H E 0 f0)
    (t : ℝ≥0) (ω : Ω) : ∃ p, SPlus033 Tm H p ∧ ∃ g ∈ E, ∀ T ∈ Icc (t : ℝ) H,
      ver039 S k₁ k₂ f0 ρ ψ s Tm c A b t ω T = p T + g (T - t) +
        ∫ u in (0:ℝ)..t, cross039 (fun v => ρ v ω) (fun v => ψ v ω) (fun j v => s j v ω) Tm
          c A b u T := by
  have := hE.finiteDimensional
  set ρω : ℝ → ℝ := fun v => ρ v ω
  set ψω : ℝ → ℝ := fun v => ψ v ω
  set sω : ℕ → ℝ → ℝ := fun j v => s j v ω
  have hP : PathScales ρω ψω sω := Novel.SpliceRandomScalesNecessityProof.path_scales hsc ω
  obtain ⟨hs, -, hψm, C', hsC, -, hψC⟩ := hP
  have hcont : ∀ g ∈ E, Continuous g := fun g hg => cont_of_analytic (hE.analytic g hg)
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  choose c₀ c₁ hc using fun j => Novel.SpliceCrossTermCurveProof.step Tm sω hs C' hsC j t t.2
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
  have hGc := Novel.SpliceQuasiExponentialBlockProof.mem_cexp c A b hctrl E hE
    (exp ((t : ℝ) • A) *ᵥ Yv039 S k₁ k₂ ρ ψ A b t ω)
  refine ⟨fun T => p0 T + ((c₀ (idx033 Tm T) + S.I k₁ (fun u ω => s (idx033 Tm T) u ω) t ω) +
      c₁ (idx033 Tm T) * T),
    Novel.SpliceCrossTermSufficiencyProof.splus_add Tm H hp0
      (Novel.SpliceCrossTermSufficiencyProof.splus_pw Tm H
        (fun j => c₀ j + S.I k₁ (fun u ω => s j u ω) t ω) c₁), _,
    E.add_mem (hE.shift g0 hg0 t t.2) (E.add_mem hGbE hGc), fun T hT => ?_⟩
  have hT0 : (0:ℝ) ≤ T := t.2.trans hT.1
  simp only [ver039, hT.1, ite_true, Pi.add_apply]
  rw [Novel.SpliceRandomScalesNecessityProof.alpha_split039 ρω ψω sω
    (Novel.SpliceRandomScalesNecessityProof.path_scales hsc ω) Tm c A b t T t.2 hT.1,
    hc _ T rfl hT.1, hf0 T ⟨hT0, hT.2⟩, sub_add_cancel, sub_zero, hbl, ← cexp_shift]
  ring

lemma uncorrelatedSplice : Standalone.SpliceRandomScalesSufficiency.uncorrelatedSpliceStatement := by
  intro Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c hstand H f0 hf0 hgood
  classical
  obtain ⟨hA, -, hctrl⟩ := hstand
  obtain ⟨hB, hxE, -⟩ := Novel.SpliceQuasiExponentialBlockProof.e1 r A hA b c
  set Nbad := toMeasurable S.μ
    {ω | ¬ (∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0)}
  have hN0 : S.μ Nbad = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hgood
  have hNm : MeasurableSet Nbad := measurableSet_toMeasurable _ _
  have hgoodN : ∀ ω ∉ Nbad, ∀ τ ∈ Tm, ∀ᵐ u ∂volume, u ∈ Ico 0 τ → jumpW ρ ψ s Tm τ u ω = 0 :=
    fun ω hω => by
      by_contra h
      exact hω (subset_toMeasurable _ _ h)
  refine ⟨hf0, fun t _ => ⟨fun ω T => if ω ∈ Nbad then 0 else
      ver039 S k₁ k₂ f0 ρ ψ s Tm c A b t ω T, fun ω => ?_, fun T => ?_, fun T hT => ?_⟩⟩
  rotate_left
  · exact Measurable.ite hNm measurable_const (ver_meas S k₁ k₂ s ρ ψ C hsc Tm c A b f0 t T)
  · filter_upwards [ver_ae S k₁ k₂ s ρ ψ C hsc Tm c A b f0 t T hT.1,
      measure_eq_zero_iff_ae_notMem.1 hN0] with ω h1 h2
    simp only [h2, ite_false]
    exact h1
  by_cases hω : ω ∈ Nbad
  · simp only [hω, ite_true]
    exact ⟨0, fun j => ⟨0, 0, fun _ _ _ => by simp⟩, 0, (E1 c A b).zero_mem, fun T _ => by simp⟩
  simp only [hω, ite_false]
  set ρω : ℝ → ℝ := fun v => ρ v ω
  set ψω : ℝ → ℝ := fun v => ψ v ω
  set sω : ℕ → ℝ → ℝ := fun j v => s j v ω
  obtain ⟨hwm, Cw, hwC⟩ := Novel.SpliceRandomScalesPathProof.wS_bounded
    (Novel.SpliceRandomScalesNecessityProof.path_scales hsc ω)
  obtain ⟨p, hp, g, hg, hdec⟩ :=
    decomp039 S k₁ k₂ s ρ ψ C hsc Tm c A b H hctrl f0 _ hB hf0 t ω
  have hcase : (1:ℝ) = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 (t : ℝ) →
      ∀ v, (t : ℝ) ≤ v → wS ρω ψω sω (idx033 Tm v) u = wS ρω ψω sω (idx033 Tm t) u := by
    right
    filter_upwards [(eventually_all_finset Tm).2 (hgoodN ω hω)] with u hu hu0
    exact Novel.SpliceCrossTermSufficiencyProof.chain Tm (wS ρω ψω sω) u t hu0.2
      fun τ hτ huτ => by
        have := hu τ hτ ⟨hu0.1, huτ⟩
        simp only [jumpW, jump033, wS] at this ⊢
        linear_combination this
  obtain ⟨K, y, z, hX⟩ := Novel.SpliceQuasiExponentialCrossProof.uncorrelated Tm (wS ρω ψω sω)
    hwm Cw hwC r A hA b c 1 t t.2 hcase
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
  have hXc : ∫ u in (0:ℝ)..t, cross039 ρω ψω sω Tm c A b u T =
      ∫ u in (0:ℝ)..t, cross035 1 (wS ρω ψω sω) Tm c A b u T :=
    intervalIntegral.integral_congr fun u _ =>
      Novel.SpliceRandomScalesPathProof.cross ρω ψω sω Tm r c A b u T
  beta_reduce
  rw [hdec T hT, hXc, hX T hT.1, e]
  simp only [Pi.add_apply]
  ring

lemma enlarged : Standalone.SpliceRandomScalesSufficiency.enlargedStatement := by
  intro Ω mΩ S k₁ k₂ s ρ ψ C hsc Tm r A b c hstand H f0 hf0
  classical
  obtain ⟨hA, -, hctrl⟩ := hstand
  obtain ⟨hB, -, -⟩ := Novel.SpliceQuasiExponentialBlockProof.e1 r A hA b c
  have hf0' : FamPlus035 c A Tm H (E1 c A b) 0 f0 := by
    obtain ⟨p0, hp0, g0, hg0, h0⟩ := hf0
    exact ⟨p0, hp0, g0, hg0, 0, 0, fun T hT => by rw [h0 T hT]; simp⟩
  refine ⟨hf0', fun t _ => ⟨fun ω T => ver039 S k₁ k₂ f0 ρ ψ s Tm c A b t ω T, fun ω => ?_,
    fun T => ver_meas S k₁ k₂ s ρ ψ C hsc Tm c A b f0 t T,
    fun T hT => ver_ae S k₁ k₂ s ρ ψ C hsc Tm c A b f0 t T hT.1⟩⟩
  set ρω : ℝ → ℝ := fun v => ρ v ω
  set ψω : ℝ → ℝ := fun v => ψ v ω
  set sω : ℕ → ℝ → ℝ := fun j v => s j v ω
  have hP := Novel.SpliceRandomScalesNecessityProof.path_scales hsc ω
  obtain ⟨p, hp, g, hg, hdec⟩ := decomp039 S k₁ k₂ s ρ ψ C hsc Tm c A b H hctrl f0 _ hB hf0 t ω
  let anchor : ℕ → ℝ := fun j =>
    if h : ∃ T0, idx033 Tm T0 = j ∧ (t : ℝ) ≤ T0 then Classical.choose h else 0
  have hanchor : ∀ T, (t : ℝ) ≤ T →
      idx033 Tm (anchor (idx033 Tm T)) = idx033 Tm T ∧ (t : ℝ) ≤ anchor (idx033 Tm T) := by
    intro T hT
    have h : ∃ T0, idx033 Tm T0 = idx033 Tm T ∧ (t : ℝ) ≤ T0 := ⟨T, rfl, hT⟩
    have hs := Classical.choose_spec h
    simp only [anchor, h, dite_true]
    exact hs
  refine ⟨fun T => p T + ((fun j => -(c ⬝ᵥ (A⁻¹ *ᵥ b)) *
      ∫ u in (0:ℝ)..t, ρω u * ψω u * sω j u) (idx033 Tm T) + (fun _ => (0:ℝ)) (idx033 Tm T) * T),
    Novel.SpliceCrossTermSufficiencyProof.splus_add Tm H hp
      (Novel.SpliceCrossTermSufficiencyProof.splus_pw Tm H
        (fun j => -(c ⬝ᵥ (A⁻¹ *ᵥ b)) * ∫ u in (0:ℝ)..t, ρω u * ψω u * sω j u) fun _ => 0), g, hg,
    fun j => yCoef035 1 (wS ρω ψω sω) Tm A b j (anchor j) t,
    fun j => zCoef035 1 (wS ρω ψω sω) A b j t, fun T hT => ?_⟩
  obtain ⟨ha1, ha2⟩ := hanchor T hT.1
  beta_reduce
  rw [hdec T hT, Novel.SpliceRandomScalesPathProof.explicit ρω ψω sω hP Tm r A hA b c
    (idx033 Tm T) t (anchor (idx033 Tm T)) t.2 ha1 ha2 T rfl hT.1]
  ring

theorem spliceRandomScalesSufficiency : Standalone.SpliceRandomScalesSufficiency.statement :=
  ⟨uncorrelatedSplice, enlarged⟩

end Novel.SpliceRandomScalesSufficiencyProof

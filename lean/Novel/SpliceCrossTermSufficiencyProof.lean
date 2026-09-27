import Standalone.SpliceCrossTermSufficiency
import Novel.SpliceCrossTermConsistencyProof
import Novel.SpliceCrossTermUncorrelatedProof

open MeasureTheory Set Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SpliceCrossTermDrift
open Standalone.SpliceCrossTermConsistency Standalone.SpliceCrossTermSufficiency
namespace Novel.SpliceCrossTermSufficiencyProof
open Novel.SpliceCrossTermConsistencyProof

lemma mem1 (a : ℝ) : (fun x => Real.exp (-a * x)) ∈ E0 a := Submodule.subset_span (by simp)
lemma memx (a : ℝ) : (fun x => x * Real.exp (-a * x)) ∈ E0 a := Submodule.subset_span (by simp)
lemma mem2 (a : ℝ) : (fun x => Real.exp (-(2 * a) * x)) ∈ E0 a := Submodule.subset_span (by simp)

lemma e0Block : e0BlockStatement := by
  intro a
  have he : ∀ (c : ℝ) (x : ℝ), AnalyticAt ℝ (fun x : ℝ => Real.exp (c * x)) x := fun c x =>
    (analyticOnNhd_rexp _ (mem_univ _)).comp (by fun_prop)
  refine ⟨FiniteDimensional.span_of_finite ℝ (Set.toFinite _), fun g hg => ?_,
    fun g hg h hh => ?_, mem1 a, mem2 a⟩
  · induction hg using Submodule.span_induction with
    | mem x hx =>
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact fun x _ => he (-a) x
      · exact fun x _ => analyticAt_id.mul (he (-a) x)
      · exact fun x _ => he (-(2 * a)) x
    | zero => exact fun x _ => analyticAt_const
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact fun x hx => analyticAt_const.mul (hf x hx)
  · induction hg using Submodule.span_induction with
    | mem x hx =>
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · convert (E0 a).smul_mem (Real.exp (-a * h)) (mem1 a) using 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
        ring_nf
      · convert (E0 a).add_mem ((E0 a).smul_mem (Real.exp (-a * h)) (memx a))
          ((E0 a).smul_mem (h * Real.exp (-a * h)) (mem1 a)) using 1
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have e : Real.exp (-a * (x + h)) = Real.exp (-a * h) * Real.exp (-a * x) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        ring
      · convert (E0 a).smul_mem (Real.exp (-(2 * a) * h)) (mem2 a) using 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
        ring_nf
    | zero => exact (E0 a).zero_mem
    | add f g _ _ hf hg => exact (E0 a).add_mem hf hg
    | smul c f _ hf => exact (E0 a).smul_mem c hf

/-- `S⁺` contains every function affine on each maturity interval. -/
lemma splus_pw (Tm : Finset ℝ) (H : ℝ) (K₀ K₁ : ℕ → ℝ) :
    SPlus033 Tm H (fun T => K₀ (idx033 Tm T) + K₁ (idx033 Tm T) * T) :=
  fun j => ⟨K₀ j, K₁ j, fun T _ hT => by show K₀ (idx033 Tm T) + K₁ (idx033 Tm T) * T = _; rw [hT]⟩

lemma splus_add (Tm : Finset ℝ) (H : ℝ) {p q : ℝ → ℝ} (hp : SPlus033 Tm H p)
    (hq : SPlus033 Tm H q) : SPlus033 Tm H (fun T => p T + q T) := by
  intro j
  obtain ⟨k₀, k₁, hk⟩ := hp j
  obtain ⟨l₀, l₁, hl⟩ := hq j
  exact ⟨k₀ + l₀, k₁ + l₁, fun T hT hTj => by
    show p T + q T = _
    rw [hk T hT hTj, hl T hT hTj]; ring⟩

/-- If every jump before `u` vanishes at `u`, the step volatility at `u` is the same on every
maturity interval after `t ≥ u`. -/
lemma chain (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (u t : ℝ) (hut : u ≤ t)
    (h : ∀ τ ∈ Tm, u < τ → s (idx033 Tm τ) u = s (idx033 Tm τ - 1) u) :
    ∀ v, t ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u := by
  classical
  suffices key : ∀ n : ℕ, ∀ v, t ≤ v → idx033 Tm v = idx033 Tm t + n →
      s (idx033 Tm v) u = s (idx033 Tm t) u by
    intro v hv
    have := Novel.SpliceCrossTermDriftProof.idx_mono Tm hv
    exact key (idx033 Tm v - idx033 Tm t) v hv (by omega)
  intro n
  induction n with
  | zero => intro v _ hv; rw [hv, add_zero]
  | succ n ih =>
    intro v htv hv
    have hne : (Tm.filter fun x => x ≤ v).Nonempty := Finset.card_pos.1 (by
      show 0 < idx033 Tm v; omega)
    set τ := (Tm.filter fun x => x ≤ v).max' hne
    have hτ : τ ∈ Tm ∧ τ ≤ v := Finset.mem_filter.1 ((Tm.filter fun x => x ≤ v).max'_mem hne)
    have hle : ∀ x ∈ Tm, x ≤ v → x ≤ τ := fun x hx hxv =>
      (Tm.filter fun x => x ≤ v).le_max' x (Finset.mem_filter.2 ⟨hx, hxv⟩)
    have hτt : t < τ := by
      by_contra hc
      have : idx033 Tm v ≤ idx033 Tm t := Finset.card_le_card fun x hx => by
        obtain ⟨hx, hxv⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨hx, (hle x hx hxv).trans (le_of_not_gt hc)⟩
      omega
    have hτv : idx033 Tm τ = idx033 Tm v := by
      unfold idx033
      congr 1
      exact Finset.filter_congr fun x hx => ⟨fun h1 => h1.trans hτ.2, hle x hx⟩
    obtain ⟨h1, τl, hl, hleft⟩ := idx_left Tm τ hτ.1
    set v' := max t ((τl + τ) / 2)
    have hv' : v' ∈ Ioo τl τ :=
      ⟨lt_of_lt_of_le (by linarith) (le_max_right _ _), max_lt hτt (by linarith)⟩
    have hjump := h τ hτ.1 (lt_of_le_of_lt hut hτt)
    rw [← hτv, hjump, ← hleft v' hv']
    exact ih v' (le_max_left _ _) (by rw [hleft v' hv', hτv, hv]; omega)

/-- The version of `f(t, ·)`: `f(0, ·)`, the drift integral, and the version of the random part. -/
noncomputable def ver {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (f0 : ℝ → ℝ) (a b ρ : ℝ) (s : ℕ → ℝ → ℝ) (Tm : Finset ℝ) (t : ℝ≥0) (ω : Ω) (T : ℝ) : ℝ :=
  f0 T + (∫ u in (0:ℝ)..t, alpha033 a b ρ s Tm u T) +
    (S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω + Real.exp (-a * T) *
      (ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
        Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω))

section Version
variable {Ω : Type} [mΩ : MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
  (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
  (hC : ∀ i u, |s i u| ≤ C) (a b ρ : ℝ) (f0 : ℝ → ℝ) (t : ℝ≥0)
include hs hC

lemma ver_ae (T : ℝ) : ∀ᵐ ω ∂S.μ, ver S k₁ k₂ f0 a b ρ s Tm t ω T =
    curve033 S k₁ k₂ f0 a b ρ s Tm t T ω := by
  filter_upwards [Novel.SpliceCrossTermCurveProof.random Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ T t]
    with ω hω
  simp only [ver, curve033]
  rw [← hω]
  ring

lemma ver_meas (T : ℝ) : Measurable fun ω => ver S k₁ k₂ f0 a b ρ s Tm t ω T := by
  have hm : ∀ k (H : ℝ≥0 → Ω → ℝ), U4 S.ℱ S.μ H → Measurable fun ω => S.I k H t ω :=
    fun k H hH => (S.int_adapted k H hH t).mono (S.ℱ.le t) le_rfl
  have h1 := hm k₁ _ (Novel.SpliceCrossTermCurveProof.step_U4 S s hs C hC (idx033 Tm T))
  have h2 := hm k₁ _ (Novel.SpliceCrossTermCurveProof.exp_U4 S a)
  have h3 := hm k₂ _ (Novel.SpliceCrossTermCurveProof.exp_U4 S a)
  unfold ver
  exact measurable_const.add (h1.add (measurable_const.mul
    ((measurable_const.mul h2).add (measurable_const.mul h3))))

end Version

/-- The version is an element of `S⁺ + E(· − t)` plus the cross term. -/
lemma decomp {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω) (k₁ k₂ : Fin S.m)
    (Tm : Finset ℝ) (s : ℕ → ℝ → ℝ) (hs : ∀ i, Measurable (s i)) (C : ℝ)
    (hC : ∀ i u, |s i u| ≤ C) (a b ρ H : ℝ) (ha : a ≠ 0) (f0 : ℝ → ℝ)
    (E : Submodule ℝ (ℝ → ℝ)) (hE : Block033 a E) (hf0 : Fam033 Tm H E 0 f0) (t : ℝ≥0)
    (ω : Ω) : ∃ p, SPlus033 Tm H p ∧ ∃ g ∈ E, ∀ T ∈ Icc (t : ℝ) H,
      ver S k₁ k₂ f0 a b ρ s Tm t ω T = p T + g (T - t) +
        ∫ u in (0:ℝ)..t, cross033 a b ρ s Tm u T := by
  obtain ⟨p0, hp0, g0, hg0, hf0⟩ := hf0
  obtain ⟨γ₁, γ₂, hγ⟩ := Novel.SpliceCrossTermCurveProof.block a b t ha
  choose c₀ c₁ hc using fun j => Novel.SpliceCrossTermCurveProof.step Tm s hs C hC j t t.2
  set Y := ρ * b * S.I k₁ (fun u _ => Real.exp (a * u)) t ω +
    Real.sqrt (1 - ρ ^ 2) * b * S.I k₂ (fun u _ => Real.exp (a * u)) t ω with hY
  refine ⟨fun T => p0 T + ((c₀ (idx033 Tm T) + S.I k₁ (fun u _ => s (idx033 Tm T) u) t ω) +
      c₁ (idx033 Tm T) * T),
    splus_add Tm H hp0 (splus_pw Tm H (fun j => c₀ j + S.I k₁ (fun u _ => s j u) t ω) c₁),
    (fun x => g0 (x + t)) + ((γ₁ * Real.exp (-a * t) + Real.exp (-a * t) * Y) •
      (fun x => Real.exp (-a * x)) + (γ₂ * Real.exp (-(2 * a) * t)) •
      (fun x => Real.exp (-(2 * a) * x))),
    E.add_mem (hE.shift g0 hg0 t t.2) (E.add_mem (E.smul_mem _ hE.exp_one)
      (E.smul_mem _ hE.exp_two)), fun T hT => ?_⟩
  have hT0 : (0:ℝ) ≤ T := t.2.trans hT.1
  simp only [ver, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [alpha_split Tm s hs C hC a b ρ t T t.2 hT.1, hγ T, hc _ T rfl hT.1, hf0 T ⟨hT0, hT.2⟩,
    sub_add_cancel, sub_zero]
  have e1 : Real.exp (-a * t) * Real.exp (-a * (T - t)) = Real.exp (-a * T) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(2 * a) * t) * Real.exp (-(2 * a) * (T - t)) =
      Real.exp (-2 * a * T) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (-(γ₁ + Y)) * e1 - γ₂ * e2

lemma uncorrelatedSplice : uncorrelatedSpliceStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ H ha f0 hf0 hjump
  refine ⟨hf0, fun t _ => ⟨fun ω T => ver S k₁ k₂ f0 a b ρ s Tm t ω T, fun ω => ?_,
    fun T => ver_meas S k₁ k₂ Tm s hs C hC a b ρ f0 t T,
    fun T _ => ver_ae S k₁ k₂ Tm s hs C hC a b ρ f0 t T⟩⟩
  obtain ⟨p, hp, g, hg, hdec⟩ :=
    decomp S k₁ k₂ Tm s hs C hC a b ρ H ha f0 (E0 a) (e0Block a) hf0 t ω
  have hcase : ρ = 0 ∨ ∀ᵐ u ∂volume, u ∈ Icc 0 (t : ℝ) →
      ∀ v, (t : ℝ) ≤ v → s (idx033 Tm v) u = s (idx033 Tm t) u := by
    by_cases hρ : ρ = 0
    · exact Or.inl hρ
    right
    filter_upwards [(Filter.eventually_all_finset Tm).2 hjump] with u hu hu0
    exact chain Tm s u t hu0.2 fun τ hτ huτ => by
      have := (mul_eq_zero.1 (hu τ hτ ⟨hu0.1, huτ⟩)).resolve_left hρ
      unfold jump033 at this
      linarith
  obtain ⟨c₀, α, β, hX⟩ :=
    Novel.SpliceCrossTermUncorrelatedProof.uncorrelated Tm s hs C hC a b ρ ha t t.2 hcase
  refine ⟨fun T => p T + (c₀ + 0 * T), splus_add Tm H hp (splus_pw Tm H (fun _ => c₀) fun _ => 0),
    g + ((Real.exp (-a * t) * (α + β * t)) • (fun x => Real.exp (-a * x)) +
      (Real.exp (-a * t) * β) • (fun x => x * Real.exp (-a * x))),
    (E0 a).add_mem hg ((E0 a).add_mem ((E0 a).smul_mem _ (mem1 a)) ((E0 a).smul_mem _ (memx a))),
    fun T hT => ?_⟩
  beta_reduce
  rw [hdec T hT, hX T hT.1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : Real.exp (-a * t) * Real.exp (-a * (T - t)) = Real.exp (-a * T) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (-(α + β * T)) * e1

lemma enlarged : enlargedStatement := by
  intro Ω mΩ S k₁ k₂ Tm s hs C hC a b ρ H ha f0 hf0
  have hf0' : FamPlus033 a Tm H (E0 a) 0 f0 := by
    obtain ⟨p0, hp0, g0, hg0, h0⟩ := hf0
    exact ⟨p0, hp0, g0, hg0, 0, 0, fun T hT => by rw [h0 T hT]; simp⟩
  refine ⟨hf0', fun t _ => ⟨fun ω T => ver S k₁ k₂ f0 a b ρ s Tm t ω T, fun ω => ?_,
    fun T => ver_meas S k₁ k₂ Tm s hs C hC a b ρ f0 t T,
    fun T _ => ver_ae S k₁ k₂ Tm s hs C hC a b ρ f0 t T⟩⟩
  obtain ⟨p, hp, g, hg, hdec⟩ :=
    decomp S k₁ k₂ Tm s hs C hC a b ρ H ha f0 (E0 a) (e0Block a) hf0 t ω
  choose d₀ α hd using fun j => Novel.SpliceCrossTermDriftProof.cross Tm s hs C hC a b ρ ha j t t.2
  refine ⟨fun T => p T + (d₀ (idx033 Tm T) + 0 * T),
    splus_add Tm H hp (splus_pw Tm H d₀ fun _ => 0), g, hg, α,
    fun j => beta033 a b ρ s j t, fun T hT => ?_⟩
  show ver S k₁ k₂ f0 a b ρ s Tm t ω T = _
  rw [hdec T hT, hd _ T rfl hT.1]
  ring

theorem spliceCrossTermSufficiency : Standalone.SpliceCrossTermSufficiency.statement := ⟨e0Block, uncorrelatedSplice, enlarged⟩

end Novel.SpliceCrossTermSufficiencyProof

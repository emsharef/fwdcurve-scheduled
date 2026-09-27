import Standalone.MaturityShapeS1
import Novel.MaturityShapeCalendarProof
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

open Set Real MeasureTheory
open Standalone.MaturityShapeS1 Standalone.MaturityShapeRank Standalone.DiffusionMeetingCalendar
  Standalone.MaturityShapeCalendar Standalone.ListedSr3Identification
namespace Novel.MaturityShapeS1Proof

/-! ### The bracket `F(0.0023) > 0 > F(0.0024)` -/

/-- `e^x` within `|x|⁸ · 9/(8!·8)` of its degree-7 Taylor polynomial, for `|x| ≤ 1`. -/
lemma exp_near {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - ∑ i ∈ Finset.range 8, x ^ i / (Nat.factorial i)| ≤
      |x| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) :=
  Real.exp_bound hx (by norm_num)

lemma exp_bounds (x : ℝ) (hx : |x| ≤ 1) :
    ∑ i ∈ Finset.range 8, x ^ i / (Nat.factorial i) -
        |x| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ Real.exp x ∧
      Real.exp x ≤ ∑ i ∈ Finset.range 8, x ^ i / (Nat.factorial i) +
        |x| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
  have := abs_sub_le_iff.1 (exp_near hx)
  constructor <;> linarith [this.1, this.2]

lemma F_lo : 0 < Fexp 0.0023 := by
  have h1 := exp_bounds (-122 * 0.0023) (by rw [abs_le]; constructor <;> norm_num)
  have h2 := exp_bounds (-364 * 0.0023) (by rw [abs_le]; constructor <;> norm_num)
  have h3 := exp_bounds (-10 * 0.0023) (by rw [abs_le]; constructor <;> norm_num)
  have h4 := exp_bounds (-182 * 0.0023) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2 h3 h4
  norm_num [abs_of_neg] at h1 h2 h3 h4
  unfold Fexp
  norm_num
  linarith [h1.1, h2.2, h3.2, h4.1]

lemma F_hi : Fexp 0.0024 < 0 := by
  have h1 := exp_bounds (-122 * 0.0024) (by rw [abs_le]; constructor <;> norm_num)
  have h2 := exp_bounds (-364 * 0.0024) (by rw [abs_le]; constructor <;> norm_num)
  have h3 := exp_bounds (-10 * 0.0024) (by rw [abs_le]; constructor <;> norm_num)
  have h4 := exp_bounds (-182 * 0.0024) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2 h3 h4
  norm_num [abs_of_neg] at h1 h2 h3 h4
  unfold Fexp
  norm_num
  linarith [h1.2, h2.1, h3.1, h4.2]

/-! ### Exactly one positive zero -/

/-- `G(x) = e^{10x} F(x)`. -/
noncomputable def Gf (x : ℝ) : ℝ := exp (-112 * x) + exp (-172 * x) - 1 - exp (-354 * x)
/-- `H(x) = e^{112x} G′(x)`. -/
noncomputable def Hf (x : ℝ) : ℝ := -112 - 172 * exp (-60 * x) + 354 * exp (-242 * x)

lemma F_eq (x : ℝ) : Fexp x = exp (-10 * x) * Gf x := by
  unfold Fexp Gf
  simp only [mul_add, mul_sub, mul_one, ← Real.exp_add]
  ring_nf

lemma G_deriv (x : ℝ) : HasDerivAt Gf (exp (-112 * x) * Hf x) x := by
  have h1 := ((hasDerivAt_id x).const_mul (-112)).exp
  have h2 := ((hasDerivAt_id x).const_mul (-172)).exp
  have h3 := ((hasDerivAt_id x).const_mul (-354)).exp
  have := ((h1.add h2).sub_const 1).sub h3
  convert this using 1
  · funext y; simp [Gf]
  · simp only [Hf, id, mul_one]
    have e1 : exp (-112 * x) * exp (-60 * x) = exp (-172 * x) := by rw [← Real.exp_add]; ring_nf
    have e2 : exp (-112 * x) * exp (-242 * x) = exp (-354 * x) := by rw [← Real.exp_add]; ring_nf
    linear_combination (-172) * e1 + 354 * e2

lemma H_deriv (x : ℝ) :
    HasDerivAt Hf (-172 * (exp (-60 * x) * -60) + 354 * (exp (-242 * x) * -242)) x := by
  have h1 := ((hasDerivAt_id x).const_mul (-60)).exp.const_mul (-172)
  have h2 := ((hasDerivAt_id x).const_mul (-242)).exp.const_mul 354
  have := (h1.const_add (-112)).add h2
  convert this using 1
  · funext y; simp [Hf]; ring
  · simp [mul_comm]

lemma exp_two_gt : 7.38 < exp 2 := by
  have h := Real.exp_one_gt_d9
  have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

lemma exp_neg_two_lt : exp (-2) < 1 / 7.38 := by
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) exp_two_gt

lemma exp_neg_two_gt : 1 / 7.4 < exp (-2) := by
  have h := Real.exp_one_lt_d9
  have h2 : exp 2 < 7.4 := by
    have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (Real.exp_pos 2) h2

lemma H_neg {x : ℝ} (hx : 1 / 100 ≤ x) : Hf x < 0 := by
  have h1 : exp (-242 * x) ≤ exp (-2) := Real.exp_le_exp.2 (by linarith)
  have h2 := exp_neg_two_lt
  have h3 := Real.exp_pos (-60 * x)
  unfold Hf
  nlinarith

lemma H_anti : StrictAntiOn Hf (Icc 0 (1 / 100)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun y _ => (H_deriv y).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(H_deriv x).deriv]
  have e : exp (-242 * x) = exp (-60 * x) * exp (-182 * x) := by rw [← Real.exp_add]; ring_nf
  have h1 : exp (-2) ≤ exp (-182 * x) := Real.exp_le_exp.2 (by linarith [hx.2])
  have h2 := exp_neg_two_gt
  have h3 := Real.exp_pos (-60 * x)
  rw [e]
  nlinarith [mul_pos h3 (show (0:ℝ) < 1 / 7.4 by norm_num)]

/-- The zero `x₁` of `H`, where `G` turns. -/
lemma H_zero : ∃ x1, 0 < x1 ∧ x1 < 1 / 100 ∧ (∀ x, 0 ≤ x → x < x1 → 0 < Hf x) ∧
    ∀ x, x1 < x → Hf x < 0 := by
  have hc : ContinuousOn Hf (Icc 0 (1 / 100)) :=
    fun y _ => (H_deriv y).continuousAt.continuousWithinAt
  have h0 : Hf 0 = 70 := by simp [Hf]; norm_num
  have hb := H_neg (le_refl (1 / 100 : ℝ))
  obtain ⟨x1, hx1, hH⟩ := intermediate_value_Icc' (by norm_num) hc ⟨hb.le, by rw [h0]; norm_num⟩
  have hx1a : 0 < x1 := lt_of_le_of_ne hx1.1 (fun h => by subst h; rw [h0] at hH; norm_num at hH)
  have hx1b : x1 < 1 / 100 := lt_of_le_of_ne hx1.2 (fun h => by subst h; linarith)
  refine ⟨x1, hx1a, hx1b, fun x hx0 hx => ?_, fun x hx => ?_⟩
  · rw [← hH]
    exact H_anti ⟨hx0, (hx.trans hx1b).le⟩ ⟨hx1.1, hx1.2⟩ hx
  · by_cases h : x ≤ 1 / 100
    · rw [← hH]
      exact H_anti ⟨hx1.1, hx1.2⟩ ⟨hx1a.le.trans hx.le, h⟩ hx
    · exact H_neg (not_le.1 h).le

lemma rootS : rootStatement := by
  obtain ⟨x1, hx1, -, hpos, hneg⟩ := H_zero
  have hGc : Continuous Gf := continuous_iff_continuousAt.2 fun y => (G_deriv y).continuousAt
  have hGmono : StrictMonoOn Gf (Icc 0 x1) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hGc.continuousOn fun x hx => by
      rw [interior_Icc] at hx
      rw [(G_deriv x).deriv]
      exact mul_pos (Real.exp_pos _) (hpos x hx.1.le hx.2)
  have hGanti : StrictAntiOn Gf (Ici x1) :=
    strictAntiOn_of_deriv_neg (convex_Ici _) hGc.continuousOn fun x hx => by
      rw [interior_Ici] at hx
      rw [(G_deriv x).deriv]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hneg x hx)
  have hG0 : Gf 0 = 0 := by simp [Gf]
  have hpos' : ∀ y, 0 < y → y ≤ x1 → 0 < Gf y := fun y hy hy1 => by
    rw [← hG0]; exact hGmono ⟨le_rfl, hx1.le⟩ ⟨hy.le, hy1⟩ hy
  have hFz : ∀ y, Fexp y = 0 ↔ Gf y = 0 := fun y => by
    rw [F_eq]; exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (Real.exp_pos _).ne', fun h => by rw [h, mul_zero]⟩
  have hbig : ∀ y, 0 < y → Fexp y = 0 → x1 < y := fun y hy hz => by
    by_contra h; push Not at h
    exact (hpos' y hy h).ne' ((hFz y).1 hz)
  have hFc : Continuous Fexp := by unfold Fexp; fun_prop
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc' (show (0.0023 : ℝ) ≤ 0.0024 by norm_num)
    hFc.continuousOn ⟨F_hi.le, F_lo.le⟩
  have hxa : 0.0023 < x := lt_of_le_of_ne hx.1 (fun h => by subst h; exact F_lo.ne' hFx)
  have hxb : x < 0.0024 := lt_of_le_of_ne hx.2 (fun h => by subst h; exact F_hi.ne hFx)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  refine ⟨x, ⟨hx0, hFx⟩, fun y hy hFy => ?_, hxa, hxb⟩
  exact hGanti.injOn (mem_Ici.2 (hbig y hy hFy).le) (mem_Ici.2 (hbig x hx0 hFx).le)
    (((hFz y).1 hFy).trans ((hFz x).1 hFx).symm)

/-! ### The diagonal of `Λ̃_E(𝒫_8)` -/

section
variable {κ : ℝ} (hκ : 0 < κ)
include hκ

lemma beta_exp (n : Fin 25) (s : ℝ) :
    beta (phiExp κ) n s ^ 2 = gK κ * exp (-2 * κ * (aW n - s)) := by
  have hw : bW n - aW n = 91 / 360 := by
    simp only [aW, bW, bDay, yr]; push_cast; ring
  have hint : ∫ T in aW n..bW n, phiExp κ s T =
      exp (κ * s) * ((exp (-κ * aW n) - exp (-κ * bW n)) / κ) := by
    have e : ∀ T, phiExp κ s T = exp (κ * s) * exp (-κ * T) := fun T => by
      unfold phiExp; rw [← Real.exp_add]; ring_nf
    simp only [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun x => exp x) (neg_ne_zero.2 hκ.ne'), integral_exp]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hb : exp (-κ * bW n) = exp (-κ * aW n) * exp (-κ * (91 / 360)) := by
    rw [← Real.exp_add, ← hw]; ring_nf
  unfold beta gK
  rw [hint, hw, hb]
  have e3 : exp (-2 * κ * (aW n - s)) = (exp (κ * s) * exp (-κ * aW n)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  rw [e3]
  field_simp

omit hκ in
/-- A set between `(c, S)` and `[c, S]` is `(c, S]` up to a null set. -/
lemma ae_Ioc {X : Set ℝ} (hX : MeasurableSet X) {c S : ℝ} (h1 : Ioo c S ⊆ X) (h2 : X ⊆ Icc c S) :
    X =ᵐ[volume] Ioc c S := by
  have hXI : X =ᵐ[volume] Icc c S := ae_eq_of_subset_of_measure_ge h2
    ((Real.volume_Icc.trans Real.volume_Ioo.symm).le.trans (measure_mono h1))
    hX.nullMeasurableSet measure_Icc_lt_top.ne
  exact hXI.trans Ioc_ae_eq_Icc.symm

/-- `D_{n,p} = (g/(2κ))(e^{−2κ(a_n − S_n)} − e^{−2κ(a_n − c_p)})` when `0 ≤ c_p ≤ S_n ≤ c_{p+1}`. -/
lemma D_exp {P : ℕ} (c : Fin (P + 1) → ℝ) (n : Fin 25) (p : Fin P) (h0 : 0 ≤ c p.castSucc)
    (h1 : c p.castSucc ≤ SCal n) (h2 : SCal n ≤ c p.succ) :
    Dsh (phiExp κ) c n p = gK κ / (2 * κ) *
      (exp (-2 * κ * (aW n - SCal n)) - exp (-2 * κ * (aW n - c p.castSucc))) := by
  have hX : Ioc 0 (SCal n) ∩ Ico (c p.castSucc) (c p.succ) =ᵐ[volume] Ioc (c p.castSucc) (SCal n) := by
    refine ae_Ioc (measurableSet_Ioc.inter measurableSet_Ico) (fun s hs => ?_) (fun s hs => ?_)
    · exact ⟨⟨h0.trans_lt hs.1, hs.2.le⟩, hs.1.le, hs.2.trans_le h2⟩
    · exact ⟨hs.2.1, hs.1.2⟩
  unfold Dsh
  rw [setIntegral_congr_set hX, ← intervalIntegral.integral_of_le h1]
  simp only [beta_exp hκ]
  have hd : ∀ s ∈ uIcc (c p.castSucc) (SCal n), HasDerivAt
      (fun s => gK κ * exp (-2 * κ * (aW n - s)) / (2 * κ)) (gK κ * exp (-2 * κ * (aW n - s))) s :=
    fun s _ => by
      have := ((((hasDerivAt_id s).const_sub (aW n)).const_mul (-2 * κ)).exp.const_mul
        (gK κ)).div_const (2 * κ)
      convert this using 1
      · simp only [id]
      · simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s => gK κ * exp (-2 * κ * (aW n - s))).intervalIntegrable _ _)]
  ring

lemma gK_pos : 0 < gK κ := by
  unfold gK
  have : 0 < 1 - exp (-κ * (91 / 360)) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by nlinarith)
  positivity

omit hκ in
lemma cell_days : ∀ k : Fin 8,
    cEight (Fin.castSucc k) ≤ gaps.getD (freeIdx k).val 0 ∧
      gaps.getD ((freeIdx k).val + 1) 0 ≤ cEight (Fin.succ k) := by decide

lemma diag_formula (k : Fin 8) : lamE8 (phiExp κ) k k = gK κ / (2 * κ) *
    ((exp (-2 * κ * (aW (freeIdx k).succ - SCal (freeIdx k).succ)) -
        exp (-2 * κ * (aW (freeIdx k).succ - cells cEight k.castSucc))) -
      (exp (-2 * κ * (aW (freeIdx k).castSucc - SCal (freeIdx k).castSucc)) -
        exp (-2 * κ * (aW (freeIdx k).castSucc - cells cEight k.castSucc)))) := by
  obtain ⟨d1, d2⟩ := cell_days k
  have hc0 : 0 ≤ cells cEight k.castSucc := by
    simp only [cells, yr]
    have : (2 : ℕ) ≤ cEight k.castSucc := by revert k; decide
    have : (2 : ℝ) ≤ (cEight k.castSucc : ℝ) := by exact_mod_cast this
    linarith
  have hcs : cells cEight k.castSucc ≤ SCal (freeIdx k).castSucc := by
    rw [Novel.MaturityShapeCalendarProof.SCal_castSucc]
    exact Novel.DiffusionMeetingCalendarProof.yr_le.2 d1
  have hle : SCal (freeIdx k).castSucc ≤ SCal (freeIdx k).succ :=
    Novel.DiffusionMeetingCalendarProof.hS.monotone (Fin.castSucc_le_succ _)
  have hsc : SCal (freeIdx k).succ ≤ cells cEight k.succ := by
    rw [Novel.MaturityShapeCalendarProof.SCal_succ]
    exact Novel.DiffusionMeetingCalendarProof.yr_le.2 d2
  simp only [lamE8, lamT]
  rw [D_exp hκ _ _ _ hc0 (hcs.trans hle) hsc, D_exp hκ _ _ _ hc0 hcs (hle.trans hsc)]
  ring

end

lemma diagonalS : diagonalStatement := by
  intro κ hκ
  have hc : 0 < gK κ / (2 * κ) := div_pos (gK_pos hκ) (by linarith)
  refine ⟨fun k hk4 hk6 => ?_, ?_, ?_⟩
  · obtain ⟨ha, -⟩ := Novel.MaturityShapeCalendarProof.same_window k hk4 hk6
    have haW : aW (freeIdx k).succ = aW (freeIdx k).castSucc := by simp only [aW, ha]
    have hlt : SCal (freeIdx k).castSucc < SCal (freeIdx k).succ :=
      Novel.DiffusionMeetingCalendarProof.hS Fin.castSucc_lt_succ
    rw [diag_formula hκ, haW]
    have : exp (-2 * κ * (aW (freeIdx k).castSucc - SCal (freeIdx k).castSucc)) <
        exp (-2 * κ * (aW (freeIdx k).castSucc - SCal (freeIdx k).succ)) :=
      Real.exp_lt_exp.2 (by nlinarith)
    apply mul_pos hc
    linarith
  · rw [diag_formula hκ]
    simp (config := {decide := true}) [freeIdx, aW, aDay, quarterStarts, SCal, gaps, expiries, t0,
      cells, cEight, yr]
    unfold Fexp
    ring_nf
    simp
  · rw [diag_formula hκ]
    simp (config := {decide := true}) [freeIdx, aW, aDay, quarterStarts, SCal, gaps, expiries, t0,
      cells, cEight, yr]
    unfold Fexp
    ring_nf
    simp

lemma identifyS : identifyStatement := by
  obtain ⟨x, ⟨hx0, hFx⟩, huniq, hxa, hxb⟩ := rootS
  refine ⟨360 * x, by linarith, by linarith, fun κ hκ => ?_⟩
  obtain ⟨hsame, h4, h6⟩ := diagonalS κ hκ
  have hc : 0 < gK κ / (2 * κ) := div_pos (gK_pos hκ) (by linarith)
  rw [Novel.MaturityShapeCalendarProof.panel_iff _ (Novel.MaturityShapeCalendarProof.Dsh_zero _ _),
    Novel.MaturityShapeCalendarProof.lamTE_iff, Novel.MaturityShapeCalendarProof.lamE8_iff]
  have hF : (∀ k, lamE8 (phiExp κ) k k ≠ 0) ↔ Fexp (κ / 360) ≠ 0 := by
    constructor
    · intro h hF0
      exact h 4 (by rw [h4, hF0, mul_zero])
    · intro hF0 k
      by_cases hk4 : k = 4
      · subst hk4; rw [h4]; exact mul_ne_zero hc.ne' hF0
      by_cases hk6 : k = 6
      · subst hk6; rw [h6]; exact mul_ne_zero hc.ne' hF0
      exact (hsame k hk4 hk6).ne'
  rw [hF]
  constructor
  · intro hF0 h
    apply hF0
    rw [h, show 360 * x / 360 = x by ring]
    exact hFx
  · intro hne hF0
    apply hne
    have := huniq (κ / 360) (by positivity) hF0
    linarith

lemma windowS : windowStatement := by
  intro κ hκ n s
  refine ⟨beta_exp hκ n s, fun n' hlt => ?_⟩
  rw [beta_exp hκ, beta_exp hκ]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by nlinarith)) (gK_pos hκ)

theorem maturityShapeS1 : Standalone.MaturityShapeS1.statement :=
  ⟨diagonalS, rootS, identifyS, windowS⟩

end Novel.MaturityShapeS1Proof

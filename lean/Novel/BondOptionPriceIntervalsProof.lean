import Standalone.BondOptionPriceIntervals
import Novel.BondOptionMeetingVariancesProof
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

open Set Matrix
open Standalone.BondOptionPriceIntervals
namespace Novel.BondOptionPriceIntervalsProof
variable {N : ℕ} (l : Fin (N+1) → ℝ) (u : Fin (N+1) → WithTop ℝ)

lemma le_L {i n : Fin (N+1)} (h : i ≤ n) : l i ≤ L l n :=
  Finset.le_sup' l (by simpa using h)

lemma L_le {n : Fin (N+1)} {a : ℝ} (h : ∀ i ≤ n, l i ≤ a) : L l n ≤ a := by
  exact Finset.sup'_le _ _ fun i hi => h i (by simpa using hi)

lemma R_le {i n : Fin (N+1)} (h : n ≤ i) : R u n ≤ u i :=
  Finset.inf'_le u (by simpa using h)

lemma le_R {n : Fin (N+1)} {a : WithTop ℝ} (h : ∀ i, n ≤ i → a ≤ u i) : a ≤ R u n := by
  exact Finset.le_inf' _ _ fun i hi => h i (by simpa using hi)

lemma L_mono : Monotone (L l) := fun _ _ hij =>
  L_le l fun _ hki => le_L l (hki.trans hij)

lemma R_mono : Monotone (R u) := fun _ _ hij =>
  le_R u fun _ hjk => R_le u (hij.trans hjk)

lemma L_zero (hl : l 0 = 0) : L l 0 = 0 := by
  apply le_antisymm
  · apply L_le l
    intro i hi
    have : i = 0 := le_antisymm hi (Fin.zero_le _)
    simp [this, hl]
  · simpa [hl] using le_L l (i := 0) (n := 0) le_rfl

lemma propagated (z : Fin (N+1) → ℝ) :
    feasible l u z ↔ z 0 = 0 ∧ Monotone z ∧
      ∀ i, L l i ≤ z i ∧ (z i : WithTop ℝ) ≤ R u i := by
  constructor
  · rintro ⟨hz, hm, hb⟩
    refine ⟨hz, hm, fun i => ⟨?_, ?_⟩⟩
    · exact L_le l fun j hji => (hb j).1.trans (hm hji)
    · exact le_R u fun j hij => (WithTop.coe_le_coe.2 (hm hij)).trans (hb j).2
  · rintro ⟨hz, hm, hb⟩
    exact ⟨hz, hm, fun i => ⟨(le_L l le_rfl).trans (hb i).1,
      (hb i).2.trans (R_le u le_rfl)⟩⟩

lemma feasible_L (hl : l 0 = 0) (hc : compatible l u) : feasible l u (L l) :=
  (propagated l u _).2 ⟨L_zero l hl, L_mono l, fun i => ⟨le_rfl, hc i⟩⟩

lemma feasible_iff (hl : l 0 = 0) : (∃ z, feasible l u z) ↔ compatible l u := by
  constructor
  · rintro ⟨z, hz⟩ i
    have h := ((propagated l u z).1 hz).2.2 i
    exact (WithTop.coe_le_coe.2 h.1).trans h.2
  · intro hc
    exact ⟨L l, feasible_L l u hl hc⟩

lemma sub_le_upper_iff (a r : ℝ) (b : WithTop ℝ) :
    ((a-r : ℝ) : WithTop ℝ) ≤ b ↔ (a : WithTop ℝ) ≤ b + (r : WithTop ℝ) := by
  by_cases hb : b = ⊤
  · simp [hb]
  · lift b to ℝ using hb
    simp only [← WithTop.coe_add, WithTop.coe_le_coe]
    exact sub_le_iff_le_add

/-- A finite witness for prescribed adjacent cumulative sums. -/
lemma adjacent_witness (hl : l 0 = 0) (hu : u 0 = 0) (hc : compatible l u)
    (n : Fin N) (x y : ℝ) (hxy : x ≤ y)
    (hx : L l n.castSucc ≤ x) (hy : L l n.succ ≤ y)
    (hxu : (x : WithTop ℝ) ≤ R u n.castSucc) (hyu : (y : WithTop ℝ) ≤ R u n.succ) :
    ∃ z, feasible l u z ∧ z n.castSucc = x ∧ z n.succ = y := by
  let f : Fin (N+1) → ℝ := fun i => if i < n.castSucc then 0 else if i = n.castSucc then x else y
  let z : Fin (N+1) → ℝ := fun i => max (L l i) (f i)
  have hL0 := L_zero l hl
  have hL (i : Fin (N+1)) : 0 ≤ L l i := by rw [← hL0]; exact L_mono l (Fin.zero_le _)
  have hx0 : 0 ≤ x := (hL _).trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hmono : Monotone f := by
    intro i j hij
    dsimp [f]
    split_ifs <;> first | assumption | exact le_rfl | omega
  have hp0 : n.castSucc = 0 → x = 0 := by
    intro hp
    have hb : (x : WithTop ℝ) ≤ 0 := by
      calc
        (x : WithTop ℝ) ≤ R u n.castSucc := hxu
        _ ≤ u 0 := R_le u (by simp [hp])
        _ = 0 := hu
    have : x ≤ 0 := by exact_mod_cast hb
    exact le_antisymm this hx0
  have hz0 : z 0 = 0 := by
    dsimp [z, f]
    rw [hL0]
    split_ifs with h h'
    · simp
    · simp [hp0 h'.symm]
    · have hp : n.castSucc = 0 := le_antisymm (not_lt.1 h) (Fin.zero_le _)
      exact (h' hp.symm).elim
  have hbound (i) : (z i : WithTop ℝ) ≤ R u i := by
    dsimp [z]
    rw [max_le_iff]
    refine ⟨hc i, ?_⟩
    dsimp [f]
    split_ifs with hi hi'
    · exact (WithTop.coe_le_coe.2 (hL i)).trans (hc i)
    · simpa [hi'] using hxu
    · have hni : n.succ ≤ i := by
        have hp : n.castSucc < i := lt_of_le_of_ne (not_lt.1 hi) (Ne.symm hi')
        exact Nat.succ_le_of_lt hp
      exact hyu.trans (R_mono u hni)
  refine ⟨z, (propagated l u z).2 ⟨hz0, (L_mono l).max hmono,
    fun i => ⟨le_max_left _ _, hbound i⟩⟩, ?_, ?_⟩
  · simp [z, f, max_eq_right hx]
  · have hn : ¬ n.succ < n.castSucc := not_lt_of_ge (show n.castSucc < n.succ from Fin.castSucc_lt_succ).le
    have hne : n.succ ≠ n.castSucc := ne_of_gt (show n.castSucc < n.succ from Fin.castSucc_lt_succ)
    simp [z, f, hn, hne, max_eq_right hy]

lemma projection (hl : l 0 = 0) (hu : u 0 = 0) (hc : compatible l u)
    (n : Fin N) (r : ℝ) :
    (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = r) ↔
      0 ≤ r ∧ (L l n.succ : WithTop ℝ) ≤ R u n.castSucc + (r : WithTop ℝ) ∧
      (L l n.castSucc + r : ℝ) ≤ R u n.succ := by
  constructor
  · rintro ⟨z, hz, hr⟩
    obtain ⟨_, hm, hb⟩ := (propagated l u z).1 hz
    have hzn : z n.castSucc ≤ z n.succ := hm (show n.castSucc < n.succ from Fin.castSucc_lt_succ).le
    refine ⟨by linarith, ?_, ?_⟩
    · apply (sub_le_upper_iff _ _ _).1
      exact (WithTop.coe_le_coe.2 (by linarith [(hb n.succ).1])).trans (hb n.castSucc).2
    · exact (WithTop.coe_le_coe.2 (by linarith [(hb n.castSucc).1])).trans (hb n.succ).2
  · rintro ⟨hr, hlo, hhi⟩
    let x := max (L l n.castSucc) (L l n.succ - r)
    have hx : L l n.castSucc ≤ x := le_max_left _ _
    have hy : L l n.succ ≤ x + r := by have := le_max_right (L l n.castSucc) (L l n.succ-r); dsimp [x]; linarith
    have hxu : (x : WithTop ℝ) ≤ R u n.castSucc := by
      change max (L l n.castSucc : WithTop ℝ) ((L l n.succ-r : ℝ) : WithTop ℝ) ≤ _
      rw [max_le_iff]
      exact ⟨hc _, (sub_le_upper_iff _ _ _).2 hlo⟩
    have hyu : ((x+r : ℝ) : WithTop ℝ) ≤ R u n.succ := by
      have heq : x+r = max (L l n.castSucc+r) (L l n.succ) := by dsimp [x]; rw [← max_add_add_right]; congr 1; ring
      rw [heq, WithTop.coe_max, max_le_iff]
      exact ⟨hhi, hc _⟩
    obtain ⟨z, hz, hxz, hyz⟩ := adjacent_witness l u hl hu hc n x (x+r)
      (by linarith) hx hy hxu hyu
    exact ⟨z, hz, by rw [hxz, hyz]; ring⟩

lemma projection_endpoints (hl : l 0 = 0) (hu : u 0 = 0) (hc : compatible l u)
    (n : Fin N) (r : ℝ) :
    (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = r) ↔
      lower0165 l u n ≤ r ∧ (r : WithTop ℝ) ≤ upper0166 l u n := by
  rw [projection l u hl hu hc, lower0165, upper0166]
  have hupper : ((L l n.castSucc+r : ℝ) : WithTop ℝ) ≤ R u n.succ ↔
      (r : WithTop ℝ) ≤ R u n.succ + ((-L l n.castSucc : ℝ) : WithTop ℝ) := by
    simpa [add_comm] using sub_le_upper_iff r (-L l n.castSucc) (R u n.succ)
  rw [hupper]
  by_cases hb : R u n.castSucc = ⊤
  · simp [hb]
  · generalize heq : R u n.castSucc = B at *
    lift B to ℝ using hb
    simp only [WithTop.coe_ne_top, ite_false, WithTop.untopD_coe, ← WithTop.coe_add,
      WithTop.coe_le_coe, max_le_iff]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, by linarith⟩, h₃⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, by linarith, h₃⟩

lemma endpoints (hl : l 0 = 0) (hu : u 0 = 0) (hc : compatible l u) (n : Fin N) :
    (∃ z, feasible l u z ∧ z n.succ - z n.castSucc = lower0165 l u n) ∧
    (∀ b : ℝ, upper0166 l u n = b → ∃ z, feasible l u z ∧ z n.succ - z n.castSucc = b) ∧
    (upper0166 l u n = ⊤ → ∀ M : ℝ,
      ∃ z, feasible l u z ∧ M < z n.succ - z n.castSucc) := by
  have he := projection_endpoints l u hl hu hc n
  let r₀ := L l n.succ - L l n.castSucc
  have hr₀ := (he r₀).1 ⟨L l, feasible_L l u hl hc, rfl⟩
  refine ⟨(he _).2 ⟨le_rfl, (WithTop.coe_le_coe.2 hr₀.1).trans hr₀.2⟩, ?_, ?_⟩
  · intro b hb
    apply (he b).2
    have hb' : r₀ ≤ b := by simpa [hb] using hr₀.2
    exact ⟨hr₀.1.trans hb', by rw [hb]⟩
  · intro htop M
    let r := max (lower0165 l u n) (M+1)
    obtain ⟨z, hz, hzr⟩ := (he r).2 ⟨le_max_left _ _, by simp [htop]⟩
    exact ⟨z, hz, by rw [hzr]; have := le_max_right (lower0165 l u n) (M+1); dsimp [r]; linarith⟩

section Pricing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open Standalone.BondOptionMeetingVariances
open BondOptionMeetingVariancesProof

lemma Φ_integral (x : ℝ) : Φ x = ∫ y in Iic x, gaussianPDFReal 0 1 y := by
  rw [Φ, cdf_eq_real]
  change ENNReal.toReal ((gaussianReal 0 1) (Iic x)) = _
  rw [gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg fun y => gaussianPDFReal_nonneg 0 1 y)

lemma φ_eq (x : ℝ) : φ0167 x = gaussianPDFReal 0 1 x := by
  simp [φ0167, gaussianPDFReal, div_eq_mul_inv, mul_comm]

lemma φ_pos (x : ℝ) : 0 < φ0167 x := by rw [φ_eq]; exact gaussianPDFReal_pos _ _ _ (by norm_num)

lemma Φ_deriv (x : ℝ) : HasDerivAt Φ (φ0167 x) x := by
  have hc : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have heq : Φ = fun y => Φ 0 + ∫ s in (0:ℝ)..y, gaussianPDFReal 0 1 s := by
    funext y
    rw [Φ_integral y, Φ_integral 0,
      ← intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  rw [heq, φ_eq]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousAt).const_add _

lemma Φ_continuous : Continuous Φ := continuous_iff_continuousAt.2 fun x => (Φ_deriv x).continuousAt

lemma Φ_pos (x : ℝ) : 0 < Φ x :=
  lt_of_le_of_lt (cdf_nonneg _ _) (Φ_strictMono (show x-1 < x by linarith))

lemma Φ_surj {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ∃ x, Φ x = p := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (show (atBot : Filter ℝ) ≤ 𝓟 (univ : Set ℝ) by simp)
    (show (atTop : Filter ℝ) ≤ 𝓟 (univ : Set ℝ) by simp)
    Φ_continuous.continuousOn (tendsto_cdf_atBot (gaussianReal 0 1))
    (tendsto_cdf_atTop (gaussianReal 0 1)) hp
  simpa using h

lemma Φ_inv {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (Function.invFun Φ p) = p :=
  Function.invFun_eq (Φ_surj hp)

lemma inv_Φ (x : ℝ) : Function.invFun Φ (Φ x) = x := Function.leftInverse_invFun Φ_strictMono.injective x

lemma inv_mono : StrictMonoOn (Function.invFun Φ) (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  apply Φ_strictMono.lt_iff_lt.1
  simpa [Φ_inv ha, Φ_inv hb] using hab

lemma inv_continuous {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt (Function.invFun Φ) p := by
  apply inv_mono.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hp)
  have heq : (Function.invFun Φ) '' Ioo (0:ℝ) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨Φ x, ⟨Φ_pos x, Φ_lt_one x⟩, inv_Φ x⟩
  simp [heq]

lemma inv_deriv {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (Function.invFun Φ) (φ0167 (Function.invFun Φ p))⁻¹ p := by
  apply (Φ_deriv _).of_local_left_inverse (inv_continuous hp) (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact Φ_inv hq

lemma y_nonneg {c : ℝ} (hc : c ∈ Ico (0:ℝ) 1) : 0 ≤ y0167 c := by
  have hp : (1+c)/2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  apply Φ_strictMono.le_iff_le.1
  change Φ 0 ≤ Φ (Function.invFun Φ ((1+c)/2))
  rw [Φ_zero, Φ_inv hp]
  linarith [hc.1]

lemma y_deriv {c : ℝ} (hc : c ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt y0167 (1/(2*φ0167 (y0167 c))) c := by
  have hp : (1+c)/2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  convert (inv_deriv hp).comp c (((hasDerivAt_id c).const_add 1).div_const 2) using 1
  · rfl
  · change 1/(2*φ0167 (y0167 c)) = (φ0167 (y0167 c))⁻¹ * (1/2)
    ring

lemma H_deriv {c : ℝ} (hc : c ∈ Ioo (-1:ℝ) 1) (h : ℝ) :
    HasDerivAt (H0162 h) (k0167 h c) c := by
  convert (((y_deriv hc).pow 2).const_mul 4).div_const (h^2) using 1
  · rfl
  · dsimp [k0167]; ring

lemma P_bounds {h z : ℝ} (hh : 0 < h) (_hz : 0 ≤ z) : P0161 h z ∈ Ico (0:ℝ) 1 := by
  have hp := Φ_strictMono.monotone (show 0 ≤ h*Real.sqrt z/2 by positivity)
  rw [Φ_zero] at hp
  have hq := Φ_lt_one (h*Real.sqrt z/2)
  change 0 ≤ 2*Φ (h*Real.sqrt z/2)-1 ∧ 2*Φ (h*Real.sqrt z/2)-1 < 1
  constructor <;> linarith

lemma P_mono {h : ℝ} (hh : 0 < h) : StrictMonoOn (P0161 h) (Ici (0:ℝ)) := by
  intro a ha b hb hab
  have hs := Real.sqrt_lt_sqrt ha hab
  have hp := Φ_strictMono (show h*Real.sqrt a/2 < h*Real.sqrt b/2 by nlinarith)
  change 2*Φ (h*Real.sqrt a/2)-1 < 2*Φ (h*Real.sqrt b/2)-1
  linarith

lemma H_P {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) : H0162 h (P0161 h z) = z := by
  have hy : y0167 (P0161 h z) = h*Real.sqrt z/2 := by
    change Function.invFun Φ ((1+(2*Φ (h*Real.sqrt z/2)-1))/2) = _
    rw [show (1+(2*Φ (h*Real.sqrt z/2)-1))/2 = Φ (h*Real.sqrt z/2) by ring, inv_Φ]
  rw [H0162, hy]
  have hs := Real.sq_sqrt hz
  field_simp
  nlinarith

lemma H_nonneg (h c : ℝ) : 0 ≤ H0162 h c := by unfold H0162; positivity

lemma P_H {h c : ℝ} (hh : 0 < h) (hc : c ∈ Ico (0:ℝ) 1) : P0161 h (H0162 h c) = c := by
  have hp : (1+c)/2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hy := y_nonneg hc
  have hs : Real.sqrt (H0162 h c) = 2*y0167 c/h := by
    apply (Real.sqrt_eq_iff_eq_sq (H_nonneg h c) (by positivity)).2
    unfold H0162
    ring
  unfold P0161
  rw [hs]
  have heq : h*(2*y0167 c/h)/2 = y0167 c := by field_simp
  rw [heq]
  change 2*Φ (Function.invFun Φ ((1+c)/2))-1 = c
  rw [Φ_inv hp]
  ring

lemma H_mono {h : ℝ} (hh : 0 < h) : StrictMonoOn (H0162 h) (Ico (0:ℝ) 1) := by
  intro a ha b hb hab
  apply (P_mono hh).lt_iff_lt (H_nonneg h a) (H_nonneg h b) |>.1
  simpa [P_H hh ha, P_H hh hb] using hab

lemma price_interval {h a b z : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (ha1 : a < 1) (hz : 0 ≤ z) :
    (a ≤ P0161 h z ∧ P0161 h z ≤ b) ↔
      H0162 h a ≤ z ∧ (b < 1 → z ≤ H0162 h b) := by
  have hP := P_bounds hh hz
  have hlo : a ≤ P0161 h z ↔ H0162 h a ≤ z := by
    simpa only [H_P hh hz] using ((H_mono hh).le_iff_le ⟨ha, ha1⟩ hP).symm
  rw [hlo]
  by_cases hb1 : b < 1
  · have hb0 : 0 ≤ b := ha.trans hab
    have hhi : P0161 h z ≤ b ↔ z ≤ H0162 h b := by
      simpa only [H_P hh hz] using ((H_mono hh).le_iff_le hP ⟨hb0, hb1⟩).symm
    simp only [hb1, forall_true_left, hhi]
  · have : b = 1 := le_antisymm hb (not_lt.1 hb1)
    simp [this, hP.2.le]

lemma φ_antitone : AntitoneOn φ0167 (Ici (0:ℝ)) := by
  intro x hx y hy hxy
  dsimp [φ0167]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (add_nonneg hx hy)]

lemma y_mono : StrictMonoOn y0167 (Ico (0:ℝ) 1) := by
  intro a ha b hb hab
  exact inv_mono ⟨by linarith [ha.1], by linarith [ha.2]⟩
    ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)

lemma k_nonneg (h : ℝ) {c : ℝ} (hc : c ∈ Ico (0:ℝ) 1) : 0 ≤ k0167 h c := by
  unfold k0167
  exact div_nonneg (mul_nonneg (by norm_num) (y_nonneg hc)) (mul_nonneg (sq_nonneg _) (φ_pos _).le)

lemma k_mono (h : ℝ) : MonotoneOn (k0167 h) (Ico (0:ℝ) 1) := by
  intro a ha b hb hab
  have hy := y_mono.monotoneOn ha hb hab
  have hp := φ_antitone (y_nonneg ha) (y_nonneg hb) hy
  unfold k0167
  by_cases hh : h = 0
  · simp [hh]
  · exact div_le_div₀ (mul_nonneg (by norm_num) (y_nonneg hb)) (by linarith)
      (mul_pos (sq_pos_of_ne_zero hh) (φ_pos _)) (mul_le_mul_of_nonneg_left hp (sq_nonneg h))

lemma H_lipschitz {h β : ℝ} (_hh : 0 < h) (hβ : β ∈ Ico (0:ℝ) 1)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) β) (hb : b ∈ Icc (0:ℝ) β) :
    |H0162 h b - H0162 h a| ≤ k0167 h β * |b-a| := by
  have hsub : Icc (0:ℝ) β ⊆ Ico (0:ℝ) 1 := fun _ hc => ⟨hc.1, hc.2.trans_lt hβ.2⟩
  have hd (c) (hc : c ∈ Icc (0:ℝ) β) : HasDerivWithinAt (H0162 h) (k0167 h c) (Icc 0 β) c :=
    (H_deriv ⟨by linarith [hc.1], (hsub hc).2⟩ h).hasDerivWithinAt
  have hbound (c) (hc : c ∈ Icc (0:ℝ) β) : ‖k0167 h c‖ ≤ k0167 h β := by
    rw [Real.norm_eq_abs, abs_of_nonneg (k_nonneg h (hsub hc))]
    exact k_mono h (hsub hc) hβ hc.2
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) β).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound ha hb

lemma H_zero (h : ℝ) : H0162 h 0 = 0 := by
  have hy : y0167 0 = 0 := by
    change Function.invFun Φ ((1+0)/2) = 0
    rw [show ((1:ℝ)+0)/2 = Φ 0 by rw [Φ_zero]; norm_num, inv_Φ]
  simp [H0162, hy]

lemma k_zero (h : ℝ) : k0167 h 0 = 0 := by
  have hy : y0167 0 = 0 := by
    change Function.invFun Φ ((1+0)/2) = 0
    rw [show ((1:ℝ)+0)/2 = Φ 0 by rw [Φ_zero]; norm_num, inv_Φ]
  simp [k0167, hy]

lemma H_unbounded {h : ℝ} (hh : 0 < h) (M : ℝ) :
    ∃ c ∈ Ico (0:ℝ) 1, M < H0162 h c := by
  let z := max 0 (M+1)
  refine ⟨P0161 h z, P_bounds hh (le_max_left _ _), ?_⟩
  rw [H_P hh (le_max_left _ _)]
  have := le_max_right (0:ℝ) (M+1)
  linarith

lemma H_tendsto {h : ℝ} (hh : 0 < h) : Tendsto (H0162 h) (𝓝[<] (1:ℝ)) atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨a, ha, hM⟩ := H_unbounded hh M
  filter_upwards [show ∀ᶠ c in 𝓝[<] (1:ℝ), a < c from
    nhdsWithin_le_nhds (Ioi_mem_nhds ha.2), self_mem_nhdsWithin] with c hac hc
  exact hM.le.trans ((H_mono hh).monotoneOn ha ⟨ha.1.trans hac.le, hc⟩ hac.le)

lemma y_tendsto : Tendsto y0167 (𝓝[<] (1:ℝ)) atTop := by
  apply tendsto_atTop.2
  intro M
  let a := max 0 (2*Φ M-1)
  have ha : a < 1 := max_lt (by norm_num) (by have := Φ_lt_one M; linarith)
  filter_upwards [show ∀ᶠ c in 𝓝[<] (1:ℝ), a < c from
    nhdsWithin_le_nhds (Ioi_mem_nhds ha), self_mem_nhdsWithin] with c hac hc
  have hc0 : 0 ≤ c := (le_max_left _ _).trans hac.le
  have hp : (1+c)/2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith [show c < 1 from hc]⟩
  apply Φ_strictMono.le_iff_le.1
  change Φ M ≤ Φ (Function.invFun Φ ((1+c)/2))
  rw [Φ_inv hp]
  have := le_max_right (0:ℝ) (2*Φ M-1)
  dsimp [a] at hac
  linarith

lemma k_tendsto {h : ℝ} (hh : 0 < h) : Tendsto (k0167 h) (𝓝[<] (1:ℝ)) atTop := by
  have hconst : 0 < 4/(h^2*φ0167 0) := div_pos (by norm_num) (mul_pos (sq_pos_of_pos hh) (φ_pos _))
  apply tendsto_atTop_mono' _ _ (y_tendsto.const_mul_atTop hconst)
  filter_upwards [show ∀ᶠ c in 𝓝[<] (1:ℝ), 0 < c from
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)), self_mem_nhdsWithin] with c hc0 hc
  have hy := y_nonneg ⟨hc0.le, hc⟩
  have hp := φ_antitone (show (0:ℝ) ∈ Ici 0 by simp) hy hy
  have hd := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hy)
    (mul_pos (sq_pos_of_pos hh) (φ_pos (y0167 c))) (mul_le_mul_of_nonneg_left hp (sq_nonneg h))
  simpa [k0167, div_mul_eq_mul_div] using hd

lemma no_uniform_lipschitz {h : ℝ} (hh : 0 < h) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Ico (0:ℝ) 1, ∀ b ∈ Ico (0:ℝ) 1,
      |H0162 h b-H0162 h a| ≤ K*|b-a| := by
  rintro ⟨K, hK, h⟩
  obtain ⟨c, hc, hbig⟩ := H_unbounded hh K
  have he := h 0 (by constructor <;> norm_num) c hc
  rw [H_zero, sub_zero, sub_zero, abs_of_nonneg (H_nonneg _ _), abs_of_nonneg hc.1] at he
  have := mul_le_mul_of_nonneg_left hc.2.le hK
  linarith

end Pricing

lemma cumulative_zero (v : Fin N → NNReal) : cumulative0161 v 0 = 0 := by simp [cumulative0161]

lemma cumulative_nonneg (v : Fin N → NNReal) (i : Fin (N+1)) : 0 ≤ cumulative0161 v i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma cumulative_mono (v : Fin N → NNReal) : Monotone (cumulative0161 v) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | exact le_rfl | positivity | omega

lemma cumulative_step (v : Fin N → NNReal) (i : Fin N) :
    cumulative0161 v i.succ = cumulative0161 v i.castSucc + (v i : ℝ) := by
  have heq (j : Fin N) :
      (if j.val < i.succ.val then (v j : ℝ) else 0) =
      (if j.val < i.castSucc.val then (v j : ℝ) else 0) + (if j = i then (v j : ℝ) else 0) := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases hj : j = i
    · subst j; simp
    · have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
      split_ifs <;> simp_all <;> omega
  unfold cumulative0161
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp

lemma cumulative_surj (z : Fin (N+1) → ℝ) (hz0 : z 0 = 0) (hm : Monotone z) :
    ∃ v : Fin N → NNReal, cumulative0161 v = z := by
  let v : Fin N → NNReal := fun i => NNReal.mk (z i.succ-z i.castSucc)
    (sub_nonneg.2 (hm (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le)))
  refine ⟨v, ?_⟩
  funext i
  induction i using Fin.induction with
  | zero => simp [cumulative_zero, hz0]
  | succ i hi =>
    rw [cumulative_step, hi]
    change z i.castSucc + (z i.succ-z i.castSucc) = z i.succ
    ring

lemma cumulative_difference (v : Fin N → NNReal) (n : Fin N) :
    cumulative0161 v n.succ - cumulative0161 v n.castSucc = (v n : ℝ) := by
  rw [cumulative_step]; ring

lemma fits_iff_feasible (h a b : Fin (N+1) → ℝ) (hh : ∀ i, 0 < h i)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 ∧ a i < 1) (v : Fin N → NNReal) :
    fits0161 h a b v ↔ feasible (l0162 h a) (u0162 h b) (cumulative0161 v) := by
  unfold feasible
  simp only [cumulative_zero, cumulative_mono, true_and]
  apply forall_congr'
  intro i
  rw [price_interval (hh i) (ha i).1 (ha i).2.1 (ha i).2.2.1 (ha i).2.2.2 (cumulative_nonneg v i)]
  unfold l0162 u0162
  by_cases hb : b i = 1
  · simp [hb]
  · have hb' : b i < 1 := lt_of_le_of_ne (ha i).2.2.1 hb
    simp [hb, hb']

lemma price_feasibility (h a b : Fin (N+1) → ℝ) (hh : ∀ i, 0 < h i)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 ∧ a i < 1) (ha0 : a 0 = 0) (_hb0 : b 0 = 0) :
    (∃ v : Fin N → NNReal, fits0161 h a b v) ↔ compatible (l0162 h a) (u0162 h b) := by
  rw [← feasible_iff (l0162 h a) (u0162 h b) (by simp [l0162, ha0, H_zero])]
  constructor
  · rintro ⟨v, hv⟩; exact ⟨cumulative0161 v, (fits_iff_feasible h a b hh ha v).1 hv⟩
  · rintro ⟨z, hz⟩
    obtain ⟨v, hv⟩ := cumulative_surj z hz.1 hz.2.1
    exact ⟨v, (fits_iff_feasible h a b hh ha v).2 (by simpa [hv] using hz)⟩

lemma price_projection (h a b : Fin (N+1) → ℝ) (hh : ∀ i, 0 < h i)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 ∧ a i < 1) (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hc : compatible (l0162 h a) (u0162 h b)) (n : Fin N) (r : ℝ) :
    (∃ v : Fin N → NNReal, fits0161 h a b v ∧ (v n : ℝ) = r) ↔
      lower0165 (l0162 h a) (u0162 h b) n ≤ r ∧
      (r : WithTop ℝ) ≤ upper0166 (l0162 h a) (u0162 h b) n := by
  rw [← projection_endpoints (l0162 h a) (u0162 h b)
    (by simp [l0162, ha0, H_zero]) (by simp [u0162, hb0, H_zero]) hc]
  constructor
  · rintro ⟨v, hv, hr⟩
    exact ⟨cumulative0161 v, (fits_iff_feasible h a b hh ha v).1 hv, by rw [cumulative_difference, hr]⟩
  · rintro ⟨z, hz, hr⟩
    obtain ⟨v, hv⟩ := cumulative_surj z hz.1 hz.2.1
    refine ⟨v, (fits_iff_feasible h a b hh ha v).2 (by simpa [hv] using hz), ?_⟩
    rw [← cumulative_difference, hv, hr]

lemma stability (v w : Fin N → NNReal) (h β ε : Fin (N+1) → ℝ)
    (hh : ∀ i, 0 < h i) (hβ : ∀ i, β i ∈ Ico (0:ℝ) 1)
    (hv : ∀ i, P0161 (h i) (cumulative0161 v i) ∈ Icc (0:ℝ) (β i))
    (hw : ∀ i, P0161 (h i) (cumulative0161 w i) ∈ Icc (0:ℝ) (β i))
    (he : ∀ i, |P0161 (h i) (cumulative0161 v i)-P0161 (h i) (cumulative0161 w i)| ≤ ε i)
    (n : Fin N) :
    |(v n : ℝ)-(w n : ℝ)| ≤ k0167 (h n.succ) (β n.succ)*ε n.succ +
      k0167 (h n.castSucc) (β n.castSucc)*ε n.castSucc := by
  have hb (i) : |cumulative0161 v i-cumulative0161 w i| ≤ k0167 (h i) (β i)*ε i := by
    have hx := H_lipschitz (hh i) (hβ i) (hw i) (hv i)
    rw [H_P (hh i) (cumulative_nonneg v i), H_P (hh i) (cumulative_nonneg w i)] at hx
    exact hx.trans (mul_le_mul_of_nonneg_left (he i) (k_nonneg _ (hβ i)))
  rw [← cumulative_difference v n, ← cumulative_difference w n]
  calc
    |(cumulative0161 v n.succ-cumulative0161 v n.castSucc) -
      (cumulative0161 w n.succ-cumulative0161 w n.castSucc)| =
      |(cumulative0161 v n.succ-cumulative0161 w n.succ) -
      (cumulative0161 v n.castSucc-cumulative0161 w n.castSucc)| := by congr 1; ring
    _ ≤ |cumulative0161 v n.succ-cumulative0161 w n.succ| +
      |cumulative0161 v n.castSucc-cumulative0161 w n.castSucc| := abs_sub _ _
    _ ≤ _ := add_le_add (hb n.succ) (hb n.castSucc)

/-- The analytic price used above equals Claim 014's actual discounted payoff integral. -/
lemma model_price (τ : ℕ → ℝ) (v : Fin N → NNReal) (S U : Fin N → ℝ)
    (hτ : StrictMonoOn τ (Iic N))
    (hS : ∀ i, τ (i.val+1) ≤ S i ∧ (i.val+1 < N → S i < τ (i.val+2)))
    (hU : ∀ i, S i < U i) (i : Fin N) :
    Standalone.BondOptionMeetingVariances.C τ v (S i) (U i) 1 =
      P0161 (U i-S i) (cumulative0161 v i.succ) := by
  open Standalone.BondOptionMeetingVariances Standalone.D3EventVariances in
  have hz : (z τ v (S i) : ℝ) = cumulative0161 v i.succ := by
    simp only [z, NNReal.coe_sum, past, cumulative0161, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    have hj : τ (j.val+1) ≤ S i ↔ j ≤ i := by
      simpa [past] using BondOptionMeetingVariancesProof.past_separating τ S hτ hS i j
    have hk : j.val < i.succ.val ↔ j ≤ i := by change j.val < i.val+1 ↔ j.val ≤ i.val; omega
    simp only [hj, hk]
    split_ifs <;> rfl
  rw [BondOptionMeetingVariancesProof.price_at_one]
  unfold P0161
  congr 2
  open Standalone.BondOptionMeetingVariances in
  have hq : (q τ v (S i) (U i) : ℝ) = (U i-S i)^2 * cumulative0161 v i.succ := by
    simp [q, Real.coe_toNNReal _ (sq_nonneg _), hz]
  rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.2 (hU i).le)]
  rfl


theorem bondOptionPriceIntervals : Standalone.BondOptionPriceIntervals.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N l u hl _hu
    exact ⟨feasible_iff l u hl, feasible_L l u hl, propagated l u⟩
  · intro N l u hl hu hc
    exact projection l u hl hu hc
  · intro N l u hl hu hc n
    exact ⟨projection_endpoints l u hl hu hc n, endpoints l u hl hu hc n⟩
  · intro h hh
    refine ⟨H_zero h, k_zero h, fun z hz => ⟨P_bounds hh hz, H_P hh hz⟩,
      fun c hc => ⟨H_nonneg _ _, P_H hh hc⟩, H_mono hh, ?_, ?_, ?_,
      H_tendsto hh, k_tendsto hh, no_uniform_lipschitz hh⟩
    · intro a b z ha hab hb ha1 hz
      exact price_interval hh ha hab hb ha1 hz
    · intro c hc
      exact H_deriv ⟨by linarith [hc.1], hc.2⟩ h
    · intro β hβ a ha b hb
      exact H_lipschitz hh hβ ha hb
  · intro N h a b hh ha ha0 hb0
    exact ⟨price_feasibility h a b hh ha ha0 hb0, price_projection h a b hh ha ha0 hb0,
      cumulative_surj⟩
  · intro N v w h β ε hh hβ hv hw he
    exact stability v w h β ε hh hβ hv hw he

end Novel.BondOptionPriceIntervalsProof

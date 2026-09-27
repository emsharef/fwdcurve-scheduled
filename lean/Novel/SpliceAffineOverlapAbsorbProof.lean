import Standalone.SpliceAffineOverlapAbsorb
import Novel.SharefFilipovicSplitProof
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open Set Filter Topology MeasureTheory
open Standalone.SpliceAffineOverlapAbsorb
namespace Novel.SpliceAffineOverlapAbsorbProof

variable {N m : ℕ}

lemma F_analytic (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ) (Z : Fin N → ℝ) :
    AnalyticOnNhd ℝ (Flin φ Z) univ := by
  have h := Finset.analyticOnNhd_sum (𝕜 := ℝ) (s := univ) (Finset.univ : Finset (Fin N))
    (f := fun i x => Z i * φ i x) fun i _ x hx => analyticAt_const.mul (hφ i x hx)
  convert h using 1
  funext x
  simp [Flin, Finset.sum_apply]

lemma dF_analytic (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ) (Z : Fin N → ℝ) :
    AnalyticOnNhd ℝ (deriv (Flin φ Z)) univ :=
  (F_analytic φ hφ Z).deriv

lemma cont (f : ℝ → ℝ) (h : AnalyticOnNhd ℝ f univ) : Continuous f :=
  continuousOn_univ.1 h.continuousOn

lemma DB_cont (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ) (Z b : Fin N → ℝ)
    (t : ℝ) : Continuous (DBlin φ Z b t) := by
  unfold DBlin
  exact ((cont _ (dF_analytic φ hφ Z)).comp (continuous_id.sub continuous_const)).neg.add
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((cont _ (hφ i)).comp (continuous_id.sub continuous_const)))

lemma sB_cont (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ)
    (sZ : Fin N → Fin m → ℝ) (t : ℝ) (l : Fin m) : Continuous fun u => sBlin φ sZ t u l := by
  unfold sBlin
  exact continuous_finsetSum _ fun i _ =>
    ((cont _ (hφ i)).comp (continuous_id.sub continuous_const)).mul continuous_const

/-- The block's quadratic term is the `a`-sum of the residual. -/
lemma block_identity (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ)
    (sZ : Fin N → Fin m → ℝ) (t T : ℝ) :
    ∑ l, (∫ u in t..T, sBlin φ sZ t u l) * sBlin φ sZ t T l =
      ∑ i, ∑ j, (∑ l, sZ i l * sZ j l) * φ i (T - t) * ∫ η in (0:ℝ)..(T - t), φ j η := by
  have hB : ∀ l, (∫ u in t..T, sBlin φ sZ t u l) =
      ∑ j, sZ j l * ∫ η in (0:ℝ)..(T - t), φ j η := by
    intro l
    unfold sBlin
    have hc : ∀ j, Continuous fun u => φ j (u - t) * sZ j l := fun j =>
      ((cont _ (hφ j)).comp (continuous_id.sub continuous_const)).mul continuous_const
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc j).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right (φ j),
      sub_self, mul_comm]
  simp only [hB]
  simp only [sBlin, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `D^B(u) = R(u − t) + σ^B(u) · ∫_t^u σ^B`. -/
lemma DB_eq (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ) (Z b : Fin N → ℝ)
    (sZ : Fin N → Fin m → ℝ) (t u : ℝ) :
    DBlin φ Z b t u = Rlin φ Z b (fun i j => ∑ k, sZ i k * sZ j k) (u - t) +
      ∑ l, (∫ v in t..u, sBlin φ sZ t v l) * sBlin φ sZ t u l := by
  rw [block_identity φ hφ sZ t u, DBlin, Rlin]
  ring

lemma analyticAt_fsum {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) (h : ∀ i, AnalyticAt ℝ (f i) x) :
    AnalyticAt ℝ (fun y => ∑ i, f i y) x := by
  have := Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset (Fin n)) (f := f) (c := x)
    fun i _ => h i
  convert this using 1
  funext y
  simp [Finset.sum_apply]

/-- The residual is real-analytic when the `φ_i` and their primitives are. -/
lemma R_analytic (φ : Fin N → ℝ → ℝ) (hφ : ∀ i, AnalyticOnNhd ℝ (φ i) univ)
    (hprim : ∀ i, AnalyticOnNhd ℝ (fun x => ∫ η in (0:ℝ)..x, φ i η) univ) (Z b : Fin N → ℝ)
    (a : Fin N → Fin N → ℝ) : AnalyticOnNhd ℝ (Rlin φ Z b a) univ := fun x hx => by
  have h1 := analyticAt_fsum (fun i y => b i * φ i y) x fun i => analyticAt_const.mul (hφ i x hx)
  have h2 := analyticAt_fsum (fun i y => ∑ j, a i j * φ i y * ∫ η in (0:ℝ)..y, φ j η) x fun i =>
    analyticAt_fsum _ x fun j => (analyticAt_const.mul (hφ i x hx)).mul (hprim j x hx)
  exact (h1.sub h2).sub (dF_analytic φ hφ Z x hx)

/-- With separate drivers the square splits with no cross term. -/
lemma sep_sum {f g : ℝ → Fin m → ℝ} (hsep : ∀ k, (∀ T, f T k = 0) ∨ (∀ T, g T k = 0))
    (t T : ℝ) :
    ∑ k, (∫ u in t..T, (f u k + g u k)) * (f T k + g T k) =
      ∑ k, (∫ u in t..T, f u k) * f T k + ∑ k, (∫ u in t..T, g u k) * g T k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases hsep k with h | h <;> simp [h]

lemma absorb : absorbStatement := by
  intro N m φ hφ hprim Z b sZ DS sS t p q htp hpq hDS hsS hdaff hsaff hsep hax
  obtain ⟨d₀, d₁, hd⟩ := hdaff
  obtain ⟨s₀, hs⟩ := hsaff
  set a : Fin N → Fin N → ℝ := fun i j => ∑ k, sZ i k * sZ j k
  have hsep' : ∀ k, (∀ T, sS T k = 0) ∨ (∀ T, sBlin φ sZ t T k = 0) := fun k => by
    rcases hsep k with h | h
    · exact Or.inl h
    · exact Or.inr fun T => by simp [sBlin, h]
  have hDSc : ContinuousOn DS (Ioo p q) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).congr fun T hT => hd T hT
  have hfc : ∀ k, ContinuousOn (fun u => sS u k + sBlin φ sZ t u k) (Ioo p q) := fun k =>
    ((continuousOn_const (c := s₀ k)).add (sB_cont φ hφ sZ t k).continuousOn).congr fun T hT => by
      simp [hs T hT]
  have hfi : ∀ k, IntervalIntegrable (fun u => sS u k + sBlin φ sZ t u k) volume t q := fun k =>
    (hsS k).add ((sB_cont φ hφ sZ t k).intervalIntegrable _ _)
  -- differentiated AX-01 on `J`
  have hder : ∀ T ∈ Ioo p q, DS T + DBlin φ Z b t T =
      ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) * (sS T k + sBlin φ sZ t T k) := by
    intro T hT
    have hL := Novel.SharefFilipovicSplitProof.ftc (f := fun u => DS u + DBlin φ Z b t u)
      (hDS.add ((DB_cont φ hφ Z b t).intervalIntegrable _ _)) hT htp
      (hDSc.add (DB_cont φ hφ Z b t).continuousOn)
    have hR : HasDerivAt (fun T => (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2)
        (∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) * (sS T k + sBlin φ sZ t T k)) T := by
      have hk := HasDerivAt.sum (u := Finset.univ) fun k _ =>
        (Novel.SharefFilipovicSplitProof.ftc (hfi k) hT htp (hfc k)).pow 2
      convert hk.const_mul (1/2 : ℝ) using 1
      · funext T; simp [Finset.sum_apply]
      · simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    have hev : (fun T => ∫ u in t..T, (DS u + DBlin φ Z b t u)) =ᶠ[𝓝 T]
        fun T => (1/2 : ℝ) * ∑ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2 := by
      filter_upwards [isOpen_Ioo.mem_nhds hT] with T' hT'
      exact hax T' hT'
    exact hL.unique (hR.congr_of_eventuallyEq hev)
  -- the front end's side is affine on `J`
  have hint : ∀ T ∈ Ioo p q, ∀ k, (∫ u in t..T, sS u k) = (∫ u in t..p, sS u k) + s₀ k * (T - p) :=
    fun T hT k => by
      have hi : ∀ x y, x ∈ uIcc t q → y ∈ uIcc t q →
          IntervalIntegrable (fun u => sS u k) volume x y := fun x y hx hy =>
        (hsS k).mono_set (uIcc_subset_uIcc hx hy)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hi t p (by rw [uIcc_of_le (htp.trans hpq.le)]; exact ⟨le_rfl, htp.trans hpq.le⟩)
          (by rw [uIcc_of_le (htp.trans hpq.le)]; exact ⟨htp, hpq.le⟩))
        (hi p T (by rw [uIcc_of_le (htp.trans hpq.le)]; exact ⟨htp, hpq.le⟩)
          (by rw [uIcc_of_le (htp.trans hpq.le)]; exact ⟨htp.trans hT.1.le, hT.2.le⟩))]
      congr 1
      rw [intervalIntegral.integral_congr_ae (g := fun _ => s₀ k) (Eventually.of_forall
        fun u hu => by
          rw [uIoc_of_le hT.1.le] at hu
          rw [hs u ⟨hu.1, lt_of_le_of_lt hu.2 hT.2⟩]),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
  have hJ : ∀ x ∈ Ioo (p - t) (q - t), Rlin φ Z b a x =
      ((∑ k, (∫ u in t..p, sS u k) * s₀ k) - (∑ k, s₀ k * s₀ k) * p - d₀ +
        ((∑ k, s₀ k * s₀ k) - d₁) * t) + ((∑ k, s₀ k * s₀ k) - d₁) * x := by
    intro x hx
    have hT : x + t ∈ Ioo p q := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 := hder (x + t) hT
    rw [DB_eq φ hφ Z b sZ t (x + t), sep_sum hsep' t (x + t), add_sub_cancel_right] at h1
    have h2 : ∑ k, (∫ u in t..(x + t), sS u k) * sS (x + t) k =
        (∑ k, (∫ u in t..p, sS u k) * s₀ k) + (∑ k, s₀ k * s₀ k) * (x + t - p) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hint _ hT k, hs _ hT]; ring
    rw [h2, hd _ hT] at h1
    linarith
  set e₁ := (∑ k, s₀ k * s₀ k) - d₁
  set e₀ := (∑ k, (∫ u in t..p, sS u k) * s₀ k) - (∑ k, s₀ k * s₀ k) * p - d₀
  refine ⟨e₀ + e₁ * t, e₁, fun x => ?_⟩
  have hg : AnalyticOnNhd ℝ (fun x => Rlin φ Z b a x - ((e₀ + e₁ * t) + e₁ * x)) univ :=
    fun y hy => (R_analytic φ hφ hprim Z b a y hy).sub
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hmid : ((p - t) + (q - t)) / 2 ∈ Ioo (p - t) (q - t) := ⟨by linarith, by linarith⟩
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
    (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with y hy; simp [hJ y hy]) (mem_univ x)
  simp only [Pi.zero_apply] at this
  linarith

lemma converse : converseStatement := by
  intro N m φ hφ Z b sZ DS sS t c₀ c₁ hR hsep T htT hDS hsS hfront
  have hDBeq : ∀ u ∈ uIcc t T, DBlin φ Z b t u = (c₀ + c₁ * (u - t)) +
      ∑ l, (∫ v in t..u, sBlin φ sZ t v l) * sBlin φ sZ t u l := fun u hu => by
    rw [uIcc_of_le htT] at hu
    rw [DB_eq φ hφ Z b sZ t u, hR (u - t) (sub_nonneg.2 hu.1)]
  have hderiv : ∀ x, HasDerivAt (fun T => (1/2 : ℝ) * ∑ l, (∫ v in t..T, sBlin φ sZ t v l) ^ 2)
      (∑ l, (∫ v in t..x, sBlin φ sZ t v l) * sBlin φ sZ t x l) x := by
    intro x
    have hl := HasDerivAt.sum (u := Finset.univ) fun l _ =>
      (((sB_cont φ hφ sZ t l).integral_hasStrictDerivAt t x).hasDerivAt).pow 2
    convert hl.const_mul (1/2 : ℝ) using 1
    · funext T; simp [Finset.sum_apply]
    · simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  have hQc : Continuous fun x => ∑ l, (∫ v in t..x, sBlin φ sZ t v l) * sBlin φ sZ t x l :=
    continuous_finsetSum _ fun l _ =>
      (intervalIntegral.continuous_primitive (fun x y => (sB_cont φ hφ sZ t l).intervalIntegrable x y)
        t).mul (sB_cont φ hφ sZ t l)
  have haff : Continuous fun u : ℝ => c₀ + c₁ * (u - t) := by fun_prop
  have hblock : ∫ u in t..T, DBlin φ Z b t u = (∫ u in t..T, (c₀ + c₁ * (u - t))) +
      (1/2 : ℝ) * ∑ l, (∫ v in t..T, sBlin φ sZ t v l) ^ 2 := by
    rw [intervalIntegral.integral_congr hDBeq, intervalIntegral.integral_add
      (haff.intervalIntegrable _ _) (hQc.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hQc.intervalIntegrable _ _)]
    simp
  have hsq : ∀ k, (∫ u in t..T, (sS u k + sBlin φ sZ t u k)) ^ 2 =
      (∫ u in t..T, sS u k) ^ 2 + (∫ u in t..T, sBlin φ sZ t u k) ^ 2 := by
    intro k
    rcases hsep k with h0 | h0
    · simp [h0]
    · have : ∀ u, sBlin φ sZ t u k = 0 := fun u => by simp [sBlin, h0]
      simp [this]
  rw [intervalIntegral.integral_add hDS ((DB_cont φ hφ Z b t).intervalIntegrable _ _), hfront,
    hblock, Finset.sum_congr rfl fun k _ => hsq k, Finset.sum_add_distrib]
  ring

theorem spliceAffineOverlapAbsorb : Standalone.SpliceAffineOverlapAbsorb.statement := ⟨absorb, converse⟩

end Novel.SpliceAffineOverlapAbsorbProof

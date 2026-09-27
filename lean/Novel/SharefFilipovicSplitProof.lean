import Standalone.SharefFilipovicSplit
import Novel.SharefFilipovicResidualProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set Polynomial Filter Topology MeasureTheory
open Standalone.SharefFilipovicResidual Standalone.SharefFilipovicSplit
namespace Novel.SharefFilipovicSplitProof
open Novel.SharefFilipovicResidualProof

lemma ep_cont (β : ℝ) {f : ℝ → ℝ} (hf : IsEP β f) : Continuous f := by
  obtain ⟨Q, hQ⟩ := hf
  rw [show f = fun x => ∑ i, (Q i).eval x * Real.exp (-(((i:ℕ):ℝ) + 1) * β * x) from funext hQ]
  exact continuous_finsetSum _ fun i _ => (Q i).continuous.mul (by fun_prop)

variable {n₁ n₂ : ℕ}

lemma phi_cont (β : ℝ) (i : Fin (n₁ + 1) ⊕ Fin (n₂ + 1)) : Continuous (phi034 β n₁ n₂ i) :=
  ep_cont β (ep_phi β i)

/-- `∂_x F` is continuous. -/
lemma dF_cont (β : ℝ) (Z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) :
    Continuous (deriv (F034 β n₁ n₂ Z)) := by
  classical
  choose g hg hgd using fun i => ep_dphi β (n₁ := n₁) (n₂ := n₂) i
  have hF : deriv (F034 β n₁ n₂ Z) = fun x => ∑ i, Z i * g i x := by
    funext x
    have := HasDerivAt.sum (u := Finset.univ) fun i _ => (hgd i x).const_mul (Z i)
    rw [show F034 β n₁ n₂ Z = ∑ i ∈ Finset.univ, fun y => Z i * phi034 β n₁ n₂ i y from by
      funext y; simp [F034, Finset.sum_apply]]
    exact this.deriv
  rw [hF]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (ep_cont β (hg i))

lemma DB_cont (β : ℝ) (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ) (t : ℝ) :
    Continuous (DB034 β Z b t) := by
  unfold DB034
  exact ((dF_cont β Z).comp (continuous_id.sub continuous_const)).neg.add
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((phi_cont β i).comp (continuous_id.sub continuous_const)))

lemma sB_cont {dB : ℕ} (β : ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin dB → ℝ) (t : ℝ)
    (l : Fin dB) : Continuous fun u => sB034 β sZ t u l := by
  unfold sB034
  exact continuous_finsetSum _ fun i _ =>
    ((phi_cont β i).comp (continuous_id.sub continuous_const)).mul continuous_const

/-- The derivative of `∫_t^T f` at a point of continuity inside an open set of continuity. -/
lemma ftc {f : ℝ → ℝ} {t q p T : ℝ} (hi : IntervalIntegrable f volume t q)
    (hT : T ∈ Ioo p q) (htp : t ≤ p) (hc : ContinuousOn f (Ioo p q)) :
    HasDerivAt (fun T => ∫ u in t..T, f u) (f T) T :=
  intervalIntegral.integral_hasDerivAt_right
    (hi.mono_set (by
      rw [uIcc_of_le (htp.trans hT.1.le), uIcc_of_le (htp.trans (hT.1.trans hT.2).le)]
      exact Icc_subset_Icc le_rfl hT.2.le))
    (hc.stronglyMeasurableAtFilter isOpen_Ioo T hT) (hc.continuousAt (isOpen_Ioo.mem_nhds hT))

/-- The block's quadratic term is the `a`-sum of the residual. -/
lemma block_identity {n₁ n₂ dB : ℕ} (β : ℝ) (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin dB → ℝ)
    (t : ℝ) : ∀ T, ∑ l, (∫ u in t..T, sB034 β sZ t u l) * sB034 β sZ t T l =
      ∑ i, ∑ j, (∑ l, sZ i l * sZ j l) * phi034 β n₁ n₂ i (T - t) *
        ∫ η in (0:ℝ)..(T - t), phi034 β n₁ n₂ j η := by
  intro T
  have hB : ∀ l, (∫ u in t..T, sB034 β sZ t u l) =
      ∑ j, sZ j l * ∫ η in (0:ℝ)..(T - t), phi034 β n₁ n₂ j η := by
    intro l
    unfold sB034
    have hc : ∀ j, Continuous fun u => phi034 β n₁ n₂ j (u - t) * sZ j l := fun j =>
      ((phi_cont β j).comp (continuous_id.sub continuous_const)).mul continuous_const
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc j).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right
      (phi034 β n₁ n₂ j), sub_self, mul_comm]
  simp only [hB]
  simp only [sB034, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Differentiating AX-01 on `J` gives (34.4). -/
lemma deriv_identity {n₁ n₂ dS dB : ℕ} (β : ℝ) (Z b : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
    (sZ : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin dB → ℝ) (DS : ℝ → ℝ) (sS : ℝ → Fin dS → ℝ)
    (t p q : ℝ) (htp : t ≤ p) (hDSi : IntervalIntegrable DS volume t q)
    (hsSi : ∀ k, IntervalIntegrable (fun u => sS u k) volume t q)
    (hDSc : ContinuousOn DS (Ioo p q)) (hsSc : ∀ k, ContinuousOn (fun u => sS u k) (Ioo p q))
    (hax : ∀ T ∈ Ioo p q, ∫ u in t..T, (DS u + DB034 β Z b t u) =
      (1/2 : ℝ) * (∑ k, (∫ u in t..T, sS u k) ^ 2 + ∑ l, (∫ u in t..T, sB034 β sZ t u l) ^ 2)) :
    ∀ T ∈ Ioo p q, DS T + DB034 β Z b t T =
      ∑ k, (∫ u in t..T, sS u k) * sS T k + ∑ l, (∫ u in t..T, sB034 β sZ t u l) * sB034 β sZ t T l := by
  intro T hT
  have hL := ftc (f := fun u => DS u + DB034 β Z b t u) (hDSi.add ((DB_cont β Z b t).intervalIntegrable _ _))
    hT htp (hDSc.add (DB_cont β Z b t).continuousOn)
  have hR : HasDerivAt (fun T => (1/2 : ℝ) * (∑ k, (∫ u in t..T, sS u k) ^ 2 +
      ∑ l, (∫ u in t..T, sB034 β sZ t u l) ^ 2))
      (∑ k, (∫ u in t..T, sS u k) * sS T k + ∑ l, (∫ u in t..T, sB034 β sZ t u l) * sB034 β sZ t T l) T := by
    have hk := HasDerivAt.sum (u := Finset.univ) fun k _ =>
      (ftc (hsSi k) hT htp (hsSc k)).pow 2
    have hl := HasDerivAt.sum (u := Finset.univ) fun l _ =>
      (ftc ((sB_cont β sZ t l).intervalIntegrable t q) hT htp (sB_cont β sZ t l).continuousOn).pow 2
    convert (hk.add hl).const_mul (1/2 : ℝ) using 1
    · funext T; simp [Finset.sum_apply]
    · simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, mul_add, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hev : (fun T => ∫ u in t..T, (DS u + DB034 β Z b t u)) =ᶠ[𝓝 T]
      fun T => (1/2 : ℝ) * (∑ k, (∫ u in t..T, sS u k) ^ 2 + ∑ l, (∫ u in t..T, sB034 β sZ t u l) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hT] with T' hT'
    exact hax T' hT'
  exact hL.unique (hR.congr_of_eventuallyEq hev)

lemma split : splitStatement := by
  intro β hβ n₁ n₂ dS dB Z b sZ DS sS t p q htp hpq hDSi hsSi ⟨d₀, d₁, hD⟩ ⟨s₀, s₁, hs⟩ hax
  classical
  have hDSc : ContinuousOn DS (Ioo p q) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.congr fun T hT => hD T hT
  have hsSc : ∀ k, ContinuousOn (fun u => sS u k) (Ioo p q) := fun k =>
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.congr
      fun T hT => hs T hT k
  have hderiv := deriv_identity β Z b sZ DS sS t p q htp hDSi hsSi hDSc hsSc hax
  have hblock := block_identity (n₁ := n₁) (n₂ := n₂) β sZ t
  -- the front end's side is a polynomial on `J`
  set m := (p + q) / 2
  have hm : m ∈ Ioo p q := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  set Ak : Fin dS → ℝ := fun k => ∫ u in t..m, sS u k
  let P : ℝ[X] := ∑ k, (C (Ak k - s₀ k * m - s₁ k * m ^ 2 / 2) + C (s₀ k) * X + C (s₁ k / 2) * X ^ 2) *
    (C (s₀ k) + C (s₁ k) * X) - (C d₀ + C d₁ * X)
  have hA : ∀ T ∈ Ioo p q, ∀ k, (∫ u in t..T, sS u k) =
      Ak k + s₀ k * (T - m) + s₁ k * (T ^ 2 - m ^ 2) / 2 := by
    intro T hT k
    have hsub : ∀ x ∈ uIcc m T, x ∈ Ioo p q := fun x hx => by
      rcases le_total m T with h | h
      · rw [uIcc_of_le h] at hx; exact ⟨hm.1.trans_le hx.1, hx.2.trans_lt hT.2⟩
      · rw [uIcc_of_ge h] at hx; exact ⟨hT.1.trans_le hx.1, hx.2.trans_lt hm.2⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((hsSi k).mono_set (by
        rw [uIcc_of_le (htp.trans hm.1.le), uIcc_of_le (htp.trans (hpq.le))]
        exact Icc_subset_Icc le_rfl hm.2.le))
      ((hsSi k).mono_set (fun x hx => by
        have := hsub x hx
        rw [uIcc_of_le (htp.trans hpq.le)]
        exact ⟨htp.trans (this.1.le), this.2.le⟩))
    rw [← hsplit, intervalIntegral.integral_congr (g := fun u => s₀ k + s₁ k * u)
      (fun x hx => hs x (hsub x hx) k)]
    simp only [Ak]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun u : ℝ => s₁ k * u).intervalIntegrable _ _),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
    ring
  have hres : ∀ x ∈ Ioo (p - t) (q - t),
      residual034 β n₁ n₂ Z b (fun i j => ∑ l, sZ i l * sZ j l) x = (P.comp (X + C t)).eval x := by
    intro x hx
    have hT : x + t ∈ Ioo p q := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 := hderiv (x + t) hT
    rw [hblock, add_sub_cancel_right] at h1
    rw [eval_comp]
    simp only [P, eval_sub, eval_finsetSum, eval_mul, eval_add, eval_C, eval_X, eval_pow]
    have hDB : DB034 β Z b t (x + t) = -deriv (F034 β n₁ n₂ Z) x +
        ∑ i, b i * phi034 β n₁ n₂ i x := by simp [DB034]
    rw [hD _ hT, hDB] at h1
    simp only [residual034]
    have hsum : ∑ k, (∫ u in t..(x + t), sS u k) * sS (x + t) k =
        ∑ k, (Ak k - s₀ k * m - s₁ k * m ^ 2 / 2 + s₀ k * (x + t) + s₁ k / 2 * (x + t) ^ 2) *
          (s₀ k + s₁ k * (x + t)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA _ hT k, hs _ hT k]
      ring
    rw [hsum] at h1
    linarith
  exact Novel.SharefFilipovicResidualProof.residual β hβ n₁ n₂ Z b _ _ (p - t) (q - t)
    (by linarith) hres

theorem sharefFilipovicSplit : Standalone.SharefFilipovicSplit.statement := split

end Novel.SharefFilipovicSplitProof

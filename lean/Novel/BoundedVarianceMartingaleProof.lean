import Standalone.BoundedVarianceMartingale
import Novel.BoundedVarianceStateProof
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Upstream.ExponentialMartingale
import Upstream.Predictability

open MeasureTheory Filter
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.BoundedVarianceState Standalone.BoundedVarianceMartingale
open Novel.BoundedVarianceStateProof
namespace Novel.BoundedVarianceMartingaleProof

/-- The audited AX-10 field is exactly the standalone restatement. -/
theorem ofUpstream {Ω : Type*} [MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (E : Upstream.ExponentialMartingale S) :
    ExponentialMartingale (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S) where
  bounded_qv_exponential_martingale := E.bounded_qv_exponential_martingale

lemma bounded_U4 {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (H : ℝ≥0 → Ω → ℝ) (hp : IsStronglyPredictable S.ℱ H)
    (C : ℝ) (hb : ∀ s ω, (H s ω)^2 ≤ C^2) : U4 S.ℱ S.μ H := by
  refine ⟨hp, fun t => Eventually.of_forall fun ω => ?_⟩
  have hle : (∫⁻ s in Set.Icc (0:ℝ) t, ENNReal.ofReal ((H (Real.toNNReal s) ω)^2)) ≤
      ENNReal.ofReal (C^2) * ENNReal.ofReal (t:ℝ) := by
    calc
      _ ≤ ∫⁻ _s in Set.Icc (0:ℝ) t, ENNReal.ofReal (C^2) :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hb _ _)
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

lemma domains {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i j : Fin S.m) (lam x : ℝ) (Y : ℝ → Ω → ℝ)
    (hp : IsStronglyPredictable S.ℱ (fun t ω => a025 (Y t ω))) :
    ∀ k, U4 S.ℱ S.μ (H025 i j lam x Y k) := by
  intro k
  change U4 S.ℱ S.μ (fun t ω => if k = i then -A025 lam 1 x else
    if k = j then -a025 (Y t ω) * A025 lam 2 x else 0)
  by_cases hi : k = i
  · simp only [ite_eq_left hi]
    exact bounded_U4 S _ stronglyMeasurable_const (A025 lam 1 x) (by intros; simp)
  · by_cases hj : k = j
    · simp only [ite_eq_right hi, ite_eq_left hj]
      apply bounded_U4 S (fun t ω => -a025 (Y t ω) * A025 lam 2 x) (hp.neg.mul_const _) (2*|A025 lam 2 x|)
      intro s ω
      have hv := bounds025 (Y s ω)
      have ha : (a025 (Y s ω))^2 = v025 (Y s ω) := Real.sq_sqrt (by linarith [hv.1])
      rw [mul_pow, neg_sq, ha]
      nlinarith [sq_nonneg (A025 lam 2 x), sq_abs (A025 lam 2 x)]
    · simp only [ite_eq_right hi, ite_eq_right hj]
      exact bounded_U4 S _ stronglyMeasurable_const 0 (by intros; simp)

lemma covariance_sum {Ω : Type*} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (i j : Fin S.m) (hij : i ≠ j)
    (hc : ∀ k l t, S.c k l t = if k = l then 1 else 0)
    (lam x : ℝ) (Y : ℝ → Ω → ℝ) (ω : Ω) (hY : Continuous fun s => Y s ω)
    (tau t : ℝ≥0) :
    quadraticVariation10 S (H025 i j lam x Y) tau t ω =
      ∫ s in (0:ℝ)..((min t tau : ℝ≥0):ℝ),
        (A025 lam 1 x)^2 + v025 (Y s ω)*(A025 lam 2 x)^2 := by
  classical
  let u : ℝ := min t tau
  have hu : 0 ≤ u := (min t tau).coe_nonneg
  have hd (k : Fin S.m) :
      (∑ l, ∫ s in (0:ℝ)..u, H025 i j lam x Y k (Real.toNNReal s) ω *
        H025 i j lam x Y l (Real.toNNReal s) ω * S.c k l (Real.toNNReal s)) =
        ∫ s in (0:ℝ)..u, (H025 i j lam x Y k (Real.toNNReal s) ω)^2 := by
    rw [Finset.sum_eq_single k]
    · simp [hc, pow_two]
    · intro l _ hl
      simp [hc, Ne.symm hl]
    · simp
  unfold quadraticVariation10
  change (∑ k, ∑ l, ∫ s in (0:ℝ)..u, _) = _
  simp_rw [hd]
  have he (k : Fin S.m) : (∫ s in (0:ℝ)..u, (H025 i j lam x Y k (Real.toNNReal s) ω)^2) =
      (if k = i then ∫ _s in (0:ℝ)..u, (A025 lam 1 x)^2 else 0) +
      (if k = j then ∫ s in (0:ℝ)..u, v025 (Y s ω)*(A025 lam 2 x)^2 else 0) := by
    by_cases hi : k = i
    · subst k
      simp [H025, hij]
    · by_cases hj : k = j
      · simp only [H025, ite_eq_right hi, ite_eq_left hj, zero_add, mul_pow, neg_sq]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs0 : 0 ≤ s := (Set.uIcc_of_le hu ▸ hs).1
        dsimp only
        rw [Real.coe_toNNReal _ hs0]
        rw [show (a025 (Y s ω))^2 = v025 (Y s ω) from
          Real.sq_sqrt (by linarith [(bounds025 (Y s ω)).1])]
      · simp [H025, hi, hj]
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hct : Continuous Real.tanh := continuous_iff_continuousAt.2 fun z =>
    (tanh_derivative025 z).continuousAt
  have hv : Continuous fun s => v025 (Y s ω)*(A025 lam 2 x)^2 :=
    (continuous_const.add (hct.comp hY)).mul continuous_const
  exact (intervalIntegral.integral_add intervalIntegrable_const (hv.intervalIntegrable _ _)).symm

lemma predictable : predictableStatement := by
  intro Ω mΩ S E i j hij hc lam x tau hl hx Y hp hY
  have hU := domains S i j lam x Y hp
  have he : ∀ᵐ ω ∂S.μ, ∀ t, quadraticVariation10 S (H025 i j lam x Y) tau t ω =
      ∫ s in (0:ℝ)..((min t tau : ℝ≥0):ℝ),
        (A025 lam 1 x)^2 + v025 (Y s ω)*(A025 lam 2 x)^2 := by
    filter_upwards [hY] with ω hω t
    exact covariance_sum S i j hij hc lam x Y ω hω tau t
  have hb : ∀ᵐ ω ∂S.μ, ∀ t, quadraticVariation10 S (H025 i j lam x Y) tau t ω ≤
      7*tau/(4*lam^2) := by
    filter_upwards [he,hY] with ω he hω t
    rw [he t]
    exact integralBound lam tau x hl tau.coe_nonneg hx (fun s => Y s ω) hω t t.coe_nonneg
  refine ⟨hU,he,hb,?_⟩
  exact E.bounded_qv_exponential_martingale _ tau _ hU (by positivity)
    (hb.mono fun ω hω => hω tau)

lemma adapted : adaptedStatement := by
  intro Ω mΩ S E P i j hij hc lam x tau hl hx Y hYa hY
  have hct : Continuous Real.tanh := continuous_iff_continuousAt.2 fun z =>
    (tanh_derivative025 z).continuousAt
  have ha : Continuous a025 := Real.continuous_sqrt.comp (continuous_const.add hct)
  have hp : IsStronglyPredictable S.ℱ (fun t ω => a025 (Y t ω)) :=
    P.continuous_predictable _ (fun t => ha.measurable.comp (hYa t))
      (fun ω => ha.comp ((hY ω).comp NNReal.continuous_coe))
  have h := predictable Ω mΩ S E i j hij hc lam x tau hl hx Y hp
    (Eventually.of_forall hY)
  exact ⟨h.1,h.2.2.2⟩

/-- The conclusion with the actual audited Upstream fields as inputs. -/
theorem upstream_adapted {Ω : Type} [mΩ : MeasurableSpace Ω]
    (S : Upstream.ItoCalculus Ω) (E : Upstream.ExponentialMartingale S)
    (P : Upstream.Predictability S.ℱ) (i j : Fin S.m) (hij : i ≠ j)
    (hc : ∀ k l t, S.c k l t = if k = l then 1 else 0)
    (lam x : ℝ) (tau : ℝ≥0) (hl : 0 < lam) (hx : 0 ≤ x)
    (Y : ℝ → Ω → ℝ) (hYa : ∀ t : ℝ≥0, Measurable[S.ℱ t] (Y t))
    (hY : ∀ ω, Continuous fun s => Y s ω) :
    Martingale (Upstream.exponential10 S (H025 i j lam x Y) tau) S.ℱ S.μ :=
  (adapted Ω mΩ (Novel.ZeroMeanReversionUpstreamBridgeProof.ofUpstream S)
    (ofUpstream S E) ⟨P.continuous_predictable⟩ i j hij hc lam x tau hl hx Y hYa hY).2

theorem boundedVarianceMartingale : Standalone.BoundedVarianceMartingale.statement :=
  ⟨predictable, adapted⟩

end Novel.BoundedVarianceMartingaleProof

import Standalone.SeparableMeetingIntegrals
import Novel.ZeroMeanReversionUpstreamBridgeProof
import Novel.BoundedVarianceIntegralComparisonProof

open MeasureTheory ProbabilityTheory Filter
open Standalone.ZeroMeanReversionUpstreamBridge
open Standalone.SeparableMeetingIntegrals
open Novel.ZeroMeanReversionUpstreamBridgeProof
open scoped NNReal
namespace Novel.SeparableMeetingIntegralsProof

lemma mask {Ω : Type*} (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0) (hle : lo ≤ hi)
    (s : ℝ≥0) (ω : Ω) :
    H026 chi lo hi s ω = if lo < s ∧ s ≤ hi then chi s ω else 0 := by
  by_cases hlo : s ≤ lo
  · simp [H026, hlo, hlo.trans hle, not_lt.mpr hlo]
  · by_cases hhi : s ≤ hi
    · simp [H026, hlo, hhi, lt_of_not_ge hlo]
    · simp [H026, hlo, hhi]

lemma stopped_domain {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (chi : ℝ≥0 → Ω → ℝ) (hchi : U4 S.ℱ S.μ chi) (b : ℝ≥0) :
    U4 S.ℱ S.μ (stoppedInt (fun _ => b) chi) := by
  refine ⟨stoppedInt_predictable S _ (stopped_const S b) chi hchi.1, fun t => ?_⟩
  filter_upwards [hchi.2 t] with ω hω
  refine (lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_).trans_lt hω
  by_cases hs : Real.toNNReal s ≤ b
  · simp [stoppedInt, hs]
  · simp [stoppedInt, hs, sq_nonneg]

lemma domain {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0) (hle : lo ≤ hi) (hchi : U4 S.ℱ S.μ chi) :
    U4 S.ℱ S.μ (H026 chi lo hi) := by
  have hlo := stopped_domain S chi hchi lo
  have hhi := stopped_domain S chi hchi hi
  refine ⟨hhi.1.sub hlo.1, fun t => ?_⟩
  filter_upwards [hchi.2 t] with ω hω
  refine (lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_).trans_lt hω
  rw [mask chi lo hi hle]
  split_ifs <;> simp [sq_nonneg]

lemma identity {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0)
    (hle : lo ≤ hi) (hchi : U4 S.ℱ S.μ chi) :
    ∀ᵐ ω ∂S.μ, ∀ t, J026 S k chi lo hi t ω =
      S.I k chi (min t hi) ω - S.I k chi (min t lo) ω := by
  apply Novel.BoundedVarianceIntegralComparisonProof.continuous_paths_eq S.μ
    (J026 S k chi lo hi) (fun t ω => S.I k chi (min t hi) ω - S.I k chi (min t lo) ω)
    (S.int_continuous k _ (domain S chi lo hi hle hchi))
  · filter_upwards [S.int_continuous k chi hchi] with ω hω
    exact (hω.comp (continuous_id.min continuous_const)).sub
      (hω.comp (continuous_id.min continuous_const))
  · intro t
    have hlin := S.int_linear k (stoppedInt (fun _ => hi) chi)
      (stoppedInt (fun _ => lo) chi) 1 (-1)
      (stopped_domain S chi hchi hi) (stopped_domain S chi hchi lo) t
    have he : (1:ℝ) • stoppedInt (fun _ => hi) chi +
        (-1:ℝ) • stoppedInt (fun _ => lo) chi = H026 chi lo hi := by
      funext s ω
      simp [H026, stoppedInt, sub_eq_add_neg, Set.Iic]
    rw [he] at hlin
    filter_upwards [hlin, S.int_stopped k chi (fun _ => hi) hchi (stopped_const S hi) t,
      S.int_stopped k chi (fun _ => lo) hchi (stopped_const S lo) t] with ω h hhi hlo
    change S.I k chi (min t hi) ω = S.I k (stoppedInt (fun _ => hi) chi) t ω at hhi
    change S.I k chi (min t lo) ω = S.I k (stoppedInt (fun _ => lo) chi) t ω at hlo
    simpa only [J026, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul,
      ← hhi, ← hlo, sub_eq_add_neg] using h

lemma integrals : Standalone.SeparableMeetingIntegrals.statement := by
  intro Ω mΩ S k chi lo hi hle hchi
  have hdom := domain S chi lo hi hle hchi
  have hid := identity S k chi lo hi hle hchi
  refine ⟨mask chi lo hi hle, hdom, S.int_adapted k _ hdom,
    S.int_continuous k _ hdom, hid, ?_, ?_⟩
  · filter_upwards [hid] with ω hω t
    constructor
    · intro ht
      simp [hω, min_eq_left ht, min_eq_left (ht.trans hle)]
    · intro ht
      simp [hω, min_eq_right ht, min_eq_right (hle.trans ht), min_eq_right hle]
  · intro a t
    simpa only [J026, zero_smul, add_zero] using S.int_linear k _ _ a 0 hdom hdom t

/-- The same result for the actual audited AX-03/AX-04 input. -/
lemma upstream_integrals {Ω : Type} [MeasurableSpace Ω] (S : Upstream.ItoCalculus Ω)
    (k : Fin S.m) (chi : ℝ≥0 → Ω → ℝ) (lo hi : ℝ≥0)
    (hle : lo ≤ hi) (hchi : Upstream.U4 S.ℱ S.μ chi) :
    Upstream.U4 S.ℱ S.μ (H026 chi lo hi) ∧
    Adapted S.ℱ (S.I k (H026 chi lo hi)) ∧
    (∀ᵐ ω ∂S.μ, Continuous fun t => S.I k (H026 chi lo hi) t ω) ∧
    (∀ᵐ ω ∂S.μ, ∀ t, S.I k (H026 chi lo hi) t ω =
      S.I k chi (min t hi) ω - S.I k chi (min t lo) ω) := by
  have h := integrals Ω _ (ofUpstream S) k chi lo hi hle hchi
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem separableMeetingIntegrals : Standalone.SeparableMeetingIntegrals.statement := integrals

end Novel.SeparableMeetingIntegralsProof

import Standalone.DiffusionMeetingPrecision
import Novel.BondOptionPriceIntervalsProof

open Standalone.BondOptionMeetingVariances Standalone.BondOptionPriceIntervals
open Standalone.DiffusionMeetingPrecision
namespace Novel.DiffusionMeetingPrecisionProof

lemma sensitivityS : Standalone.DiffusionMeetingPrecision.sensitivityStatement := by
  intro P0 m δ ε Q hP hm hδ hQ
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hφ := Novel.BondOptionPriceIntervalsProof.φ_pos (δ * Real.sqrt Q / 2)
  have hg : HasDerivAt (fun Q => δ * Real.sqrt Q / 2) (δ * (1 / (2 * Real.sqrt Q)) / 2) Q :=
    ((Real.hasDerivAt_sqrt hQ.ne').const_mul δ).div_const 2
  have hΦ := (Novel.BondOptionPriceIntervalsProof.Φ_deriv (δ * Real.sqrt Q / 2)).comp Q hg
  have hC := ((hΦ.const_mul 2).sub_const 1).const_mul (P0 * m)
  refine ⟨P0 * m * (2 * (φ0167 (δ * Real.sqrt Q / 2) * (δ * (1 / (2 * Real.sqrt Q)) / 2))), hC,
    by positivity, ?_⟩
  rw [eta]
  field_simp

lemma estimatorS : Standalone.DiffusionMeetingPrecision.estimatorStatement := by
  intro lam hlam
  refine ⟨fun Q w u hQ0 hw1 hinc ℓ hℓ => ?_, fun η hη0 hη ℓ hℓ => ⟨fun Q e he0 he => ?_, ?_⟩⟩
  · have h1 := hinc 1 le_rfl
    simp only [Nat.sub_self, hQ0, sub_zero, hw1, zero_add] at h1
    have hu : Q 1 / lam 1 = u := by rw [h1]; field_simp [(hlam 1).ne']
    rw [vhat, hu, hinc ℓ (by omega)]
    ring
  · have hdiff : vhat lam (Q + e) ℓ - vhat lam Q ℓ = e ℓ - e (ℓ - 1) - lam ℓ / lam 1 * e 1 := by
      simp only [vhat, Pi.add_apply]
      field_simp
      ring
    rw [hdiff]
    have h1 : |lam ℓ / lam 1 * e 1| ≤ lam ℓ / lam 1 * η 1 := by
      rw [abs_mul, abs_of_pos (div_pos (hlam ℓ) (hlam 1))]
      exact mul_le_mul_of_nonneg_left (he 1) (div_pos (hlam ℓ) (hlam 1)).le
    calc |e ℓ - e (ℓ - 1) - lam ℓ / lam 1 * e 1|
        ≤ |e ℓ| + |e (ℓ - 1)| + |lam ℓ / lam 1 * e 1| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ η ℓ + η (ℓ - 1) + lam ℓ / lam 1 * η 1 := by
          linarith [he ℓ, he (ℓ - 1)]
  · refine ⟨fun k => if k = ℓ then η k else if k = ℓ - 1 ∨ k = 1 then -η k else 0, ?_,
      fun k => ?_, fun Q => ?_⟩
    · simp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · simp only
      split_ifs <;> simp [abs_of_nonneg (hη k), hη k]
    · have hne1 : ℓ - 1 ≠ ℓ := by omega
      have hne2 : (1 : ℕ) ≠ ℓ := by omega
      simp only [vhat, Pi.add_apply, ite_eq_right hne1, ite_eq_right hne2, true_or, or_true,
        ite_true]
      have hpos : 0 ≤ η ℓ + η (ℓ - 1) + lam ℓ / lam 1 * η 1 :=
        add_nonneg (add_nonneg (hη ℓ) (hη _)) (mul_nonneg (div_pos (hlam ℓ) (hlam 1)).le (hη 1))
      rw [← abs_of_nonneg hpos]
      congr 1
      field_simp
      ring

theorem diffusionMeetingPrecision : Standalone.DiffusionMeetingPrecision.statement :=
  ⟨sensitivityS, estimatorS⟩

end Novel.DiffusionMeetingPrecisionProof

import Standalone.LemmaB
import Novel.MGF

/-!
# Claim 001 (Lemma B): proof

Follows `math/claims/001-lemma-b.md` with `t = -λ`: the two hypotheses say
`mgf X μ t = 1` and `mgf X μ (t / 2) = 1`, so `mgf X μ (t / 2) ^ 2 = mgf X μ t`, and the
equality case `Novel.MGF.ae_eq_const_of_mgf_half_sq_eq` gives `X = (2 / t) * log 1 = 0` a.s.
The second integrability hypothesis of the paper statement is not used: it follows from the
first (`Novel.MGF.integrable_exp_mul_half`).
-/

open MeasureTheory Real

namespace Novel.LemmaBProof

theorem lemmaB : Standalone.LemmaB.statement := by
  intro Ω _ μ _ X l hl hint1 h1 _ h2
  have hsq : ProbabilityTheory.mgf X μ (-l / 2) ^ 2 = ProbabilityTheory.mgf X μ (-l) := by
    simp only [ProbabilityTheory.mgf]
    rw [h1, h2, one_pow]
  filter_upwards [Novel.MGF.ae_eq_const_of_mgf_half_sq_eq (neg_ne_zero.mpr hl) hint1 hsq] with ω hω
  rw [hω]
  simp only [ProbabilityTheory.mgf]
  rw [h2, log_one, mul_zero]

end Novel.LemmaBProof

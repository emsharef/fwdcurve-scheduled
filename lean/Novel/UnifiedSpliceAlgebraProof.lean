import Standalone.UnifiedSpliceAlgebra

open Matrix NormedSpace
open Standalone.UnifiedSpliceAlgebra
namespace Novel.UnifiedSpliceAlgebraProof

variable {k r : ℕ} (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)

/-- `σ^B·W = ∑_μ x^μ (H^{0,μ}·W) + φ_ζ(x)·(H^ζ W)`. -/
lemma sigB_dot (x : ℝ) (W : Fin k → ℝ) :
    sigB Hp Hz c A d x ⬝ᵥ W =
      (∑ μ ∈ Finset.range (d + 1), x ^ μ * (Hp μ ⬝ᵥ W)) + ephi c A x ⬝ᵥ (Hz *ᵥ W) := by
  simp only [sigB, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_mulVec]

/-- `W·Σ^B = ∑_μ x^{μ+1}/(μ+1) (H^{0,μ}·W) + Φ_ζ(x)·(H^ζ W)`. -/
lemma dot_SigB (x : ℝ) (W : Fin k → ℝ) :
    W ⬝ᵥ SigB Hp Hz c A d x =
      (∑ μ ∈ Finset.range (d + 1), x ^ (μ + 1) / (μ + 1) * (Hp μ ⬝ᵥ W)) +
        ePhi c A x ⬝ᵥ (Hz *ᵥ W) := by
  rw [dotProduct_comm]
  simp only [SigB, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_mulVec]

lemma sigB_sharp (V : Fin k → ℝ) (x : ℝ) :
    sigB (sharp Hp V) Hz c A d x = sigB Hp Hz c A d x + V := by
  simp only [sigB, Finset.sum_range_succ', sharp, Function.update_self, pow_zero, one_smul]
  have : ∀ μ ∈ Finset.range d, x ^ (μ + 1) • Function.update Hp 0 (Hp 0 + V) (μ + 1) =
      x ^ (μ + 1) • Hp (μ + 1) := fun μ _ => by rw [Function.update_of_ne (Nat.succ_ne_zero μ)]
  rw [Finset.sum_congr rfl this]
  abel

lemma SigB_sharp (V : Fin k → ℝ) (x : ℝ) :
    SigB (sharp Hp V) Hz c A d x = SigB Hp Hz c A d x + x • V := by
  simp only [SigB, Finset.sum_range_succ', sharp, Function.update_self]
  have : ∀ μ ∈ Finset.range d, (x ^ (μ + 1 + 1) / (↑(μ + 1) + 1)) •
      Function.update Hp 0 (Hp 0 + V) (μ + 1) = (x ^ (μ + 1 + 1) / (↑(μ + 1) + 1)) • Hp (μ + 1) :=
    fun μ _ => by rw [Function.update_of_ne (Nat.succ_ne_zero μ)]
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, pow_one, Nat.cast_zero, div_one, smul_add]
  abel

lemma effectiveS : effectiveLevelStatement := by
  intro k r d Hp Hz c A bP zP bZ z V x
  have e : resid Hp Hz c A d bP zP bZ z x - resid (sharp Hp V) Hz c A d bP zP bZ z x =
      x * (sigB Hp Hz c A d x ⬝ᵥ V) + V ⬝ᵥ SigB Hp Hz c A d x + x * (V ⬝ᵥ V) := by
    simp only [resid, sigB_sharp, SigB_sharp, add_dotProduct, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    ring
  rw [e, sigB_dot, dot_SigB, Kfun]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hK : ∀ μ ∈ Finset.range d,
      x * (x ^ (μ + 1) * (Hp (μ + 1) ⬝ᵥ V)) + x ^ (μ + 1 + 1) / (↑(μ + 1) + 1) * (Hp (μ + 1) ⬝ᵥ V) =
        (Hp (μ + 1) ⬝ᵥ V) * (((μ : ℝ) + 3) / ((μ : ℝ) + 2)) * x ^ (μ + 2) := fun μ _ => by
    push_cast
    field_simp
    ring
  have hS : x * (∑ μ ∈ Finset.range d, x ^ (μ + 1) * (Hp (μ + 1) ⬝ᵥ V)) +
      ∑ μ ∈ Finset.range d, x ^ (μ + 1 + 1) / (↑(μ + 1) + 1) * (Hp (μ + 1) ⬝ᵥ V) =
      ∑ μ ∈ Finset.range d, (Hp (μ + 1) ⬝ᵥ V) * (((μ : ℝ) + 3) / ((μ : ℝ) + 2)) * x ^ (μ + 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hK
  rw [dotProduct_smul, smul_eq_mul]
  simp only [pow_zero, one_mul, zero_add, pow_one, Nat.cast_zero, div_one]
  linear_combination hS

lemma jumpS : jumpStatement := by
  intro k r d Hp Hz c A V₀ V₁ κ₀ κ₁ Tm u T h
  have e : T • V₁ + κ₁ = (T • V₀ + κ₀) + (T - Tm) • (V₁ - V₀) := by
    have : κ₁ = κ₀ + -Tm • (V₁ - V₀) := by rw [← h]; abel
    rw [this]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp only [cross, e, dotProduct_add, sub_dotProduct]
  ring

/-- Along the later intervals, the non-level loadings see the current noise and `κ = −u V`. -/
lemma chain {Hp : ℕ → Fin k → ℝ} {Hz : Matrix (Fin r) (Fin k) ℝ} {d : ℕ} {V κ : ℕ → Fin k → ℝ}
    {Tm : ℕ → ℝ} {j m : ℕ} {u : ℝ} (hjm : j ≤ m) (hκ : κ j = -u • V j)
    (hcont : ∀ m', j < m' → m' ≤ m → κ m' - κ (m' - 1) = -Tm m' • (V m' - V (m' - 1)))
    (horth : ∀ m', j < m' → m' ≤ m → (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V m' - V (m' - 1)) = 0) ∧
      Hz *ᵥ (V m' - V (m' - 1)) = 0) :
    (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ V m = Hp μ ⬝ᵥ V j ∧ Hp μ ⬝ᵥ κ m = -u * (Hp μ ⬝ᵥ V j)) ∧
      Hz *ᵥ V m = Hz *ᵥ V j ∧ Hz *ᵥ κ m = -u • (Hz *ᵥ V j) := by
  induction m, hjm using Nat.le_induction with
  | base =>
    refine ⟨fun μ _ _ => ⟨rfl, by rw [hκ, dotProduct_smul, smul_eq_mul]⟩, rfl, ?_⟩
    rw [hκ, mulVec_smul]
  | succ n hjn ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun m' h1 h2 => hcont m' h1 (h2.trans (Nat.le_succ n)))
      (fun m' h1 h2 => horth m' h1 (h2.trans (Nat.le_succ n)))
    have hc := hcont (n + 1) (Nat.lt_succ_of_le hjn) le_rfl
    obtain ⟨ho1, ho2⟩ := horth (n + 1) (Nat.lt_succ_of_le hjn) le_rfl
    simp only [Nat.add_sub_cancel] at hc ho1 ho2
    have hV : V (n + 1) = V n + (V (n + 1) - V n) := by abel
    have hK : κ (n + 1) = κ n + -Tm (n + 1) • (V (n + 1) - V n) := by rw [← hc]; abel
    refine ⟨fun μ h1 h2 => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hV, dotProduct_add, ho1 μ h1 h2, add_zero, (ih1 μ h1 h2).1]
    · rw [hK, dotProduct_add, dotProduct_smul, ho1 μ h1 h2, smul_zero, add_zero, (ih1 μ h1 h2).2]
    · rw [hV, mulVec_add, ho2, add_zero, ih2]
    · rw [hK, mulVec_add, mulVec_smul, ho2, smul_zero, add_zero, ih3]

lemma nonLevelS : nonLevelStatement := by
  intro k r d Hp Hz c A V κ Tm j m u T hjm hκ hcont horth
  obtain ⟨h1, h2, h3⟩ := chain hjm hκ hcont horth
  have hW : ∀ μ : ℕ, Function.update Hp 0 0 (μ + 1) = Hp (μ + 1) := fun μ =>
    Function.update_of_ne (Nat.succ_ne_zero μ) _ _
  unfold crossNL cross
  rw [sigB_dot, dot_SigB, Finset.sum_range_succ', Finset.sum_range_succ', Function.update_self,
    zero_dotProduct, zero_dotProduct, mul_zero, mul_zero, add_zero, add_zero]
  simp only [hW]
  have hT : ∀ μ ∈ Finset.range d, (T - u) ^ (μ + 1) * (Hp (μ + 1) ⬝ᵥ (T • V m + κ m)) +
      (T - u) ^ (μ + 1 + 1) / (↑(μ + 1) + 1) * (Hp (μ + 1) ⬝ᵥ V m) =
      (Hp (μ + 1) ⬝ᵥ V j) * (((μ : ℝ) + 3) / ((μ : ℝ) + 2)) * (T - u) ^ (μ + 2) := fun μ hμ => by
    have hb := h1 (μ + 1) (Nat.succ_pos μ) (Finset.mem_range.1 hμ)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hb.1, hb.2]
    push_cast
    field_simp
    ring
  have hS : (∑ μ ∈ Finset.range d, (T - u) ^ (μ + 1) * (Hp (μ + 1) ⬝ᵥ (T • V m + κ m))) +
      ∑ μ ∈ Finset.range d, (T - u) ^ (μ + 1 + 1) / (↑(μ + 1) + 1) * (Hp (μ + 1) ⬝ᵥ V m) =
      ∑ μ ∈ Finset.range d, (Hp (μ + 1) ⬝ᵥ V j) * (((μ : ℝ) + 3) / ((μ : ℝ) + 2)) * (T - u) ^ (μ + 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hT
  rw [Kfun, mulVec_add, mulVec_smul, h2, h3]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hS ⊢
  linear_combination hS

theorem unifiedSpliceAlgebra : Standalone.UnifiedSpliceAlgebra.statement :=
  ⟨effectiveS, jumpS, nonLevelS⟩

end Novel.UnifiedSpliceAlgebraProof

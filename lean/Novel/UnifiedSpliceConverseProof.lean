import Standalone.UnifiedSpliceConverse
import Novel.UnifiedSpliceNecessityProof
import Novel.SpliceStateBlockAX01Proof

open Matrix NormedSpace Set Filter
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceConverse
namespace Novel.UnifiedSpliceConverseProof

variable {k r : ℕ} (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)

/-! ### Analyticity -/

lemma ephi_an (i : Fin r) (x : ℝ) : AnalyticAt ℝ (fun y => ephi c A y i) x :=
  Novel.SpliceStateBlockAX01Proof.row_analytic c A i x (mem_univ x)

lemma ePhi_an (i : Fin r) (x : ℝ) : AnalyticAt ℝ (fun y => ePhi c A y i) x := by
  have e : (fun y => ePhi c A y i) = fun y => ((c ᵥ* A⁻¹) ᵥ* exp (y • A)) i - (c ᵥ* A⁻¹) i := by
    funext y
    simp only [ePhi, mul_sub, mul_one, vecMul_sub, vecMul_vecMul, Pi.sub_apply]
  rw [e]
  exact (Novel.SpliceStateBlockAX01Proof.row_analytic _ A i x (mem_univ x)).sub analyticAt_const

lemma sigB_an (l : Fin k) (x : ℝ) : AnalyticAt ℝ (fun y => sigB Hp Hz c A d y l) x := by
  have h := fun i => ephi_an c A i x
  simp only [sigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
  fun_prop

lemma SigB_an (l : Fin k) (x : ℝ) : AnalyticAt ℝ (fun y => SigB Hp Hz c A d y l) x := by
  have h := fun i => ePhi_an c A i x
  simp only [SigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
  fun_prop

lemma resid_an (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (x : ℝ) :
    AnalyticAt ℝ (fun y => resid Hp Hz c A d bP zP bZ z y) x := by
  have h1 := fun i => ephi_an c A i x
  have h2 := fun l => sigB_an Hp Hz c A d l x
  have h3 := fun l => SigB_an Hp Hz c A d l x
  simp only [resid, dotProduct]
  fun_prop

/-- `T ↦ R(T − u) − c_m(u, T)` is real-analytic. -/
lemma f_an (bP zP : ℕ → ℝ) (bZ z : Fin r → ℝ) (V κ : Fin k → ℝ) (u T : ℝ) :
    AnalyticAt ℝ (fun T => resid Hp Hz c A d bP zP bZ z (T - u) - cross Hp Hz c A d V κ u T) T := by
  have hs : AnalyticAt ℝ (fun T : ℝ => T - u) T := by fun_prop
  have h0 := (resid_an Hp Hz c A d bP zP bZ z (T - u)).comp_of_eq hs rfl
  have h1 := fun l => (sigB_an Hp Hz c A d l (T - u)).comp_of_eq hs rfl
  have h2 := fun l => (SigB_an Hp Hz c A d l (T - u)).comp_of_eq hs rfl
  simp only [Function.comp_def] at h0 h1 h2
  simp only [cross, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- An analytic function affine on an open interval is affine on `ℝ`. -/
lemma affine_ext {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) {a b α β : ℝ} (hab : a < b)
    (h : ∀ T ∈ Ioo a b, f T = α + β * T) : ∀ T, f T = α + β * T := by
  have hg : AnalyticOnNhd ℝ (fun T => f T - (α + β * T)) univ := fun x _ =>
    (hf x).sub (by fun_prop)
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  intro T
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _)
    (by filter_upwards [isOpen_Ioo.mem_nhds hmid] with y hy; simp [h y hy]) (mem_univ T)
  simp only [Pi.zero_apply] at this
  linarith

/-- The level part of the cross term is affine in `T`. -/
lemma cross_split (V κ : Fin k → ℝ) (u T : ℝ) :
    cross Hp Hz c A d V κ u T = crossNL Hp Hz c A d V κ u T +
      (T * (Hp 0 ⬝ᵥ V) + Hp 0 ⬝ᵥ κ + (T - u) * (V ⬝ᵥ Hp 0)) := by
  have e : sharp (Function.update Hp 0 0) (Hp 0) = Hp := by
    simp [sharp, Function.update_idem, Function.update_eq_self]
  have hs := Novel.UnifiedSpliceAlgebraProof.sigB_sharp (Function.update Hp 0 0) Hz c A d (Hp 0) (T - u)
  have hS := Novel.UnifiedSpliceAlgebraProof.SigB_sharp (Function.update Hp 0 0) Hz c A d (Hp 0) (T - u)
  rw [e] at hs hS
  simp only [crossNL, cross, hs, hS, add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm (Hp 0) κ]
  ring

/-! ### (b)(iv) -/

lemma converseS : converseStatement := by
  intro k r d Hp Hz c A hA hobs bP zP bZ z V κ Tm lo hi j M u hjM hκj hκ hlo
  have hNL : ∀ m, j ≤ m → m ≤ M → (∀ m', j < m' → m' ≤ m →
      (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V m' - V (m' - 1)) = 0) ∧ Hz *ᵥ (V m' - V (m' - 1)) = 0) →
      ∀ T, crossNL Hp Hz c A d (V m) (κ m) u T = Kfun Hp Hz c A d (V j) (T - u) :=
    fun m hjm hmM h492 T => Novel.UnifiedSpliceAlgebraProof.nonLevelS k r d Hp Hz c A V κ Tm j m u T
      hjm hκj (fun m' h1 h2 => hκ m' h1 (h2.trans hmM)) h492
  have hEff := Novel.UnifiedSpliceAlgebraProof.effectiveS k r d Hp Hz c A bP zP bZ z (V j)
  constructor
  · intro hcons
    have hall : ∀ m, j ≤ m → m ≤ M → ∃ α β : ℝ, ∀ T,
        resid Hp Hz c A d bP zP bZ z (T - u) - cross Hp Hz c A d (V m) (κ m) u T = α + β * T :=
      fun m h1 h2 => by
        obtain ⟨α, β, h⟩ := hcons m h1 h2
        exact ⟨α, β, affine_ext (fun x => f_an Hp Hz c A d bP zP bZ z (V m) (κ m) u x)
          (hlo m h1 h2) h⟩
    have h492 : ∀ m, j < m → m ≤ M → (∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ (V m - V (m - 1)) = 0) ∧
        Hz *ᵥ (V m - V (m - 1)) = 0 := fun m h1 h2 => by
      obtain ⟨α₁, β₁, e1⟩ := hall m h1.le h2
      obtain ⟨α₀, β₀, e0⟩ := hall (m - 1) (by omega) (by omega)
      exact Novel.UnifiedSpliceNecessityProof.necessityS k r d Hp Hz c A hA hobs (V (m - 1)) (V m)
        (κ (m - 1)) (κ m) (Tm m) u 0 1 (α₀ - α₁) (β₀ - β₁) one_pos (hκ m h1 h2) fun T _ => by
          linear_combination e0 T - e1 T
    refine ⟨h492, ?_⟩
    obtain ⟨α, β, e⟩ := hall j le_rfl hjM
    refine ⟨α + β * u + u * (Hp 0 ⬝ᵥ V j) + Hp 0 ⬝ᵥ κ j,
      β + (V j ⬝ᵥ Hp 0) - (Hp 0 ⬝ᵥ V j) - V j ⬝ᵥ V j, fun x => ?_⟩
    have e1 := e (x + u)
    have e2 := cross_split Hp Hz c A d (V j) (κ j) u (x + u)
    have e3 := hNL j le_rfl hjM (fun m' h1 h2 => absurd (h1.trans_le h2) (lt_irrefl j)) (x + u)
    have e4 := hEff x
    simp only [add_sub_cancel_right] at e1 e2 e3
    linear_combination (-1:ℝ) * e4 + e1 + e2 + e3
  · rintro ⟨h492, α, β, hR⟩ m hjm hmM
    refine ⟨α - β * u - (2 * (Hp 0 ⬝ᵥ V j) + V j ⬝ᵥ V j) * u - Hp 0 ⬝ᵥ κ m + u * (V m ⬝ᵥ Hp 0),
      β + (2 * (Hp 0 ⬝ᵥ V j) + V j ⬝ᵥ V j) - (Hp 0 ⬝ᵥ V m) - V m ⬝ᵥ Hp 0, fun T _ => ?_⟩
    have e2 := cross_split Hp Hz c A d (V m) (κ m) u T
    have e3 := hNL m hjm hmM (fun m' h1 h2 => h492 m' h1 (h2.trans hmM)) T
    have e4 := hEff (T - u)
    have e5 := hR (T - u)
    linear_combination e4 + e5 - e2 - e3

theorem unifiedSpliceConverse : Standalone.UnifiedSpliceConverse.statement := converseS

end Novel.UnifiedSpliceConverseProof

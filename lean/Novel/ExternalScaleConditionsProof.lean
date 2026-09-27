import Standalone.ExternalScaleConditions
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Matrix
open scoped NNReal
open Standalone.RecurrentLoadingAlgebra Standalone.RecurrentLoadingDrift
open Standalone.RecurrentLoadingStateP Standalone.RecurrentLoadingStateQ
open Standalone.RecurrentLoadingRestartP Standalone.ExternalScaleConditions
namespace Novel.ExternalScaleConditionsProof

variable {n d p r : ℕ}

/-- A linear map between finite-dimensional spaces is Lipschitz. -/
lemma lip_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ₗ[ℝ] F) : ∃ L : ℝ≥0, LipschitzWith L f :=
  ⟨_, by simpa using (LinearMap.toContinuousLinearMap f).lipschitz⟩

/-- The linear part of the drift. -/
noncomputable def driftLin (u v : Fin p → ℝ) (c b : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) :
    State031 n p r →ₗ[ℝ] State031 n p r where
  toFun y := (0, Ahat030 A *ᵥ y.2.1,
    fun i j => (Ahat030 (p := p) A * of y.2.2.1 + of y.2.2.1 * (Ahat030 A)ᵀ :
      Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) i j,
    Ahat030 A *ᵥ y.2.2.2 + of y.2.2.1 *ᵥ gamma030 u c)
  map_add' x y := by
    ext <;> simp [Matrix.mul_apply, mulVec, dotProduct, mul_add, add_mul,
      Finset.sum_add_distrib] <;> ring
  map_smul' a x := by
    ext <;> simp [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, mul_add] <;>
      (try simp only [Finset.mul_sum, Finset.sum_mul]) <;>
      simp only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- The scale part of the drift, as a linear function of `(μ_Z(Z), ψ(Z)²)`. -/
noncomputable def driftScale (v : Fin p → ℝ) (b : Fin r → ℝ) :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] State031 n p r where
  toFun m := (m.1, 0, fun i j => m.2 * (beta030 v b i * beta030 v b j), 0)
  map_add' x y := by ext <;> simp [add_mul]
  map_smul' a x := by ext <;> simp [mul_assoc]

/-- The diffusion, as a linear function of `(Σ_Z(Z), ψ(Z))`. -/
noncomputable def diffLin (j₀ : Fin d) (v : Fin p → ℝ) (b : Fin r → ℝ) :
    ((Fin d → Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin d → State031 n p r) where
  toFun m := fun l => (m.1 l, if l = j₀ then (fun i => m.2 * beta030 v b i) else 0, 0, 0)
  map_add' x y := by
    funext l
    by_cases hl : l = j₀ <;> ext <;> simp [hl, add_mul]
  map_smul' a x := by
    funext l
    by_cases hl : l = j₀ <;> ext <;> simp [hl, mul_assoc]

/-- The restart map as a linear map. -/
noncomputable def restartLin (M : Matrix (Fin p) (Fin p) ℝ) :
    State031 n p r →ₗ[ℝ] State031 n p r where
  toFun := restart031 M
  map_add' x y := by
    ext <;> simp [restart031, Matrix.mul_apply, mulVec, dotProduct, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' a x := by
    ext <;> simp [restart031, Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum] <;>
      (try simp only [Finset.mul_sum, Finset.sum_mul]) <;>
      simp only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- The curve map at `(D, x)` as a linear map. -/
noncomputable def curveLin (u : Fin p → ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin r → ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (D : Finset ℝ) (x : ℝ) : State031 n p r →ₗ[ℝ] ℝ where
  toFun y := curve031 u M c A y D x
  map_add' y y' := by
    simp only [curve031, Prod.fst_add, Prod.snd_add]
    simp [mulVec, dotProduct, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a y := by
    simp only [curve031, Prod.smul_fst, Prod.smul_snd]
    simp [mulVec, dotProduct, mul_add, Finset.mul_sum]
    simp only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- A bounded Lipschitz function has a Lipschitz square. -/
lemma lip_sq (ψ : (Fin n → ℝ) → ℝ) (Lψ : ℝ≥0) (Kψ : ℝ) (hψ : LipschitzWith Lψ ψ)
    (hK : ∀ z, |ψ z| ≤ Kψ) : LipschitzWith (Real.toNNReal (2 * Kψ) * Lψ) (fun z => ψ z ^ 2) := by
  have hK0 : 0 ≤ Kψ := (abs_nonneg _).trans (hK 0)
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  have h1 := hψ.dist_le_mul z z'
  rw [Real.dist_eq] at h1 ⊢
  have e : ψ z ^ 2 - ψ z' ^ 2 = (ψ z + ψ z') * (ψ z - ψ z') := by ring
  rw [e, abs_mul, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith)]
  have hs : |ψ z + ψ z'| ≤ 2 * Kψ := (abs_add_le _ _).trans (by linarith [hK z, hK z'])
  calc |ψ z + ψ z'| * |ψ z - ψ z'| ≤ 2 * Kψ * (Lψ * dist z z') :=
        mul_le_mul hs h1 (abs_nonneg _) (by linarith)
    _ = 2 * Kψ * Lψ * dist z z' := by ring

lemma conditions : conditionsStatement := by
  intro n d p r μZ sZ ψ j₀ u v M c b A Lμ Ls Lψ Kψ hμ hs hψ hK
  refine ⟨?_, ?_, ⟨LinearMap.toContinuousLinearMap (restartLin M),
      LinearMap.coe_toContinuousLinearMap' _⟩, fun y => rfl,
    fun D x => ⟨LinearMap.toContinuousLinearMap (curveLin u M c A D x),
      LinearMap.coe_toContinuousLinearMap' _⟩, fun D x y y' hy => ?_⟩
  · obtain ⟨L1, h1⟩ := lip_linear (driftLin (n := n) u v c b A)
    obtain ⟨L2, h2⟩ := lip_linear (driftScale (n := n) (p := p) v b)
    have hm : LipschitzWith _ (fun y : State031 n p r => (μZ y.1, ψ y.1 ^ 2)) :=
      (hμ.comp LipschitzWith.prod_fst).prodMk ((lip_sq ψ Lψ Kψ hψ hK).comp LipschitzWith.prod_fst)
    have heq : drift031 μZ ψ u v c b A =
        fun y => driftLin u v c b A y + driftScale v b (μZ y.1, ψ y.1 ^ 2) := by
      funext y
      ext <;> simp [drift031, driftLin, driftScale]
    rw [heq]
    exact ⟨_, h1.add (h2.comp hm)⟩
  · obtain ⟨L1, h1⟩ := lip_linear (diffLin (n := n) (p := p) j₀ v b)
    have hm : LipschitzWith _ (fun y : State031 n p r => (sZ y.1, ψ y.1)) :=
      (hs.comp LipschitzWith.prod_fst).prodMk (hψ.comp LipschitzWith.prod_fst)
    have heq : diff031 sZ ψ j₀ v b = fun y => diffLin j₀ v b (sZ y.1, ψ y.1) := by
      funext y l
      simp only [diff031, diffLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [heq]
    exact ⟨_, h1.comp hm⟩
  · simp only [curve031, hy]

theorem externalScaleConditions : Standalone.ExternalScaleConditions.statement := conditions

end Novel.ExternalScaleConditionsProof

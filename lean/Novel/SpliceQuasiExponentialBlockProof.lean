import Standalone.SpliceQuasiExponentialBlock
import Novel.SpliceQuasiExponentialKeyProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Matrix NormedSpace Set Filter Topology MeasureTheory
open Standalone.SpliceQuasiExponentialCross Standalone.SpliceQuasiExponentialBlock
namespace Novel.SpliceQuasiExponentialBlockProof

variable {r : ℕ}

section Concrete
variable (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)

/-- `φ_i(x) = (e^{Ax} b)_i`. -/
noncomputable def φ (i : Fin r) : ℝ → ℝ := fun x => (exp (x • A) *ᵥ b) i
noncomputable def ψ (i : Fin r) : ℝ → ℝ := fun x => x * φ A b i x
noncomputable def χ (p : Fin r × Fin r) : ℝ → ℝ := fun x => φ A b p.1 x * φ A b p.2 x

/-- The generators `φ_i`, `x φ_i`, `φ_i φ_j`. -/
def gens : Set (ℝ → ℝ) := range (φ A b) ∪ range (ψ A b) ∪ range (χ A b)

/-- Their span, a block containing `λ`, `x λ(x)` and `λΛ`. -/
noncomputable def V : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (gens A b)

lemma exp_add' (x h : ℝ) : exp ((x + h) • A) = exp (h • A) * exp (x • A) := by
  rw [add_smul, add_comm, Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left h).smul_right x)]

lemma φ_shift (i : Fin r) (x h : ℝ) : φ A b i (x + h) = ∑ k, exp (h • A) i k * φ A b k x := by
  simp only [φ, exp_add', ← mulVec_mulVec]
  rfl

lemma φ_mem (i : Fin r) : φ A b i ∈ V A b := Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
lemma ψ_mem (i : Fin r) : ψ A b i ∈ V A b := Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))
lemma χ_mem (p : Fin r × Fin r) : χ A b p ∈ V A b := Submodule.subset_span (Or.inr ⟨p, rfl⟩)

lemma φ_analytic (i : Fin r) : AnalyticOnNhd ℝ (φ A b i) univ := by
  have := Novel.SpliceQuasiExponentialKeyProof.analytic_g A (Pi.single i 1) b
  show AnalyticOnNhd ℝ (fun x => (exp (x • A) *ᵥ b) i) univ
  simpa [single_dotProduct] using this

lemma V_shift : ∀ g ∈ V A b, ∀ h : ℝ, (fun x => g (x + h)) ∈ V A b := by
  intro g hg h
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨p, rfl⟩
    · have e : (fun x => φ A b i (x + h)) = ∑ k, exp (h • A) i k • φ A b k := by
        funext x; simp [φ_shift, Finset.sum_apply]
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (φ_mem A b k)
    · have e : (fun x => ψ A b i (x + h)) =
          ∑ k, exp (h • A) i k • ψ A b k + ∑ k, (h * exp (h • A) i k) • φ A b k := by
        funext x
        simp only [ψ, φ_shift, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          add_mul, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ψ_mem A b k))
        (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (φ_mem A b k))
    · have e : (fun x => χ A b p (x + h)) =
          ∑ k, ∑ l, (exp (h • A) p.1 k * exp (h • A) p.2 l) • χ A b (k, l) := by
        funext x
        simp only [χ, φ_shift, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (χ_mem A b (k, l))
  | zero => exact (V A b).zero_mem
  | add f g _ _ hf hg => exact (V A b).add_mem hf hg
  | smul a f _ hf => exact (V A b).smul_mem a hf

lemma V_analytic : ∀ g ∈ V A b, AnalyticOnNhd ℝ g univ := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨p, rfl⟩
    · exact φ_analytic A b i
    · exact fun x hx => analyticAt_id.mul (φ_analytic A b i x hx)
    · exact fun x hx => (φ_analytic A b p.1 x hx).mul (φ_analytic A b p.2 x hx)
  | zero => exact fun x _ => analyticAt_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul a f _ hf => exact fun x hx => analyticAt_const.mul (hf x hx)

lemma lam_eq_sum (c : Fin r → ℝ) : lam035 c A b = ∑ i, c i • φ A b i := by
  funext x
  simp [lam035, φ, dotProduct, Finset.sum_apply]

lemma V_block (c : Fin r → ℝ) : Block035 c A b (V A b) ∧ (fun x => x * lam035 c A b x) ∈ V A b := by
  have hlam : lam035 c A b ∈ V A b := by
    rw [lam_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (φ_mem A b i)
  set d := c ᵥ* A⁻¹
  have hLam : ∀ x, Lam035 c A b x = ∑ k, d k * φ A b k x - d ⬝ᵥ b := fun x => by
    rw [Lam035, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
      dotProduct_mulVec c A⁻¹ (exp (x • A) *ᵥ b), dotProduct_mulVec c A⁻¹ b]
    rfl
  refine ⟨⟨FiniteDimensional.span_of_finite ℝ ((((finite_range _).union (finite_range _)).union
    (finite_range _))), V_analytic A b, fun g hg h _ => V_shift A b g hg h, hlam, ?_⟩, ?_⟩
  · have e : (fun x => lam035 c A b x * Lam035 c A b x) =
        ∑ i, ∑ k, (c i * d k) • χ A b (i, k) - (d ⬝ᵥ b) • lam035 c A b := by
      funext x
      simp only [hLam, lam_eq_sum, χ, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        mul_sub]
      rw [Finset.sum_mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      · rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (χ_mem A b (i, k))) (Submodule.smul_mem _ _ hlam)
  · have e : (fun x => x * lam035 c A b x) = ∑ i, c i • ψ A b i := by
      funext x
      simp only [lam_eq_sum, ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ψ_mem A b i)

end Concrete

lemma e1 : e1Statement := by
  intro r A hA b c
  have hV := V_block A b c
  have hle : E1 c A b ≤ V A b := sInf_le hV
  have := hV.1.finiteDimensional
  have hmem : ∀ g, g ∈ E1 c A b ↔ ∀ E : Submodule ℝ (ℝ → ℝ),
      Block035 c A b E ∧ (fun x => x * lam035 c A b x) ∈ E → g ∈ E := fun g => by
    rw [E1, Submodule.mem_sInf]; rfl
  refine ⟨⟨Submodule.finiteDimensional_of_le hle, fun g hg => V_analytic A b g (hle hg),
    fun g hg h hh => (hmem _).2 fun E hE => hE.1.shift g ((hmem g).1 hg E hE) h hh,
    (hmem _).2 fun E hE => hE.1.lam_mem, (hmem _).2 fun E hE => hE.1.lamLam_mem⟩,
    (hmem _).2 fun E hE => hE.2, fun E hE hx => sInf_le ⟨hE, hx⟩⟩

lemma exp_add'' (A : Matrix (Fin r) (Fin r) ℝ) (x h : ℝ) :
    exp ((x + h) • A) = exp (x • A) * exp (h • A) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left x).smul_right h)]

/-- For `(A, b)` controllable, the vectors `e^{hA} b`, `h ≥ 0`, span `ℝ^r`. -/
lemma span_top (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (hctrl : ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0) :
    Submodule.span ℝ (range fun h : Ici (0:ℝ) => exp ((h : ℝ) • A) *ᵥ b) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.2 hne) inferInstance
  let w : Fin r → ℝ := fun i => f (Pi.single i 1)
  have hfw : ∀ v, f v = w ⬝ᵥ v := fun v => by
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp only [dotProduct, smul_eq_mul, w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ h : ℝ, 0 ≤ h → w ⬝ᵥ (exp (h • A) *ᵥ b) = 0 := fun h hh => by
    rw [← hfw]
    have hm := Submodule.mem_map_of_mem (f := f)
      (Submodule.subset_span ⟨⟨h, hh⟩, rfl⟩ : exp (h • A) *ᵥ b ∈
        Submodule.span ℝ (range fun h : Ici (0:ℝ) => exp ((h : ℝ) • A) *ᵥ b))
    rw [hmap] at hm
    simpa using hm
  have hall : ∀ u, w ⬝ᵥ (exp (u • A) *ᵥ b) = 0 := fun u =>
    (Novel.SpliceQuasiExponentialKeyProof.analytic_g A w b).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ 1) (by
        filter_upwards [Ioi_mem_nhds one_pos] with v hv using hzero v (le_of_lt hv))
      (mem_univ u)
  have hk : ∀ k : ℕ, ∀ u : ℝ, w ⬝ᵥ ((A ^ k * exp (u • A)) *ᵥ b) = 0 := by
    intro k
    induction k with
    | zero => intro u; rw [pow_zero, one_mul]; exact hall u
    | succ k ih =>
      intro u
      have hd := Novel.RecurrenceNecessityReductionProof.deriv_g A w b k u
      have h0 : HasDerivAt (fun u : ℝ => w ⬝ᵥ ((A ^ k * exp (u • A)) *ᵥ b)) 0 u := by
        rw [show (fun u : ℝ => w ⬝ᵥ ((A ^ k * exp (u • A)) *ᵥ b)) = fun _ => (0:ℝ) from funext ih]
        exact hasDerivAt_const u 0
      exact hd.unique h0
  have hw : w = 0 := hctrl w fun k => by simpa using hk k 0
  exact hf0 (LinearMap.ext fun v => by rw [hfw, hw, zero_dotProduct]; rfl)

/-- Every block contains `x ↦ c e^{Ax} y` for every `y`, when `(A, b)` is controllable. -/
lemma mem_cexp (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (hctrl : ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0)
    (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E) (y : Fin r → ℝ) :
    (fun x => c ⬝ᵥ (exp (x • A) *ᵥ y)) ∈ E := by
  let Φ : (Fin r → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun y x => c ⬝ᵥ (exp (x • A) *ᵥ y)
      map_add' := fun y z => by funext x; simp [mulVec_add, dotProduct_add]
      map_smul' := fun a y => by funext x; simp [mulVec_smul, dotProduct_smul] }
  have hle : Submodule.span ℝ (range fun h : Ici (0:ℝ) => exp ((h : ℝ) • A) *ᵥ b) ≤ E.comap Φ :=
    Submodule.span_le.2 (by
      rintro _ ⟨⟨h, hh⟩, rfl⟩
      show Φ (exp (h • A) *ᵥ b) ∈ E
      have e : Φ (exp (h • A) *ᵥ b) = fun x => lam035 c A b (x + h) := by
        funext x
        simp [Φ, lam035, mulVec_mulVec, exp_add'']
      rw [e]
      exact hE.shift _ hE.lam_mem h hh)
  rw [span_top A b hctrl] at hle
  exact hle (Submodule.mem_top : y ∈ ⊤)

/-- A block containing `x λ(x)` contains `x ↦ x c e^{Ax} y` for every `y`. -/
lemma mem_xcexp (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → ℝ)
    (hctrl : ∀ w : Fin r → ℝ, (∀ k : ℕ, w ⬝ᵥ ((A ^ k) *ᵥ b) = 0) → w = 0)
    (E : Submodule ℝ (ℝ → ℝ)) (hE : Block035 c A b E) (hx : (fun x => x * lam035 c A b x) ∈ E)
    (y : Fin r → ℝ) : (fun x => x * c ⬝ᵥ (exp (x • A) *ᵥ y)) ∈ E := by
  let Ψ : (Fin r → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun y x => x * c ⬝ᵥ (exp (x • A) *ᵥ y)
      map_add' := fun y z => by funext x; simp [mulVec_add, dotProduct_add, mul_add]
      map_smul' := fun a y => by funext x; simp [mulVec_smul, dotProduct_smul]; ring }
  have hle : Submodule.span ℝ (range fun h : Ici (0:ℝ) => exp ((h : ℝ) • A) *ᵥ b) ≤ E.comap Ψ :=
    Submodule.span_le.2 (by
      rintro _ ⟨⟨h, hh⟩, rfl⟩
      show Ψ (exp (h • A) *ᵥ b) ∈ E
      have e : Ψ (exp (h • A) *ᵥ b) =
          (fun x => (x + h) * lam035 c A b (x + h)) - h • fun x => lam035 c A b (x + h) := by
        funext x
        simp [Ψ, lam035, mulVec_mulVec, exp_add'']
        ring
      rw [e]
      exact E.sub_mem (hE.shift _ hx h hh) (E.smul_mem h (hE.shift _ hE.lam_mem h hh)))
  rw [span_top A b hctrl] at hle
  exact hle (Submodule.mem_top : y ∈ ⊤)

/-- A finite-dimensional, forward-shift invariant space of continuous functions is closed under
`g ↦ (x ↦ ∫_0^t w(u) g(x + t − u) du)`. -/
lemma int_mem (E : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ E]
    (hcont : ∀ g ∈ E, Continuous g) (hshift : ∀ g ∈ E, ∀ h : ℝ, 0 ≤ h → (fun x => g (x + h)) ∈ E)
    (g : ℝ → ℝ) (hg : g ∈ E) (w : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hw : IntervalIntegrable w volume 0 t) :
    (fun x => ∫ u in (0:ℝ)..t, w u * g (x + (t - u))) ∈ E := by
  let τ : ℝ → E := fun h => ⟨fun x => g (x + max h 0), hshift g hg _ (le_max_right _ _)⟩
  have hτc : Continuous τ := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro x
    exact (hcont g hg).comp (continuous_const.add (continuous_id.max continuous_const))
  let B := Module.finBasis ℝ E
  have hcoord : ∀ k, Continuous fun h => B.coord k (τ h) := fun k =>
    (LinearMap.continuous_of_finiteDimensional (B.coord k)).comp hτc
  have hexp : ∀ h x, g (x + max h 0) = ∑ k, B.coord k (τ h) * (B k : ℝ → ℝ) x := by
    intro h x
    have h1 : ((τ h : E) : ℝ → ℝ) = ∑ k, B.repr (τ h) k • ((B k : E) : ℝ → ℝ) := by
      have h0 := congrArg Subtype.val (B.sum_repr (τ h))
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    have h2 := congrFun h1 x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have hi : ∀ k, IntervalIntegrable (fun u => w u * B.coord k (τ (t - u))) volume 0 t := fun k =>
    hw.mul_continuousOn ((hcoord k).comp (continuous_const.sub continuous_id)).continuousOn
  have e : (fun x => ∫ u in (0:ℝ)..t, w u * g (x + (t - u))) =
      ∑ k, (∫ u in (0:ℝ)..t, w u * B.coord k (τ (t - u))) • (B k : ℝ → ℝ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [← intervalIntegral.integral_mul_const]
    rw [← intervalIntegral.integral_finsetSum fun k _ => (hi k).mul_const _]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht] at hu
    have hm : max (t - u) 0 = t - u := max_eq_left (by linarith [hu.2])
    have := hexp (t - u) x
    rw [hm] at this
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (B k).2

lemma blockPart : blockPartStatement := by
  intro r A b c E hE t ht
  have := hE.finiteDimensional
  have h := int_mem E (fun g hg => continuousOn_univ.1 (hE.analytic g hg).continuousOn)
    (fun g hg h hh => hE.shift g hg h hh) _ hE.lamLam_mem (fun _ => (1:ℝ)) t ht
    intervalIntegrable_const
  simpa only [one_mul] using h

theorem spliceQuasiExponentialBlock : Standalone.SpliceQuasiExponentialBlock.statement := ⟨e1, blockPart⟩

end Novel.SpliceQuasiExponentialBlockProof

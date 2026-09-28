import Standalone.FrontEndConstructionRepresentation
import Novel.FrontEndConstructionProcessProof
import Novel.SpliceLocalizationRegularityProof
import Novel.SeparableMeetingRepresentationProof
import Novel.RecurrentLoadingStatePProof

/-! # Claim 055 (c): the assembled representation satisfies (2.2) (proof)

* `lin_derivs`: for `f(s, y) = Σ_i a_i(s) y_i` with `a_i ∈ C²`, `∂_t f = Σ a_i' y_i`, `∂_i f = a_i`
  and every second state derivative vanishes (Check, Part 1).
* (c)(i): AX-05 (`ito_formula`) for the stack `X = (Z, L_m, C_m)` and
  `Φ_T(t, y) = Σ_μ (T − t)^μ z_{0,μ} + c e^{(T−t)A} ζ + l + c T`, with `m = n(T)`. The drift is
  `−∂_x F(T − u, Z_u) + Σ_k b_k φ_k(T − u) + ℓ_m(u) + c_m(u) T = alpha049`, and the noise, combined by
  linearity (`integral_sum_all`), is `V_m + Σ_k φ_k(T − u) H^k = sig049`. At `t = 0` the stack is
  its initial value almost surely (`int_zero`).
* (c)(ii): `alpha049` and `sig049` are Borel in the data, which is progressive (stage 2). The
  envelopes are Claim 050's (`SpliceLocalizationRegularity`), path by path.

Reused, not reproved: stage 2 (`driverForm_pred`, `driftS`, `pt_fields`, `prog_path_meas`,
`drift_int`'s events), `Novel.SpliceLocalizationRegularityProof` (`sigEnvS`, `alphaEnvS`,
`envelopeS`), `Novel.SeparableMeetingRepresentationProof.integral_sum_all`, `domain_sum`,
`Novel.ZeroMeanReversionUpstreamBridgeProof.dT_general`, `dX_general`,
`Novel.RecurrentLoadingStatePProof.exp_entry_hasDerivAt`, and the calculus fields `ito_formula`,
`int_zero`.
-/

open MeasureTheory Set Filter Matrix Topology NormedSpace
open scoped NNReal ENNReal
open Standalone.ZeroMeanReversionUpstreamBridge (ItoCalculus U4 LocallyIntegrableDrift driverForm dT dX
  dXX)
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.SpliceLocalizationConverse Standalone.FrontEndConstructionMatching
  Standalone.FrontEndConstructionProcess Standalone.FrontEndConstructionRepresentation

namespace Novel.FrontEndConstructionRepresentationProof

/-! ### Functions linear in the state -/

section Lin
variable {n : ℕ} (a : Fin n → ℝ → ℝ)

/-- `Σ_i a_i(s) y_i`. -/
noncomputable def linF (p : ℝ × (Fin n → ℝ)) : ℝ := ∑ i, a i p.1 * p.2 i

variable {a} (ha : ∀ i, ContDiff ℝ 2 (a i))
include ha

lemma linF_smooth : ContDiff ℝ 2 (linF a) :=
  ContDiff.sum fun i _ => ((ha i).comp contDiff_fst).mul ((contDiff_apply ℝ ℝ i).comp contDiff_snd)

lemma linF_dT (s : ℝ) (y : Fin n → ℝ) : dT (linF a) (s, y) = ∑ i, deriv (a i) s * y i := by
  rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dT_general _ (linF_smooth ha)]
  have h : HasDerivAt (fun u => ∑ i, a i u * y i) (∑ i, deriv (a i) s * y i) s :=
    HasDerivAt.fun_sum fun i _ =>
      (((ha i).differentiable (by norm_num) s).hasDerivAt).mul_const (y i)
  exact h.deriv

lemma linF_dX (s : ℝ) (y : Fin n → ℝ) (j : Fin n) : dX (linF a) (s, y) j = a j s := by
  classical
  rw [Novel.ZeroMeanReversionUpstreamBridgeProof.dX_general _ (linF_smooth ha)]
  have e : (fun u => linF a (s, Function.update y j u)) =
      fun u => (∑ i, a i s * y i) + a j s * (u - y j) := by
    funext u
    have hu : Function.update y j u = y + Pi.single j (u - y j) := by
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    simp only [linF, hu, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [e]
  have h : HasDerivAt (fun u => (∑ i, a i s * y i) + a j s * (u - y j)) (a j s) (y j) := by
    simpa using (((hasDerivAt_id (y j)).sub_const (y j)).const_mul (a j s)).const_add
      (∑ i, a i s * y i)
  exact h.deriv

lemma linF_dXX (s : ℝ) (y : Fin n → ℝ) (i j : Fin n) : dXX (linF a) (s, y) i j = 0 := by
  have hf := linF_smooth ha
  have hf' : Differentiable ℝ (fderiv ℝ (linF a)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc : (fun q : ℝ × (Fin n → ℝ) => fderiv ℝ (linF a) q (0, Pi.single j 1)) =
      fun q => a j q.1 := funext fun q => linF_dX ha q.1 q.2 j
  have h1 : HasFDerivAt (fun q : ℝ × (Fin n → ℝ) => fderiv ℝ (linF a) q (0, Pi.single j 1))
      ((fderiv ℝ (fderiv ℝ (linF a)) (s, y)).flip (0, Pi.single j 1)) (s, y) := by
    simpa using (hf' (s, y)).hasFDerivAt.clm_apply (hasFDerivAt_const (0, Pi.single j 1) (s, y))
  have h2 : HasFDerivAt (fun q : ℝ × (Fin n → ℝ) => a j q.1)
      ((fderiv ℝ (a j) s).comp (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (s, y) :=
    (((ha j).differentiable (by norm_num) s).hasFDerivAt).comp (s, y) (hasFDerivAt_fst)
  rw [hc] at h1
  have e := congrArg (fun L => L (0, Pi.single i 1)) (h1.unique h2)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', map_zero] at e
  exact e

end Lin

/-! ### The coefficients of `Φ_T` -/

section Coef
variable {d r : ℕ} (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (T : ℝ)

/-- The coefficients of `Φ_T(t, y) = Σ_μ (T − t)^μ z_{0,μ} + c e^{(T−t)A} ζ + l + c T`, on the stack
`(Z, L, C)`. -/
noncomputable def aT : Fin (d + 1 + r + 2) → ℝ → ℝ :=
  Fin.append (Fin.append (fun (μ : Fin (d + 1)) (s : ℝ) => (T - s) ^ (μ : ℕ))
    (fun (i : Fin r) (s : ℝ) => ephi c A (T - s) i)) ![fun _ => 1, fun _ => T]

lemma sum_split {M : Type*} [AddCommMonoid M] (g : Fin (d + 1 + r + 2) → M) :
    ∑ i, g i = (∑ μ : Fin (d + 1), g (Fin.castAdd 2 (Fin.castAdd r μ))) +
      (∑ i : Fin r, g (Fin.castAdd 2 (Fin.natAdd (d + 1) i))) +
      g (Fin.natAdd (d + 1 + r) 0) + g (Fin.natAdd (d + 1 + r) 1) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [add_assoc]

lemma ephi_hasDeriv (i : Fin r) (x : ℝ) :
    HasDerivAt (fun y => ephi c A y i) ((ephi c A x ᵥ* A) i) x := by
  have h : HasDerivAt (fun y => ephi c A y i) (∑ j, c j * (A * exp (x • A)) j i) x := by
    simp only [ephi, vecMul, dotProduct]
    exact HasDerivAt.fun_sum fun j _ =>
      (Novel.RecurrentLoadingStatePProof.exp_entry_hasDerivAt A j i x).const_mul _
  convert h using 1
  have hc : A * exp (x • A) = exp (x • A) * A :=
    (Commute.exp_right ((Commute.refl A).smul_right x)).eq
  show (ephi c A x ᵥ* A) i = (c ᵥ* (A * exp (x • A))) i
  rw [hc, ← vecMul_vecMul]
  rfl

lemma aT_smooth : ∀ i, ContDiff ℝ 2 (aT (d := d) c A T i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun μ => ?_) (fun i => ?_) j
    · simp only [aT, Fin.append_left]
      fun_prop
    · simp only [aT, Fin.append_left, Fin.append_right]
      refine contDiff_iff_contDiffAt.2 fun s => ?_
      have hs : AnalyticAt ℝ (fun s : ℝ => T - s) s := by fun_prop
      exact ((Novel.UnifiedSpliceConverseProof.ephi_an c A i (T - s)).comp_of_eq hs rfl).contDiffAt
  · simp only [aT, Fin.append_right]
    fin_cases j <;> simp <;> fun_prop

lemma daP (μ : Fin (d + 1)) (s : ℝ) :
    deriv (aT (r := r) c A T (Fin.castAdd 2 (Fin.castAdd r μ))) s =
      -((μ : ℕ) * (T - s) ^ ((μ : ℕ) - 1)) := by
  simp only [aT, Fin.append_left]
  have h : HasDerivAt (fun s => (T - s) ^ (μ : ℕ)) ((μ : ℕ) * (T - s) ^ ((μ : ℕ) - 1) * -1) s := by
    convert ((hasDerivAt_id s).const_sub T).pow (μ : ℕ) using 1
    · funext x; simp
    · simp
  rw [h.deriv]
  ring

lemma daZ (i : Fin r) (s : ℝ) :
    deriv (aT (d := d) c A T (Fin.castAdd 2 (Fin.natAdd (d + 1) i))) s =
      -((ephi c A (T - s) ᵥ* A) i) := by
  simp only [aT, Fin.append_left, Fin.append_right]
  have h : HasDerivAt (fun s => ephi c A (T - s) i) ((ephi c A (T - s) ᵥ* A) i * -1) s :=
    (ephi_hasDeriv c A i (T - s)).comp s ((hasDerivAt_id s).const_sub T)
  rw [h.deriv]
  ring

lemma daL (s : ℝ) : deriv (aT (d := d) (r := r) c A T (Fin.natAdd (d + 1 + r) 0)) s = 0 := by
  simp [aT, Fin.append_right]

lemma daC (s : ℝ) : deriv (aT (d := d) (r := r) c A T (Fin.natAdd (d + 1 + r) 1)) s = 0 := by
  simp [aT, Fin.append_right]

end Coef

/-! ### The drift and the noise, pointwise -/

section Alg
variable {k d r : ℕ} (c : Fin r → ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) (T s : ℝ)

/-- AX-05's drift for `Φ_T` is `alpha049` with the matching front-end drifts. -/
lemma drift_alg (p : Pt049 k r) (y kv : Fin (d + 1 + r + 2) → ℝ)
    (hzP : ∀ μ : Fin (d + 1), p.zP μ = y (Fin.castAdd 2 (Fin.castAdd r μ)))
    (hz : ∀ i, p.z i = y (Fin.castAdd 2 (Fin.natAdd (d + 1) i)))
    (hbP : ∀ μ : Fin (d + 1), p.bP μ = kv (Fin.castAdd 2 (Fin.castAdd r μ)))
    (hbZ : ∀ i, p.bZ i = kv (Fin.castAdd 2 (Fin.natAdd (d + 1) i)))
    (hL : kv (Fin.natAdd (d + 1 + r) 0) = dL050 c A d S p s (nS S T))
    (hC : kv (Fin.natAdd (d + 1 + r) 1) = dC050 c A d S p s (nS S T)) :
    (∑ i, deriv (aT c A T i) s * y i) + ∑ i, aT c A T i s * kv i =
      alpha049 c A d S (matched c A d S p s) s T := by
  rw [sum_split, sum_split]
  simp only [daP, daZ, daL, daC]
  simp only [aT, Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp only [alpha049, matched, driftB049, dotProduct, Finset.sum_range, hzP, hbP, hbZ, hL, hC]
  simp only [vecMul, dotProduct]
  have e1 : ∑ μ : Fin (d + 1), -((μ : ℕ) * (T - s) ^ ((μ : ℕ) - 1)) *
      y (Fin.castAdd 2 (Fin.castAdd r μ)) = -∑ μ : Fin (d + 1),
        ((μ : ℕ) : ℝ) * y (Fin.castAdd 2 (Fin.castAdd r μ)) * (T - s) ^ ((μ : ℕ) - 1) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have e2 : ∑ i : Fin r, -(∑ j, ephi c A (T - s) j * A j i) * y (Fin.castAdd 2 (Fin.natAdd (d + 1) i)) =
      -∑ i : Fin r, (∑ j, ephi c A (T - s) j * A j i) * y (Fin.castAdd 2 (Fin.natAdd (d + 1) i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ μ : Fin (d + 1), (T - s) ^ (μ : ℕ) * kv (Fin.castAdd 2 (Fin.castAdd r μ)) =
      ∑ μ : Fin (d + 1), kv (Fin.castAdd 2 (Fin.castAdd r μ)) * (T - s) ^ (μ : ℕ) :=
    Finset.sum_congr rfl fun μ _ => by ring
  have e4 : ∑ i, ephi c A (T - s) i * (A *ᵥ p.z) i =
      ∑ i : Fin r, (∑ j, ephi c A (T - s) j * A j i) * y (Fin.castAdd 2 (Fin.natAdd (d + 1) i)) := by
    have h := Matrix.dotProduct_mulVec (ephi c A (T - s)) A p.z
    simp only [dotProduct, vecMul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [hz]
  rw [e1, e2, e3, e4]
  ring

/-- AX-05's noise for `Φ_T` is `sig049`. -/
lemma noise_alg (p : Pt049 k r) (h : Fin (d + 1 + r + 2) → Fin k → ℝ) (l : Fin k)
    (hHp : ∀ μ : Fin (d + 1), p.Hp μ l = h (Fin.castAdd 2 (Fin.castAdd r μ)) l)
    (hHz : ∀ i, p.Hz i l = h (Fin.castAdd 2 (Fin.natAdd (d + 1) i)) l)
    (hV : h (Fin.natAdd (d + 1 + r) 0) l = p.V (nS S T) l)
    (h0 : h (Fin.natAdd (d + 1 + r) 1) l = 0) :
    ∑ i, aT c A T i s * h i l = sig049 c A d S p s T l := by
  rw [sum_split]
  simp only [aT, Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hV, h0]
  simp only [sig049, sigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, Finset.sum_range, hHp, hHz]
  ring

end Alg

/-! ### (c)(i) -/

open Novel.FrontEndConstructionProcessProof in
theorem representationS : representationStatement := by
  intro Ω _ IC d r c A S H x₀ HB KB V hSet l₀ c₀ T hT0 hTH
  obtain ⟨hm, hHB, hKB, hV⟩ := id hSet
  have hmS : nS S T ≤ S.card := Finset.card_filter_le _ _
  obtain ⟨hL, hC⟩ := driftS Ω IC d r c A S H x₀ HB KB V hSet (nS S T) hmS
  let x' : Fin (d + 1 + r + 2) → ℝ := Fin.append x₀ ![l₀ (nS S T), c₀ (nS S T)]
  let H' : Fin (d + 1 + r + 2) → Fin IC.m → ℝ≥0 → Ω → ℝ :=
    Fin.append HB ![V (nS S T), fun _ _ _ => 0]
  let K' : Fin (d + 1 + r + 2) → ℝ≥0 → Ω → ℝ :=
    Fin.append KB ![ell IC c A S H x₀ HB KB V (nS S T), cee IC c A S H x₀ HB KB V (nS S T)]
  have hH' : ∀ i k, U4 IC.ℱ IC.μ (H' i k) := fun i k => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [H'] using hHB j k
    · fin_cases j
      · simpa [H'] using hV (nS S T) k
      · simpa [H'] using U4_const IC 0
  have hK' : ∀ i, LocallyIntegrableDrift IC.ℱ IC.μ (K' i) := fun i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [K'] using hKB j
    · fin_cases j
      · simpa [K'] using hL
      · simpa [K'] using hC
  have ha := aT_smooth (d := d) c A T
  obtain ⟨h1, h2⟩ := IC.ito_formula _ x' H' K' (linF (aT c A T)) hH' hK' (linF_smooth ha)
  set X := driverForm IC.I x' H' K' with hXdef
  have hXZ : ∀ t ω j, X t ω (Fin.castAdd 2 j) = driverForm IC.I x₀ HB KB t ω j := fun t ω j => by
    simp [hXdef, driverForm, x', H', K']
  have hXL : ∀ t ω, X t ω (Fin.natAdd (d + 1 + r) 0) =
      Lproc IC c A S H x₀ HB KB V (nS S T) (l₀ (nS S T)) t ω := fun t ω => by
    simp [hXdef, driverForm, x', H', K', Lproc]
  have hXC : ∀ t ω, X t ω (Fin.natAdd (d + 1 + r) 1) =
      Cproc IC c A S H x₀ HB KB V (nS S T) (c₀ (nS S T)) t ω := fun t ω => by
    simp [hXdef, driverForm, x', H', K', Cproc]
  have hfX : ∀ (t : ℝ≥0) ω, linF (aT c A T) ((t : ℝ), X t ω) =
      fwd IC c A S H x₀ HB KB V l₀ c₀ t T ω := fun t ω => by
    simp only [linF]
    rw [sum_split]
    simp only [aT, Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hXZ, hXL, hXC, fwd, Fblock, dotProduct, pIdx, zIdx]
    ring_nf
  -- the noise
  let g : Fin (d + 1 + r + 2) → Fin IC.m → ℝ≥0 → Ω → ℝ := fun i k s ω =>
    dX (linF (aT c A T)) ((s : ℝ), X s ω) i * H' i k s ω
  have hg : ∀ k, (fun (s : ℝ≥0) ω => ∑ i, (1 : ℝ) * g i k s ω) =
      fun (s : ℝ≥0) ω => sig049 c A d S (pt IC x₀ HB KB V s ω) s T k := fun k => by
    funext s ω
    simp only [one_mul, g, linF_dX ha]
    refine noise_alg c A S T s (pt IC x₀ HB KB V s ω) (fun i l => H' i l s ω) k
      (fun μ => ?_) (fun i => ?_) ?_ ?_
    · simp [pt, H', pIdx]
      simp only [Nat.lt_succ_iff.1 μ.2, ↓reduceDIte]; rfl
    · simp [pt, H', zIdx]
    · simp [pt, H']
    · simp [H']
  refine ⟨fun l => ?_, ?_⟩
  · rw [← hg l]
    exact Novel.SeparableMeetingRepresentationProof.domain_sum IC (fun i => g i l) (fun _ => 1)
      (fun i => h1 i l) Finset.univ
  have hsum : ∀ᵐ ω ∂IC.μ, ∀ k t, IC.I k (fun u ω => ∑ i, (1 : ℝ) * g i k u ω) t ω =
      ∑ i, (1 : ℝ) * IC.I k (g i k) t ω := ae_all_iff.2 fun k =>
    Novel.SeparableMeetingRepresentationProof.integral_sum_all IC k (fun i => g i k) (fun _ => 1)
      (fun i => h1 i k)
  have hX0 : ∀ᵐ ω ∂IC.μ, ∀ j k, IC.I k (H' j k) 0 ω = 0 :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => IC.int_zero k _ (hH' j k)
  filter_upwards [h2, hsum, hX0] with ω hito hsum hX0 t ht
  have e0 : X 0 ω = x' := by
    funext j
    simp [hXdef, driverForm, hX0]
  have hf0 : linF (aT c A T) (0, x') = fwd IC c A S H x₀ HB KB V l₀ c₀ 0 T ω := by
    rw [← hfX 0 ω, e0, NNReal.coe_zero]
  rw [← hfX t ω, hito t, hf0]
  congr 1
  · congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hsH : s ≤ H := hs.2.trans (ht.trans hTH)
    simp only [linF_dT ha, linF_dX ha, linF_dXX ha, zero_mul, Finset.sum_const_zero, mul_zero,
      add_zero]
    refine drift_alg c A S T s (pt IC x₀ HB KB V s ω) (X s.toNNReal ω)
      (fun i => K' i s.toNNReal ω) (fun μ => ?_) (fun i => ?_) (fun μ => ?_) (fun i => ?_) ?_ ?_
    · simp [pt, hXZ, pIdx]
      simp only [Nat.lt_succ_iff.1 μ.2, ↓reduceDIte]; rfl
    · simp [pt, hXZ, zIdx]
    · simp [pt, K', pIdx]
      simp only [Nat.lt_succ_iff.1 μ.2, ↓reduceDIte]; rfl
    · simp [pt, K', zIdx]
    · simp [K', ell, Real.coe_toNNReal _ hs.1, hsH]
    · simp [K', cee, Real.coe_toNNReal _ hs.1, hsH]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hg k, hsum k t]
    simp [g]

/-! ### (c)(ii) -/

section RegMeas
variable {α : Type*} {mα : MeasurableSpace α} {k d r : ℕ} (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset ℝ) {p : α → Pt049 k r} {u T : α → ℝ}

lemma comp_nat {F : α → ℕ → ℝ} (hF : ∀ m, Measurable[mα] fun a => F a m) {n : α → ℕ}
    (hn : Measurable[mα] n) : Measurable[mα] fun a => F a (n a) := by
  let _ := mα
  have h : Measurable fun q : α × ℕ => F q.1 q.2 := measurable_from_prod_countable_left hF
  exact h.comp (measurable_id'.prodMk hn)

lemma ephi_cont (i : Fin r) : Continuous fun x => ephi c A x i :=
  continuous_iff_continuousAt.2 fun x => (Novel.UnifiedSpliceConverseProof.ephi_an c A i x).continuousAt

variable (hHp : ∀ μ l, Measurable[mα] fun a => (p a).Hp μ l)
  (hHz : ∀ i l, Measurable[mα] fun a => (p a).Hz i l) (hbP : ∀ μ, Measurable[mα] fun a => (p a).bP μ)
  (hzP : ∀ μ, Measurable[mα] fun a => (p a).zP μ) (hbZ : ∀ i, Measurable[mα] fun a => (p a).bZ i)
  (hz : ∀ i, Measurable[mα] fun a => (p a).z i) (hV : ∀ m l, Measurable[mα] fun a => (p a).V m l)
  (hu : Measurable[mα] u) (hT : Measurable[mα] T)
include hHp hHz hbP hzP hbZ hz hV hu hT

/-- `α(u, T)` is Borel in the data and `(u, T)`. -/
lemma alpha_meas :
    Measurable[mα] fun a => alpha049 c A d S (matched c A d S (p a) (u a)) (u a) (T a) := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hT
  have hL : Measurable fun a => dL050 c A d S (p a) (u a) (nS S (T a)) :=
    comp_nat (F := fun a m => dL050 c A d S (p a) (u a) m) (fun m =>
      Novel.FrontEndConstructionProcessProof.dL_meas c A d S hHp hHz hbP hzP hbZ hz hV hu m) hn
  have hC : Measurable fun a => dC050 c A d S (p a) (u a) (nS S (T a)) :=
    comp_nat (F := fun a m => dC050 c A d S (p a) (u a) m) (fun m =>
      Novel.FrontEndConstructionProcessProof.dC_meas c A d S hHp hHz hbP hzP hbZ hz hV hu m) hn
  have he : ∀ i, Measurable fun a => ephi c A (T a - u a) i := fun i =>
    (ephi_cont c A i).measurable.comp (hT.sub hu)
  simp only [alpha049, matched, driftB049, dotProduct, mulVec]
  fun_prop

omit hbP hzP hbZ hz in
/-- `σ_l(u, T)` is Borel in the data and `(u, T)`. -/
lemma sig_meas (l : Fin k) : Measurable[mα] fun a => sig049 c A d S (p a) (u a) (T a) l := by
  let _ := mα
  have hn := (Novel.UnifiedSpliceStep0Proof.nS_meas S).comp hT
  have hVc := Novel.FrontEndConstructionProcessProof.Vidx_meas hV hn l
  have he : ∀ i, Measurable fun a => ephi c A (T a - u a) i := fun i =>
    (ephi_cont c A i).measurable.comp (hT.sub hu)
  simp only [sig049, sigB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct]
  fun_prop

end RegMeas

section Joint
variable {Ω : Type} [MeasurableSpace Ω] (IC : ItoCalculus Ω)

/-- A progressive process is jointly measurable in `(u, ω)`. -/
lemma prog_joint {P : ℝ≥0 → Ω → ℝ} (hP : IsStronglyProgressive IC.ℱ P) :
    Measurable fun q : ℝ × Ω => P q.1.toNNReal q.2 := by
  have hN : ∀ N : ℕ, Measurable fun q : ℝ × Ω => P (min q.1 (N : ℝ)).toNNReal q.2 := fun N => by
    have h1 : Measurable[Subtype.instMeasurableSpace.prod (IC.ℱ (N : ℝ≥0))]
        fun p : Set.Iic (N : ℝ≥0) × Ω => P p.1 p.2 := (hP (N : ℝ≥0)).measurable
    have h3 : Measurable fun q : ℝ × Ω => (⟨(min q.1 (N : ℝ)).toNNReal, by
        simp only [Set.mem_Iic]
        exact Real.toNNReal_le_iff_le_coe.2 (by simp)⟩ : Set.Iic (N : ℝ≥0)) :=
      (measurable_real_toNNReal.comp (measurable_fst.min measurable_const)).subtype_mk
    have h4 : @Measurable (ℝ × Ω) Ω _ (IC.ℱ (N : ℝ≥0)) Prod.snd :=
      measurable_snd.mono le_rfl (IC.ℱ.le _)
    exact h1.comp (h3.prodMk h4)
  refine measurable_of_tendsto_metrizable hN (tendsto_pi_nhds.2 fun q => ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈q.1⌉₊) fun N hN => ?_
  rw [min_eq_left ((Nat.le_ceil q.1).trans (by exact_mod_cast hN))]

open Novel.FrontEndConstructionProcessProof in
/-- The fields of `D(u, ω)` are jointly measurable in `(u, T, ω)`. -/
lemma pt_joint {d r : ℕ} {x₀ : Fin (d + 1 + r) → ℝ} {HB : Fin (d + 1 + r) → Fin IC.m → ℝ≥0 → Ω → ℝ}
    {KB : Fin (d + 1 + r) → ℝ≥0 → Ω → ℝ} {V : ℕ → Fin IC.m → ℝ≥0 → Ω → ℝ}
    (hSet : Setting IC HB KB V) :
    let p := fun q : ℝ × ℝ × Ω => pt IC x₀ HB KB V q.1 q.2.2
    (∀ μ l, Measurable fun q => (p q).Hp μ l) ∧ (∀ i l, Measurable fun q => (p q).Hz i l) ∧
    (∀ μ, Measurable fun q => (p q).bP μ) ∧ (∀ μ, Measurable fun q => (p q).zP μ) ∧
    (∀ i, Measurable fun q => (p q).bZ i) ∧ (∀ i, Measurable fun q => (p q).z i) ∧
    (∀ m l, Measurable fun q => (p q).V m l) := by
  intro p
  obtain ⟨hm, hHB, hKB, hV⟩ := hSet
  have hZ : ∀ j, IsStronglyProgressive IC.ℱ fun t ω => driverForm IC.I x₀ HB KB t ω j := fun j =>
    (driverForm_pred IC hm x₀ HB KB hHB hKB j).isStronglyProgressive
  have P : ∀ {Q : ℝ≥0 → Ω → ℝ}, IsStronglyProgressive IC.ℱ Q →
      Measurable fun q : ℝ × ℝ × Ω => Q q.1.toNNReal q.2.2 := fun hQ =>
    (prog_joint IC hQ).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  refine ⟨fun μ l => ?_, fun j l => ?_, fun μ => ?_, fun μ => ?_, fun j => ?_, fun j => ?_,
    fun m l => ?_⟩
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hHB _ l).1.isStronglyProgressive
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · simp only [p, pt, Matrix.of_apply]; exact P (hHB _ l).1.isStronglyProgressive
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hKB _).1
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · by_cases h : μ < d + 1
    · simp only [p, pt, h, ↓reduceDIte]; exact P (hZ _)
    · simp only [p, pt, h, ↓reduceDIte]; exact measurable_const
  · exact P (hKB _).1
  · exact P (hZ _)
  · exact P (hV m l).1.isStronglyProgressive

end Joint

open Novel.FrontEndConstructionProcessProof in
theorem regularityS : regularityStatement := by
  intro Ω _ IC d r c A S H x₀ HB KB V hSet
  obtain ⟨hm, hHB, hKB, hV⟩ := id hSet
  refine ⟨fun T i => ?_, fun T l i => ?_, ?_, fun l => ?_, ?_⟩
  · obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, hVf, hu⟩ := pt_fields (x₀ := x₀) hSet i
    let _ : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (IC.ℱ i)
    exact (alpha_meas c A S hHp hHz hbP hzP hbZ hz hVf hu measurable_const).stronglyMeasurable
  · obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, hVf, hu⟩ := pt_fields (x₀ := x₀) hSet i
    let _ : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (IC.ℱ i)
    exact (sig_meas c A S hHp hHz hVf hu measurable_const l).stronglyMeasurable
  · obtain ⟨hHp, hHz, hbP, hzP, hbZ, hz, hVf⟩ := pt_joint IC (x₀ := x₀) hSet
    exact alpha_meas c A S hHp hHz hbP hzP hbZ hz hVf measurable_fst
      (measurable_fst.comp measurable_snd)
  · obtain ⟨hHp, hHz, -, -, -, -, hVf⟩ := pt_joint IC (x₀ := x₀) hSet
    exact sig_meas c A S hHp hHz hVf measurable_fst (measurable_fst.comp measurable_snd) l
  · obtain ⟨Cσ, hσ⟩ := Novel.SpliceLocalizationRegularityProof.sigEnvS IC.m r d c A S H
    obtain ⟨Cα, hα⟩ := Novel.SpliceLocalizationRegularityProof.alphaEnvS IC.m r d c A S H
    filter_upwards [path_hyps (S := S) (H := H) (x₀ := x₀) hSet] with ω ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hE := Novel.SpliceLocalizationRegularityProof.envelopeS IC.m r d c A S H
      (fun u => pt IC x₀ HB KB V u ω) h1 h2 h3 h4 h5 h6 h7
    set Bσ : Fin IC.m → ℝ → ℝ := fun l u =>
      (∑ m ∈ Finset.range (S.card + 1), |(pt IC x₀ HB KB V u ω).V m l|) +
        Cσ * ((∑ μ ∈ Finset.range (d + 1), |(pt IC x₀ HB KB V u ω).Hp μ l|) +
          ∑ i, |(pt IC x₀ HB KB V u ω).Hz i l|)
    refine ⟨fun u => ∑ l, Bσ l u, _, memLp_finsetSum _ fun l _ => (hE Cσ).1 l, (hE Cα).2,
      fun u T hu huT hTH => ⟨fun l => ?_, ?_⟩⟩
    · have hb : ∀ l', |sig049 c A d S (pt IC x₀ HB KB V u ω) u T l'| ≤ Bσ l' u := fun l' =>
        hσ _ u T hu huT hTH l'
      exact (hb l).trans (Finset.single_le_sum (f := fun l' => Bσ l' u)
        (fun l' _ => (abs_nonneg _).trans (hb l')) (Finset.mem_univ l))
    · exact hα _ u T hu huT hTH

theorem frontEndConstructionRepresentation : Standalone.FrontEndConstructionRepresentation.statement := ⟨representationS, regularityS⟩

end Novel.FrontEndConstructionRepresentationProof

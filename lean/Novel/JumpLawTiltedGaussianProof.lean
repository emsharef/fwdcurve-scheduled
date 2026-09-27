import Standalone.JumpLawTiltedGaussian
import Novel.PiecewiseAffineIntegralProof
import Novel.JumpLawCore
import Novel.JumpLawExample
import Novel.Theorem1Proof

/-!
# Claim 008 (jump law, tilted Gaussian): proof

Follows `math/claims/008-jump-law-tilted-gaussian.md`.

Proved here:

* Step 0, the identity (8.2), from Claim 006's Part (a) in the form (6.5)
  (`Novel.PiecewiseAffineIntegralProof.integral_eq'`) with `t = T_n`, `j = n`, and the
  identification of the constant `e_{nk}(T_n)` of (6.4) with `S_k` (`e_eq_S`).
* Part (a). Steps 1 to 3 without regular conditional distributions: (H) is read as an identity
  of lower integrals over `G`-sets (`lintegral_of_H`), the exponent is split by (8.2) and
  `exp (-S_k) = D_k` (`exp_neg_S`), and the `G`-measurable factor `exp (-y_k τ²/2)` is
  stripped by the trim lemma (`Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq`),
  giving the Laplace identity on `G`-sets (`Novel.JumpLawCore.LaplaceOn`) for each interval.
  Then (8.3) by the trim lemma with the weight `Z_k`; (8.4) and (8.5) by the single-interval
  core (`Novel.JumpLawCore.ae_nonneg_of_laplaceOn`, `law_eq_of_laplaceOn`), which contain
  Steps 4 to 6: the dyadic iteration of Claim 001's inequality and the law identification on
  each `G`-set by the one-sided uniqueness theorem of `Novel/MGFUniqueness.lean`.
* Part (b). From (8.5) on `A ∈ G`, the tilted law of `X_k` on `A` and the Gaussian mixture
  over `A` agree as measures on `ℝ`, so their lower integrals against `exp (-τ x)` agree; the
  trim lemma restores the factor `exp (-y_k τ²/2)`, and `ae_eq_condExp_of_forall_setIntegral_eq`
  gives (H). The hypothesis (8.3) is not needed for this direction.

* Part (c). The tilt vectors `θ_t = θ₀ + t e` make the exponent of the conditional Gaussian
  identity a quadratic in `t` (`lin_add`, `quad_add`, `sum_ico_ite`, `sum_eq_ite`); (H) forces
  (8.6) through the Laplace identity, the trim lemma, a.e. equality via the trimmed measure, and
  Claim 006's three-point identification at `t = 0, L_k/4, L_k/2`; (8.6) gives (H) through
  `const_term_eq` and the passage from set identities back to (H).
* Part (d). The example of `Novel/JumpLawExample.lean`, `P = N(0,1) ⊗ N(0,1)`,
  `X₁ = fst`, `X₂ = sign (X₁ + 1) · |snd|`, with (H) by Fubini and the symmetry of the
  tilted density, and non-Gaussianity of `X₂` from the symmetrized moment generating
  function identity at `u = 1, 2` (which forces `N(0, 1)`) against `P(X₂ > 0) > 1/2`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.JumpLawTiltedGaussianProof

open Standalone.JumpLawTiltedGaussian Standalone.LemmaA Standalone.PiecewiseAffineIntegral

/-- The constant `e_{nk}(T_n)` of (6.4), for the data `a m = X m`, `b m = y m` (`m ≥ n`) and
`0` before `n`, is `S_k` of (8.2). -/
lemma e_eq_S {Ω : Type} {τ : ℕ → ℝ} {n k : ℕ} {X y : ℕ → Ω → ℝ} (ω : Ω) (hnk : n ≤ k) :
    e τ (fun m => if n ≤ m then X m ω else 0) (fun m => if n ≤ m then y m ω else 0) n k (τ n) =
      S τ n X y k ω := by
  rcases hnk.lt_or_eq with hlt | rfl
  · simp only [e, hlt, ↓reduceIte, S, L]
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    simp only [le_refl, ↓reduceIte, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_eq_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hnm : n ≤ m := (Nat.le_succ n).trans (Finset.mem_Ico.1 hm).1
      simp only [hnm, ↓reduceIte]
      ring
  · simp [e, S]

/-- `exp (-S_k) = D_k = R_k / Z_k`. -/
lemma exp_neg_S {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (X y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    Real.exp (-S τ n X y k ω) = D τ n X y k ω := by
  simp only [S, D, R, Z, ← Real.exp_sub]
  congr 1
  rw [Finset.sum_add_distrib, neg_add, sub_eq_add_neg]
  congr 2
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- `D_k > 0`. -/
lemma D_pos {Ω : Type} (τ : ℕ → ℝ) (n : ℕ) (X y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    0 < D τ n X y k ω :=
  div_pos (Real.exp_pos _) (Real.exp_pos _)

/-- Measurability of `D_k` (from that of the `X m`, `y m`). -/
lemma measurable_D {Ω : Type} {m₀ : MeasurableSpace Ω} (τ : ℕ → ℝ) (n : ℕ) {X y : ℕ → Ω → ℝ}
    {k : ℕ} (hX : ∀ m ∈ Finset.Ico n k, Measurable[m₀] (X m))
    (hy : ∀ m ∈ Finset.Ico n k, Measurable[m₀] (y m)) :
    Measurable[m₀] (D τ n X y k) := by
  unfold D R Z
  refine Measurable.div (Real.measurable_exp.comp (Measurable.neg ?_))
    (Real.measurable_exp.comp ?_)
  · exact Finset.measurable_sum _ fun m hm => measurable_const.mul (hX m hm)
  · exact Finset.measurable_sum _ fun m hm => ((hy m hm).mul measurable_const).div_const _

/-- `Z_k` is `G`-measurable when the `y m` are. -/
lemma measurable_Z {Ω : Type} {G : MeasurableSpace Ω} (τ : ℕ → ℝ) (n : ℕ) {y : ℕ → Ω → ℝ}
    {k : ℕ} (hy : ∀ m ∈ Finset.Ico n k, Measurable[G] (y m)) : Measurable[G] (Z τ n y k) := by
  unfold Z
  exact Real.measurable_exp.comp
    (Finset.measurable_sum _ fun m hm => ((hy m hm).mul measurable_const).div_const _)

/-- (H) as an identity of lower integrals over `G`-sets: `∫⁻_A exp (-∫ ξ) dP = P A`. -/
lemma lintegral_of_H {Ω : Type} {m₀ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {G : MeasurableSpace Ω} (hG : G ≤ m₀) {τ : ℕ → ℝ} {n : ℕ}
    {ξ : ℝ → Ω → ℝ} (h : H P G τ n ξ) {T : ℝ} (hT : τ n ≤ T) {A : Set Ω}
    (hA : MeasurableSet[G] A) :
    ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P = P A := by
  let _inst : MeasurableSpace Ω := m₀
  have hce := h T hT
  have hint : Integrable (fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω))) P := by
    by_contra hni
    rw [condExp_of_not_integrable hni] at hce
    obtain ⟨ω, hω⟩ := hce.exists
    simp at hω
  have h1 : ∫ ω in A, Real.exp (-(∫ u in τ n..T, ξ u ω)) ∂P = (P A).toReal := by
    rw [← setIntegral_condExp hG hint hA, setIntegral_congr_ae (hG _ hA) (hce.mono fun ω hω _ => hω)]
    simp
    rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), h1,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Linear form of `a + t b`. -/
lemma lin_add (s : Finset ℕ) (a b v : ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ s, (a m + t * b m) * v m = ∑ m ∈ s, a m * v m + t * ∑ m ∈ s, b m * v m := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Quadratic form of `a + t b`. -/
lemma quad_add (s : Finset ℕ) (a b : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ s, ∑ m' ∈ s, (a m + t * b m) * (a m' + t * b m') * C m m' =
      ∑ m ∈ s, ∑ m' ∈ s, a m * a m' * C m m' +
        t * (∑ m ∈ s, ∑ m' ∈ s, (a m * b m' + b m * a m') * C m m') +
        t ^ 2 * ∑ m ∈ s, ∑ m' ∈ s, b m * b m' * C m m' := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m' _ => ?_
  ring

/-- A sum over `Icc n N` of a function supported on `Ico n k`, `k ≤ N`. -/
lemma sum_ico_ite {n k N : ℕ} (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc n N, (if m ∈ Finset.Ico n k then f m else 0) = ∑ m ∈ Finset.Ico n k, f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- A sum over `Icc n N` of a function supported at `k`, `n ≤ k ≤ N`. -/
lemma sum_eq_ite {n k N : ℕ} (hnk : n ≤ k) (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc n N, (if m = k then f m else 0) = f k := by
  rw [Finset.sum_ite_eq']
  simp [hnk, hk]

/-- The constant term of the tilted exponent under (8.6): with `μ m = ∑_{m' < m} L m' C m m'` and
`C` symmetric, `-∑_{m<k} L m μ m + ½ ∑∑ L L C = ½ ∑_{m<k} L m² C m m`. -/
lemma const_term_eq (Lf μ : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (hsym : ∀ a b, C a b = C b a) (n : ℕ) :
    ∀ k, n ≤ k → (∀ m ∈ Finset.Ico n k, μ m = ∑ m' ∈ Finset.Ico n m, Lf m' * C m m') →
      -(∑ m ∈ Finset.Ico n k, Lf m * μ m) +
        (∑ m ∈ Finset.Ico n k, ∑ m' ∈ Finset.Ico n k, Lf m * Lf m' * C m m') / 2 =
      ∑ m ∈ Finset.Ico n k, Lf m ^ 2 * C m m / 2 := by
  intro k hnk
  induction k, hnk using Nat.le_induction with
  | base => intro _; simp
  | succ k hnk ih =>
    intro hμ
    have ih' := ih fun m hm => hμ m (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hm).1,
      (Finset.mem_Ico.1 hm).2.trans (Nat.lt_succ_self k)⟩)
    have hμk := hμ k (Finset.mem_Ico.2 ⟨hnk, Nat.lt_succ_self k⟩)
    rw [Finset.sum_Ico_succ_top hnk, Finset.sum_Ico_succ_top hnk, Finset.sum_Ico_succ_top hnk]
    simp_rw [Finset.sum_Ico_succ_top hnk]
    rw [Finset.sum_add_distrib]
    have hcross : ∑ m ∈ Finset.Ico n k, Lf m * Lf k * C m k = ∑ m' ∈ Finset.Ico n k, Lf k * Lf m' * C k m' := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsym m k]
      ring
    rw [hcross, hμk, Finset.mul_sum]
    have : ∑ m' ∈ Finset.Ico n k, Lf k * Lf m' * C k m' = ∑ m' ∈ Finset.Ico n k, Lf k * (Lf m' * C k m') := by
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    linarith [ih']

theorem jumpLawTiltedGaussian : Standalone.JumpLawTiltedGaussian.statement := by
  refine ⟨?_, ?_⟩
  · intro Ω m₀ P _ G N n τ X y ξ hG hτ0 hτ hn1 hnN hXm hy h81 h81'
    have mono : ∀ {a b : ℕ}, a ≤ b → b ≤ N → τ a ≤ τ b := fun hab hb =>
      hτ.monotoneOn (mem_Iic.2 (hab.trans hb)) (mem_Iic.2 hb) hab
    -- (8.2)
    have h82 : ∀ ω k, n ≤ k → k ≤ N → ∀ T ∈ I τ N k,
        ∫ u in τ n..T, ξ u ω =
          S τ n X y k ω + X k ω * (T - τ k) + y k ω * (T - τ k) ^ 2 / 2 := by
      intro ω k hnk hk T hT
      have hg : ∀ k ≤ N, ∀ u ∈ I τ N k,
          ξ u ω = (if n ≤ k then X k ω else 0) + (u - τ k) • (if n ≤ k then y k ω else 0) := by
        intro k hk u hu
        split_ifs with hnk'
        · rw [h81 k hnk' hk u hu ω, smul_eq_mul]
          ring
        · rw [LemmaAProof.mem_I_iff] at hu
          have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_le hnk')
          have hkN : k < N := lt_of_lt_of_le hkn hnN
          rw [h81' u ω ((hu.2 hkN).trans_le (mono hkn hnN))]
          simp
      have htn : τ n ∈ I τ N n := by
        rw [LemmaAProof.mem_I_iff]
        exact ⟨le_rfl, fun hnN' => hτ (mem_Iic.2 hnN) (mem_Iic.2 hnN') (Nat.lt_succ_self n)⟩
      have hT' := LemmaAProof.mem_I_iff.1 hT
      have hnT : τ n ≤ T := (mono hnk hk).trans hT'.1
      have hmax : max (τ k) (τ n) = τ k := max_eq_left (mono hnk hk)
      have hτk : τ k ∈ I τ N k := LemmaAProof.mem_I_iff.2
        ⟨le_rfl, fun hkN => hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k)⟩
      rw [PiecewiseAffineIntegralProof.integral_eq' hτ hg hnT hnN hk htn hT, hmax,
        hg k hk (τ k) hτk, e_eq_S ω hnk]
      simp only [hnk, ↓reduceIte, smul_eq_mul]
      ring
    -- the interval length used for the Laplace identity on `I_k`: `L k` for `k < N`, `1` on `I_N`
    set Lk : ℕ → ℝ := fun k => if k < N then L τ k else 1 with hLk
    have hLkpos : ∀ k, k ≤ N → 0 < Lk k := fun k hk => by
      simp only [hLk]
      split_ifs with hkN
      · exact sub_pos.2 (hτ (mem_Iic.2 hk) (mem_Iic.2 hkN) (Nat.lt_succ_self k))
      · exact one_pos
    have hmemI : ∀ k, n ≤ k → k ≤ N → ∀ t ∈ Ico (0 : ℝ) (Lk k), τ k + t ∈ I τ N k := by
      intro k hnk hk t ht
      refine LemmaAProof.mem_I_iff.2 ⟨by linarith [ht.1], fun hkN => ?_⟩
      have : Lk k = L τ k := by simp [hLk, hkN]
      rw [this] at ht
      simp only [L] at ht
      linarith [ht.2]
    have hyG : ∀ m, n ≤ m → m ≤ N → Measurable[m₀] (y m) := fun m h1 h2 =>
      (hy m h1 h2).mono hG le_rfl
    have hDm : ∀ k, n ≤ k → k ≤ N → Measurable[m₀] (D τ n X y k) := fun k hnk hk =>
      measurable_D τ n (fun m hm => hXm m (Finset.mem_Ico.1 hm).1 ((Finset.mem_Ico.1 hm).2.le.trans hk))
        (fun m hm => hyG m (Finset.mem_Ico.1 hm).1 ((Finset.mem_Ico.1 hm).2.le.trans hk))
    have hZG : ∀ k, n ≤ k → k ≤ N → Measurable[G] (Z τ n y k) := fun k hnk hk =>
      measurable_Z τ n (fun m hm => hy m (Finset.mem_Ico.1 hm).1 ((Finset.mem_Ico.1 hm).2.le.trans hk))
    -- `exp (-∫ ξ)` at `T = τ k + t` as a product, from (8.2)
    have hexp : ∀ k, n ≤ k → k ≤ N → ∀ t : ℝ, τ k + t ∈ I τ N k → ∀ ω,
        Real.exp (-(∫ u in τ n..τ k + t, ξ u ω)) =
          Real.exp (-(y k ω * t ^ 2 / 2)) * (D τ n X y k ω * Real.exp (-t * X k ω)) := by
      intro k hnk hk t hT ω
      rw [h82 ω k hnk hk _ hT, ← exp_neg_S, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hFm : ∀ k, n ≤ k → k ≤ N → ∀ t : ℝ, Measurable[m₀] fun ω =>
        ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)) *
          (D τ n X y k ω * Real.exp (-t * X k ω))) := fun k hnk hk t =>
      ((Real.measurable_exp.comp (((hyG k hnk hk).mul measurable_const).div_const _).neg).mul
        ((hDm k hnk hk).mul (Real.measurable_exp.comp (measurable_const.mul (hXm k hnk hk))))).ennreal_ofReal
    -- Steps 2 and 3: (H) gives the Laplace identity on `G`-sets, for each `k`
    have hlapH : H P G τ n ξ → ∀ k, n ≤ k → k ≤ N →
        Novel.JumpLawCore.LaplaceOn P G (D τ n X y k) (X k) (y k) (Lk k) := by
        intro hH k hnk hk t ht A hA
        have hT : τ n ≤ τ k + t := (mono hnk hk).trans (by linarith [ht.1])
        have hexp := hexp k hnk hk t (hmemI k hnk hk t ht)
        have hF := hFm k hnk hk t
        have hgG : Measurable[G] (A.indicator fun ω => ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2))) :=
          (Real.measurable_exp.comp (((hy k hnk hk).mul measurable_const).div_const _)).ennreal_ofReal.indicator hA
        have hkey := Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq hG hF
          measurable_const (F' := fun _ => (1 : ℝ≥0∞))
          (fun A' hA' => by
            have := lintegral_of_H hG hH hT hA'
            simp_rw [hexp] at this
            rw [this, setLIntegral_one]) hgG
        simp only [mul_one, lintegral_indicator (hG _ hA)] at hkey
        have hL : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2))) ω *
              ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)) *
                (D τ n X y k ω * Real.exp (-t * X k ω))) ∂P =
            ∫⁻ ω in A, ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) ∂P := by
          rw [← lintegral_indicator (hG _ hA)]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ A
          · simp only [indicator_of_mem hω]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
            congr 1
            rw [show y k ω * t ^ 2 / 2 + -(y k ω * t ^ 2 / 2) = 0 by ring, Real.exp_zero, one_mul]
          · simp only [indicator_of_notMem hω, zero_mul]
        rw [← hL, hkey]
    -- from set identities back to (H): the conditional expectation is `1`
    have hH_of_set : ∀ T : ℝ, τ n ≤ T →
        (∀ A : Set Ω, MeasurableSet[G] A →
          ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P = P A) →
        Measurable[m₀] (fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω))) →
        P[fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω)) | G] =ᵐ[P] 1 := by
      intro T _ hset hfm
      let _inst : MeasurableSpace Ω := m₀
      have hint : Integrable (fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω))) P := by
        refine ⟨hfm.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
        have := hset univ MeasurableSet.univ
        rw [Measure.restrict_univ] at this
        rw [this]
        exact measure_lt_top _ _
      have hcond : (fun _ => (1 : ℝ)) =ᵐ[P]
          P[fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω)) | G] :=
        ae_eq_condExp_of_forall_setIntegral_eq hG hint
          (fun s _ _ => (integrable_const (1 : ℝ)).integrableOn)
          (fun s hs _ => by
            rw [setIntegral_const, smul_eq_mul, mul_one,
              integral_eq_lintegral_of_nonneg_ae
                (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
                hfm.aestronglyMeasurable, hset s hs]
            rfl) aestronglyMeasurable_const
      exact hcond.symm
    refine ⟨h82, ?_, ?_, ?_⟩
    · -- Part (a)
      intro hH
      have hlap := hlapH hH
      -- (8.4)
      have h84 : cond84 P n N y := fun k hnk hk =>
        Novel.JumpLawCore.ae_nonneg_of_laplaceOn hG (hDm k hnk hk) (fun ω => (D_pos τ n X y k ω).le)
          (hXm k hnk hk) (hy k hnk hk) (hLkpos k hk) (hlap k hnk hk)
      refine ⟨?_, h84, ?_⟩
      · -- (8.3): from the identity at `τ = 0` and the trim lemma with the weight `Z_k`
        intro k hnk hk A hA
        have h0 := hlap k hnk hk 0 ⟨le_rfl, hLkpos k hk⟩
        have hF : Measurable[m₀] fun ω => ENNReal.ofReal (D τ n X y k ω) := (hDm k hnk hk).ennreal_ofReal
        have hkey := Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq hG hF
          measurable_const (F' := fun _ => (1 : ℝ≥0∞))
          (fun A' hA' => by
            have := h0 A' hA'
            simp only [neg_zero, zero_mul, mul_zero, Real.exp_zero, mul_one, ne_eq,
              OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, ENNReal.ofReal_one] at this
            rw [this])
          ((hZG k hnk hk).ennreal_ofReal.indicator hA)
        simp only [mul_one, lintegral_indicator (hG _ hA)] at hkey
        have hL : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Z τ n y k ω)) ω *
              ENNReal.ofReal (D τ n X y k ω) ∂P = ∫⁻ ω in A, ENNReal.ofReal (R τ n X k ω) ∂P := by
          rw [← lintegral_indicator (hG _ hA)]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ A
          · simp only [indicator_of_mem hω]
            have hZpos : 0 ≤ Z τ n y k ω := (Real.exp_pos _).le
            rw [← ENNReal.ofReal_mul hZpos]
            congr 1
            unfold D
            have hZne : Z τ n y k ω ≠ 0 := (Real.exp_pos _).ne'
            rw [mul_div_assoc', mul_div_cancel_left₀ _ hZne]
          · simp only [indicator_of_notMem hω, zero_mul]
        rw [← hL, hkey]
      · -- (8.5)
        intro k hnk hk B hB A hA
        exact Novel.JumpLawCore.law_eq_of_laplaceOn hG (hDm k hnk hk) (fun ω => (D_pos τ n X y k ω).le)
          (hXm k hnk hk) (hy k hnk hk) (h84 k hnk hk) (hLkpos k hk) (hlap k hnk hk) hA hB
    · -- Part (b)
      intro _h83 h84 h85 T hT
      have h0T : 0 ≤ T := by
        have := mono (Nat.zero_le n) hnN
        rw [hτ0] at this
        exact this.trans hT
      obtain ⟨k, hk, hTk⟩ := Theorem1Proof.exists_index (N := N) hτ0 h0T
      have hnk : n ≤ k := Theorem1Proof.index_mono hτ hnN
        (LemmaAProof.mem_I_iff.2 ⟨le_rfl, fun hnN' => hτ (mem_Iic.2 hnN) (mem_Iic.2 hnN')
          (Nat.lt_succ_self n)⟩) hTk hT
      set t := T - τ k with htdef
      have hTt : τ k + t = T := by rw [htdef]; ring
      have hTt' : τ k + t ∈ I τ N k := hTt ▸ hTk
      -- the set-function identity (8.5) on `A` gives the lower integral of `exp (-t X)`
      have hlapA : ∀ A : Set Ω, MeasurableSet[G] A →
          ∫⁻ ω in A, ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) ∂P =
            ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) ∂P := by
        intro A hA
        let _inst : MeasurableSpace Ω := m₀
        have hy' : Measurable[m₀] (y k) := hyG k hnk hk
        have hκ : Measurable[m₀] (fun ω => gaussianReal 0 (y k ω).toNNReal) :=
          (Novel.MGFUniqueness.measurable_gaussianReal 0).comp
            (measurable_real_toNNReal.comp hy')
        -- the two measures on `ℝ`
        set μ₁ : Measure ℝ :=
          ((P.restrict A).withDensity (fun ω => ENNReal.ofReal (D τ n X y k ω))).map (X k)
          with hμ₁
        set μ₂ : Measure ℝ := (P.restrict A).bind (fun ω => gaussianReal 0 (y k ω).toNNReal)
          with hμ₂
        have hμ : μ₁ = μ₂ := by
          ext B hB
          rw [hμ₁, hμ₂, Measure.map_apply (hXm k hnk hk) hB,
            withDensity_apply _ ((hXm k hnk hk) hB), Measure.bind_apply hB hκ.aemeasurable,
            ← h85 k hnk hk B hB A hA, ← lintegral_indicator ((hXm k hnk hk) hB)]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ X k ⁻¹' B
          · simp [indicator_of_mem hω]
          · simp [indicator_of_notMem hω]
        have h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (-t * x)) ∂μ₁ =
            ∫⁻ ω in A, ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) ∂P := by
          rw [hμ₁, lintegral_map (by fun_prop) (hXm k hnk hk),
            lintegral_withDensity_eq_lintegral_mul _ (hDm k hnk hk).ennreal_ofReal (by fun_prop)]
          refine lintegral_congr fun ω => ?_
          simp only [Pi.mul_apply]
          rw [ENNReal.ofReal_mul (D_pos τ n X y k ω).le]
        have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (-t * x)) ∂μ₂ =
            ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) ∂P := by
          rw [hμ₂, Measure.lintegral_bind hκ.aemeasurable (by fun_prop)]
          refine lintegral_congr_ae (ae_restrict_of_ae ((h84 k hnk hk).mono fun ω hω => ?_))
          show ∫⁻ x, ENNReal.ofReal (Real.exp (-t * x)) ∂(gaussianReal 0 (y k ω).toNNReal) =
            ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2))
          rw [Novel.JumpLawCore.lintegral_exp_gaussianReal, Real.coe_toNNReal _ hω]
        rw [← h1, ← h2, hμ]
      -- restore the factor `exp (-y t²/2)` with the trim lemma: `∫⁻_A exp (-∫ ξ) dP = P A`
      have hset : ∀ A : Set Ω, MeasurableSet[G] A →
          ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P = P A := by
        intro A hA
        have hF : Measurable[m₀] fun ω => ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) :=
          ((hDm k hnk hk).mul (Real.measurable_exp.comp (measurable_const.mul (hXm k hnk hk)))).ennreal_ofReal
        have hF' : Measurable[m₀] fun ω => ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) :=
          (Real.measurable_exp.comp (((hyG k hnk hk).mul measurable_const).div_const _)).ennreal_ofReal
        have hgG : Measurable[G] (A.indicator fun ω => ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)))) :=
          (Real.measurable_exp.comp (((hy k hnk hk).mul measurable_const).div_const _).neg).ennreal_ofReal.indicator hA
        have hkey := Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq hG hF hF'
          hlapA hgG
        have hL : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)))) ω *
              ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) ∂P =
            ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P := by
          rw [← lintegral_indicator (hG _ hA)]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ A
          · simp only [indicator_of_mem hω]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hTt, hexp k hnk hk t hTt' ω]
          · simp only [indicator_of_notMem hω, zero_mul]
        have hR : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)))) ω *
              ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) ∂P = P A := by
          rw [← setLIntegral_one A, ← lintegral_indicator (hG _ hA)]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ A
          · simp only [indicator_of_mem hω]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
              show -(y k ω * t ^ 2 / 2) + y k ω * t ^ 2 / 2 = 0 by ring, Real.exp_zero,
              ENNReal.ofReal_one]
          · simp only [indicator_of_notMem hω, zero_mul]
        rw [← hL, hkey, hR]
      -- (H) at `T`
      have hfm : Measurable[m₀] fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω)) := by
        have : (fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω))) = fun ω =>
            Real.exp (-(y k ω * t ^ 2 / 2)) * (D τ n X y k ω * Real.exp (-t * X k ω)) := by
          funext ω
          rw [← hTt, hexp k hnk hk t hTt' ω]
        rw [this]
        exact (Real.measurable_exp.comp (((hyG k hnk hk).mul measurable_const).div_const _).neg).mul
          ((hDm k hnk hk).mul (Real.measurable_exp.comp (measurable_const.mul (hXm k hnk hk))))
      exact hH_of_set T hT hset hfm
    · -- Part (c)
      intro μc C hμG hCG hCsym hgauss
      let _inst : MeasurableSpace Ω := m₀
      -- the tilt vectors `θ_t = θ₀ + t e` (supported on `[n, N]`)
      set θ₀ : ℕ → ℕ → ℝ := fun k m => if m ∈ Finset.Ico n k then -L τ m else 0 with hθ₀
      set e : ℕ → ℕ → ℝ := fun k m => if m = k then -1 else 0 with he
      have hlin : ∀ k, n ≤ k → k ≤ N → ∀ (t : ℝ) (v : ℕ → ℝ),
          ∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * v m =
            -(∑ m ∈ Finset.Ico n k, L τ m * v m) - t * v k := by
        intro k hnk hk t v
        rw [lin_add]
        have h1 : ∑ m ∈ Finset.Icc n N, θ₀ k m * v m =
            -(∑ m ∈ Finset.Ico n k, L τ m * v m) := by
          simp only [hθ₀, ite_mul, zero_mul]
          rw [sum_ico_ite hk, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
        have h2 : ∑ m ∈ Finset.Icc n N, e k m * v m = -v k := by
          simp only [he, ite_mul, zero_mul]
          rw [sum_eq_ite hnk hk]
          ring
        rw [h1, h2]
        ring
      have hDexp : ∀ k, n ≤ k → k ≤ N → ∀ (t : ℝ) ω,
          D τ n X y k ω * Real.exp (-t * X k ω) =
            1 / Z τ n y k ω * Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * X m ω) := by
        intro k hnk hk t ω
        rw [hlin k hnk hk t (fun m => X m ω)]
        unfold D R
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring
      have hZpos : ∀ k ω, 0 < Z τ n y k ω := fun k ω => Real.exp_pos _
      -- the quadratic form
      have hQ0 : ∀ k, n ≤ k → k ≤ N → ∀ ω,
          ∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N, θ₀ k m * θ₀ k m' * C m m' ω =
            ∑ m ∈ Finset.Ico n k, ∑ m' ∈ Finset.Ico n k, L τ m * L τ m' * C m m' ω := by
        intro k hnk hk ω
        have hin : ∀ m, ∑ m' ∈ Finset.Icc n N, θ₀ k m * θ₀ k m' * C m m' ω =
            θ₀ k m * ∑ m' ∈ Finset.Ico n k, -L τ m' * C m m' ω := by
          intro m
          rw [Finset.mul_sum, ← sum_ico_ite hk]
          refine Finset.sum_congr rfl fun m' _ => ?_
          simp only [hθ₀]
          split_ifs <;> ring
        simp_rw [hin]
        simp only [hθ₀, ite_mul, zero_mul]
        rw [sum_ico_ite hk]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m' _ => ?_
        ring
      have hQe : ∀ k, n ≤ k → k ≤ N → ∀ ω,
          ∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N, e k m * e k m' * C m m' ω = C k k ω := by
        intro k hnk hk ω
        have hin : ∀ m, ∑ m' ∈ Finset.Icc n N, e k m * e k m' * C m m' ω = e k m * (-C m k ω) := by
          intro m
          have : ∀ m', e k m * e k m' * C m m' ω = if m' = k then e k m * -1 * C m m' ω else 0 := by
            intro m'
            simp only [he]
            split_ifs <;> ring
          simp_rw [this]
          rw [sum_eq_ite hnk hk]
          ring
        simp_rw [hin]
        have : ∀ m, e k m * (-C m k ω) = if m = k then -1 * -C m k ω else 0 := by
          intro m
          simp only [he]
          split_ifs <;> ring
        simp_rw [this]
        rw [sum_eq_ite hnk hk]
        ring
      have hcross : ∀ k, n ≤ k → k ≤ N → ∀ ω,
          ∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
              (θ₀ k m * e k m' + e k m * θ₀ k m') * C m m' ω =
            2 * ∑ m ∈ Finset.Ico n k, L τ m * C m k ω := by
        intro k hnk hk ω
        simp only [add_mul, Finset.sum_add_distrib]
        have hin1 : ∀ m, ∑ m' ∈ Finset.Icc n N, θ₀ k m * e k m' * C m m' ω =
            θ₀ k m * (-C m k ω) := by
          intro m
          have : ∀ m', θ₀ k m * e k m' * C m m' ω =
              if m' = k then θ₀ k m * -1 * C m m' ω else 0 := by
            intro m'
            simp only [he]
            split_ifs <;> ring
          simp_rw [this]
          rw [sum_eq_ite hnk hk]
          ring
        have hin2 : ∀ m', ∑ m ∈ Finset.Icc n N, e k m * θ₀ k m' * C m m' ω =
            θ₀ k m' * (-C k m' ω) := by
          intro m'
          have : ∀ m, e k m * θ₀ k m' * C m m' ω =
              if m = k then -1 * θ₀ k m' * C m m' ω else 0 := by
            intro m
            simp only [he]
            split_ifs <;> ring
          simp_rw [this]
          rw [sum_eq_ite hnk hk]
          ring
        rw [Finset.sum_comm (f := fun m m' => e k m * θ₀ k m' * C m m' ω)]
        simp_rw [hin1, hin2]
        have h1 : ∑ m ∈ Finset.Icc n N, θ₀ k m * (-C m k ω) = ∑ m ∈ Finset.Ico n k, L τ m * C m k ω := by
          simp only [hθ₀, ite_mul, zero_mul]
          rw [sum_ico_ite hk]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
        have h2 : ∑ m' ∈ Finset.Icc n N, θ₀ k m' * (-C k m' ω) =
            ∑ m ∈ Finset.Ico n k, L τ m * C m k ω := by
          simp only [hθ₀, ite_mul, zero_mul]
          rw [sum_ico_ite hk]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hCsym k m]
          ring
        rw [h1, h2]
        ring
      -- the exponent of the Gaussian identity as a quadratic in `t`
      set q0 : ℕ → Ω → ℝ := fun k ω => -(∑ m ∈ Finset.Ico n k, L τ m * μc m ω) +
        (∑ m ∈ Finset.Ico n k, ∑ m' ∈ Finset.Ico n k, L τ m * L τ m' * C m m' ω) / 2 with hq0
      set q1 : ℕ → Ω → ℝ := fun k ω => -μc k ω + ∑ m ∈ Finset.Ico n k, L τ m * C m k ω with hq1
      have hq : ∀ k, n ≤ k → k ≤ N → ∀ (t : ℝ) ω,
          ∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * μc m ω +
            (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
              (θ₀ k m + t * e k m) * (θ₀ k m' + t * e k m') * C m m' ω) / 2 =
            q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2) := by
        intro k hnk hk t ω
        rw [hlin k hnk hk t (fun m => μc m ω), quad_add, hQ0 k hnk hk ω, hQe k hnk hk ω,
          hcross k hnk hk ω]
        simp only [hq0, hq1]
        ring
      -- `Z_k = exp z_k`
      set z : ℕ → Ω → ℝ := fun k ω => ∑ m ∈ Finset.Ico n k, y m ω * L τ m ^ 2 / 2 with hz
      have hZ : ∀ k ω, Z τ n y k ω = Real.exp (z k ω) := fun k ω => rfl
      -- measurability of the pieces, for `G`
      have hq0G : ∀ k, Measurable[G] (q0 k) := fun k => by
        simp only [hq0]
        refine Measurable.add (Measurable.neg (Finset.measurable_sum _ fun m _ =>
          measurable_const.mul (hμG m))) (Measurable.div_const (Finset.measurable_sum _ fun m _ =>
          Finset.measurable_sum _ fun m' _ => measurable_const.mul (hCG m m')) _)
      have hq1G : ∀ k, Measurable[G] (q1 k) := fun k => by
        simp only [hq1]
        exact (hμG k).neg.add (Finset.measurable_sum _ fun m _ => measurable_const.mul (hCG m k))
      have hyGm : ∀ m, n ≤ m → m ≤ N → Measurable[G] (y m) := hy
      constructor
      · -- (⇒): (H) forces (8.6)
        intro hH
        have hlap := hlapH hH
        -- for each `k` and `t ∈ [0, L_k)`: `exp (q_t) / Z_k = exp (y_k t²/2)` a.s.
        have hpt : ∀ k, n ≤ k → k ≤ N → ∀ t ∈ Ico (0 : ℝ) (Lk k), ∀ᵐ ω ∂P,
            q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2) = z k ω + y k ω * t ^ 2 / 2 := by
          intro k hnk hk t ht
          -- the set identity
          have hsetid : ∀ A : Set Ω, MeasurableSet[G] A →
              ∫⁻ ω in A, ENNReal.ofReal (Real.exp (q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2)) /
                Z τ n y k ω) ∂P = ∫⁻ ω in A, ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) ∂P := by
            intro A hA
            rw [← hlap k hnk hk t ht A hA]
            have hF : Measurable[m₀] fun ω =>
                ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * X m ω)) := by
              refine (Real.measurable_exp.comp (Finset.measurable_sum _ fun m hm => ?_)).ennreal_ofReal
              exact measurable_const.mul (hXm m (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2)
            have hF' : Measurable[m₀] fun ω =>
                ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * μc m ω +
                  (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
                    (θ₀ k m + t * e k m) * (θ₀ k m' + t * e k m') * C m m' ω) / 2)) := by
              refine (Real.measurable_exp.comp (Measurable.add (Finset.measurable_sum _ fun m _ =>
                measurable_const.mul ((hμG m).mono hG le_rfl)) (Measurable.div_const
                (Finset.measurable_sum _ fun m _ => Finset.measurable_sum _ fun m' _ =>
                  measurable_const.mul ((hCG m m').mono hG le_rfl)) _))).ennreal_ofReal
            have hgG : Measurable[G] (A.indicator fun ω => ENNReal.ofReal (1 / Z τ n y k ω)) :=
              ((hZG k hnk hk).const_div 1).ennreal_ofReal.indicator hA
            have hkey := Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq hG hF hF'
              (fun A' hA' => hgauss (fun m => θ₀ k m + t * e k m) A' hA') hgG
            have hL : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (1 / Z τ n y k ω)) ω *
                  ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * X m ω)) ∂P =
                ∫⁻ ω in A, ENNReal.ofReal (D τ n X y k ω * Real.exp (-t * X k ω)) ∂P := by
              rw [← lintegral_indicator (hG _ hA)]
              refine lintegral_congr fun ω => ?_
              by_cases hω : ω ∈ A
              · simp only [indicator_of_mem hω]
                rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (hZpos k ω).le), hDexp k hnk hk t ω]
              · simp only [indicator_of_notMem hω, zero_mul]
            have hR : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (1 / Z τ n y k ω)) ω *
                  ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * μc m ω +
                    (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
                      (θ₀ k m + t * e k m) * (θ₀ k m' + t * e k m') * C m m' ω) / 2)) ∂P =
                ∫⁻ ω in A, ENNReal.ofReal (Real.exp (q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2)) /
                  Z τ n y k ω) ∂P := by
              rw [← lintegral_indicator (hG _ hA)]
              refine lintegral_congr fun ω => ?_
              by_cases hω : ω ∈ A
              · simp only [indicator_of_mem hω]
                rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (hZpos k ω).le), hq k hnk hk t ω]
                congr 1
                ring
              · simp only [indicator_of_notMem hω, zero_mul]
            rw [← hR, ← hkey, hL]
          -- a.s. equality of the `G`-measurable integrands, through the trimmed measure
          have hfG : Measurable[G] fun ω =>
              ENNReal.ofReal (Real.exp (q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2)) / Z τ n y k ω) :=
            ((Real.measurable_exp.comp (((hq0G k).add ((hq1G k).const_mul t)).add
              (((hCG k k).div_const 2).const_mul (t ^ 2)))).div (hZG k hnk hk)).ennreal_ofReal
          have hgGm : Measurable[G] fun ω => ENNReal.ofReal (Real.exp (y k ω * t ^ 2 / 2)) :=
            (Real.measurable_exp.comp (((hyGm k hnk hk).mul measurable_const).div_const _)).ennreal_ofReal
          have hae := ae_eq_of_ae_eq_trim (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
            (μ := P.trim hG) hfG hgGm fun A hA _ => by
              rw [setLIntegral_trim hG hfG hA, setLIntegral_trim hG hgGm hA]
              exact hsetid A hA)
          filter_upwards [hae] with ω hω
          rw [ENNReal.ofReal_eq_ofReal_iff (div_nonneg (Real.exp_pos _).le (hZpos k ω).le)
            (Real.exp_pos _).le, hZ, div_eq_iff (Real.exp_pos _).ne', ← Real.exp_add] at hω
          have := Real.exp_injective hω
          linarith
        -- three tilt parameters per interval identify the polynomial
        have hall : ∀ᵐ ω ∂P, ∀ k, n ≤ k → k ≤ N →
            ∀ t ∈ ({0, Lk k / 4, Lk k / 2} : Set ℝ),
              q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2) = z k ω + y k ω * t ^ 2 / 2 := by
          rw [ae_all_iff]
          intro k
          by_cases hk : n ≤ k ∧ k ≤ N
          · have hL := hLkpos k hk.2
            filter_upwards [hpt k hk.1 hk.2 0 ⟨le_rfl, hL⟩,
              hpt k hk.1 hk.2 (Lk k / 4) ⟨by linarith, by linarith⟩,
              hpt k hk.1 hk.2 (Lk k / 2) ⟨by linarith, by linarith⟩] with ω h0 h1 h2
            intro _ _ t ht
            simp only [mem_insert_iff, mem_singleton_iff] at ht
            rcases ht with rfl | rfl | rfl
            · exact h0
            · exact h1
            · exact h2
          · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hk
        filter_upwards [hall] with ω hω k hnk hk
        have hL := hLkpos k hk
        have hx := hω k hnk hk
        have e0 := hx 0 (by simp)
        have e1 := hx (Lk k / 4) (by simp)
        have e2 := hx (Lk k / 2) (by simp)
        have key := Novel.PiecewiseAffineIntegralProof.quadratic_zero (E := ℝ)
          (x₁ := 0) (x₂ := Lk k / 4) (x₃ := Lk k / 2) (by linarith) (by linarith) (by linarith)
          (c₀ := q0 k ω - z k ω) (c₁ := q1 k ω) (c₂ := C k k ω / 2 - y k ω / 2)
          (by simp only [smul_eq_mul]; linarith) (by simp only [smul_eq_mul]; linarith)
          (by simp only [smul_eq_mul]; linarith)
        obtain ⟨_, h1, h2⟩ := key
        refine ⟨?_, by linarith⟩
        simp only [hq1] at h1
        have : μc k ω = ∑ m ∈ Finset.Ico n k, L τ m * C m k ω := by linarith
        rw [this]
        exact Finset.sum_congr rfl fun m _ => by rw [hCsym m k]
      · -- (⇐): (8.6) gives (H)
        intro hcond T hT
        have h0T : 0 ≤ T := by
          have := mono (Nat.zero_le n) hnN
          rw [hτ0] at this
          exact this.trans hT
        obtain ⟨k, hk, hTk⟩ := Theorem1Proof.exists_index (N := N) hτ0 h0T
        have hnk : n ≤ k := Theorem1Proof.index_mono hτ hnN
          (LemmaAProof.mem_I_iff.2 ⟨le_rfl, fun hnN' => hτ (mem_Iic.2 hnN) (mem_Iic.2 hnN')
            (Nat.lt_succ_self n)⟩) hTk hT
        set t := T - τ k with htdef
        have hTt : τ k + t = T := by rw [htdef]; ring
        have hTt' : τ k + t ∈ I τ N k := hTt ▸ hTk
        -- on the event of (8.6), the weight times `exp (q_t)` is `1`
        have hone : ∀ᵐ ω ∂P, Real.exp (-(y k ω * t ^ 2 / 2)) / Z τ n y k ω *
            Real.exp (q0 k ω + t * q1 k ω + t ^ 2 * (C k k ω / 2)) = 1 := by
          filter_upwards [hcond] with ω hω
          have hq1z : q1 k ω = 0 := by
            simp only [hq1]
            rw [(hω k hnk hk).1]
            have : ∑ m ∈ Finset.Ico n k, L τ m * C k m ω = ∑ m ∈ Finset.Ico n k, L τ m * C m k ω :=
              Finset.sum_congr rfl fun m _ => by rw [hCsym k m]
            linarith
          have hq0z : q0 k ω = z k ω := by
            simp only [hq0, hz]
            have := const_term_eq (L τ) (fun m => μc m ω) (fun a b => C a b ω)
              (fun a b => congrFun (hCsym a b) ω)
              n k hnk (fun m hm => (hω m (Finset.mem_Ico.1 hm).1
                ((Finset.mem_Ico.1 hm).2.le.trans hk)).1)
            rw [this]
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [(hω m (Finset.mem_Ico.1 hm).1 ((Finset.mem_Ico.1 hm).2.le.trans hk)).2]
            ring
          rw [hq1z, hq0z, (hω k hnk hk).2, hZ, div_mul_eq_mul_div, ← Real.exp_add,
            div_eq_one_iff_eq (Real.exp_pos _).ne']
          congr 1
          ring
        have hset : ∀ A : Set Ω, MeasurableSet[G] A →
            ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P = P A := by
          intro A hA
          have hF : Measurable[m₀] fun ω =>
              ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * X m ω)) := by
            refine (Real.measurable_exp.comp (Finset.measurable_sum _ fun m hm => ?_)).ennreal_ofReal
            exact measurable_const.mul (hXm m (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2)
          have hF' : Measurable[m₀] fun ω =>
              ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * μc m ω +
                (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
                  (θ₀ k m + t * e k m) * (θ₀ k m' + t * e k m') * C m m' ω) / 2)) := by
            refine (Real.measurable_exp.comp (Measurable.add (Finset.measurable_sum _ fun m _ =>
              measurable_const.mul ((hμG m).mono hG le_rfl)) (Measurable.div_const
              (Finset.measurable_sum _ fun m _ => Finset.measurable_sum _ fun m' _ =>
                measurable_const.mul ((hCG m m').mono hG le_rfl)) _))).ennreal_ofReal
          have hgG : Measurable[G] (A.indicator fun ω =>
              ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)) / Z τ n y k ω)) :=
            ((Real.measurable_exp.comp (((hyGm k hnk hk).mul measurable_const).div_const _).neg).div
              (hZG k hnk hk)).ennreal_ofReal.indicator hA
          have hkey := Novel.CondCalculus.lintegral_mul_eq_of_forall_setLIntegral_eq hG hF hF'
            (fun A' hA' => hgauss (fun m => θ₀ k m + t * e k m) A' hA') hgG
          have hL : ∫⁻ ω, A.indicator (fun ω =>
                ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)) / Z τ n y k ω)) ω *
                ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * X m ω)) ∂P =
              ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(∫ u in τ n..T, ξ u ω))) ∂P := by
            rw [← lintegral_indicator (hG _ hA)]
            refine lintegral_congr fun ω => ?_
            by_cases hω : ω ∈ A
            · simp only [indicator_of_mem hω]
              rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (hZpos k ω).le), ← hTt,
                hexp k hnk hk t hTt' ω, hDexp k hnk hk t ω]
              congr 1
              ring
            · simp only [indicator_of_notMem hω, zero_mul]
          have hR : ∫⁻ ω, A.indicator (fun ω =>
                ENNReal.ofReal (Real.exp (-(y k ω * t ^ 2 / 2)) / Z τ n y k ω)) ω *
                ENNReal.ofReal (Real.exp (∑ m ∈ Finset.Icc n N, (θ₀ k m + t * e k m) * μc m ω +
                  (∑ m ∈ Finset.Icc n N, ∑ m' ∈ Finset.Icc n N,
                    (θ₀ k m + t * e k m) * (θ₀ k m' + t * e k m') * C m m' ω) / 2)) ∂P = P A := by
            rw [← setLIntegral_one A, ← lintegral_indicator (hG _ hA)]
            refine lintegral_congr_ae (hone.mono fun ω hω => ?_)
            by_cases hωA : ω ∈ A
            · simp only [indicator_of_mem hωA]
              rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (hZpos k ω).le),
                hq k hnk hk t ω, hω, ENNReal.ofReal_one]
            · simp only [indicator_of_notMem hωA, zero_mul]
          rw [← hL, hkey, hR]
        have hfm : Measurable[m₀] fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω)) := by
          have : (fun ω => Real.exp (-(∫ u in τ n..T, ξ u ω))) = fun ω =>
              Real.exp (-(y k ω * t ^ 2 / 2)) * (D τ n X y k ω * Real.exp (-t * X k ω)) := by
            funext ω
            rw [← hTt, hexp k hnk hk t hTt' ω]
          rw [this]
          exact (Real.measurable_exp.comp (((hyG k hnk hk).mul measurable_const).div_const _).neg).mul
            ((hDm k hnk hk).mul (Real.measurable_exp.comp (measurable_const.mul (hXm k hnk hk))))
        exact hH_of_set T hT hset hfm
  · -- Part (d): the example of `Novel/JumpLawExample.lean`
    refine ⟨ℝ × ℝ, inferInstance, JumpLawExample.P, inferInstance, JumpLawExample.τ,
      fun k ω => if k = 1 then JumpLawExample.X1 ω else JumpLawExample.X2 ω, fun _ => 1,
      JumpLawExample.ξ, by simp [JumpLawExample.τ], Nat.strictMono_cast.strictMonoOn _,
      one_pos, one_pos, ?_, ?_, JumpLawExample.H_example, ?_, ?_⟩
    · intro k hk1 hk2 u hu ω
      rw [LemmaAProof.mem_I_iff] at hu
      interval_cases k
      · simp only [JumpLawExample.τ, Nat.cast_one, one_mul, ↓reduceIte] at hu ⊢
        have h1 : ¬ u < 1 := not_lt.2 hu.1
        have h2 : u < 2 := hu.2 (by norm_num)
        simp only [JumpLawExample.ξ, h1, h2, ↓reduceIte]
      · simp only [JumpLawExample.τ, Nat.cast_ofNat, one_mul, OfNat.ofNat_ne_one,
          ↓reduceIte] at hu ⊢
        have h1 : ¬ u < 1 := not_lt.2 (by linarith [hu.1])
        have h2 : ¬ u < 2 := not_lt.2 hu.1
        simp only [JumpLawExample.ξ, h1, h2, ↓reduceIte]
    · intro u ω hu
      simp only [JumpLawExample.τ, Nat.cast_one] at hu
      simp only [JumpLawExample.ξ, hu, ↓reduceIte]
    · simpa using JumpLawExample.hasLaw_X1'
    · simpa using JumpLawExample.not_gaussian_X2

end Novel.JumpLawTiltedGaussianProof

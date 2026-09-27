import Standalone.UnifiedSpliceConverseAX01
import Novel.UnifiedSpliceQuantifiersProof

open Matrix NormedSpace MeasureTheory Set Filter Topology
open Standalone.UnifiedSpliceAlgebra Standalone.UnifiedSpliceStep0
  Standalone.UnifiedSpliceConverseAX01
open Novel.UnifiedSpliceQuantifiersProof (nS_const nS_step prim_lin)
namespace Novel.UnifiedSpliceConverseAX01Proof

variable {k r : ℕ}

/-! ### Meetings and the interval index -/

lemma nS_mono (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b) : nS S a ≤ nS S b :=
  Finset.card_le_card fun τ hτ => by
    simp only [Finset.mem_filter] at hτ ⊢; exact ⟨hτ.1, hτ.2.trans hab⟩

/-- Equal indices mean no meeting in between. -/
lemma same_free (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b) (h : nS S a = nS S b) :
    ∀ τ ∈ S, τ ∉ Ioc a b := by
  intro τ hτ hI
  have hsub : S.filter (fun x => x ≤ a) ⊂ S.filter (fun x => x ≤ b) := by
    refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨τ, ?_, ?_⟩
    · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hab⟩
    · simp only [Finset.mem_filter]; exact ⟨hτ, hI.2⟩
    · simp only [Finset.mem_filter, not_and, not_le]; exact fun _ => hI.1
  have := Finset.card_lt_card hsub
  unfold nS at h
  omega

/-- By (49.2), a non-level row sees the same front-end noise on `[u, H)`. -/
lemma row_const (S : Finset ℝ) (V : ℕ → Fin k → ℝ) (h : Fin k → ℝ) {u H : ℝ}
    (hj : ∀ τ ∈ S, u < τ → τ < H → h ⬝ᵥ (V (nS S τ) - V (nS S τ - 1)) = 0) :
    ∀ v, u ≤ v → v < H → h ⬝ᵥ V (nS S v) = h ⬝ᵥ V (nS S u) := by
  classical
  suffices ∀ N v, (S.filter fun τ => u < τ ∧ τ ≤ v).card = N → u ≤ v → v < H →
      h ⬝ᵥ V (nS S v) = h ⬝ᵥ V (nS S u) from fun v h1 h2 => this _ v rfl h1 h2
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro v hN huv hvH
  set M := S.filter fun τ => u < τ ∧ τ ≤ v
  by_cases hM : M.Nonempty
  · set τ := M.max' hM
    have hτM := M.max'_mem hM
    simp only [M, Finset.mem_filter] at hτM
    have hvτ : nS S v = nS S τ := nS_const S hτM.2.2 fun τ' hτ' hI => by
      have : τ' ≤ τ := M.le_max' τ' (by simp [M, hτ', hτM.2.1.trans hI.1, hI.2])
      linarith [hI.1]
    have hjump := hj τ hτM.1 hτM.2.1 (lt_of_le_of_lt hτM.2.2 hvH)
    rw [dotProduct_sub, sub_eq_zero] at hjump
    rw [hvτ, hjump]
    set M' := S.filter fun τ' => u < τ' ∧ τ' < τ
    by_cases hM' : M'.Nonempty
    · set w := M'.max' hM'
      have hwM := M'.max'_mem hM'
      simp only [M', Finset.mem_filter] at hwM
      have hstep : nS S w = nS S τ - 1 := nS_step S hτM.1 hwM.2.2 fun τ' hτ' hI => by
        have : τ' ≤ w := M'.le_max' τ' (by simp [M', hτ', hwM.2.1.trans hI.1, hI.2])
        linarith [hI.1]
      rw [← hstep]
      refine ih _ ?_ w rfl hwM.2.1.le (by linarith [hwM.2.2, hτM.2.2])
      rw [← hN]
      refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨τ, ?_, ?_⟩)
      · simp only [M, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.1, hx.2.2.trans (hwM.2.2.le.trans hτM.2.2)⟩
      · simp only [M, Finset.mem_filter]; exact hτM
      · simp only [Finset.mem_filter, not_and, not_le]; exact fun _ _ => hwM.2.2
    · have hstep : nS S u = nS S τ - 1 := nS_step S hτM.1 hτM.2.1 fun τ' hτ' hI =>
        hM' ⟨τ', by simp [M', hτ', hI.1, hI.2]⟩
      rw [hstep]
  · have : nS S v = nS S u := nS_const S huv fun τ hτ hI => hM ⟨τ, by simp [M, hτ, hI.1, hI.2]⟩
    rw [this]

/-- `h · P(u, T) = (T − u) h · V_{n(u)}` for a row that sees constant noise. -/
lemma row_prim (S : Finset ℝ) (p : Pt049 k r) (h : Fin k → ℝ) {u H T : ℝ} (huT : u ≤ T) (hTH : T < H)
    (hc : ∀ v, u ≤ v → v < H → h ⬝ᵥ p.V (nS S v) = h ⬝ᵥ p.V (nS S u)) :
    h ⬝ᵥ prim049 S p u T = h ⬝ᵥ ((T - u) • p.V (nS S u)) := by
  have hii : ∀ l, IntervalIntegrable (fun v => p.V (nS S v) l) volume u T := fun l =>
    Novel.UnifiedSpliceStep0Proof.pc_ii (fun n => p.V n l) S u T
  have e : h ⬝ᵥ prim049 S p u T = ∫ v in u..T, h ⬝ᵥ p.V (nS S v) := by
    simp only [prim049, dotProduct]
    rw [intervalIntegral.integral_finsetSum fun l _ => (hii l).const_mul (h l)]
    exact Finset.sum_congr rfl fun l _ => (intervalIntegral.integral_const_mul _ _).symm
  rw [e, intervalIntegral.integral_congr (g := fun _ => h ⬝ᵥ p.V (nS S u)) fun v hv => by
    rw [uIcc_of_le huT] at hv; exact hc v hv.1 (lt_of_le_of_lt hv.2 hTH)]
  simp [dotProduct_smul]

section NL
variable (Hp : ℕ → Fin k → ℝ) (Hz : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
  (A : Matrix (Fin r) (Fin r) ℝ) (d : ℕ)

/-- The non-level parts see `W` only through `H^{0,μ} W` (`μ ≥ 1`) and `H^ζ W`. -/
lemma NL_eq (x : ℝ) {W W' : Fin k → ℝ} (h1 : ∀ μ, 1 ≤ μ → μ ≤ d → Hp μ ⬝ᵥ W = Hp μ ⬝ᵥ W')
    (h2 : Hz *ᵥ W = Hz *ᵥ W') :
    sigB (Function.update Hp 0 0) Hz c A d x ⬝ᵥ W = sigB (Function.update Hp 0 0) Hz c A d x ⬝ᵥ W' ∧
    W ⬝ᵥ SigB (Function.update Hp 0 0) Hz c A d x = W' ⬝ᵥ SigB (Function.update Hp 0 0) Hz c A d x := by
  have hμ : ∀ μ ∈ Finset.range (d + 1), Function.update Hp 0 0 μ ⬝ᵥ W =
      Function.update Hp 0 0 μ ⬝ᵥ W' := fun μ hμ => by
    rcases Nat.eq_zero_or_pos μ with rfl | hpos
    · simp
    · rw [Function.update_of_ne (by omega)]
      exact h1 μ hpos (by simpa [Nat.lt_succ_iff] using hμ)
  refine ⟨?_, ?_⟩
  · rw [Novel.UnifiedSpliceAlgebraProof.sigB_dot, Novel.UnifiedSpliceAlgebraProof.sigB_dot, h2,
      Finset.sum_congr rfl fun μ hm => by rw [hμ μ hm]]
  · rw [Novel.UnifiedSpliceAlgebraProof.dot_SigB, Novel.UnifiedSpliceAlgebraProof.dot_SigB, h2,
      Finset.sum_congr rfl fun μ hm => by rw [hμ μ hm]]

/-- `σ^B = σ^B_{NL} + H^{0,0}` and `Σ^B = Σ^B_{NL} + x H^{0,0}`. -/
lemma level_split (x : ℝ) :
    sigB Hp Hz c A d x = sigB (Function.update Hp 0 0) Hz c A d x + Hp 0 ∧
    SigB Hp Hz c A d x = SigB (Function.update Hp 0 0) Hz c A d x + x • Hp 0 := by
  have e : sharp (Function.update Hp 0 0) (Hp 0) = Hp := by
    simp [sharp, Function.update_idem, Function.update_eq_self]
  have hs := Novel.UnifiedSpliceAlgebraProof.sigB_sharp (Function.update Hp 0 0) Hz c A d (Hp 0) x
  have hS := Novel.UnifiedSpliceAlgebraProof.SigB_sharp (Function.update Hp 0 0) Hz c A d (Hp 0) x
  rw [e] at hs hS
  exact ⟨hs, hS⟩

end NL

/-! ### (b)(iv), "if" -/

/-- The front end's drift slope on interval `m`, given `R♯ = α + β x`. -/
noncomputable def dCk (S : Finset ℝ) (p : Pt049 k r) (u β : ℝ) (m : ℕ) : ℝ :=
  p.V m ⬝ᵥ p.V m + p.Hp 0 ⬝ᵥ p.V m + p.V m ⬝ᵥ p.Hp 0 - β -
    (2 * (p.Hp 0 ⬝ᵥ p.V (nS S u)) + p.V (nS S u) ⬝ᵥ p.V (nS S u))

/-- The front end's drift level on interval `m`, given `R♯ = α + β x` and the primitive's `κ`. -/
noncomputable def dLk (S : Finset ℝ) (p : Pt049 k r) (u α β : ℝ) (κ : ℕ → Fin k → ℝ) (m : ℕ) : ℝ :=
  p.V m ⬝ᵥ κ m + p.Hp 0 ⬝ᵥ κ m - u * (p.V m ⬝ᵥ p.Hp 0) - α + β * u +
    (2 * (p.Hp 0 ⬝ᵥ p.V (nS S u)) + p.V (nS S u) ⬝ᵥ p.V (nS S u)) * u

/-- (b)(iv) "if", for any `κ` with `P(u, T) = T V_{n(T)} + κ_{n(T)}` off the meetings. -/
lemma converse_kappa {d : ℕ} {c : Fin r → ℝ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : IsUnit A.det)
    {S : Finset ℝ} {H u : ℝ} (p : Pt049 k r) (hu0 : 0 ≤ u) (huH : u < H) (huS : u ∉ S)
    (h492 : ∀ τ ∈ S, u < τ → τ < H →
      (∀ μ, 1 ≤ μ → μ ≤ d → p.Hp μ ⬝ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0) ∧
      p.Hz *ᵥ (p.V (nS S τ) - p.V (nS S τ - 1)) = 0)
    {α β : ℝ} (hR : ∀ x, resid (sharp p.Hp (p.V (nS S u))) p.Hz c A d p.bP p.zP p.bZ p.z x =
      α + β * x)
    (κ : ℕ → Fin k → ℝ)
    (hPk : ∀ T ∈ Ioo u H, T ∉ S → prim049 S p u T = T • p.V (nS S T) + κ (nS S T)) :
    ∀ T ∈ Icc u H, ax01At c A d S { p with dL := dLk S p u α β κ, dC := dCk S p u β } u T := by
  classical
  set j := nS S u
  set Vj := p.V j
  set Hp0 := p.Hp 0
  set sV := 2 * (Hp0 ⬝ᵥ Vj) + Vj ⬝ᵥ Vj
  -- the non-level rows see constant noise
  have hrow1 : ∀ μ, 1 ≤ μ → μ ≤ d → ∀ v, u ≤ v → v < H →
      p.Hp μ ⬝ᵥ p.V (nS S v) = p.Hp μ ⬝ᵥ Vj := fun μ h1 h2 =>
    row_const S p.V (p.Hp μ) fun τ hτ a b => (h492 τ hτ a b).1 μ h1 h2
  have hrow2 : ∀ v, u ≤ v → v < H → p.Hz *ᵥ p.V (nS S v) = p.Hz *ᵥ Vj := fun v h1 h2 =>
    funext fun i => row_const S p.V (fun l => p.Hz i l)
      (fun τ hτ a b => by
        have := congrFun (h492 τ hτ a b).2 i
        simpa only [mulVec, Pi.zero_apply] using this) v h1 h2
  let dC : ℕ → ℝ := fun m =>
    p.V m ⬝ᵥ p.V m + Hp0 ⬝ᵥ p.V m + p.V m ⬝ᵥ Hp0 - β - sV
  let dL : ℕ → ℝ := fun m =>
    p.V m ⬝ᵥ κ m + Hp0 ⬝ᵥ κ m - u * (p.V m ⬝ᵥ Hp0) - α + β * u + sV * u
  intro T hT
  show ax01At c A d S { p with dL := dL, dC := dC } u T
  set p' : Pt049 k r := { p with dL := dL, dC := dC }
  -- Step 0's identity off the meetings: `α = σ · ∫σ`
  have hE : ∀ t ∈ Ioo u H, t ∉ S → alpha049 c A d S p' u t =
      ∑ l, (∫ v in u..t, sig049 c A d S p' u v l) * sig049 c A d S p' u t l := by
    intro t ht htS
    set x := t - u
    set m := nS S t
    have hP := hPk t ht htS
    have hNL := NL_eq p.Hp p.Hz c A d x (W := prim049 S p u t) (W' := x • Vj)
      (fun μ h1 h2 => by rw [row_prim S p (p.Hp μ) ht.1.le ht.2 fun v a b => hrow1 μ h1 h2 v a b])
      (by
        funext i
        have := row_prim S p (fun l => p.Hz i l) ht.1.le ht.2
          (fun v a b => congrFun (hrow2 v a b) i)
        simpa only [mulVec] using this)
    have hNL' := NL_eq p.Hp p.Hz c A d x (W := p.V m) (W' := Vj)
      (fun μ h1 h2 => hrow1 μ h1 h2 t ht.1.le ht.2) (hrow2 t ht.1.le ht.2)
    have hK := Novel.UnifiedSpliceAlgebraProof.nonLevelS k r d p.Hp p.Hz c A p.V
      (fun _ => -u • Vj) (fun _ => 0) j j u t le_rfl rfl
      (fun m' h1 h2 => absurd (h1.trans_le h2) (lt_irrefl _))
      (fun m' h1 h2 => absurd (h1.trans_le h2) (lt_irrefl _))
    have hEff := Novel.UnifiedSpliceAlgebraProof.effectiveS k r d p.Hp p.Hz c A p.bP p.zP p.bZ
      p.z Vj x
    obtain ⟨hs, hS⟩ := level_split p.Hp p.Hz c A d x
    have hint : ∀ l, ∫ v in u..t, sig049 c A d S p' u v l =
        prim049 S p u t l + SigB p.Hp p.Hz c A d x l := fun l =>
      Novel.UnifiedSpliceStep0Proof.int_sig c A d S p' u hA t l
    have hres : resid p.Hp p.Hz c A d p.bP p.zP p.bZ p.z x = driftB049 c A d p x -
        sigB p.Hp p.Hz c A d x ⬝ᵥ SigB p.Hp p.Hz c A d x := rfl
    have hsum : ∑ l, (∫ v in u..t, sig049 c A d S p' u v l) * sig049 c A d S p' u t l =
        (prim049 S p u t + SigB p.Hp p.Hz c A d x) ⬝ᵥ (p.V m + sigB p.Hp p.Hz c A d x) := by
      simp only [dotProduct, hint]; rfl
    rw [hsum]
    show dL m + dC m * t + driftB049 c A d p x = _
    have hRx := hR x
    have hK' : sigB (Function.update p.Hp 0 0) p.Hz c A d x ⬝ᵥ (x • Vj) +
        Vj ⬝ᵥ SigB (Function.update p.Hp 0 0) p.Hz c A d x = Kfun p.Hp p.Hz c A d Vj x := by
      simp only [crossNL, cross] at hK
      convert hK using 3
      funext l; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, x, Vj]; ring
    set N := sigB (Function.update p.Hp 0 0) p.Hz c A d x
    set Ns := SigB (Function.update p.Hp 0 0) p.Hz c A d x
    set sg := sigB p.Hp p.Hz c A d x
    set Sg := SigB p.Hp p.Hz c A d x
    set P := prim049 S p u t
    set V := p.V m
    have e1 : (P + Sg) ⬝ᵥ (V + sg) = P ⬝ᵥ V + P ⬝ᵥ sg + Sg ⬝ᵥ V + Sg ⬝ᵥ sg := by
      simp only [add_dotProduct, dotProduct_add]; ring
    have e2 : P ⬝ᵥ sg = N ⬝ᵥ P + P ⬝ᵥ Hp0 := by rw [hs, dotProduct_add, dotProduct_comm P N]
    have e3 : Sg ⬝ᵥ V = V ⬝ᵥ Ns + x * (Hp0 ⬝ᵥ V) := by
      rw [hS, add_dotProduct, dotProduct_comm Ns V, smul_dotProduct, smul_eq_mul]
    have e4 : Sg ⬝ᵥ sg = sg ⬝ᵥ Sg := dotProduct_comm _ _
    have e5 := hP
    have e6 : P ⬝ᵥ V = t * (V ⬝ᵥ V) + V ⬝ᵥ κ m := by
      rw [e5, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (κ m) V]
    have e7 : P ⬝ᵥ Hp0 = t * (Hp0 ⬝ᵥ V) + Hp0 ⬝ᵥ κ m := by
      rw [e5, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (κ m) Hp0,
        dotProduct_comm V Hp0]
    have e8 : V ⬝ᵥ Hp0 = Hp0 ⬝ᵥ V := dotProduct_comm _ _
    simp only [dL, dC, sV]
    linear_combination -e1 - e2 - e3 - e4 - e6 - e7 - hNL.1 - hNL'.2 - hK' + hEff + hRx - hres
      + (t - u) * e8
  -- AX-01, by the fundamental theorem of calculus off the finitely many meetings
  have huT : u ≤ T := hT.1
  set f : Fin k → ℝ → ℝ := fun l t => ∫ v in u..t, sig049 c A d S p' u v l
  set G : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ∑ l, f l t * f l t
  have hfc : ∀ l, ContinuousOn (f l) (Icc u T) := fun l => by
    have := intervalIntegral.continuousOn_primitive_interval'
      (Novel.UnifiedSpliceStep0Proof.sig_ii c A d S p' u l u T) left_mem_uIcc
    rwa [uIcc_of_le huT] at this
  have hGc : ContinuousOn G (Icc u T) :=
    continuousOn_const.mul (continuousOn_finsetSum _ fun l _ => (hfc l).mul (hfc l))
  have hGd : ∀ t ∈ Ioo u T \ (S : Set ℝ), HasDerivAt G (alpha049 c A d S p' u t) t := by
    rintro t ⟨ht, htS⟩
    have hf : ∀ l, HasDerivAt (f l) (sig049 c A d S p' u t l) t := fun l =>
      intervalIntegral.integral_hasDerivAt_right
        (Novel.UnifiedSpliceStep0Proof.sig_ii c A d S p' u l u t)
        (Novel.UnifiedSpliceStep0Proof.sig_meas c A d S p' u l).aestronglyMeasurable.stronglyMeasurableAtFilter
        (Novel.UnifiedSpliceStep0Proof.sig_contAt c A d S p' u l (by simpa using htS))
    have := (HasDerivAt.fun_sum (u := Finset.univ) fun l _ => (hf l).mul (hf l)).const_mul
      (1 / 2 : ℝ)
    rw [hE t ⟨ht.1, lt_of_lt_of_le ht.2 hT.2⟩ (by simpa using htS)]
    convert this using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le G (alpha049 c A d S p' u) huT
    S.countable_toSet hGc hGd (Novel.UnifiedSpliceStep0Proof.alpha_ii c A d S p' u u T)
  unfold ax01At
  rw [hFTC]
  simp [G, f, dotProduct]

theorem converseAX01S : converseAX01Statement := by
  classical
  intro k r d c A hA S H u p hu0 huH huS h492 hRs
  obtain ⟨α, β, hR⟩ := hRs
  -- the front end's primitive on each interval: `T V_m + κ_m`
  let κ : ℕ → Fin k → ℝ := fun m =>
    if h : ∃ T₀, T₀ ∈ Ioo u H ∧ T₀ ∉ S ∧ nS S T₀ = m then
      prim049 S p u h.choose - h.choose • p.V m else 0
  have hPk : ∀ T ∈ Ioo u H, T ∉ S → prim049 S p u T = T • p.V (nS S T) + κ (nS S T) := by
    intro T hT hTS
    have hex : ∃ T₀, T₀ ∈ Ioo u H ∧ T₀ ∉ S ∧ nS S T₀ = nS S T := ⟨T, hT, hTS, rfl⟩
    simp only [κ, hex, ↓reduceDIte]
    obtain ⟨_, _, hn⟩ := hex.choose_spec
    set T₀ := hex.choose
    rcases le_total T₀ T with h | h
    · rw [prim_lin S p u h fun τ hτ hI => same_free S h hn τ hτ ⟨hI.1, hI.2.le⟩, hn]
      funext l; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    · rw [prim_lin S p u h fun τ hτ hI => same_free S h hn.symm τ hτ ⟨hI.1, hI.2.le⟩]
      funext l; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  exact ⟨_, _, converse_kappa hA p hu0 huH huS h492 hR κ hPk⟩

theorem unifiedSpliceConverseAX01 : Standalone.UnifiedSpliceConverseAX01.statement := converseAX01S

end Novel.UnifiedSpliceConverseAX01Proof

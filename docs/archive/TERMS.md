# Terminology and notation

Allowed vocabulary. Populated 2026-09-21 from `refs/text/fontana2022term.md` (sections as in arXiv:2202.00929v4), `refs/text/gellert2021short.md` (sections as in arXiv:2101.04308v1), and the vocabulary of Claims 001 to 006. Add a term only by PR with a citation. Where the lab's notation differs from the source's, both are given; the specializations (S1) to (S7) of `ledger/AXIOMS.md` explain the differences. "Claim NNN (x.y)" points to the labelled display in `math/claims/`. "Standard" marks textbook vocabulary that no registered source needs to introduce; the claim that first uses it is named.

## Probability and measure

| Term | Notation | Source |
|---|---|---|
| stochastic basis (filtered probability space) satisfying the usual conditions | (Ω, F, (F_t)_{t ≥ 0}, Q); source writes F = (F_t) | `fontana2022term` §3, p. 6; Claim 005 |
| risk-neutral measure (P(·,T)/S^0 is a local martingale for every T > 0) | Q | `fontana2022term` §3, p. 7 (definition before Lemma 3.4) |
| spot risk-neutral measure (the same measure, named for the bank-account numéraire) | Q | `gellert2021short` §3.1.4; `brace2024sofr` §3.4 |
| Brownian motion, d-dimensional | W = (W_t)_{t ≥ 0}, d | `fontana2022term` §3, p. 6 |
| left limit of the filtration at a date | F_{T_n−} := σ(∪_{t < T_n} F_t); source F_{τ−}; Lean `Upstream.leftLimit` | `fontana2022term` Theorem 3.5, (3.6); ledger AX-02 |
| conditional expectation given a sub-σ-algebra | E[· \| G], E[· \| F_{T_n−}] | `fontana2022term` Theorem 3.5 (iv); Claim 003 (3.5) |
| almost surely; almost everywhere for the product measure | Q-a.s.; (Q ⊗ dt)-a.e. | `fontana2022term` Theorem 3.5 (i)–(ii); Claim 005 (5.5) |
| sigma-integrable (with respect to a σ-algebra) | — | `fontana2022term` Theorem 3.5, (3.6), and proof p. 9 |
| evanescent set | — | `fontana2022term` Assumption 3.6 |
| random measure, compensator | μ(dt, dx), ν(dt, dx) = λ_t(dx) dt (excluded by (S2)) | `fontana2022term` §3, p. 6 |
| progressively measurable coefficient | — | `fontana2022term` Assumption 3.3 (ii)–(iii), footnote 3 |
| random variable, expectation, integrable | X, E[X], "E[X] finite" | standard; Claim 001 |
| exponential moment (moment generating function at −λ) | E[exp(−λX)], λ ∈ ℝ | standard; Claim 001 (1.1)–(1.2); Lean `Novel.MGF` |
| cumulant generating function | t ↦ log E[exp(tX)] | standard; Claim 001 Review; D2 question in `board/ROADMAP.md` |
| tower property (of conditional expectation) | E[E[Y \| G]] = E[Y] | standard; Claim 003 Corollary |
| conditional variance; risk-neutral event variance (of the short-rate jump at a scheduled date) | Var_Q(Δr_{T_n} \| F_t), t < T_n; v_n in Claim 011 | [fontana2022term] Example 3.10, independent Gaussian jump variances; Claim 011 (11.4) |
| regular conditional distribution (of a real random variable given a sub-σ-algebra) | κ(ω, ·) | standard; Claim 008, Step 1, (8.8) |
| Laplace transform (of a probability measure on ℝ; the moment generating function at −τ) | M(τ) = ∫ e^{−τx} κ(dx) | standard; Claim 008 (8.10); `curtiss1942note` for its uniqueness theorem |
| tilt, tilted measure (change of measure by a positive density with conditional expectation one); accumulated tilt (by the exponent of the earlier intervals) | P_D(A) := E[D 1_A]; D_k = R_k / Z_k, R_k = exp(−Σ_{m<k} L_m X_m) | standard; Claim 008 (8.3), (8.7); `brace2024sofr` has no counterpart |
| abstract Bayes formula (conditional expectation under a tilted measure) | E_{P_D}[h(Y) \| G] = E_P[D h(Y) \| G] | standard; Claim 008 (8.7) |
| Lebesgue integral over an interval | ∫_t^T g(u) du (componentwise for ℝ^d values) | standard; Claim 002 |
| Euclidean inner product and norm on ℝ^d | ⟨·,·⟩, \|·\| | standard; Claim 002 (2.5)–(2.6) |
| usual conditions (F_0 contains the null sets; (F_t) right-continuous) | — | [bauerschmidt2020stochastic] §2.2, p. 16; ledger AX-03 to AX-07 (C1), (U1) |
| predictable σ-algebra; predictable process; simple process | 𝒫; H predictable; H = Σ_i H_{i−1} 1_{(t_{i−1},t_i]} ∈ ℰ with H_{i−1} bounded F_{t_{i−1}}-measurable; Lean `IsStronglyPredictable` | [bauerschmidt2020stochastic] §2.1, p. 14, §3.1, p. 37; ledger (C2) |
| stopped process; optional stopping theorem (OST) | X^T_t := X_{t∧T}; OST | [bauerschmidt2020stochastic] §2.2, p. 16; ledger AX-04 |
| local martingale; reducing sequence; uniformly integrable (UI) martingale | (T_n) with T_n ↑ ∞ a.s. and each X^{T_n} a martingale | [bauerschmidt2020stochastic] §2.2, pp. 17–19; ledger (C4) |
| square-integrable (L²-bounded) martingales H², continuous ones H²_c; the H²-norm | ‖X‖_{H²} = (sup_t E X_t²)^{1/2} = (E X_∞²)^{1/2} | [bauerschmidt2020stochastic] §2.3, pp. 22–23; ledger (C5) |
| continuous semimartingale and its decomposition | X = X_0 + M + A, M a continuous local martingale, A continuous of finite variation | [bauerschmidt2020stochastic] §2.6, p. 36; ledger (C7) |
| Itô integral (stochastic integral) of a predictable process against a continuous local martingale; the integrand classes L²(M) and L²_loc(M) | H·M = ∫_0^· H_s dM_s; ‖H‖_{L²(M)} = (E ∫_0^∞ H² d⟨M⟩)^{1/2}; L²_loc(M): ∫_0^t H² d⟨M⟩ < ∞ a.s. for all t; the lab's driver integral ∫ H dB^k is Lean `Upstream.ItoCalculus` field `I` | [bauerschmidt2020stochastic] §3.1–3.3, pp. 37–47; ledger AX-03, AX-04, (C8), (U4)–(U5) |
| Itô isometry; Kunita–Watanabe identity | ‖H·M‖_{H²} = ‖H‖_{L²(M)}; ⟨H·M, N⟩ = H·⟨M,N⟩, ⟨H·M, K·N⟩ = (HK)·⟨M,N⟩ | [bauerschmidt2020stochastic] §3.2, p. 40, §3.3, p. 43; ledger AX-03 |
| Itô formula; integration by parts and the Itô correction term | f(X_t) = f(X_0) + Σ_i ∫ ∂_i f(X) dX^i + ½ Σ_{i,j} ∫ ∂_i∂_j f(X) d⟨X^i,X^j⟩; X_tY_t = X_0Y_0 + ∫ X dY + ∫ Y dX + ⟨X,Y⟩_t | [bauerschmidt2020stochastic] §3.5, pp. 50–51; ledger AX-05 |
| driver processes with deterministic covariation density; driver-form process | B^1, …, B^m with [B^k,B^l]_t = ∫_0^t c_{kl}(s) ds; X = x + Σ_k ∫ H^k dB^k + ∫ K ds | the lab's specialization (U2), (U6) in ledger AX-03 to AX-07 of [bauerschmidt2020stochastic] §5.1, p. 65 |
| (F_t)-Brownian motion; weak solution and strong solution of an SDE; pathwise uniqueness (strong uniqueness); uniqueness in law | E(σ,b): dX_t = b(t,X_t) dt + σ(t,X_t) dB_t; Definition 1.1 solution pair (W,X) | [bauerschmidt2020stochastic] §5.1, pp. 65–67; [altay2013lecture] Definitions 1.1 and 1.4, p. 2; ledger (C9), AX-06, AX-07 |
| mean-reverting square-root (Cox–Ingersoll–Ross, CIR) process; its degrees of freedom; Feller boundary classification (zero attainable or not) | dV_t = κ(θ − V_t) dt + ε√V_t dW_t; ν := 4κθ/ε²; the lab's (13.2) has κ = θ_j, θ = 1, ε = α_j | [feller1951singular] (1.1) and cases (i)–(iii), pp. 173–174 (drift bx + c, diffusion coefficient ax, classification by c ≤ 0, 0 < c < a, c ≥ a); [cox1985theory] (17) and footnote 8, p. 391; [malham2008square] §4.1, p. 16; [altay2013lecture] §1, p. 1; ledger AX-08 |
| noncentral chi-square distribution (degrees of freedom ν, noncentrality λ) and its scaled form as the square-root transition law | χ²_ν(λ), F_{χ²_ν(λ)}; V_{t+h} \| V_t ∼ (e^{−κh}/η(h)) χ²_ν(η(h)V_t) | [cox1985theory] (18), p. 392; [malham2008square] Proposition 1, p. 17; the Laplace transform and Bessel form of the fundamental solution are [feller1951singular] Lemma 7 (5.7) and Lemma 9 (6.2), p. 180; ledger AX-08 |
| globally or locally Lipschitz coefficients; Hölder-1/2 (Yamada–Watanabe) diffusion condition; Osgood condition | \|b(t,x) − b(t,y)\| ≤ K\|x − y\|; \|σ(t,x) − σ(t,y)\| ≤ C√\|x − y\|; ∫_0^γ du/ϱ²(u) = ∞ | [bauerschmidt2020stochastic] §5.2, pp. 68–69; [altay2013lecture] Theorem 2.1, p. 3, Corollary 2.19, p. 5; ledger AX-06, AX-07 |

## Dates and intervals

| Term | Notation | Source |
|---|---|---|
| scheduled dates (the lab's name for the source's expected jump dates and for FOMC meeting dates) | 0 = T_0 < T_1 < … < T_N; source S = {s_1, …, s_M}; `gellert2021short` x_i | `fontana2022term` §3, p. 6, item (ii); `gellert2021short` §3.1.1, (15); Claim 002 (2.1) |
| expected jump dates | S = {s_1, …, s_M} | `fontana2022term` §1 and §3, p. 6 |
| roll-over dates (atoms of η; excluded by (S1)) | T = {t_1, t_2, …} | `fontana2022term` §2.1, (2.3) |
| FOMC meeting date | x_i | `gellert2021short` §2.1, §3.1.1 |
| stochastic discontinuity (jump at a predetermined date) | — | `fontana2022term` §1; §3, p. 6 |
| scheduled interval | I_k := [T_k, T_{k+1}), k = 0, …, N, with T_{N+1} := +∞ | Claim 002 (2.1) |
| current interval index | j(t): the index with t ∈ I_{j(t)} | Claim 005, Proof |
| left end of the integration piece | m_k := max(T_k, t) | Claim 004 (4.3) |
| time-to-left-end variable | τ := T − m_k; the D4a homogeneity Finding instead writes x := T − τ for T ≥ τ, with τ denoting the fixed scheduled date | Claim 004 (4.8); Claim 006 (6.5); [brace2024sofr] (42)--(43) use scheduled dates as maturity-integration endpoints |
| meeting (informal for a scheduled date T_n, n ≥ 1; T_0 = 0 is not a jump date) | T_n | ledger AX-02, (S4) |

## Rates, curves and coefficients

| Term | Notation | Source |
|---|---|---|
| overnight rate, risk-free rate (RFR) | ρ (source); r_t := f(t, t) (ours, (S3)) | `fontana2022term` §2.1, (2.2); Remark 3.9, (3.12) |
| numéraire (source), bank account (ours) | S^0_t = exp(∫_0^t ρ_u η(du)); B_t = exp(∫_0^t r_u du) | `fontana2022term` §2.1, (2.2); ledger (S1) |
| term-structure measure with atoms (Lebesgue under (S1)) | η(du) = du + Σ_n δ_{t_n}(du) | `fontana2022term` §2.1, (2.3) |
| zero-coupon bond price (bond) | P(t, T) = exp(−∫_{(t,T]} f(t, u) η(du)) | `fontana2022term` §2.2, p. 4; (3.1) |
| instantaneous forward rate (forward curve at time t: T ↦ f(t, T)) | f(t, T) | `fontana2022term` §3, (3.2) |
| forward-rate equation (HJM representation) | f(t,T) = f(0,T) + ∫_0^t α(s,T) ds + ∫_0^t σ(s,T)·dW_s + Σ_{n : T_n ≤ t} ξ_n(T) | `fontana2022term` (3.2); ledger common setting |
| initial forward curve | f(0, ·), Lean `f₀` | `fontana2022term` Assumption 3.3 (i) |
| drift (of the forward rate) | α(t, T) | `fontana2022term` (3.2), Assumption 3.3 (ii) |
| volatility (diffusive volatility of the forward rate) | σ(t, T) ∈ ℝ^d; source φ(t, T) | `fontana2022term` (3.2), Assumption 3.3 (iii); ledger (S4) |
| curve jump at a scheduled date | ξ_n(u); source ΔV(s_n, u), V(·, T) the stochastic discontinuity process | `fontana2022term` (3.2), Assumption 3.3 (v); ledger (S4) |
| integrated coefficients | ᾱ(t,T) = ∫_{[t,T]} α(t,u) η(du), φ̄(t,T) likewise | `fontana2022term` §3, p. 7 |
| HJM drift condition, integrated form (Axiom A1) | ∫_t^T α(t,u) du = ½ \|∫_t^T σ(t,u) du\|² | `fontana2022term` Theorem 3.5 (ii); ledger AX-01; `heath1992bond` |
| HJM drift condition, differentiated form (derived, not the axiom) | α(t,T) = ⟨σ(t,T), ∫_t^T σ(t,u) du⟩ | `heath1992bond`; `gellert2021short` §3.1.4, (17); ledger AX-01 "Derived form" |
| jump martingale condition (Axiom A2) | E[exp(−∫_{T_n}^T ξ_n(u) du) \| F_{T_n−}] = 1 for all T ≥ T_n | `fontana2022term` Theorem 3.5 (iv), Remark 3.9; ledger AX-02 |
| short rate (short end of the forward curve) | r(t) = f(t, t) | `gellert2021short` §3.1.2, (8); `fontana2022term` Remark 3.9 |
| short-rate jump | Δr_{T_n} := r_{T_n} − r_{T_n−} | [fontana2022term] Remark 3.9 and Example 3.10; Claim 011 (11.4) |
| call on a short-rate jump; strike; positive part | C_n(t,K), K; z^+ := max(z,0) | standard call payoff; [fontana2022term] Proposition 4.12 for caplet valuation, Claim 011 (11.5) for this ideal payoff (not a listed option) |
| option-implied event variance (for a specified payoff and model) | v_n inferred from C_n(t,0)/P(t,T_n) in Claim 011; no listed-contract identification assumed | [fontana2022term] Proposition 4.12, Gaussian caplet valuation; Claim 011 (11.5)–(11.6) |
| target rate (FOMC policy target; piecewise constant between meetings) | — | `gellert2021short` §2.1, §3.1 |
| indicator volatility (step factor of meeting i) | ξ_i(t, T) = ξ_i 1(t < x_i) 1(T ≥ x_i) | `gellert2021short` §3.1.1, (15) |
| ramp drift (accumulated drift of indicator volatilities) | Σ_{q,i} ξ_q ξ_i (…) 1(T ≥ x_q ∨ x_i)(T − x_i)(t ∧ x_q ∧ x_i) | `gellert2021short` §3.1.5, (28)–(30); `brace2024sofr` §3.4, (18) |
| backward-looking rate (setting-in-arrears rate) | R(S, T) | `fontana2022term` §2.2.1, (2.4) |
| forward-looking rate | F(S, T) | `fontana2022term` §2.2.2 |
| forward term rate | R(t, S, T) | `fontana2022term` §2.2.3 |

## Families and functions on the partition (the lab's objects)

| Term | Notation | Source |
|---|---|---|
| step function on the partition | σ(u) := s_k for u ∈ I_k, s_k ∈ ℝ^d | Claim 002 (2.2) |
| step value; step volatility (deterministic in D2) | s_k; s_k(t) | Claim 002 (2.1); Claim 005 (5.2); `board/ROADMAP.md` D2 |
| piecewise-affine function on the partition | g(u) := a_k + b_k (u − T_k) for u ∈ I_k | Claim 006 (6.2) |
| level and slope (of a piecewise-affine function on I_k) | a_k, b_k | Claim 006 (6.2), (6.7) |
| ramp (at a scheduled date T_m) | (T − T_m) 1{T ≥ T_m}, coefficient C_m | Claim 006 (6.8); `gellert2021short` §3.1.5, footnote 18 |
| ramp coefficient | C_{nm}(t); on I_k the slope b_k = Σ_{m ≤ k} C_m | `board/ROADMAP.md` D2; Claim 006 (6.8) |
| maturity-step family (family S) | f(t,T) = b_k(t) for T ∈ I_k; coefficient form: α(t,T) = μ_k(t), σ(t,T) = s_k(t), ξ_n(u) = X_{n,k} on I_k | Claim 005 (5.2)–(5.3) |
| step-plus-ramp family (family S⁺) | Σ_{m : T_m ≤ T} [M_m + C_m (T − T_m)] on each interval | Claim 006 Remark (6.8); `board/ROADMAP.md` D2 |
| maturity-step jump (of the curve at T_n) | ξ_n(u) = X_{n,k} for u ∈ I_k, k ≥ n | Claim 003 (3.2) |
| Lemma A constant (integral of a step up to the current piece) | c_{jk}(t); C_k, A_k in Claim 004 | Claim 002 (2.4); Claim 004 (4.7) |
| Lemma C constant | e_{jk}(t) | Claim 006 (6.4) |
| level jump (of the curve at T_n on the interval I_k) | X_{n,k}; a_k in the level-and-slope form | Claim 008 (8.1); Claim 010 (10.3) |
| slope jump (of the curve at T_n on the interval I_k) | y_{n,k}; b_k in the level-and-slope form | Claim 008 (8.1); Claim 010 (10.3) |
| differentiated HJM drift (of a step volatility from time t) | α*(u) = ⟨σ(u), ∫_t^u σ(v) dv⟩ | Claim 007 (7.3) |
| tilted-Gaussian characterization (of the level jumps) | X_n ~ N(0, y_n); X_k ~ N(0, y_k) under the accumulated tilt | Claim 008 (8.3)–(8.5) |
| matching covariances (jointly Gaussian level jumps) | μ_k = Σ_{m<k} L_m Σ_{km}, y_k = Σ_{kk} | Claim 008 (8.6); `board/ROADMAP.md` D2 |
| compensating shape (of a scheduled jump: the maturity-dependent part of the curve jump beside the level jump) | ξ(T_n + u) = X + h(u), h B⊗G-measurable; H(τ) = ∫_0^τ h | `board/REQUEST-publication-claims.md` Request 2; Claim 045 (45.1); the Gaussian case is the compensator U^d of `fontana2022term` Example 3.10, (3.14) |
| tilted conditional law; tilted mean and variance (of the level jump, by e^{−τx}) | κ_τ(dx) = e^{−τx} κ(dx)/M(τ); Ẽ_τ[X], Ṽ_τ[X] | standard; Claim 045 (45.2), (45.5) |
| short-rate jump (at a scheduled date) | J_n = r_{T_n} − r_{T_n−}; J in Claim 045 (d) | paper (5.1); `kim2014jumps` §3; Claim 045 (45.11) |
| Theorem 2a | Claim 010 | `math/claims/010-theorem-2a-step-plus-ramp.md` |
| two maturities per interval (refinement hypothesis) | T_k + h_k, T_k + h_k/2; any two distinct points of (m_k, T_{k+1}) | Claim 003 (3.4); Claim 004 (4.5) |
| three-point identification | a quadratic vanishing at three distinct points is zero | Claim 006 Part (b) |
| Lemma A | Claim 002 | `math/claims/002-lemma-a.md` |
| Lemma B | Claim 001 | `math/claims/001-lemma-b.md` |
| Lemma C | Claim 006 | `math/claims/006-piecewise-affine-integral.md` |
| Theorem 1 | Claim 005 | `math/claims/005-theorem-1-step-family.md` |
| hypothesis structure (for the axioms) | `Upstream.HJMScheduled`, fields `drift_integrated`, `jump_martingale` | ledger AX-01, AX-02; `lean/Upstream/HJMScheduled.lean` |
| non-vacuity instance | an instance of `Upstream.HJMScheduled` with nonzero coefficients | `RESEARCH_PROPOSAL.md` §3 "Axiom policy"; `lean/Upstream/HJMScheduled.lean` |

## Consistency and finite-dimensional realizations (D2 to D5 vocabulary)

| Term | Notation | Source |
|---|---|---|
| forward curve manifold; invariant manifold | G; "G is invariant under the forward rate process" | `bjork1999interest` §2, Definitions 2.1–2.2 |
| consistent (interest rate model with a family of forward curves) | the pair (M, G) is consistent iff G is invariant | `bjork1999interest` §2, p. after Definition 2.2; `filipovic2000exponential` §2, Definition 2.1 |
| consistent Itô process (state process whose curves stay in the family) | Z consistent with {F(·, z)}_{z ∈ Z} | `filipovic2000exponential` §2, Definition 2.1 |
| biexponential-polynomial family; nontrivial factor | F(x,z) = p_1(x,z_1) e^{−βx} + p_2(x,z_2) e^{−2βx} with polynomial p_i of degree n_i; a component Z^{i,μ} of a consistent parameter process is nontrivial when its diffusion a_{(i,μ),(i,μ)} is not identically zero | [sharef2004conditions] §2.2 (family), §4.2 (factors); ledger AX-14 |
| exponential-polynomial family; bounded exponential-polynomial family | EP(K, n); BEP(K, n) | `filipovic2000exponential` §3 |
| exponent (of an exponential-polynomial family) | z_{i, n_i + 1} | `filipovic2000exponential` §3, Theorem 3.2 |
| finite-dimensional realization | — | `bjork2001existence` (abstract and §1); `tappe2010alternative` |
| full state; state dimension (excluding deterministic time and fixed model parameters) | X_t; the number of current coordinates needed for the curve and conditional law of future short rates | [fontana2022term] Example 3.10, scalar Markov representation after (3.14); [gellert2021short] paragraph after (35); Claim 011 (11.1)–(11.3) |
| diffusion factor; diffusion-factor count | the Brownian drivers with nonzero volatility, distinct from full state dimension | [gellert2021short] (26), (35) and the following paragraph; Claim 011 |
| time-inhomogeneous Markov state | conditional future law determined by (t, X_t) | [fontana2022term] Example 3.10, representation after (3.14); Claim 011 |
| F-Markov process | an F-adapted X with E[f(X_t) \| F_s] = E[f(X_t) \| X_s] for all s ≤ t and bounded Borel f; no transition function or composition law is implied | [vanhandel2007stochastic] Definition 3.1.8, p. 72; proposed ledger AX-13 gives it for Lipschitz SDE solutions with time-dependent coefficients |
| time-homogeneous Markov diffusion; fixed state-to-curve map | state equations have coefficients depending only on the current state, with a transition law depending on elapsed time; the source writes r_t = G(Z_t) for a fixed map G into the curve function space (its r_t denotes the curve, not our short rate) | [bjork2001existence] Definition 3.1; Section 3.3 treats time-varying systems by adding running time; the D4a Finding of 2026-09-23 distinguishes this from scalar shape normalization |
| bounded Borel test functions; transition semigroup | B_b(R^n) with the sup norm; P_t : B_b(R^n) -> B_b(R^n), positive linear contractions preserving one, P_0 = id and P_{s+t} = P_s P_t; the source writes Q_t, whereas our Q denotes the probability measure | [bauerschmidt2020stochastic] §6.3, pp. 87--88; proposed ledger AX-12 records the deterministic-time conditional identity for Lipschitz SDE solutions |
| variance map; state image; model parameters | the vector of conditional event variances as the current state varies with parameters fixed; v = (v_1,…,v_N) in Claim 011 | [fontana2022term] Example 3.10, deterministic jump-law parameters; Claim 011(c) distinguishes parameter variation from state variation |
| affine semimartingale | X with stochastic discontinuities | `fontana2022term` §4.1 |
| quasi-exponential function | f(x) = c e^{Ax} b (c a row vector, A a square matrix, b a column vector); equivalently the derivatives of f span a finite-dimensional space | [bjork2001existence] Corollary 5.1 and Remark 5.1; [tappe2010alternative] Definition 3.5 and Lemma 3.6 |
| constant direction volatility | σ(r, x) = γ(r) λ(x), a scalar functional γ of the curve times a fixed function λ of time to maturity x = T − t | [bjork2001existence] §6, (31); [tappe2010alternative] (7.1) |
| separable volatility | σ(t, T) = χ(t) φ(T) | `brace2024sofr` §3.5, (20); `fontana2022term` Example 3.10 |
| Cheyette model (with stochastic discontinuities) | — | `fontana2022term` Example 3.10 |
| quasi-Gaussian (Heston/Hull–White) model | — | `brace2024sofr` §3.5 |
| accumulated variance state | Φ(t) = ∫_0^t σ(s, t)² ds; Φ(u, t) between meetings | `brace2024sofr` §3.5, (28), (34); Appendix A, (A22) |
| deterministic maturity shape and its primitive on a scheduled interval; realized variance coefficient | Claim 026: φ_j, g_{j,k}(T)=a_{j,k,m}φ_j(T) on I_m, G_{j,k}(T)=∫_0^T g_{j,k}, Φ_{j,m}(T)=∫_{T_m}^T φ_j; A_{j,k}, M_{j,k}, C_{j,m}, V_{j,m} in (26.3), (26.5). Here Φ_{j,m} is deterministic, distinct from the accumulated variance Φ above. | [brace2024sofr] (20)--(22), (36)--(43) give the separable volatility and meeting precedent; Claim 026 extends the coefficient computation to arbitrary continuous φ_j, without asserting Markov closure |
| Gaussian jump law (of a curve jump) | ξ_i ~ N(μ_i, σ_i²) | `fontana2022term` Example 3.10 |
| compensator of a Gaussian scheduled jump (the ramp that makes it consistent) | U^d(t, T) | `fontana2022term` Example 3.10, (3.14) |
| stochastic volatility (multiplicative, on a deterministic shape) | σ(t) → σ(t) √v(t), v a Heston-type process | `brace2024sofr` §3.5, (29)–(30) |
| American exercise; option on a specified SOFR futures contract | exercise may occur before expiry; the underlying is the futures contract | [itkin2024semi] Introduction and §1; CME Rulebook 460A01.B and 460A02.A–B, https://www.cmegroup.com/rulebook/CME/V/450/460A/460A.pdf |
| bond-implied overnight simple rate; discrete compounded rate | L_j=[P(u_j,u_{j+1})^{-1}−1]/d_j, d_j=u_{j+1}−u_j; R=[Π_j(1+d_jL_j)−1]/(b−a) | [skov2021dynamic] (2)–(3), (18); Claim 018 (18.2) fixes the model and partition |
| American cash call with a specified exercise window; stopping time; optimal exercise time | U(A,S,a,b,K); τ∈𝒯[A,S] means {τ≤t}∈F_t for every t and A≤τ≤S; τ_* in (18.6) | [itkin2024semi] Introduction and §1 provide American-exercise context; Claim 018 (18.3) explicitly defines its cash stopping problem, without asserting equality to listed exercise |
| largest discount factor over the exercise window | D_{V,L}(x)=max_{0≤u≤L}exp(−xu−Vu²/2), L=S−A; V=Σ_i v_i, H=Σ_i T_i v_i | Claim 018 (18.7), (18.11) derives this from Claim 011's bank account and pathwise quadratic minimization; [fontana2022term] Example 3.10 is the Gaussian-model precedent |
| American cash exercise across one scheduled date; value of waiting for its revelation | T=T_N, V_−=Σ_{i<N}v_i, w=v_N, ℓ=T−A, L=S−T; f_−, f_+, p, c, u_{q,d} as in Claim 019 (19.3)–(19.5) | [leung2014accounting] §6.1, (6.1)–(6.2) supplies the scheduled-event exercise precedent for equity options; Claim 019 derives its own cash-rate formulas in Claim 011's model and retains the largest-discount notation of Claim 018 |
| continuously compounded backward-looking rate; ideal futures rate for that rate | (exp(∫_a^b r_u du)−1)/(b−a); F(t;a,b), G_t(a,b)=1+(b−a)F(t;a,b) | [skov2021dynamic] §2.3, (13), (19)–(20); Claim 017 (17.2) specifies a continuous idealization, including during accrual, rather than discrete settlement |
| European cash call on an ideal compounded-rate futures rate | C(S,a,b,K)=E_Q[B_S^{-1}(G_S(a,b)−K)^+]; C/(b−a) is the rate-call price with strike (K−1)/(b−a) | [skov2021dynamic] (20) supplies the underlying convention; [fontana2022term] Lemma 4.11 and Proposition 4.12 supply Gaussian valuation precedents; Claim 017 (17.3) specifies the cash payoff |
| futures-style (future-style) margining of an option on a futures price: premium paid on expiry, mark-to-market variations exchanged daily with the initial margins, so the price is the undiscounted expectation of the payoff; equity-style margining: premium paid on trade date, price discounted to the payment date | futures-style: C^marg_t = E_t[(F_{T}−K)^+]; equity-style: C^coll_t = E_t[(F_T−K)^+ D(t,T_p;e)]; the lab's futures-style American value is Ũ(A,S,a,b,K)=sup_τ E_Q[(F(τ;a,b)−K)^+] | [nastasi2018smile] §2.2, eq. (3) (future-style) and eq. (4) (equity-style), pp. 6–7, with its statement that European and American prices coincide under future-style margining; Claim 021 (21.2) specifies the lab's contract; the discounted cash contract of Claim 018 (18.3) is the equity-style counterpart |
| accrual coefficients and linear combinations identified by futures and complete call surfaces | w_i,d_i,h_i,j_i,k_i; p=h·v,z=j·v,q=k·v,m=exp(p−z); matrix M with rows h,j,k; V=Σ_i v_i,H=Σ_i T_i v_i | Claim 017 (17.4)–(17.12), elementary integration and Gaussian valuation from [skov2021dynamic] (20) and [fontana2022term] Lemma 4.11; notation is local to Claim 017 |
| effective level (of a correlated splice); covariation with the current front-end noise | H^{0,0}♯ = H^{0,0} + V_{j(u)}, a♯, R♯; ω̄_k = H^k V_{j(u)}^⊤ | `board/REQUEST-5-approximation-and-unified-splice.md` §2; Claim 049 (49.4)–(49.6) |
| parallel diffusion between meetings (piecewise-constant variance rate on a partition; cells) | σ(s)² = u_p on [c_{p−1}, c_p); σ(s,T) = σ(s), α(s,T) = σ(s)²(T − s) | `board/REQUEST-publication-claims.md` Request 1; Claim 046 (46.1)–(46.2) |
| panel of accumulated variances; gap between consecutive expiries; meeting-free gap | Q(S) = q(S)/δ² = Σ_{T_i ≤ S} v_i + ∫_0^S σ²; G_ℓ = (S_{ℓ−1}, S_ℓ]; E, Λ_E | Claim 022 (22.4)–(22.5); Claim 046 (46.6)–(46.8) |
| maturity-dependent diffusion shape; window weight; window-dependent gap weights | σ(s,T) = σ(s)φ(s,T), Φ(s,T) = ∫_s^T φ(s,x)dx; β(s) = δ^{−1}∫_a^b φ(s,T)dT; D_{ℓ,p}, Λ̃_{ℓ,p} = D_{ℓ,p} − D_{ℓ−1,p} | `board/REQUEST-3-maturity-dependent-diffusion.md`; `brace2024sofr` §3.1 (4)–(7) for (S2); Claim 047 (47.1)–(47.5) |
| identification from two fixed European call strikes; derivatives of the Gaussian call formula | K=1,K_*>1; c_K(m,s) is (17.6) with q=s²; μ_c(s) solves c_1(μ_c(s),s)=c>0 | Claim 017(d), (17.13)–(17.15), elementary differentiation of the Gaussian valuation formula with precedent [fontana2022term] Proposition 4.12; φ/Φ is differentiated explicitly and the zero-variance case uses m≥1 |
| variance mean reversion, volatility of volatility, within-factor Brownian correlation | θ_j(s), α_j(s), ρ_j(s); α_j is distinct from forward drift α(s,T) | [brace2024sofr] (30)–(31), (39)–(41); Claim 013 |
| quadratic covariation; stochastic product rule; conditional martingale isometry | [W_i,U_j]; d(Rv); conditional second moment equals conditional expected quadratic variation; the source writes ⟨M⟩, ⟨M,N⟩ | [bauerschmidt2020stochastic] §2.4–2.5, pp. 24–33 (quadratic variation and covariation of continuous local martingales), §3.5, p. 50 (integration by parts); ledger (C6), AX-03, AX-05; [brace2024sofr] (30)–(31), (40)–(41); Claim 013 (13.12)–(13.14) |
| stochastic exponential; uniformly integrable martingale | ℰ(M)_t = exp(M_t − ½[M]_t) for a continuous local martingale starting at zero; {X_t : t ≥ 0} uniformly integrable | [bauerschmidt2020stochastic] §4.3, pp. 58, 60–61; AX-10 records the bounded-quadratic-variation case and requests only its martingale conclusion |
| left-endpoint sums for the Itô integral; uniform convergence on compact time intervals in probability (UCP); convergence in probability | Σ_i H_{t_{i−1}}(X_{t_i∧t} − X_{t_{i−1}∧t}); for each S, ε > 0, Q(sup_{t≤S}|Xⁿ_t−X_t|>ε) → 0; at fixed T, Q(|Xⁿ_T−X_T|≥ε) → 0 | [bauerschmidt2020stochastic] §2.4, p. 24 (convergence convention), §3.4, p. 48 (Corollary); AX-11 specializes to a driver, continuous bounded integrands and fixed-time convergence |
| completed natural filtration; strong solution; pathwise uniqueness | G_t = σ(B_s : s ≤ t), augmented by null sets; solution adapted to G on the given space with the given B; solutions with the same driver and initial value are indistinguishable | [bauerschmidt2020stochastic] §5.1, pp. 65–66; AX-06 distinguishes integrals computed in G from those in a larger filtration |
| affine conditional variance map; containing affine space | V(t)=C(t)+A(t)v(t); C(t)+range A(t) | [fontana2022term] (4.1) for affine transforms; Claim 013 derives the explicit variance map from [brace2024sofr] (35)–(41) |
| ordinal meeting index; meeting loadings and their cumulative sums | i = number of meetings ahead; γ_{i,j}, G_{i,j} = Σ_{h≤i} γ_{h,j}, G_{0,j} = 0 | [brace2024sofr] (3), (16), (36); Claims 012 and 013 |
| linearly recurrent (ordinal) loadings; approximating loadings; loading error | a_i = u M^i v, equivalently a recurrence (3.141); ã_i; ε = max_{i≤N} \|a_i − ã_i\| over the indices occurring on [0, H] | Claim 030 (H2); `board/REQUEST-5-approximation-and-unified-splice.md` §1; Claim 048 (48.1)–(48.5) |
| deterministic volatility scale and decay parameter | a_j(s) (source σ_j(s)), λ_j | [brace2024sofr] (37)–(39); Claim 012 fixes v_j ≡ 1; Claim 013 allows stochastic v_j |
| conditional variance of a future short-rate jump | V_n(t) = Var_Q(Δr_{T_n} \| F_t), t < T_n | [brace2024sofr] (10), (35)–(39); Claim 012 (12.3) |
| column space, rank, left nullspace, cone generated by columns | A q for q ∈ ℝ^d; rank A; ker A^T; A[0,∞)^d | standard linear algebra; Claim 012 derives A from [brace2024sofr] (36) |
| unspanned stochastic volatility; incomplete bond market | volatility risk not fully hedged by bonds; the maximal rank of stacked bond-price diffusion rows is below the diffusion-factor count | [collindufresne2002bonds] §II, Definition 2 and Proposition 1; this concerns dynamic hedging, not by itself identification from a current curve |
| European call on a zero-coupon bond; option expiry and underlying bond maturity | C(S,U,K), payoff (P(S,U)−K)^+ at S, U>S | [fontana2022term] §4.4, Proposition 4.12 uses terminal bond payoffs in Gaussian caplet valuation; Claim 014 specifies this ideal call |
| forward measure at an expiry | Q^S, density 1/(B_S P(0,S)) on F_S | [fontana2022term] definition before Lemma 4.11; Claim 014 has P(0,S)=1 |
| standard normal distribution function and inverse | Φ, Φ^{-1}; in Claim 014, Φ is a distribution function, not an accumulated-variance state | [fontana2022term] Proposition 4.12; standard inverse on (0,1) |
| variance of the logarithm of a bond price under the forward measure | q(S,U); q_n=q(S_n,U_n), z_n=Σ_{m≤n}v_m | [fontana2022term] Lemma 4.11 and Proposition 4.12 for Gaussian valuation; Claim 014 (14.3), (14.7) |
| price interval for a specified ideal bond call; inverse of its strike-one price formula | [a_n,b_n], C_n(v), h_n=U_n−S_n; H_n(c)=4[Φ^{-1}((1+c)/2)]²/h_n² | [fontana2022term] Proposition 4.12 is the Gaussian valuation precedent; Claim 014 (14.5)–(14.7) gives the formula, and Claim 016 (16.1)–(16.2) specifies deterministic allowed price intervals |
| lower and upper bounds on cumulative variance; sharp individual bounds | l_n, u_n∈[0,+∞], L_n=max_{i≤n}l_i, R_n=min_{j≥n}u_j; +∞ means no finite upper restriction | Claim 016 (16.2)–(16.6), elementary bounds derived from Claim 014 and [fontana2022term] Gaussian valuation; finite l_n and finite model parameters are required |
| standard normal density; Lipschitz bound for the inverse price formula | φ(y)=exp(−y²/2)/√(2π), k_n; φ is not a volatility shape here | [fontana2022term] Proposition 4.12, normal distribution in Gaussian valuation; Claim 016 (16.7)–(16.8) derives the inverse derivative and error bound by elementary calculus |
| topological support of a random vector; affine hull | supp(V(t)), supp(law_Q(V(t) \| F_s)); aff denotes the smallest affine subspace containing that support | [fontana2025extended] §3.3 and Lemma A.3; Claim 015 uses finite-dimensional Euclidean support, also for its explicit regular conditional distribution in (15.14) |
| joint Laplace transform; zero-drift square-root diffusion | E[exp(−Σ_j λ_j v_j(t))], λ_j≥0; dv_j=α_j√v_j dU_j | [li2019continuous] Theorem 1.1, (2.19), Examples 8.3–8.4; [brace2024sofr] (39) with θ_j=0 |
| Poisson random sum of exponential variables; mass at zero | L_j∼Poisson(1/c_j), E_{j,k}∼Exponential(mean c_j), c_j=α_j²t/2; Σ_{k=1}^{L_j} E_{j,k} | Claim 015 (15.3) derives this fixed-time law for the classical diffusion in [li2019continuous] Example 8.3; it is not a jump-path representation |
| factors with nonzero volatility of volatility; covariance of the variance vector | J={j:α_j>0}, J_s={j∈J:v_j(s)>0}, A_J, A_{J_s}; Cov_Q(V(t)), Cov_Q(V(t) \| F_s); with piecewise-constant α_j and mean reversion θ_j≥0 (Claim 023): J={j:α_j>0 on some piece of (0,t]}, J_+={j∈J:α_j>0 on the last piece before t}, J_s={j:α_j>0 on some piece of (s,t], and θ_j>0 or v_j(s)>0}, which is the earlier J_s when θ_j=0 | [brace2024sofr] (39) and Table 2; Claim 015 distinguishes these covariances from the conditional jump variances V_n(t); (15.13)–(15.16) derive the earlier-information restriction using the scalar transition-law precedent [li2019continuous] (2.19) |

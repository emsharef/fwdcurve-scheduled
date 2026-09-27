# Publication completion request: check every mathematical claim and close the Lean gaps

Date: 2026-09-27.

**Human instruction:** everything asserted in the papers must be checked and formalized. This request replaces the earlier permission to leave publication extensions as paper-only arguments. It does not authorize calling an unfinished result complete because a weaker source theorem compiles.

This file is a request for the next lab run. Preparing it does not restart the lab. The human will restart it.

## 1. Objective and authoritative sources

Bring the mathematical statements in both publication papers into exact correspondence with checked Lean results, and audit the original research manuscript's proof-coverage claims. Include substantive unnumbered claims in proofs, remarks, examples, appendices, calibration formulas and use cases. A table of numbered theorems alone is insufficient.

Read these sources, in this order:

1. `paper_pub2/main.tex` and the files it inputs: *Forward curves with scheduled dates: consistency, realizations, and correlation*.
2. `paper_pub3/main.tex` and the files it inputs: *What options reveal about policy-meeting risk: identification and factor-model restrictions*.
3. `paper/PAPER.md` and `paper/PROOFMAP.md`: the original manuscript, with numbered results through Proposition 53.
4. The actual declarations and proof terms under `lean/Standalone/`, `lean/Novel/`, and `lean/Upstream/`, including the relevant assemblies.
5. `ledger/AXIOMS.md`, the registered bibliography, and the existing source claims.

The public snapshot is `emsharef/fwdcurve-scheduled`, initial commit `bba97cd`, available locally at `release/fwdcurve-scheduled/`. Its publication copies are `papers/structure/` and `papers/identification/`; its original manuscript is `papers/lab/`. `docs/proof-map.json` lists all 22 numbered publication results and `docs/lab-results.json` lists 49 original source entries. Use these as navigation aids, **not as evidence of coverage**. Prefer stable LaTeX labels to page numbers. Reconcile subsequent source changes explicitly.

Do not use `paper_pub`, revive the excluded standalone Sharef–Filipović correction in either publication article, fetch unrelated literature, acquire new market data, refit models, or generate new illustrations. Existing examples are in scope for checking their mathematical claims. Explicitly labelled open problems and conjectures need accurate status, not new solutions for this request.

### A correction discovered while preparing this request

The existing publication source map and public proof map understate the American formalization. The header of `lean/Standalone/PreWindowVarianceAggregates.lean` says that the reverse inequality is not yet asserted, but the **same file actually defines** `sectioningStatement`, `americanFullStatement`, `sectioningFullStatement`, and `americanGeneralStatement`, and includes them in its final `statement`.

`lean/Novel/PreWindowVarianceAggregatesProof.lean` contains the corresponding proofs `sectioning`, `americanFull`, `sectioningFull`, and `americanGeneral`; the last assembly includes them. In particular, `sectioningFull` proves the equality of the full-history and state-rule values, and `americanGeneral` proves equality across allocations in the encoded pure-jump payoff class, including zero earlier variance. These declarations are also present in the published snapshot.

**Do not redo that proof on the basis of the stale header.** Verify the bridge from that encoded payoff class, filtration and domination condition to the publication's precise statement, then repair the stale comments and maps. The continuous-background extension is a separate target. More generally, inspect proof terms and final assembly types rather than accepting either optimistic or pessimistic coverage summaries.

The original map also says `GaussLaw` and `ShapeGaussLaw` are “satisfiable only without diffusion.” The claim records explain that only a zero-diffusion instance was **constructed**, not that nonzero diffusion was proved impossible. Correct this wording after checking the interfaces; absence of a constructed instance and inconsistency are different findings.

## 2. Meaning of completion

For each mathematical assertion, supply a declaration proving its actual conclusion from its actual paper assumptions. A more general existing result is sufficient only with a checked specialization. A proof of the same-looking formula for a narrower model is not sufficient.

- Check all quantifiers: fixed maturity versus simultaneous maturities; almost everywhere versus indistinguishability; a fixed calendar versus all finite calendars and horizons; fixed parameters versus recalibrated parameters; existence versus coefficient-level compatibility.
- Check degenerate cases, domains and endpoints: zero variance, coincident decays, inactive factors, empty observations, first and last meetings, zero-width intervals, and unattained or infinite optimization bounds where applicable.
- State ordinary model hypotheses openly. For example, the second paper's stochastic-support theorem **assumes** suitable square-root SDE solutions; this request does not turn that theorem into a new existence theorem. Conversely, existence and uniqueness are conclusions of the first paper's three-exponent example and must not be assumed there.
- Standard published stochastic-calculus results may remain clearly identified, faithfully sourced upstream inputs under the repository rules. Do not rebuild textbook stochastic calculus unnecessarily. Reuse Mathlib and existing interfaces. However, derive each paper-specific construction, representation, law and pricing identity from those standard inputs; do not install the desired result as a new premise.
- Where the paper assumes an ordinary Brownian model but Lean assumes a bundle such as `GaussLaw`, prove the bridge from the model assumptions to that bundle. A zero-driver or vacuous instance does not discharge that bridge for the nonzero diffusion described in the paper. Check compatibility of interfaces on the same space, filtration, driver and stochastic integral.
- A successful global-axiom audit establishes kernel dependencies, not fidelity of the theorem statement or non-vacuity of its hypotheses. Both need review.
- A false or inadequately specified publication statement must be reported with a counterexample or exact missing hypothesis and a proposed corrected statement. Do not silently weaken a theorem, remove a conclusion, or hide a new assumption inside a structure and then mark the old statement complete.
- If the requested bridge cannot be completed under the current upstream rules, identify the exact unresolved obligation and required decision. It remains open; the earlier degenerate-instance exceptions do not certify full coverage of the publication model.

The requirement concerns mathematical assertions. Market observations and provider conventions are external inputs, not theorems about real-world prices. All claimed analytic formulas and finite mathematical conclusions based on supplied inputs are in scope. The empirical tables still require reproducible numerical checks; a data-source assertion or a SciPy return code must not be described as a Lean proof.

## 3. Full statement inventory and fidelity check

Before closing any assignment, inventory the 22 numbered results below, their conclusions and hypotheses, every supporting mathematical assertion actually used, and all original manuscript theorem claims. Mark each as:

1. exact existing Lean coverage, with an explicit checked specialization where needed;
2. existing proof but missing assembly/model/paper bridge;
3. genuinely missing proof or strengthened publication conclusion;
4. an incorrect or underspecified paper assertion requiring correction;
5. a numerical or externally supplied fact, with its validation route;
6. an explicitly open conjecture, which must not be advertised as proved.

For every item in categories 2–4, create a concrete proof obligation and resolve it. The list below is the initial inventory, not permission to ignore another gap found in a proof or appendix.

| Paper | Result and label | Existing starting point | Required attention |
|---|---|---|---|
| First | Lemma 2.3, `lem:maturitynull` | No separate mapped declaration | New simultaneous-maturity null-set result and application |
| First | Proposition 3.1, `prop:profile` | `JumpShapeAssembly`, original Proposition 48 | Exact conditional-law, smoothness, uniqueness and common-version scope |
| First | Theorem 3.3, `thm:tilts` | `JumpLawTiltedGaussian`, original Proposition 9 | Normalization and successive tilts; no independent-announcement substitution |
| First | Theorem 4.2, `thm:realization` | Original Propositions 30–33; `MeetingLoadingObstruction`, `RecurrenceNecessityAssembly`, `RecurrentLoadingAssembly`, `ExternalScaleAssembly` | One exact biconditional with the publication's varying-calendar/horizon convention |
| First | Proposition 4.3, `prop:scaledconstruction` | `ExternalScaleAssembly`, original Proposition 31 | Autonomous diffusion, restart, recovery, dimension and regularity bridge |
| First | Proposition 4.5, `prop:varianceexample` | `BoundedVarianceCompletion`, original Proposition 27 | Compatible calculus/SDE inputs; full strong-solution and martingale conclusions |
| First | Theorem 5.1, `thm:approximation` | `RecurrentApproxAssembly`, original Proposition 51 | Exact sharpened constants, pointwise bounds, versions and recurrence specialization |
| First | Theorem 6.1, `thm:splice` | `UnifiedSpliceAssembly`, `SpliceLocalizationAssembly`, original Propositions 52–53 | Stochastic-process completion and exact two-condition equivalence |
| First | Corollary 6.2, `cor:diagonal` | `UnifiedSpliceDiag` | Match polynomial bounds and all restrictions actually stated |
| First | Corollary 6.3, `cor:svensson` | `SvenssonSplice`, original Proposition 40 | Resonance, reverse resonance, PSD conditions and fixed-drift conventions |
| First | Theorem 6.4, `thm:varyingexponents` | `SpliceVaryingExponentsAssembly`, original Proposition 46 | Full Hessian; adaptedness, positivity and same-decay grouping; constant-process conclusion |
| Second | Proposition 2.1, `prop:bond` | `DiffusionMeetingConsistency`, original Proposition 49 | Nonzero-diffusion model bridge and true discounted-bond martingale |
| Second | Proposition 2.2, `prop:pricing` | `DiffusionMeetingAssembly`, original Proposition 49 | Actual futures/cash laws and full parameter identification, including zero variance |
| Second | Proposition 2.3, `prop:finitequotes` | `CompoundedFuturesIdentification`, original Lemma 18/Proposition 19 | Nonzero initial curve and deterministic-background rescaling |
| Second | Theorem 3.1, `thm:rank` | `DiffusionMeetingRank`, `DiffusionMeetingRankValue`, `DiffusionMeetingInversion` | Exact nonnegative-parameter injectivity and calendar conventions |
| Second | Corollary 3.2, `cor:shape` | `MaturityShapeAssembly`, original Proposition 50 | Model bridge where pricing is used; known-shape rank specialization |
| Second | Theorem 4.1, `thm:aggregate` | `PreWindowVarianceAggregates`, original Proposition 20 | Reuse existing full American proof; verify payoff/envelope/filtration bridge |
| Second | Corollary 4.2, `cor:generalaggregate` | Original Propositions 20 and 49 separately | Missing combined initial-curve/continuous-risk aggregation theorem |
| Second | Proposition 5.1, `prop:cumulative` | `BondOptionPriceIntervals`, original Proposition 17 | Finite-endpoint specialization and attained sharpness |
| Second | Theorem 6.1, `thm:scales` | `GaussianMeetingVarianceCone`, `SurvivingScaleRestrictions`, original Propositions 13/25 | Derive variance representation from the model; all recalibration conclusions |
| Second | Theorem 6.2, `thm:svsupport` | `ZeroMeanReversionUpstreamBridge`, `PositiveMeanReversionSupport`, original Propositions 16/26 | Exact support and conditional-law specialization under the stated SDE assumptions |
| Second | Proposition B.1, `prop:svmap` | `StochasticMeetingVariance`, original Proposition 14 | Derive stochastic representation/isometry/orthogonality/moments; do not assume the target variance identity |

Names above denote `Standalone/<name>.lean` and associated `Novel/*Proof.lean` modules. Additional supporting modules may contain the required lemmas; inspect them before proposing new work.

## 4. Shared stochastic-model and interface bridges

This assignment is necessary wherever a paper-level Brownian model has been replaced by stronger supplied identities in Lean. It is not a request to replace every standard theorem with a first-principles proof.

### 4.1 Gaussian meeting models

Start with `DiffusionMeetingGauss`, `DiffusionMeetingInstance`, `MaturityShapeGauss`, `MaturityShapeInstance`, and their consistency/pricing modules. From independent Gaussian scheduled surprises and a Brownian motion with the paper's augmented information, establish the required integral linearity, joint Gaussian laws and covariance, adaptedness, independence of unrevealed increments, path/maturity versions and stochastic Fubini identities. Instantiate `GaussLaw` and `ShapeGaussLaw` in the paper's scope, including nonzero deterministic background volatility.

Do not pass off the existing no-diffusion instances as this construction. A single nonzero numerical example also does not prove the bridge for every bounded piecewise-constant volatility and every maturity shape admitted by the publication. The general shape extension must have the regularity actually stated in the article.

Assemble bond consistency, true martingales, futures prices, cash prices and observation identities from this bridge. Check the conditional-expectation meaning of `G_t`, the discount-density normalization, and the usual augmentation of the filtration.

### 4.2 First-paper constructions

Check `ItoCalculus`, `LipschitzSDE`, `Predictability`, `IntegralApproximation` and `ExponentialMartingale` inputs used by `BoundedVarianceCompletion`, recurrent constructions and approximation. Supply the model-specific compatibility bridge between the natural and joint filtrations and their integral operators. The example must deliver its stated existence, uniqueness, curve-visible variance, independent noises and true bond martingales from standard assumptions on the same model.

For the recurrence necessity theorem, connect the paper's Brownian-driver assumption to the formal Gaussian rank hypotheses. For sufficiency, check the joint state is the stipulated autonomous diffusion between deterministic restarts, not merely a collection of pointwise curve identities.

### 4.3 Factor models

The deterministic cone currently assumes the variance-integral representation. Derive it from the stated forward model and independent Brownian drivers. For Proposition B.1 derive the random drift contribution, leverage term, conditional isometry, cross-factor orthogonality and required moments from the explicit SDE/calculus assumptions. Retain genuinely assumed SDE solutions as assumptions, as the article does. Verify that the support theorem is about the resulting conditional-variance vector, not an unrelated affine proxy.

## 5. First-paper missing proofs and assemblies

### 5.1 Common exceptional set: Lemma 2.3

Prove the common time–probability null-set argument from rational maturities and continuity of the maturity primitives. Handle the domain `t ≤ T`, all finite horizons, local integrability, and the differentiation step inside maturity intervals. Check that the hypotheses provide one full-measure set on which the required primitives exist; make any missing joint measurability/integrability explicit rather than silently changing quantifiers.

Use the result in the splice and varying-decay arguments. Where stochastic curve recovery only holds for each fixed maturity, separately prove the measurable-version/Fubini step needed for bond integrals; equality at each fixed maturity is not itself simultaneous samplewise equality.

### 5.2 Exact stability theorem: Theorem 5.1

Formalize the **published** constants, not only the looser original Proposition 51 constants. With `ε`, `ā`, `Λ`, `H` and `F₀` defined in `sections/05_approximation.tex`, prove:

\[
\mathbb E|f(t,T)-\widetilde f(t,T)|^2
\leq \varepsilon^2\{\Lambda^2t+4\bar a^2\Lambda^4(tT-t^2/2)^2\},
\]
\[
\sup_{0\leq t\leq T\leq H}\mathbb E|f-\widetilde f|^2
\leq\varepsilon^2(\Lambda^2H+\bar a^2\Lambda^4H^4).
\]

For the jointly measurable quasi-exponential maturity versions define

\[
B_{t,T}=\Lambda^2t(T-t)^2+\bar a^2\Lambda^4t^2T^2(T-t)^2,
\quad E_{t,T}=\bar a^2\Lambda^2\{tT(T-t)+4t(T-t)^2\},
\]
\[
C_H=\frac4{27}\Lambda^2H^3+\frac1{16}\bar a^2\Lambda^4H^6.
\]

Prove both pointwise log-price and price bounds,

\[
\mathbb E|\log P-\log\widetilde P|^2\leq\varepsilon^2B_{t,T},
\quad
\mathbb E|P-\widetilde P|^2\leq\sqrt6\,e^{2F_0(T-t)+E_{t,T}}
\varepsilon^2B_{t,T},
\]

and the stated uniform constants `C_H` and `√6 exp(2HF₀ + ā²Λ²H³) C_H`. Include the noncentred Gaussian fourth-moment inequality, exponential-moment estimate, common initial-curve factor, endpoint cases and the absence of separate dependence on meeting count or spacing.

Complete the application to the realized approximating model, including its own HJM drift, equality of maturity-integrated versions, and the restriction of the realization remark to zero initial curve. Check/formalize the constant-loading example showing the forward error's order and asymptotic drift constant. Do not turn a supremum of expected errors into an expected pathwise supremum.

### 5.3 Splice: Theorem 6.1 and its consequences

Starting from original Propositions 52–53, prove the publication's equivalence as stated: given an existing continuous block process and predictable locally square-integrable noises, the aggregate step orthogonality conditions and affine effective-level residual are equivalent to the existence of admissible front-end drifts. Connect the pathwise formulas to progressively measurable, locally integrable coefficients; construct `L_m` and `C_m` as the appropriate stochastic/time integrals. Establish the required maturity version and integrated drift identity.

For preassigned drifts, prove the additional matching equation rather than interpreting covariance restrictions alone as sufficient. Formalize the split into the two displayed conditions, any observable-coordinate reduction actually invoked, and every polynomial/diagonalizable consequence retained in the article. Do not claim existence of an arbitrary block SDE, minimal state dimension, or true bond martingales from this local criterion.

### 5.4 Remaining structural fidelity

Assemble Theorem 4.2 with exactly Definition 4.1's schedule-independent equations, fixed restart and future-distance input, across **all finite horizons**. Verify the controllable reduction, current/earlier Gaussian interval decomposition, compactness-to-recurrence step and treatment of the first loading entry. Check the dimension bound in Proposition 4.3 counts symmetric coordinates correctly. Prove any missing recovery/no-fixed-maturity-jump and harmonic nonrecurrence claims rather than merely pointing to separately compiled ingredients.

For Theorem 6.4, reconcile the entire Itô Hessian, the permission for diffusive front-end slopes in this subsection, positivity even on vanishing-polynomial sets, adapted initial state, the bounded-family condition and the grouping of equal decay exponents. Check the application of the cited restrictions [filipovic2000exponential] through AX-16. Prove the final indistinguishability-from-initial-value conclusion. This does not enlarge the theorem to correlated moving decays or exponent zero.

Check the precise resonance/PSD cases of Corollary 6.3 and all conclusions of Corollary 6.2 against their standalone statements, including zero-coordinate cases. Existing pointwise classifications do not require new SDE-existence claims.

## 6. Second-paper missing proofs and assemblies

### 6.1 Generalized two-strike identification

For Proposition 2.3 and Appendix D.1, derive `m ≥ K₀ = exp(A₀)` from the paper's window weights for every allowed `S ≤ b`, including diffusion. Prove the strike/price/mean scaling by `K₀` and the known discount factor, then invoke the exact existing injectivity theorem where its premises match. Include `q = 0`, zero first-call price, strict second-strike inequality, and the recovery of `(p,z,q)` after observing futures and the initial curve.

Verify that the preceding whole-surface result identifies the discount factor, mean and variance at the boundary as stated. Do not confuse two-strike identification with numerical stability or availability of those strikes in listed contracts.

### 6.2 Pure-jump American aggregation: verify the existing proof's application

Start with `sectioningFull`, `americanGeneral` and `preWindowVarianceAggregates` already proved in `Novel.PreWindowVarianceAggregatesProof`. Compare their jointly measurable state-functional payoff `Φ(t,state)` and state-measurable dominating function `D(state)` to Theorem 4.1's fixed nonanticipating Borel function of post-cutoff curve history, càdlàg discounted payoff, and integrable envelope under the tilted measure.

Prove any missing factorization/measurability and domination bridge, the raw/completed/right-continuous filtration correspondence, and the identification of stopping rules and values. Include the zero-total-variance case. A state-rule result is not enough, but neither should an already proved full-history result be reported as absent. Any finite-grid approximation route must prove preservation of the stopping-time property, the direction of rounding, and dominated convergence; alternatively specialize the existing direct sectioning result rigorously.

Also check all other parts of Theorem 4.1: fixed contract across allocations, arbitrary integrable post-cutoff cash claims, normalization of the tilted measure, independence of later surprises, futures' dependence on `(V,M₁)`, and the two-window identification statement.

### 6.3 Continuous-risk aggregation: Corollary 4.2

This is a genuinely missing combined publication theorem. With an arbitrary allowed fixed deterministic initial curve and fixed post-cutoff parameters, let

\[
V_A=\sum_{T_i\leq A}v_i+\int_0^A\sigma(s)^2\,ds,
\qquad M_{1,A}=\sum_{T_i\leq A}T_i v_i+\int_0^A s\sigma(s)^2\,ds.
\]

Prove the normalization of `B_A^{-1}/P(0,A)`, that `r_A-f₀(A)` has law `N(0,V_A)` under that measure, and its independence from future drivers. Derive the entire post-cutoff curve representation and price invariance of fixed cash contracts at fixed `V_A`. Derive the futures formula with `δ(bV_A-M_{1,A})` and the known initial-curve/post-cutoff terms.

For the American conclusion, supply the Gaussian-history regression and measurable product/sectioning argument for the continuous pre-cutoff history. Explain/prove where rational-time generation of continuous Brownian paths is used. Check integrable envelopes under the correct tilted measure, usual augmentation, and `V_A = 0`. Reusing only the finite-dimensional pure-jump residual theorem without this bridge does not complete the corollary.

### 6.4 Calibration and optimization mathematics

Formalize or give exact existing specializations for the substantive deductions in Sections 3–5 and 9, not merely the numbered statements:

- `q = δ²𝒱(S)` and `z/δ = ∫₀ˢ𝒱(x) dx`, including background variance and all endpoint conventions.
- Injectivity on the nonnegative orthant, identification of a coordinate or linear quantity by row space, grouped meeting totals, and the additional information from mean rows. Distinguish global parameter injectivity from uniqueness at a boundary point.
- Conditional ATM inversion with fixed discount, mean and strike, its attainable domain, clipping and infinite upper endpoint. Establish monotonicity used for interval inversion at other strikes.
- Price-interval intersection and the precise feasible set; sharp bounds for its linear images, compact-case attainment and recession/unboundedness. No claim of sharpness for omitted structural mean constraints or discarded dependence between observations.
- Cumulative bounds as the exact finite-endpoint specialization of the existing theorem.
- The premium sensitivity derivative, the worst-case box-error formula `Σ |a_ℓ|η_ℓ`, and its weighted-absolute-value LP subject to `Aᵀa=c`; handle the repeated first observation when the meeting is in the second gap.
- Local straddle variance sensitivities, background-cancelling weights, retained earlier-meeting exposure and delta formula. Prove the analytical identities; do not claim an executable or profitable hedge.
- Ideal futures–single-period-swap convexity formula, nonnegative model gap, and infinite upper bound when an unobserved positive tail contribution is unrestricted. Prove the needed feasible direction rather than equating rank deficiency with unboundedness.

Standard finite-dimensional results can be imported from Mathlib. A wrapper theorem proving the actual application is still needed. Do not implement a new general LP solver merely to state these mathematical conclusions.

### 6.5 Factor restrictions and the published-model specialization

After the model bridges in Section 4, verify the full exact-cone and exact-support statements, all rank/affine-hull/atom/conditional variants asserted in Appendix B, and the deterministic terminal-piece and inactive-factor conventions. Include the consequences about partition refinement, bounded-decay recalibration, closure as decay grows, and freely varying ordinal loadings where they appear in the text.

Check the equation-by-equation specialization to [brace2024sofr] in `sections/h_bgs_mapping.tex`, both parameter columns, and the “at most two”/“at most three” active-support conclusions. Source parameter transcription is an external factual input; the mathematical inference from those specified coefficients must be formalized. Do not upgrade upper bounds to exact numerical independence or identify the factor model's pricing map with the independent-announcement model's map.

## 7. Examples, numerical claims, and original-manuscript residual coverage

Audit mathematical content outside the theorem environments. Reuse existing lab checks/declarations, then add the missing exact results or proof-producing certificates needed for assertions made in the publication. The known items requiring a coverage check include:

1. **First-paper examples:** two-point versus Gaussian profile inequalities; exact rank/recurrence of the two-loading example; harmonic nonrecurrence and integral representation; the quadrature-generated recurrence and its order bound; Gaussian forward/bond error formulas; the displayed correlation cross term and its non-affine curvature.
2. **Second-paper aggregation geometry:** feasibility, compactness, relative dimension under strict positivity, coordinate extrema on at most two coordinates, and the three-meeting illustration. Much is already in `PreWindowVarianceAggregates`; verify the exact generality, including the affine-dimension claim.
3. **Calendars and critical decay:** actual versus ideal listing assumptions, finite exact rank counts, mean-row rank restoration, the confounding vector, critical-decay uniqueness and sign changes, and a certified bracket for any quoted rigorous bound. `MaturityShapeS1` and the calendar modules contain existing results; inspect their conclusions before listing them as missing. Rounded numerical roots and singular values must be distinguished from exact rank certificates.
4. **Discrete-meeting ATM example:** binomial-normal option formula, true-variance additivity, failure of ATM-proxy additivity, implied-meeting-increment formula and Gaussian control in Appendix F.3. Prove the general identities and an exact or certified counterexample; check numerical table entries separately. Do not infer that the magnitude observed in a synthetic example is an empirical finding.
5. **Mixture/shape sensitivities:** the centred mixture's second moment, positive scaling of ATM price and quadratic scaling of variance, interval transformation including clipping, the analytic maturity averages used for exposure matrices, and invariance/rank consequences of common nonzero normalization. Certify exact finite-rank claims or correct them to explicitly numerical rank assessments when that is all that has been checked.
6. **Numerical optimization assertions:** retain reproducible checks of feasibility, endpoints and nested-set comparisons. Where the paper calls an optimum sharp for a concrete finite dataset, prefer primal/dual or rational/interval certificates that can be independently checked; specify numerical tolerances and data conversion. Do not label rounded solver outputs or fitted parameter selection as Lean theorems without such a route.

No new data, estimation, synthetic scenario design or plotting is requested. Mathematical identities underlying existing examples and calibration are requested. For empirical observations, preserve the external-input boundary and ensure the validation record says exactly what was checked. Checking a formula in Lean does not certify extraction from a PDF, a provider convention, or the economic suitability of a pricing approximation.

The original manuscript's existing map identifies additional non-formalized pieces: original Corollary 2; finite-calendar/Markov representation qualifications in Propositions 28–29; controllability/minimal-representation reductions; remarks attached to recurrent approximation; and the block decomposition, polynomial carry-over and Jordan remarks around Proposition 52. Audit every such entry against the original text and actual Lean declarations. Close asserted mathematical results retained in the archive, or correct their status explicitly. Do not remove these gaps from consideration just because the publication map does not contain a separate row. Explicit conjectures and excluded publication topics remain labelled as such; no new research programme is requested for them.

## 8. Work order, deliverables, and acceptance

Suggested dependency order:

1. Statement inventory and correction of stale coverage descriptions, especially the American declarations.
2. Shared model/interface bridges; in independent work, the common exceptional-set lemma, exact stability constants and finite-quote scaling.
3. Continuous-risk aggregation and any remaining pure-jump payoff/filtration bridge.
4. Splice stochastic completion, factor-model derivations and realization assemblies.
5. Unnumbered deductions, example identities, finite certificates and remaining original-manuscript coverage.
6. Full fidelity review and updated proof maps.

Keep claims and branches focused under the normal lab process. The human requested the entire completion programme; these stages are not optional assignments. A genuinely blocked item remains visibly open while independent work continues.

Deliver:

- Mathematically reviewed statements/proofs and corresponding `Standalone` and `Novel` results for every new or strengthened claim; sourced and audited upstream changes only where necessary.
- Explicit assembly/specialization theorems connecting the published assumptions and conclusions to the formal statements. Expose inherited assumptions at the publication-result level.
- One complete coverage record with publication label, source result, exact Lean declaration, assumptions, and status; include unnumbered assertions and original-only asserted results. Repair stale module comments as well as Markdown summaries.
- Corrections to publication wording where required, with the precise mathematical reason. Update both publication verification supplements/maps and original manuscript coverage where affected. Do not claim full coverage while a substantive paper-only bridge remains.
- Evidence that the complete Lean project and standard-axiom audit pass; relevant independent mathematical checks/certificates; and paper builds after any LaTeX correction.
- A handoff listing the files to synchronize into the public repository. **Do not push to GitHub as part of this lab request.** The publication export will be updated after the completed work is reviewed.

The final review must compare the LaTeX statement itself to the formal type and its model bridge, not just check that a named declaration exists. It must inspect the unnumbered assertions and the mathematical meaning of any finite numerical certificate. Source data and expressly assumed standard results remain identified inputs.

**Acceptance:** every asserted mathematical result in scope has exact formal coverage from the stated hypotheses, or has been explicitly corrected with the correction carried through the paper and maps. No result is marked complete through a weaker conditional theorem, an uninstantiated extra model assumption, a vacuous example, a stale comment, or a passing Python calculation. Any unresolved substantive obligation prevents reporting “everything checked and formalized.”

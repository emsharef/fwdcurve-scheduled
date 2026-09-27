# Lab request: complete the identified publication gaps

Date: 2026-09-27. Revised following the human's instruction: **do not redo completed work. If a proof is done, it is done.**

This revision supersedes the earlier, broader version of this file. The previous 22-result inventory was not a list of missing proofs and is withdrawn as a lab assignment. There is no request to re-audit the completed research programme, reproduce established proofs, or add new wrappers solely for publication numbering.

The human will restart the lab. Preparing this file does not restart it.

## Scope

There are **two publication results with no corresponding formalization**, followed by **three identified extensions to existing formalized results**. Only the missing parts described below are assigned. Use the existing proofs as dependencies. If an item is already covered by an existing declaration, give that reference and close the item without new proof work.

The target statements are in `paper_pub2/` (the first paper) and `paper_pub3/` (the second paper). Original proposition numbers refer to `paper/PAPER.md`. Lean statements and proofs are under `lean/Standalone/` and `lean/Novel/`.

Completed lab proofs and previously accepted upstream assumptions retain their status. Do not reopen them or reconstruct Brownian motion or stochastic calculus for this request. Keep the existing assumptions explicit when reporting coverage; reuse of a conditional theorem does not make its assumptions disappear.

Do not undertake a new inventory of every theorem, remark, example or original-manuscript result. Do not acquire data, refit models, create illustrations, formalize numerical solvers, pursue conjectures, or restore excluded material. Publication bookkeeping and any further identification of concrete gaps are separate from the lab's proof assignments below.

## 1. New formalization: common exceptional set

**First paper, Lemma 2.3**, `lem:maturitynull`, in `paper_pub2/sections/02_setting.tex`.

Formalize the written argument that the integrated HJM drift identity can hold outside one time–probability null set for every maturity simultaneously. Use the countable union of exceptional sets at rational maturities and continuity of the maturity primitives. Include the domain `t ≤ T`, the stated local-integrability hypotheses, and the differentiation conclusion inside intervals where the coefficients are continuous.

Reuse existing common-null-set or continuity lemmas wherever available. If a measurability or integrability hypothesis is missing from the published lemma, identify the precise correction. This task does not reopen the already proved splice or varying-exponent results that use this kind of argument.

**Deliverable:** the missing lemma, under the publication's hypotheses or an explicitly justified correction, with its Lean declaration.

## 2. New formalization: aggregation with continuous pre-cutoff risk

**Second paper, Corollary 4.2**, `cor:generalaggregate`, in `paper_pub3/sections/04_aggregation.tex`.

The missing result combines the existing pure-jump aggregation theory with the Gaussian meeting/diffusion model. Reuse original Propositions 20 and 49 and their Lean developments. Keep the initial curve and post-cutoff parameters fixed. Define

\[
V_A=\sum_{T_i\leq A}v_i+\int_0^A\sigma(s)^2\,ds,
\qquad
M_{1,A}=\sum_{T_i\leq A}T_i v_i+\int_0^A s\sigma(s)^2\,ds.
\]

Formalize the additional conclusions in the corollary:

- Under the normalized discount density `B_A^{-1}/P(0,A)`, the centred level `r_A-f₀(A)` has law `N(0,V_A)` and is independent of future driving increments.
- The post-cutoff curve representation implies that fixed post-cutoff cash claims depend on the earlier variance allocation only through `V_A`.
- Later-accruing futures have the displayed initial-curve term plus `δ(bV_A-M_{1,A})` and the fixed post-cutoff contribution.
- The American conclusion extends to the continuous pre-cutoff history under the corollary's stated payoff regularity and integrable-envelope assumptions. Supply the new Gaussian-history regression/product representation and the application of the existing sectioning argument. Include `V_A = 0`.

**The pure-jump American proof is already done.** In `Novel.PreWindowVarianceAggregatesProof`, reuse `sectioning`, `sectioningFull`, `americanFull`, `americanGeneral` and the final assembly `preWindowVarianceAggregates`. Do not reprove their reverse inequality, completed-filtration treatment, or zero-variance case. Only prove the additional steps needed for this continuous-risk extension. The existing module header and publication maps saying the reverse inequality is absent are stale documentation, not evidence of a missing proof.

Use the existing Gaussian/calculus interfaces. Do not make construction of a new foundational probability library a prerequisite for this extension, and do not replace the extension itself with an assumption.

**Deliverable:** the corollary's new formalization, assembled from existing results and the genuinely new continuous-history steps.

## 3. Extension only: sharpened approximation bounds

**First paper, Theorem 5.1**, `thm:approximation`, in `paper_pub2/sections/05_approximation.tex`.

Original Proposition 51 and `RecurrentApproxAssembly` already prove the approximation result with its original constants. Its coefficient estimates, stochastic identities, Gaussian estimates, maturity versions and recurrent realization are completed work. Reuse them; do not redo the theorem's foundations or realization construction.

Formalize only the additional published bounds or constants not already supplied by that development. In the paper's notation, the target forward bounds are

\[
\mathbb E|f(t,T)-\widetilde f(t,T)|^2
\leq\varepsilon^2\{\Lambda^2t+4\bar a^2\Lambda^4(tT-t^2/2)^2\},
\]
\[
\sup_{0\leq t\leq T\leq H}\mathbb E|f-\widetilde f|^2
\leq\varepsilon^2(\Lambda^2H+\bar a^2\Lambda^4H^4).
\]

For prices, use

\[
B_{t,T}=\Lambda^2t(T-t)^2+\bar a^2\Lambda^4t^2T^2(T-t)^2,
\quad
E_{t,T}=\bar a^2\Lambda^2\{tT(T-t)+4t(T-t)^2\},
\]
\[
C_H=\frac4{27}\Lambda^2H^3+\frac1{16}\bar a^2\Lambda^4H^6.
\]

The additional pointwise conclusions are

\[
\mathbb E|\log P-\log\widetilde P|^2\leq\varepsilon^2B_{t,T},
\qquad
\mathbb E|P-\widetilde P|^2
\leq\sqrt6\,e^{2F_0(T-t)+E_{t,T}}\varepsilon^2B_{t,T},
\]

with the published uniform bounds using `C_H` and `√6 exp(2HF₀ + ā²Λ²H³) C_H`. The initial curve is common and bounded. Preserve the quasi-exponential maturity-version condition for the price conclusions and the distinction between a supremum of expectations and an expected pathwise supremum.

The formulas specify the target, not a requirement to write a new proof for every line. Cite any existing bound that already has the required strength and add only the remaining inequalities/specializations.

**Deliverable:** the sharpened statements as consequences of the completed approximation development, with the exact published constants.

## 4. Extension only: two-strike identification with the initial curve and background

**Second paper, Proposition 2.3**, `prop:finitequotes`, and Appendix D.1, in `paper_pub3/sections/02_prices.tex` and `paper_pub3/sections/e_calendar_examples.tex`.

The two-strike injectivity argument in `CompoundedFuturesIdentification` (original Lemma 18/Proposition 19) is completed. Do not reprove it, the Black formula, or whole-surface identification.

Add the publication's rescaling step for a nonzero deterministic initial curve and deterministic background volatility. Establish `m ≥ K₀ = exp(A₀)` from `p-z ≥ 0` for the permitted `S ≤ b`, normalize strikes, prices and mean by `K₀` and the known discount factor, and apply the existing injectivity result. Include the publication's `q = 0` boundary and recovery of `(p,z,q)` using the futures quote and initial curve, reusing the existing boundary results.

**Deliverable:** a corollary/specialization covering the publication's additional inputs. The original two-strike theorem remains closed.

## 5. Extension only: constructing the front end from the splice coefficients

**First paper, Theorem 6.1**, `thm:splice`, in `paper_pub2/sections/06_splice.tex`.

Original Propositions 52–53, `UnifiedSpliceAssembly` and `SpliceLocalizationAssembly` are completed. They establish the coefficient criterion, explicit converse drifts, their local integrability, and maturity-uniform envelopes. Do not redo aggregate orthogonality, the effective-level calculation, the diagonalizable case, or their existing converse identities.

The documented remaining paper-only step is the process-level implementation: from the existing block and the specified predictable locally square-integrable front-end noises, construct the front-end levels `L_m` and finite-variation slopes `C_m` by stochastic/time integration of the already derived coefficients. Prove the required progressive measurability of the assembled representation and connect its coefficients to the existing integrated-drift result. Use the common exceptional-set lemma from task 1 where needed.

This is not an existence theorem for an arbitrary block process; the block is given. It does not assert a true-martingale result from local bounds alone. Preassigned drifts continue to require the existing matching equation.

**Deliverable:** the missing process/measurability connection, using the completed splice and localization results unchanged wherever possible.

## Documentation corrections, not proof assignments

Repair only documentation affected by this work:

- Replace the stale claim that the pure-jump American reverse inequality is unproved with the existing declaration references. Do not open a new proof task for it.
- Replace “satisfiable only without diffusion” with the accurate statement that the exhibited instance has zero diffusion and no nonzero-diffusion instance was constructed. This correction does not itself commission a new instance or reopen an accepted interface.
- Add the new declaration references for tasks 1–5 to the publication proof maps, keeping existing entries closed. Reuse existing proofs by citation; a change of publication numbering alone does not require a wrapper theorem.

If an additional suspected gap arises during one of these tasks, identify the exact assertion and the unmatched hypothesis/conclusion in the handoff. Do not turn it into a blanket re-audit or silently enlarge this request. A demonstrated error affecting the assigned extension must be stated plainly and corrected through the normal claim process.

## Completion and handoff

Use the normal review and Lean checks for the new lemmas and extensions. Existing dependencies remain accepted; a regression build is a build check, not a reassignment of their proofs.

For each of the five tasks, report the new declarations, the existing declarations reused, and any remaining limitation. If already covered, report the existing declaration and no further work. Do not claim a gap is closed by assuming its requested conclusion or by silently weakening the publication statement.

Update affected mathematical wording only where a genuine correction is needed. Supply the files and mappings needed for the publication export. Do not push to GitHub or start additional research directions as part of this request.

The author will handle publication-wide bookkeeping, synthetic illustrations and empirical reproduction separately. **Completed proofs are not being reopened.**

# Historical analysis

Run from the repository root:

```sh
python3 papers/identification/analysis/run_analysis.py
python3 papers/identification/analysis/decompose_fit.py
tectonic -X compile papers/identification/main.tex --outdir papers/identification/build
```

The analysis runs offline with NumPy, SciPy, and Matplotlib. It reads prepared data, performs deterministic calculations, and writes tables, figures, and CSV/JSON outputs in `papers/identification/`. It does not start the lab or build Lean. A full run takes a few minutes. Source extraction and acquisition are documented separately in `../data/README.md`; downloads are not needed to reproduce the analysis from the supplied files.

## Inputs and selection

The three inputs in `../data/processed/` are:

- `calibration_panel_with_discount.csv`: same-date FINAL standard calls, puts, futures, and exact-date Eris discount factors.
- `midcurve_monthly_panel_with_discount.csv`: corresponding monthly S0/S2/S3 data with available discount factors.
- `fomc_meetings_asof_2026-03-30.csv`: the Federal Reserve calendar captured before the first sample close.

`input_hashes.json` records their SHA-256 hashes. Missing midcurve curve dates and unmapped weekly options are excluded, not filled. The manually transcribed September 24 excerpt is not an input.

For every date, retain expiries 7–365 calendar days away, strictly before accrual starts, and strikes within 25 rate bp of the futures index. A chain is one expiry on one underlying future. Require at least three paired strikes in total and at least one strike on each side of the future. Use the put when the futures index is at or above the strike, otherwise the call. The nearest strike minimizes absolute moneyness, with lower strike breaking a tie. This yields 555 chains and 4,100 selected strikes on 78 irregularly observed dates, March 30–September 14, 2026.

Premiums and moneyness are in rate bp: one IMM index point is 100 bp. Variances are in bp²; background variance rates are in bp² per ACT/360 year. The normal formula uses the expiry discount factor and the observed futures index as mean. It omits early exercise and the exact cash model's discounting-related mean adjustment. Its rate-index variance (`\mathcal V_N` in the manuscript) is not exactly the theoretical normalized log variance `\mathcal V(S)`. Code variables and output columns retain their existing names such as `Q`, `nearest_Q`, and `nearest_sd`; this notation change does not change the calculations. Each date is analyzed independently, without temporal smoothing or a physical-measure return model.

## Calculations

1. **Calendar:** build the meeting indicator matrix with meetings after valuation and on or before the last selected expiry. Append background exposures for a constant rate, successive 90-calendar-day cells, or every observed expiry gap. The latter two partitions are not nested. Report matrix rank and whether each individual meeting coordinate is in its row space. These are interior variance-panel identification tests.
2. **Price compatibility:** invert each selected premium interval under the normal diagnostic and intersect all intervals in its chain. Solve for nonnegative meeting variances and background rates. Bisect the common premium tolerance to a bracket narrower than 0.0001 bp; the output is the feasible upper endpoint. Fixed tolerances of 0.25, 0.5, and 1 bp are sensitivity choices, not observed spreads.
3. **Risk ranges:** at 0.5 and 1 bp, optimize each meeting variance and their total over the feasible set. Endpoints for different targets need not coexist. The figure uses the earliest date where all three specifications fit at 1 bp: June 18, 2026.
4. **Withheld prices:** fit the nearest strike in each chain, then check other selected strikes. Separately withhold the entire second chronological expiry on every date, retain the full parameter horizon, fit all other strikes under constant background, and bound the closest-strike premium at the omitted expiry. A candidate requires its quote interval to be disjoint from the predicted range. Training failures do not produce a prediction.
5. **Activity sensitivity:** keep selected sides with positive volume and open interest at least 100, then reapply the three-strike/both-sides chain requirement. Dates need at least two chains. This is not an executable-liquidity test.
6. **Midcurves:** apply a standard chain's nearest-strike implied variance to the same-expiry midcurve's nearest strike, using the latter's futures price and discount factor. S0/S2/S3 advance the underlying reference quarter by one/two/three years. This tests the joint normal, parallel-loading, and exercise approximation; it does not isolate any one cause of a discrepancy.
7. **Futures and curve forwards:** deduplicate date/underlying-quarter pairs from standard options 7–365 days to expiry, independently of the moneyness/chain screen. Compare the futures rate with `(D(a)/D(b)-1)/ACT360(a,b)`. The resulting 309 comparisons use a provider-built curve, not independent executable OIS quotes. No fitted model convexity adjustment is subtracted.
8. **Local calendar hedge:** use the first two selected expiries on September 14. Compute straddle weights cancelling first-order constant-background sensitivity, and the corresponding futures delta hedge. Sensitivity to a meeting before both expiries remains: it is g2(1−S2/S1), equal to about −0.01170 premium bp per bp² in the example, versus +0.01337 for the intervening meeting. These local diagnostic Greeks imply neither a static event-variance payoff nor a trading recommendation.

## Outputs

| File | Contents |
|---|---|
| `summary.json` | Sample counts and aggregate results used in the manuscript |
| `calendar.csv` | Rank and individual-identification counts by date and background |
| `fit_tolerances.csv` | Minimum uniform premium tolerances, all strikes and nearest strikes |
| `risk_ranges.csv` | Conditional variance endpoints by target, date, background, and tolerance |
| `held_expiry.csv` | Training feasibility, withheld premium, prediction endpoints, and interval separation |
| `chain_diagnostics.csv` | Nearest-strike variance, omitted-strike error, best chain fit, and discount effect |
| `activity_screen.csv` | Fit after the volume/open-interest screen |
| `midcurve_transport.csv` | Predicted and observed midcurve premiums and implied standard deviations |
| `futures_curve_gaps.csv` | Same-window rates, gaps, and implied convexity exponents |
| `local_hedge_example.json` | Contract dates, strikes, straddle and futures weights |
| `fit_table.tex` | Generated manuscript fit table |

Four `../figures/empirical_*.pdf` files reproduce the manuscript figures. `range_figure_date.json` records the date-selection outcome.

## Results and checks

No selected variance panel identifies the full meeting allocation. Constant background fits all selected strikes within 0.5 bp on 4 of 78 dates; expiry-gap background does so on 5. Their median minimum tolerances are 1.683 and 1.411 bp. The median largest omitted-strike error per chain is 1.000 bp. Same-expiry midcurve transport has a median absolute error of 3.438 bp across 165 comparisons. The held-expiry training sets fit on 4 dates at 0.5 bp and 26 dates at 1 bp; every corresponding held quote interval overlaps its conditional prediction interval.

The script checks inversion by repricing every selected premium, checks LP constraints at optimized endpoints, and reprices all input strikes at each reported feasible minimum tolerance. It also checks the calendar hedge's background cancellation and its straddle variance derivative by finite differences. These are floating-point checks, not formal error certificates. The results are conditional sensitivity sets under a deliberately limited approximation, not confidence intervals, a validated American calibration, or a P&L backtest.

## Decomposition of the minimum fitting error

The script decompose_fit.py consumes chain_diagnostics.csv and fit_tolerances.csv and writes fit_decomposition.csv and fit_decomposition.json. It compares the per-date maximum of the independently optimized chain errors with the expiry-gap, constant, and 90-day background fits. The first two agree on every date to within 0.000051 premium bp, below the 0.0001 bp bisection precision. Thus the expiry-gap model's minimum tolerance is already required by within-chain pricing errors. The standard panel has one chain per expiry/date; it cannot separately identify cross-expiry ordering and underlying-window effects. The script checks this uniqueness and all relevant nested-feasibility inequalities. Constant background increases the tolerance on 30 dates, 90-day background on nine, using 0.0002 bp as the numerical comparison threshold. These are deterministic sample calculations.

## Smile, maturity, and exercise extensions

Run `python3 papers/identification/analysis/extend_empirics.py --refit`. Without `--refit`, saved chain fits are reused. The program verifies input hashes against the baseline. All inputs are existing local files; no lab or network process is involved.

- `mixture_chains.json`: equal-weight two-normal price interpolants with means +/-d, separate scales, fitted ATM price, equivalent-normal ATM variance, distinct mixture second moment, and closest-strike holdout errors. Three bounded least-squares starts are used. Holdout scaling uses training strikes only. The mixture is not a stochastic-rate exercise model.
- `mixture_calendar.csv`, `mixture_ranges.csv`: calendar fits and conditional LP ranges from allowances around the interpolated ATM price, not around every original strike.
- `shape_grid.csv`: the original 42-parameter-pair grid (37 distinct shapes) for a common hump, trained on 219 standard/S0/S2 observations on 14 dates; the 37 S3 observations are withheld. Allocations are separate by date. Reported selection uses training SD RMSE only. The seven zero-amplitude entries are the same parallel shape.
- `shape_calendars.csv`, `shape_ranges.csv`: subsequent all-product fits/ranges using the selected shape. These are separate from the holdout test.
- `shape_profile.csv`: endpoints for each grid shape compatible at a 1 bp ATM allowance, under constant background. Their union is finite-grid sensitivity, not confidence coverage over all loadings.
- `exercise_sensitivity.csv`: 69 selected strikes on the first/middle/last dates, with 400/800/1600-step American-minus-European premiums on the same arithmetic-normal trinomial lattice. European error against the closed form is recorded separately. The zero-rate early-exercise premium is checked to vanish.
- `mean_sensitivity.csv`: June18 bounds on the Gaussian mean adjustment after inserting compatible ATM-proxy allocations as a conditional sensitivity calculation. No joint exact-cash calibration is claimed.
- `extensions_summary.json`, `extensions_checks.json`, `extensions_input_hashes.json`: reported aggregates, nested-normal/quadrature/held-row-span checks, and input hashes.
- `coverage_diagnostics.json`: meeting-proximity counts for captured dates and a weekday benchmark. Weekdays are not adjusted for exchange holidays.

The fixed mixture parameter bounds and the finite maturity-shape grid are modelling restrictions. The exercise calculations size a benchmark effect; they do not Europeanize all quotes. ATM proxy additivity is an empirical specification, not a theorem about mixture second moments or exact HJM log variances. The fitted hump's withheld S3 error is worse than the parallel model's, and that failure is retained.

Run `python3 papers/identification/analysis/calendar_examples.py` for `calendar_examples.json`, `critical_shape.csv`, and `figures/critical_shape.pdf`. This standalone program reproduces the listing distinction, uses Fraction elimination to check parallel ranks exactly, brackets the unique positive critical decay, and verifies the equal-variance confounding direction and its tiny mean effect. It does not import or run the lab checks.

## Second-round calculations

Run `python3 papers/identification/analysis/round2_analysis.py` **after** `extend_empirics.py`: the second-round program regenerates the current two-loading version of `figures/empirical_extensions.pdf`. It reuses `mixture_chains.json`, checks the existing input hashes, and requires no network or lab operations.

- `round2_allowances.csv`: seven expiry-specific June 18 allowances, each split into 0.25 bp, the ATM American-normal exercise benchmark, and the largest discounted mean-shift upper bound across the three 1 bp seed feasible sets. Every allowance is below 1 bp, verifying seed containment.
- `round2_robust_ranges.csv`: all meeting endpoints under each background with the same allowance vector. Constant-background September and January lower bounds remain positive.
- `round2_loading_grid.csv`: 496 distinct free-long-end shapes, trained on 219 observations; 37 S3 observations enter reported errors only. The expanded pure-hump subset has 64 distinct shapes.
- `round2_loading_boundary.csv`: 1,081-shape training-only boundary check extending both amplitudes to 64; it retains the primary optimum (12,8,1.5).
- `round2_loading_predictions.csv`: fitted and S3 predicted SDs under the selected new shape. S3 MAE is 1.131 bp. Family choice was informed by the previous S3 failure, so this is diagnostic sample reuse, not fresh validation.
- `round2_window_bands.csv`: representative maturity-distance quartiles and full exposure-distance ranges. Figure bands use the quartiles.
- `round2_atm_additivity.csv`: exact binomial-normal ATM prices for eight ±25 bp meetings at 1/8-year intervals, four background volatilities, and 4% discounting; additive-proxy price errors and inferred meeting allocations.
- `round2_summary.json`: all new headline results, training selection and boundary-check outcomes.
- `round2_checks.json`: 20/40-point integration agreement, comparison with the original hump implementation, independent nested adaptive integration, and Gaussian additivity controls.

The original empirical outputs remain available. The new program overwrites only its own outputs and the revised smile/loading figure. The broad exercise benchmark is not a uniform exercise bound, and ATM-proxy allocations are not automatically true discrete-outcome variances.

## Third-round sensitivities

Run `python3 papers/identification/analysis/round3_analysis.py` after the second-round analysis. It reuses the saved mixtures and allowance vector, verifies prepared-panel hashes, and writes only its own outputs.

- `round3_moment_observations.csv`: June 18 mixture second moments, their ratios to ATM variances, inherited ATM allowances, and scale-perturbation moment intervals.
- `round3_moment_ranges.csv`: feasibility and all meeting endpoints under constant, 90-day, and expiry-gap backgrounds, with extra relative moment allowances 0, 0.10, 0.25, and 0.50. The CSV field `eta` denotes the appendix's scalar ζ; it is not the factor model's scale-weight vector. Empty endpoints denote infeasibility, not unboundedness.
- `round3_front_sensitivity.csv`: July 22 all-product expiry-gap exposure ranks and singular values after flattening the selected free-level loading through 0, 0.5, 1, 1.5, and 4 years. Curves are normalized at one year, and parameter coordinates retain ACT/360 units. No allocations or shapes are refitted.
- `round3_summary.json`: headline results and numerical checks.
- `round3_input_hashes.json`: exact input-panel, fitted-mixture, and inherited-allowance hashes.

The second-moment intervals scale the whole centred mixture using the existing ATM allowances, then widen its moment endpoints by the chosen relative allowance. This is a sensitivity protocol, not a fitted tail-error distribution or a new American exercise calculation. Constant and 90-day backgrounds fail at zero extra allowance. Both constant-background headline lower bounds survive at 10%, only January survives at 25%, and neither survives at 50%. These unfavorable cases are retained.

The front sensitivity uses an analytic maturity primitive and Gauss–Legendre time integration split at clamping boundaries. It checks 20-versus-40-point agreement, rank thresholds, and the fully flattened parallel control. The exposure singular values are scaling-dependent sensitivity diagnostics, not confidence statements.

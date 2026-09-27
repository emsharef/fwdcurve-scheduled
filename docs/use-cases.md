# Worked uses of the software

The second paper supplies calculations for evaluating a model and diagnosing
prices. Its code is a research reproduction package; the examples below use
the supplied conventions and data.

## Can the calendar distinguish a meeting's risk?

Run `python scripts/reproduce.py examples` and inspect
`papers/identification/analysis/calendar_examples.json`. The meeting indicators
and background exposures form an observation matrix. Its rank and row space
show which meeting coordinates can be identified. More option expiries need
not identify more meetings when their exposure columns coincide.

For the historical sample, `analysis/calendar.csv` reports this calculation
date by date under three background-volatility assumptions.

## How much meeting risk is compatible with a price interval?

Run `python scripts/reproduce.py analysis --refit`. `analysis/risk_ranges.csv`
contains lower and upper endpoints obtained by linear programming after
inverting premium allowances. `round2_robust_ranges.csv` uses expiry-specific
allowances; `round3_moment_ranges.csv` changes the variance interpretation.

The relevant comparison is across assumptions as well as across meetings:
a positive lower bound under constant background can become zero under a
flexible background. Endpoints for different meetings need not occur at the
same allocation. These are conditional bounds, not estimated probabilities
of policy decisions.

## Does a loading fit longer-underlying options?

`analysis/midcurve_transport.csv` compares same-expiry standard and midcurve
observations under a parallel loading. `round2_loading_predictions.csv` reports
the maturity-shaped experiment. Training uses standard/S0/S2 observations;
S3 errors are reported separately. Family selection reused the previously
examined S3 sample, so its improvement is a diagnostic rather than independent
out-of-sample validation.

## Futures versus curve forwards

`analysis/futures_curve_gaps.csv` compares a futures rate to the same-window
forward rate from the provider curve. It is a starting point for assessing
convexity and curve-input choices. It does not identify an executable OIS
arbitrage: the inputs are not independent synchronized bid/ask quotes, and
the computation does not subtract a fitted exact convexity adjustment.

## Local calendar hedges

`analysis/local_hedge_example.json` gives straddle and futures weights that
cancel first-order constant-background sensitivity in the chosen example.
An earlier meeting's sensitivity remains, as shown in the paper. Inspect the
residual exposures before interpreting the spread as an event-risk position.
No transaction-cost or historical P&L result is supplied.

For a different panel, start with the supplied input schemas and
`analysis/run_analysis.py`: change data and selection explicitly, then rerun
all stages. Do not compare modified inputs to the release's benchmark hashes
as though they reproduced the published sample.

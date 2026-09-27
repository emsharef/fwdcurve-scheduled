# Reproducing the papers

Run the commands from the repository root. Python 3.13 is the release
environment. Install `requirements.txt` in a virtual environment; the scripts
use NumPy, SciPy/HiGHS, and Matplotlib. No credentials or live market-data feed
are needed for numerical reproduction.

## Synthetic examples

```sh
python scripts/reproduce.py examples
```

This regenerates the first paper's jump-profile, Hankel-rank, approximation,
and splice-correlation figures; checks its three-exponent and Svensson
examples with exact rational arithmetic; and regenerates the second paper's
aggregation, premium-precision, calendar, and critical-loading examples.
The programs assert the relevant identities, ranks, feasibility and inversion
checks. They do not rely on random simulation.

Outputs are beside their programs in `papers/*/examples/`, with figure PDFs
in `papers/*/figures/`. The obsolete September 24 exploratory market example
from an early draft is not part of this release's example program.

## Full empirical analysis

```sh
python scripts/reproduce.py analysis --refit
python scripts/check_results.py
```

The prepared inputs are the three files named in
[`analysis/input_hashes.json`](../papers/identification/analysis/input_hashes.json).
Their hashes are also checked against the independent release source snapshot.
The runner executes these stages in order:

| Program under `papers/identification/analysis/` | Reproduces |
|---|---|
| `run_analysis.py` | Sample selection, variance inversion, calendar rank, price-compatible LP sets, risk ranges, withheld prices, activity screen, midcurve comparisons and futures/curve gaps |
| `decompose_fit.py` | Independent-chain versus calendar fitting-error decomposition |
| `extend_empirics.py --refit` | All smile-mixture fits and strike holdouts, original maturity-shape grid, exercise and mean sensitivities |
| `calendar_examples.py` | Exact rational calendar ranks, critical decay and confounding direction |
| `round2_analysis.py` | Expiry-specific allowances, free-long-end loading grid and boundary check, discrete-meeting ATM nonadditivity |
| `round3_analysis.py` | Mixture-second-moment ranges and front-loading rank/conditioning sensitivity |

Historical script names identify calculation batches, not journal review
status. The order matters: `round2_analysis.py` writes the current version of
`empirical_extensions.pdf`. Logs and an environment/timing record are written
to ignored `build/`; numerical outputs remain in the article's `analysis/`
directory. A full run can take several minutes or longer, depending on CPU
and linear-program solver performance.

Without `--refit`, the runner reuses the included `mixture_chains.json` and
recomputes subsequent calculations. This is useful for reading sensitivities,
but is not a fresh estimation of the mixtures.

`check_results.py` compares six summary files with the release benchmarks in
[`expected-results.json`](expected-results.json). Counts and strings must agree
exactly. Floating-point comparisons allow relative error `1e-5` or absolute
error `1e-3` in the stored variable's units. Script-level checks are additional;
passing these checks does not validate the empirical pricing approximation.
PDF byte identity is not expected because timestamps and font metadata can vary.

For column conventions and every output, see the
[analysis reference](../papers/identification/analysis/README.md).

## Compile the papers

Install Tectonic separately and put `tectonic` on `PATH`, then run:

```sh
python scripts/reproduce.py papers
```

This builds the two publication papers, the first paper's verification
supplement, and the original full manuscript. It places intermediate files
under each paper's ignored `build/` directory and refreshes the top-level
`paper.pdf` or `verification.pdf`. The first use of Tectonic may need network
access to download TeX packages; numerical analysis itself is offline.

The original lab Markdown is retained as the historical source. Its generated
LaTeX and bibliography are supplied so that recompiling the original PDF
requires no lab converter or scheduler. This command compiles the supplied
LaTeX; it does not regenerate that LaTeX from the Markdown.

## Formal proofs

Follow the [formalization guide](formalization.md). The Python and TeX commands
do not run Lean. Conversely, the Lean build does not run data analysis.

## Validate the package

```sh
python scripts/proof_map.py --check
python scripts/check_results.py
python scripts/check_package.py
```

The source snapshot records the exact inputs copied from the lab; it is not
a substitute for this repository's commit ID. Publication directories were
not tracked in the source lab's Git history, so the snapshot includes per-file
hashes rather than attributing all paper content to the lab commit alone.

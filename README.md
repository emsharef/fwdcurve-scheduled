# Forward curves with scheduled dates

Research papers, reproducible calculations, and Lean proofs for interest-rate
models with scheduled policy meetings. The papers ask two related questions:
which forward-curve dynamics are consistent with bond pricing, and which
meeting risks derivative prices can distinguish.

| Paper | Read | Source |
|---|---|---|
| **Forward curves with scheduled dates: consistency, realizations, and correlation** | [PDF](papers/structure/paper.pdf) | [LaTeX](papers/structure/main.tex) |
| **What options reveal about policy-meeting risk: identification and factor-model restrictions** | [PDF](papers/identification/paper.pdf) | [LaTeX](papers/identification/main.tex) |
| **Original full research manuscript** — the broader development, proofs, and open questions | [PDF](papers/lab/paper.pdf) | [Markdown](papers/lab/PAPER.md) · [LaTeX](papers/lab/main.tex) |

These are research manuscripts. The first paper treats announcement laws,
finite-dimensional realizations, approximation, and the correlation restrictions
on combining curve families. The second treats identification, calibration
bounds, factor restrictions, and SOFR option diagnostics.

## Start here

- **Read the mathematics:** the [consolidated proof map](docs/proof-map.md)
  links each numbered publication result to the original manuscript and exact
  Lean statements and proofs. It records paper-only extensions and explicit
  hypotheses. The [formalization guide](docs/formalization.md) explains how to
  interpret and check these proofs.
- **Reproduce an example:** install the numerical dependencies and run the
  examples below. No market-data account is needed.
- **Reproduce the empirical results:** use the included prepared inputs and
  the [reproduction guide](docs/reproducing.md). Source URLs, hashes, extraction
  code, and optional downloads are documented in the [data guide](docs/data.md).
- **Use the calculations:** see [worked uses](docs/use-cases.md) for calendar
  identification, conditional risk ranges, midcurve comparisons, and local hedges.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python scripts/reproduce.py examples
```

The full analysis, including refitting the saved smile interpolants, is:

```sh
python scripts/reproduce.py analysis --refit
python scripts/check_results.py
```

To compile all papers with an installed Tectonic executable:

```sh
python scripts/reproduce.py papers
```

The Lean project has its own pinned toolchain and dependency manifest:

```sh
cd lean
lake exe cache get
lake build
```

The build includes an axiom audit. Lean proves the encoded statements under
their explicit assumptions; it does not construct every stochastic-calculus
interface used by the papers. Numerical fits and the general American-exercise
extension are not Lean-verified. See the proof map for result-level coverage.

## Repository contents

| Directory | Contents |
|---|---|
| `papers/structure/` | First paper, formal-verification supplement, synthetic examples |
| `papers/identification/` | Second paper, analysis programs, data, numerical outputs |
| `papers/lab/` | Original complete lab manuscript, preserved as a research archive |
| `lean/` | `Standalone` statements, `Novel` proofs, `Upstream` hypothesis interfaces |
| `docs/` | Proof map, reproduction instructions, provenance, and mathematical scope |
| `scripts/` | Standalone reproduction and validation commands |

No lab scheduler, agent configuration, private inbox, or development history is
needed. The package is a snapshot; the archived lab manuscript is broader than
the two publication papers. [Citation information](CITATION.md) and
[licensing scope](NOTICE.md) are supplied separately. Code and Lean proofs are MIT.

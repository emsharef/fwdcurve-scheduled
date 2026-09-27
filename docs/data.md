# Data and provenance

The second paper can be reproduced from the prepared data included in
[`papers/identification/data/processed/`](../papers/identification/data/processed/).
The historical sample contains **555 standard chains and 4,100 selected strikes
on 78 dates, 30 March–14 September 2026**. It is an irregular archive sample,
not a complete daily series.

## Inputs used by the analysis

| File | Role |
|---|---|
| `calibration_panel_with_discount.csv` | Standard monthly options, matched final calls/puts and futures, exact-date Eris discount factors |
| `midcurve_monthly_panel_with_discount.csv` | Monthly S0/S2/S3 comparisons with available same-date curves |
| `fomc_meetings_asof_2026-03-30.csv` | Meeting dates from a calendar captured by the first sample date |

The source-level processed tables are also included so readers can inspect
selection, exclusions, raw-cell transcription, source pages and coordinates,
and contract-total checks. The [data inventory](../papers/identification/data/README.md)
records counts, units, product conventions and known gaps. References there to
bulk `raw/` downloads describe the original collection; most bulk source files
are intentionally retrieved on demand in this repository.

## Source downloads and extraction

Four manifests preserve exact URLs, retrieval metadata, filenames, SHA-256
hashes and failures: `download_manifest.csv`, `midcurve_download_manifest.csv`,
`midcurve_call_replay_manifest.csv`, and `free_supplement_manifest.json`.
Small calendar snapshots and archive indexes are included. Bulk CME PDFs and
Eris curve CSVs are omitted from Git.

```sh
python scripts/restore_data.py --list
python scripts/restore_data.py --download
python -m pip install -r requirements-data.txt
python papers/identification/data/prepare_bulletins.py
python papers/identification/data/prepare_midcurves.py
python papers/identification/data/prepare_free_supplement.py
python papers/identification/data/prepare_calendar_vintage.py
```

The downloader selects successful historical manifest entries and verifies
their recorded hashes. It does not replace immutable manifests with a new
download history. A changed or unavailable response is an error. Internet
Archive availability and provider retention can change; these network steps
are optional and may not recover every original file. Use a separate checkout
for extraction experiments if you want to preserve the supplied inputs.

The historical `fetch_*.py` discovery tools are retained for research use, but
they may rewrite their manifests. The fixed-manifest downloader above is the
appropriate starting point for reproducing this snapshot.

## Interpretation

The primary observations are settlement prices, not historical executable
bid/ask spreads. The normal European diagnostic omits full listed-American
exercise and stochastic discounting. The paper studies the sensitivity to
those choices; its fitted ranges are conditional compatible sets, not
confidence intervals or a P&L backtest.

Eris supplies a constructed curve. Same-date joining does not establish
synchronized intraday observations or independence from futures used as curve
inputs. Weekly options with unverified expiry mapping and midcurve dates
without curves are excluded. Missing quotes are not filled with adjacent dates.
The [provenance record](../papers/identification/data/PROVENANCE.md) gives more
detail. Provider data are outside the software's MIT license; see [NOTICE](../NOTICE.md).

# Settlement excerpt used in the manuscript

Observation date: **24 September 2026**. Source header: CME Daily Information Bulletin **184**, **FINAL**.

Public sources inspected on 26 September 2026:

- [Daily Bulletin landing page](https://www.cmegroup.com/market-data/daily-bulletin.html).
- [Section 51: STIR Call Options](https://www.cmegroup.com/daily_bulletin/current/Section51_STIR_Call_Options.pdf), printed page/side 03 for the October, November, December standard SR3 calls, and side 02 for the December SR3 futures settlement.
- [Section 52: STIR Put Options](https://www.cmegroup.com/daily_bulletin/current/Section52_STIR_Put_Options.pdf), printed page/side 01 for matching puts.

These are rotating current-file URLs. The numeric CSV preserves the exact excerpt used; it is not a claim that the current URL will continue serving that date. Browser extraction exposed the dated PDF text. Direct downloads from CME originally timed out. A subsequent Wayback investigation recovered the original **24 September 2026 FINAL call bulletin**, now saved as `raw/cme_calls_2026-09-24_final_wayback.pdf`, from [capture 20260926000441](https://web.archive.org/web/20260926000441id_/https://www.cmegroup.com/daily_bulletin/current/Section51_STIR_Call_Options.pdf). Its printed date and bulletin number 184 were verified from the downloaded PDF. The matching put PDF has not yet been recovered. The excerpt was manually transcribed from the browser tool's extracted PDF text, not obtained from a bulk API; the CSV has not been re-extracted from this recovered file.

## Selection and units

The file contains five common strikes in each of three standard option months: October, November, December 2026. The strike set was chosen as a small nearby sample, not by a liquidity-ranking algorithm. Columns `call` and `put` are **settlement prices**, not closing-range observations, highs, lows, or current bid/ask quotes. The B/A suffixes attached to other bulletin fields were not interpreted as a bid/ask spread.

The December 2026 quarterly SR3 future settlement was **95.6300**. The option headers' displayed “FUTURES SETT. .00” are not usable underlying quotes; the separately listed futures settlement is used.

All prices in the CSV are IMM index points. Multiply a premium by 100 to obtain rate-basis-point premium units. Multiply a price-index difference by 100 to obtain a rate-basis-point strike difference. Selected strike codes decode as follows:

| Bulletin code | Strike |
|---|---:|
| 9550 | 95.500 |
| 9562 | 95.625 |
| 9575 | 95.750 |
| 9587 | 95.875 |
| 9600 | 96.000 |

The options expire 16 October, 13 November, and 11 December 2026. Their underlying is the December 2026 quarterly future, reference quarter **16 December 2026 through 17 March 2027**, not the monthly October/November futures. Contract mapping and expiry rules use the registered rulebook sources [cme2026sr3options] and [cme2026sr3futures]. The October 28 and December 9 decision dates use [fomc2026calendar]. Decision days are used; changing to a next-day effective date leaves the variance-panel meeting/expiry assignments unchanged.

The two tolerance scenarios, ±0.0025 and ±0.0050 index points, equal ±0.25 and ±0.5 rate bp. These are one and two settlement increments under the registered rulebook, **not inferred spreads**. Outright trading increments are contract- and premium-dependent.

## What is and is not calibrated

Only the three calls at strike 95.625 enter the reported near-the-money calibration. The remaining twelve calls are an additional price check. Puts are preserved for a parity and transcription diagnostic, not used in the LP bounds. The pricing approximation fixes the futures mean, omits discounting, and uses a European normal terminal distribution. It does not include American exercise or exact daily compounding. The interval inversion is exact for that approximation, not for the actual listed contract.

No account, paid feed, intraday history, or historical bid/ask collection was used. No statistical claim is based on this convenience sample.

## Historical archive check, 26 September 2026

The CDX archive index lists 105 distinct call-PDF captures and 105 distinct put-PDF captures during March–September 2026 after collapsing identical content digests. The saved JSON indexes are in `raw/wayback_calls_2026_index.json` and `raw/wayback_puts_2026_index.json`. These are capture records, not verified counts of matching trading-date pairs; each PDF header and preliminary/final status must be checked. The simpler Wayback availability API returned empty results for URLs that the full CDX index successfully located, so its negative responses were not conclusive.

A second downloaded sample is `raw/cme_calls_2024-08-06_preliminary_wayback.pdf`, seven pages, printed trading date 6 August 2024, PRELIMINARY, bulletin 151. It comes from [capture 20240807064405](https://web.archive.org/web/20240807064405id_/https://www.cmegroup.com/daily_bulletin/current/Section51_STIR_Call_Options.pdf). No claim of complete daily historical coverage is made.

## Expanded data collection

The subsequent historical download is complete: 210 indexed PDFs are stored under `raw/wayback/`, with SHA-256 hashes and printed dates in the manifests. The prepared historical panels and their precise coverage are described in [README.md](README.md). This separate dataset contains 78 dates with matching final calls, puts, and underlying futures. All 3,793 extracted contract totals agree with the PDFs. The original fifteen call prices have now been cross-checked automatically against the recovered September 24 PDF and agree; the original put-price excerpt remains without a matching archived source PDF. The expanded panels do not fill this gap with a different date.

## Free curve and midcurve supplement

The next collection recovered Eris SOFR discount curves for all 78 standard-panel dates and September 24, with provider par-rate files and a holiday/cash-flow example. Exact-date discount factors are now attached to every standard-panel pair. Separately, 131 additional CME midcurve PDF downloads yield 3,139 matched monthly strike pairs on 17 dates; 2,755 also have matching downloaded curves. The two remaining curve dates timed out and are not filled. All 2,951 midcurve contract-total comparisons pass. Weekly rows are retained but not mapped into calibration. Full counts, source URLs, hashes, missing requests and reproduction commands are in [README.md](README.md) and its linked manifests.

A March 30, 2026 archive capture of the Federal Reserve calendar supplies the 16 scheduled 2026–27 decision dates available by the start of the standard calibration panel. All agree with the September calendar. These additions are prepared data, not new fitted results; the manuscript's existing numerical illustration and its pricing limitations have not been changed.

## Historical analysis incorporated in the manuscript

The current empirical sections supersede the original single-date illustration. They use the prepared standard and midcurve panels with discount factors and the March calendar vintage. The original manual excerpt, including its unverified put transcription, is excluded. The fixed protocol, numerical checks, output guide, and precise pricing limitations are in [../analysis/README.md](../analysis/README.md); input hashes are in `../analysis/input_hashes.json`.

## Eris curve-input clarification

CME Clearing Advisory 23-050 (14 February 2023, production effective 27 February 2023) was read through the browser PDF extractor on 26 September 2026: https://www.cmegroup.com/notices/clearing/2023/02/Chadv23-050.pdf . It specifies one monthly SR1 and up to thirteen quarterly SR3 futures, Eris SOFR swap futures, and SOFR OIS as curve inputs, and identifies the same public FTP destination used by this dataset. Direct PDF downloads timed out; no local original of this notice is claimed. All 309 futures/curve comparisons have quarter starts no farther than 1.025 ACT/360 years from valuation, inside the maximum front-end futures-input horizon. The discount-factor outputs do not expose daily input membership, weights, or Jacobians; they cannot quantify a percentage SR3 contribution. The paper therefore uses the comparison as a curve-consistency diagnostic, not independent market validation of a futures convexity premium.

## Second-round manuscript sensitivities

The second-round calculations add no market data. `analysis/round2_analysis.py` checks the prepared-panel hashes against `analysis/extensions_input_hashes.json` and reuses the saved mixture fits. New allowance, loading-grid, and synthetic outputs are listed in `analysis/README.md`. S3 data were already examined in the original loading experiment; the extra family's result is therefore diagnostic reuse of that sample.

The third-round second-moment and front-loading sensitivities also use only these existing panels. `analysis/round3_input_hashes.json` additionally records the saved mixture fits and second-round allowance file consumed by the calculation. No new market observations were fetched.

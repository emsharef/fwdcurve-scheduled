# Data for the second paper

Start with [`processed/calibration_near_money.csv`](processed/calibration_near_money.csv): **8,492 matched call/put strike observations on 78 trading dates**, within 50 rate basis points of the underlying future and with option expiry through December 2027.

**Free discount curves are now available for every calibration date.** [`processed/calibration_panel_with_discount.csv`](processed/calibration_panel_with_discount.csv) adds same-date Eris SOFR discount factors at option expiry and both accrual boundaries to all **20,498** pairs. See the free supplement below for source conventions and limitations.

The full matched panel, [`processed/calibration_panel.csv`](processed/calibration_panel.csv), contains **20,498 call/put strike pairs**. Each pair has its same-date SR3 futures settlement, exact strike decoding, rule-derived option expiry, underlying reference quarter, accrual day count, and links back to the source PDF and page. These panels contain **FINAL** bulletins only, positive time to expiry, and numerical settlements on both sides. They impose no minimum-volume or open-interest screen. The near-money subset is a starting universe, not a claim of executable liquidity or model adequacy.

## Coverage

| Item | Available |
|---|---:|
| Archived 2026 bulletin PDFs downloaded | 210 |
| Distinct printed trading dates across either side | 118 |
| Printed-date range across either side | 18 March–24 September 2026 |
| Dates with matching final calls, puts, and SR3 futures | 78 |
| Matched-panel date range | 30 March–14 September 2026 |
| Selected PDF editions after per-date/side deduplication | 201 |
| Extracted standard SR3 option rows | 104,329 |
| Numerical option settlements | 92,936 |
| Cabinet quotes retained but excluded from calibration | 11,044 |
| Blank option settlements retained but excluded | 349 |
| Extracted SR1/SR3 futures rows | 5,020 |
| Independent contract-total comparisons | 3,793; all agree |
| NY Fed SOFR fixings | 144; 2 March–24 September 2026 |

This is an irregular historical sample, not a complete daily series. See [`processed/date_coverage.csv`](processed/date_coverage.csv). Capture dates are not trading dates: all matching uses the date printed inside each PDF. Preliminary editions remain in the archive and source manifest but do not enter the final-only calibration panel.

## Files

- `raw/wayback/`: all 210 original PDF responses, named by side and archive capture timestamp.
- `download_manifest.csv`: archive URLs, effective download URLs, printed dates, edition status, SHA-256 checksums, and transfer results. All indexed downloads succeeded after retrying at a slower rate.
- `processed/source_manifest.csv`: verified PDF metadata used by the extractor.
- `processed/options_all.csv`: all selected standard SR3 option rows, including cabinet and blank cells, volume, open interest, reported delta, raw cells, source page and vertical coordinate.
- `processed/futures_all.csv`: SR1 and SR3 settlements extracted from the call bulletins.
- `processed/contract_total_checks.csv`: parsed sums compared with printed contract volume and open-interest totals. Every comparison passes.
- `processed/parse_issues.csv`: 349 rows where the **source settlement cell is blank**; these are disclosed source omissions rather than invented prices.
- `processed/sofr_fixings.csv` and `raw/nyfed_sofr_2026.json`: published SOFR observations, including rate percentiles, volume, and revision indicator.
- `processed/fomc_meetings.csv` and `raw/fomc_calendar_retrieved_2026-09-26.html`: official decision dates for 2026–27 and January 2028, with source and retrieval date.
- `processed/summary.json`: machine-readable counts.

## Units and contract conventions

Premiums, futures prices and strikes are in IMM index points; one index point is 100 rate basis points. Columns ending `_rate_bp` apply that conversion. Reported deltas are transcribed rather than recalculated. Blank volume/open-interest cells remain blank; they are not asserted to be executable liquidity.

The abbreviated strike code `9562` means `95.625`, and `9587` means `95.875`. The parser validates the permitted sixteenth-point code endings rather than dividing the code by 100. Cabinet (`CAB`) settlements are retained textually, without assigning an assumed numerical value.

Standard quarterly options reference the quarter beginning in their expiry month; standard serial options reference the next quarterly month. Option expiry is the Friday before the third Wednesday, adjusted for Good Friday when relevant. Reference-quarter boundaries are third Wednesdays; ACT/360 is stored for accrual. These are mappings under the registered rulebooks [cme2026sr3options] and [cme2026sr3futures], not an independently downloaded exchange expiry master. Emergency closures or contract-specific deviations would require separate verification. FLEX, block-trade summaries, and mid-curve products are excluded by the extractor.

`undiscounted_parity_residual_bp` is a diagnostic, not an arbitrage rejection criterion: listed options are American, and the pipeline does not impose European put–call parity. No prices are changed to force parity, monotonicity or convexity.

## Provenance and limits

CME source files were retrieved from Wayback snapshots of Sections 51 and 52; exact URLs and hashes are in the manifests. Archive indexes are preserved in `raw/wayback_calls_2026_index.json` and `raw/wayback_puts_2026_index.json`. Of the raw editions, 200 are final and 10 preliminary. Selection prefers final over preliminary, then the latest archived capture of the same printed date and side.

The original manuscript's fifteen call settlements on 24 September were independently checked against the recovered PDF and agree. Its fifteen put settlements still lack a recovered PDF for that printed date. They are **not imported into this historical panel**. The current CME put download still timed out; no adjacent-date PDF was substituted.

SOFR comes from the [New York Fed](https://www.newyorkfed.org/markets/reference-rates/sofr), via `https://markets.newyorkfed.org/api/rates/secured/sofr/search.json?startDate=2026-03-01&endDate=2026-09-24`. These are effective-date fixings retrieved now, not point-in-time publication vintages. A next-business-day publication lag and revisions must be handled before any backtest.

The [FOMC calendar](https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm) was retrieved on 26 September 2026. It is not a historical schedule-vintage database; future dates remain tentative. The CSV includes a warning to prevent look-ahead claims based on an earlier valuation date. It is related to the registered calendar source [fomc2026calendar].

**Still not supplied:** historical executable bid/ask spreads or a validated listed-American option pricer. An external SOFR discount-curve panel is now supplied by Eris, as described below. The data support a substantially broader cross-sectional calibration and robustness exercise, but do not resolve the American exercise and valuation choices.

## Free supplement collected 26 September 2026

### Eris SOFR curves

The [Eris public file server](https://files.erisfutures.com/ftp/) and its [2026 archives](https://files.erisfutures.com/ftp/archives/2026/) supplied discount-factor and par-coupon files for **79 dates: all 78 calibration dates, plus 24 September**. The collection contains **1,450,385 daily discount factors** across the raw curve files and **1,895 par-rate rows**, including short tenors. No purchase or login was required. The raw files, four archived directory listings, September 24 holiday file and swap-leg calculation file are in `raw/free_supplement/`. Exact URLs, retrieval timestamps and SHA-256 hashes are in `free_supplement_manifest.json`.

- `processed/eris_par_rates.csv`: provider par rates in **percent**, with effective/maturity dates and original symbols. These are curve-derived par rates, not individual executed OIS quotes.
- `processed/eris_discount_factors_3y.csv`: daily discount factors for the first **1,080 days (3 ACT/360 years)** of each curve. Longer maturities remain in the original files.
- `processed/eris_curve_checks.csv`: valuation-date checks, positive finite factors, unique sorted dates, initial factor equal to one, and agreement between factors and the provider's ACT/360 continuously compounded zero rates. The largest zero-rate identity discrepancy is below 5.1e-11 in decimal rate units.
- `processed/calibration_panel_with_discount.csv`: exact-date lookup at expiry and both accrual boundaries. **No interpolation or date substitution** was needed; all 20,498 pairs match.
- `processed/midcurve_monthly_panel_with_discount.csv`: **2,755 of the 3,139 midcurve pairs**, on 15 dates. The remaining 384 pairs fall on August 4 and August 17, whose curve and par-rate downloads timed out after retries. They remain in the undiscounted-input panel, with no substituted curve. The failed requests are recorded in the manifest; this does not affect any of the original 78 calibration dates.
- `processed/free_supplement_summary.json`: counts and validation results.

Eris is an external, provider-constructed curve, not a direct observation of every discount factor. [CME's description](https://www.cmegroup.com/articles/2023/how-eris-futures-help-leveraged-investors.html) relates Eris valuation curves to Eris futures order-book mid-prices. The same-date joins do not establish synchronized intraday observation times with the option settlements, nor immutable historical publication vintages. The provider's interpolation and input choices remain part of the curve. Use it as a documented valuation input and sensitivity benchmark; it does not by itself establish joint consistency with the paper's stochastic model. The downloaded Eris holiday calendar is not an authoritative CME option-expiry master.

One secondary-source USD par-rate snapshot, `raw/checkmyswap_USD_2026-09-14.json`, was also obtained from [CheckMySwap](https://www.checkmyswap.com/rates). It contains transaction-derived estimates with method and observation-count fields. It is retained for source exploration only and is **not used** in the prepared discount panel; its historical processing and raw transaction inputs have not been independently reproduced.

### Meeting-calendar vintage

`processed/fomc_meetings_asof_2026-03-30.csv` contains the **16 scheduled 2026–27 decision dates** extracted from the Federal Reserve calendar [captured on 30 March 2026 at 08:30:05 UTC](https://web.archive.org/web/20260330083005id_/https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm). The original compressed response and decoded HTML are preserved in `raw/`; checksums and comparison results are in `processed/fomc_vintage_summary.json`. All 16 dates agree with the September calendar. This establishes availability by the first calibration date, not the original announcement dates or a complete record of intervening revisions. Future dates were tentative.

### Midcurve and weekly options

New source PDFs are in `raw/midcurves/`: **131 downloads (101 puts and 30 calls)**, plus two duplicate initial sample files in `raw/`. After selecting editions, there are **50,690 quote rows on 99 printed dates**, including 464 weekly rows; 45,721 settlements are numeric. All **2,951** printed volume/open-interest total comparisons pass. `processed/midcurve_summary.json` gives the counts, and `processed/midcurve_date_coverage.csv` shows the uneven daily coverage. `processed/midcurve_quotes_unmapped.csv` retains all extracted S0/S0W/S2/S3/S4 quote rows with their printed labels, raw settlement cells, source coordinates, volume and open interest.

`processed/midcurve_monthly_panel.csv` contains **3,139 matched strike pairs on 17 dates, July 22–September 24**. It matches numeric FINAL calls and puts to same-date FINAL SR3 futures for monthly S0/S2/S3 contracts. The reference quarter is advanced by one, two or three years under [cme2026sr3options], Rule 460A01.D.3–5; expiry dates use the same rule-derived convention as the standard panel. The bulletin's placeholder `FUTURES SETT. .00` is never used as a price. No minimum-volume/OI screen is imposed. This is a prepared dataset, not a completed calibration.

Weekly S0W quotes remain **excluded from the matched panel** until their precise expiry weeks can be verified. Some expiration-table row labels are absent in the source PDF itself, so we do not assign a week from position alone. The retained September 24 sample image shows this limitation. The [CME 2026 product guide](https://web.archive.org/web/20260609150138id_/https://www.cmegroup.com/articles/2026/sofr-options-the-new-criteria-to-hedge-interest-rate-risk.html) is preserved as `raw/cme_sofr_options_specs_2026_archive.html`; the registered rulebook remains the basis for monthly mapping.

The put index contains 107 entries: 101 succeeded, two failed after retries, and four earliest captures were not attempted before stopping the download. Both failures and the successful hashes are preserved. The two failed put capture timestamps are `20260422220615` and `20260420215852`. The failed and unattempted dates are outside the July–September call sample used in the matched midcurve panel. The downloader is resumable and now stops after a failed request's retries by default.

The section 54 CDX index is preserved in `raw/wayback_midcurve54_2026_index.json`. Section 53 index requests repeatedly returned errors; call PDFs were instead obtained by requesting the nearest archived capture to selected put timestamps. `midcurve_call_replay_manifest.csv` records both requested and effective capture timestamps/URLs. Filenames for those calls contain the **requested** timestamp. Matching and deduplication always use the **printed trading date** and FINAL status, never assumed capture-date equality. `midcurve_download_manifest.csv` records indexed downloads. Two initially retrieved sample files in `raw/` are named `midcurve53_sample.pdf` and `midcurve54_sample.pdf` ("sample" denotes how they were collected; their printed publication status is FINAL).

## Reproduce

From the repository root, using the existing Python environment with PyMuPDF:

```sh
python papers/identification/data/fetch_bulletins.py
python papers/identification/data/prepare_bulletins.py
python papers/identification/data/fetch_midcurves.py
python papers/identification/data/fetch_midcurves.py --calls-near-puts --limit 30
python papers/identification/data/prepare_midcurves.py
python papers/identification/data/fetch_free_supplement.py
python papers/identification/data/prepare_free_supplement.py
python papers/identification/data/prepare_calendar_vintage.py
```

The `fetch_*` commands need network access and resume existing downloads. The `prepare_*` commands run offline. The original September FOMC CSV is a manual transcription; the March vintage is extracted reproducibly from the preserved HTML. No lab, Lean build, scheduler, or board operation is involved. The subsequent offline analysis is documented in [../analysis/README.md](../analysis/README.md) and incorporated in manuscript Sections 8 and 9. It uses the prepared panels directly; rerunning downloads is unnecessary.

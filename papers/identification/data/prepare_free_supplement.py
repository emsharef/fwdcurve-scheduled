"""Validate public Eris curves and attach exact-date discount factors offline."""
from pathlib import Path
from datetime import datetime, date
import csv, hashlib, json, math

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'processed'

def iso(s): return datetime.strptime(s, '%m/%d/%Y').date().isoformat()
def write(name, rows):
    with (OUT/name).open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]) if rows else [])
        writer.writeheader(); writer.writerows(rows)

def main():
    manifest = json.loads((ROOT/'free_supplement_manifest.json').read_text())
    curves, pars, checks, short = {}, [], [], []
    for entry in manifest.values():
        if entry.get('error') or not entry.get('file'): continue
        path = ROOT/entry['file']
        assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256']
        kind = entry['kind']
        if kind not in ['DiscountFactors_SOFR', 'ParCouponCurve_SOFR']: continue
        rows = list(csv.DictReader(path.open()))
        val = entry['expected_date']
        if kind == 'ParCouponCurve_SOFR':
            assert all(iso(r['EvaluationDate']) == val for r in rows)
            for r in rows:
                pars.append(dict(trade_date=val, symbol=r['Symbol'],
                    effective_date=iso(r['EffectiveDate']), maturity_date=iso(r['MaturityDate']),
                    par_rate_percent=float(r['FairCoupon (%)']), index=r['Index'],
                    source_file=entry['file']))
            continue
        assert iso(rows[0]['Date']) == val and abs(float(rows[0]['DiscountFactor'])-1) < 1e-12
        grid, errors = {}, []
        for r in rows:
            d = iso(r['Date']); df = float(r['DiscountFactor'])
            assert d not in grid and math.isfinite(df) and df > 0
            t = (date.fromisoformat(d) - date.fromisoformat(val)).days/360
            assert t >= 0
            zero = float(r['SpotRate (Actual360 Continuous)'])
            if t > 0: errors.append(abs(-math.log(df)/t-zero))
            grid[d] = df
            if t <= 3:
                short.append(dict(trade_date=val, maturity_date=d, discount_factor=df,
                    zero_rate_act360_continuous=zero, source_file=entry['file']))
        assert max(errors) < 1e-8, (val, max(errors))
        assert list(grid) == sorted(grid)
        curves[val] = (grid, entry['file'])
        checks.append(dict(trade_date=val, rows=len(grid), first_date=min(grid),
            last_date=max(grid), initial_discount_factor=grid[val],
            max_zero_rate_identity_error=max(errors), source_file=entry['file']))
    panel = list(csv.DictReader((OUT/'calibration_panel.csv').open()))
    enriched, missing = [], []
    for r in panel:
        val = r['trade_date']; grid, path = curves.get(val, ({}, ''))
        ds = [r['option_expiry'], r['accrual_start'], r['accrual_end']]
        if any(d not in grid for d in ds):
            missing.append(dict(trade_date=val, contract_label=r['contract_label'], reason='missing exact curve date'))
            continue
        enriched.append(dict(r, discount_to_expiry=grid[ds[0]],
            discount_to_accrual_start=grid[ds[1]], discount_to_accrual_end=grid[ds[2]],
            discount_curve_source=path))
    write('eris_curve_checks.csv', checks)
    write('eris_par_rates.csv', pars)
    write('eris_discount_factors_3y.csv', short)
    write('calibration_panel_with_discount.csv', enriched)
    write('eris_missing_panel_rows.csv', missing)
    midcurve = OUT/'midcurve_monthly_panel.csv'
    mid_joined, mid_missing = [], []
    if midcurve.exists():
        for r in csv.DictReader(midcurve.open()):
            grid, path = curves.get(r['trade_date'], ({}, ''))
            ds = [r['option_expiry'],r['accrual_start'],r['accrual_end']]
            if any(d not in grid for d in ds):
                mid_missing.append(r)
                continue
            mid_joined.append(dict(r,discount_to_expiry=grid[ds[0]],
                discount_to_accrual_start=grid[ds[1]],discount_to_accrual_end=grid[ds[2]],
                discount_curve_source=path))
        write('midcurve_monthly_panel_with_discount.csv',mid_joined)
    summary = dict(curve_dates=len(curves), first_date=min(curves), last_date=max(curves),
        raw_discount_factor_rows=sum(c['rows'] for c in checks), par_rate_rows=len(pars),
        discount_rows_first_1080_days=len(short), matched_option_pairs=len(enriched),
        matched_option_dates=len({r['trade_date'] for r in enriched}), missing_option_pairs=len(missing),
        matched_midcurve_pairs=len(mid_joined),missing_midcurve_pairs=len(mid_missing),
        max_zero_rate_identity_error=max(c['max_zero_rate_identity_error'] for c in checks),
        download_errors=sum(bool(e.get('error')) for e in manifest.values()))
    (OUT/'free_supplement_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__': main()

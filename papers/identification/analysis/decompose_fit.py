"""Decompose existing offline calibration errors; no lab or network operations.

Input: chain_diagnostics.csv and fit_tolerances.csv from run_analysis.py.
The independent-chain benchmark is the maximum of each chain's minimax error.
The expiry-gap increment imposes a nondecreasing cumulative variance sequence;
with one standard chain per expiry it cannot distinguish time effects from
underlying-window effects. Numerical differences below 0.0002 bp are bisection
precision, not economic increments.
"""
from pathlib import Path
import csv
import json
import statistics

ROOT = Path(__file__).resolve().parent
chains = list(csv.DictReader((ROOT / 'chain_diagnostics.csv').open()))
fits = list(csv.DictReader((ROOT / 'fit_tolerances.csv').open()))
by_date = {}
seen = set()
for row in chains:
    key = row['trade_date'], row['expiry']
    assert key not in seen, 'The decomposition requires one standard chain per expiry.'
    seen.add(key)
    by_date[row['trade_date']] = max(
        by_date.get(row['trade_date'], 0), float(row['smile_min_tolerance']))
tolerances = {}
for row in fits:
    tolerances.setdefault(row['trade_date'], {})[row['background']] = float(row['min_tolerance_bp'])
assert set(tolerances) == set(by_date)
records = []
for day in sorted(by_date):
    fit = tolerances[day]
    independent = by_date[day]
    gap = fit['gap']
    assert gap >= independent - 0.0002
    assert fit['constant'] >= gap - 0.0002
    # Nonnegative piecewise background always gives monotone cumulative variance.
    assert fit['90day'] >= gap - 0.0002
    records.append(dict(
        trade_date=day, independent_chain_bp=independent,
        expiry_gap_bp=gap, constant_bp=fit['constant'], cell90_bp=fit['90day'],
        cross_chain_increment_bp=max(0, gap-independent),
        constant_increment_bp=max(0, fit['constant']-gap),
        cell90_increment_bp=max(0, fit['90day']-gap)))
with (ROOT / 'fit_decomposition.csv').open('w', newline='') as f:
    writer = csv.DictWriter(f, fieldnames=records[0])
    writer.writeheader()
    writer.writerows(records)
summary = {
    'dates': len(records),
    'median_independent_chain_bp': statistics.median(r['independent_chain_bp'] for r in records),
    'median_cross_chain_increment_bp': statistics.median(r['cross_chain_increment_bp'] for r in records),
    'max_cross_chain_increment_bp': max(r['cross_chain_increment_bp'] for r in records),
    'dates_cross_chain_increment_gt_00002': sum(r['cross_chain_increment_bp'] > .0002 for r in records),
    'median_constant_increment_bp': statistics.median(r['constant_increment_bp'] for r in records),
    'max_constant_increment_bp': max(r['constant_increment_bp'] for r in records),
    'dates_constant_increment_gt_00002': sum(r['constant_increment_bp'] > .0002 for r in records),
    'dates_cell90_increment_gt_00002': sum(r['cell90_increment_bp'] > .0002 for r in records),
    'median_cell90_increment_bp': statistics.median(r['cell90_increment_bp'] for r in records),
    'independent_feasible_050': sum(r['independent_chain_bp'] <= .5 for r in records),
    'independent_feasible_100': sum(r['independent_chain_bp'] <= 1 for r in records),
}
(ROOT / 'fit_decomposition.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps(summary, indent=2))

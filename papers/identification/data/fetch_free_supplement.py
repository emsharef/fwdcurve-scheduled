"""Fetch public Eris curves for the existing paper sample; no lab operations.

Only public, unauthenticated files. Resumes from validated local files and records
URLs, retrieval times, hashes and failures. Run prepare_free_supplement.py offline.
"""
from pathlib import Path
from datetime import datetime, timezone
from urllib.parse import urljoin
import csv, hashlib, json, re, subprocess, time

ROOT = Path(__file__).resolve().parent
RAW = ROOT / 'raw' / 'free_supplement'
RAW.mkdir(parents=True, exist_ok=True)
MANIFEST = ROOT / 'free_supplement_manifest.json'
records = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}

def fetch(url, name, kind, expected_date=''):
    target = RAW / name
    entry = records.get(name, dict(url=url, file=str(target.relative_to(ROOT)), kind=kind,
                                 expected_date=expected_date))
    try:
        if not target.exists():
            tmp = target.with_suffix(target.suffix + '.part')
            for attempt in range(2):
                time.sleep(0.3 if attempt == 0 else 3)
                result = subprocess.run(['curl', '-L', '--fail', '--silent', '--show-error',
                    '--connect-timeout', '10', '--max-time', '30', url, '-o', str(tmp)],
                    capture_output=True, text=True, timeout=40)
                if result.returncode == 0:
                    data = tmp.read_bytes()
                    if name.endswith('.csv') and (b'<html' in data[:500].lower() or b',' not in data[:500]):
                        raise ValueError('not a CSV response')
                    tmp.replace(target)
                    entry['retrieved_utc'] = datetime.now(timezone.utc).isoformat()
                    break
                if attempt == 1: raise RuntimeError(result.stderr.strip())
        data = target.read_bytes()
        entry.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest(), error='')
    except Exception as exc:
        entry['error'] = str(exc)
    records[name] = entry
    MANIFEST.write_text(json.dumps(records, indent=2) + '\n')
    return target if not entry['error'] else None

def main():
    base = 'https://files.erisfutures.com/ftp/'
    listings = [(base, ROOT/'raw'/'eris_directory.html')]
    for month in ['03-March', '04-April', '05-May', '06-June']:
        url = base + 'archives/2026/' + month + '/'
        path = fetch(url, 'eris_' + month + '_directory.html', 'directory')
        if path: listings.append((url, path))
    available = {}
    for url, path in listings:
        for name in re.findall(r'href="([^"]+\.csv)"', path.read_text()):
            available[name] = urljoin(url, name)
    dates = {r['trade_date'] for r in csv.DictReader((ROOT/'processed'/'calibration_panel.csv').open())} | {'2026-09-24'}
    midcurve = ROOT/'processed'/'midcurve_monthly_panel.csv'
    if midcurve.exists(): dates |= {r['trade_date'] for r in csv.DictReader(midcurve.open())}
    dates = sorted(dates)
    jobs = []
    for date in dates:
        for kind in ['DiscountFactors_SOFR', 'ParCouponCurve_SOFR']:
            name = 'Eris_' + date.replace('-', '') + '_EOD_' + kind + '.csv'
            if name in available: jobs.append((available[name], name, kind, date))
            else:
                records[name] = dict(kind=kind, expected_date=date, error='not found in public directory listings')
    for kind in ['Holidays', 'CurveSwapLegAnalysis_SOFR']:
        name = 'Eris_20260924_EOD_' + kind + '.csv'
        if name in available: jobs.append((available[name], name, kind, '2026-09-24'))
    for i, args in enumerate(jobs, 1):
        fetch(*args)
        if i % 10 == 0 or i == len(jobs):
            print(f'{i}/{len(jobs)} curve/support downloads; failures: {sum(bool(r.get("error")) for r in records.values())}', flush=True)
    MANIFEST.write_text(json.dumps(records, indent=2) + '\n')

if __name__ == '__main__': main()

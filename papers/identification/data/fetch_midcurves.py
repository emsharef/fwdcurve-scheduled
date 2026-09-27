"""Resume-safe public Wayback downloads of CME sections 53/54; no lab tools."""
from pathlib import Path
import argparse, csv, json, re
import fetch_bulletins as source

ROOT = Path(__file__).resolve().parent
source.RAW = ROOT/'raw'/'midcurves'
source.RAW.mkdir(exist_ok=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int)
    parser.add_argument('--calls-near-puts', action='store_true',
                        help='Use put capture times as nearest-replay requests for calls; record redirects.')
    parser.add_argument('--continue-after-error', action='store_true')
    args = parser.parse_args()
    jobs = []
    for section in ['53', '54']:
        path = ROOT/'raw'/f'wayback_midcurve{section}_2026_index.json'
        if not path.exists(): continue
        data = json.loads(path.read_text())
        jobs.extend((f'midcurve{section}', dict(zip(data[0], row))) for row in data[1:])
    if args.calls_near_puts:
        data = json.loads((ROOT/'raw'/'wayback_midcurve54_2026_index.json').read_text())
        jobs = []
        for vals in data[1:]:
            row = dict(zip(data[0], vals))
            row['original'] = 'https://www.cmegroup.com/daily_bulletin/current/Section53_Midcurve_Options.pdf'
            jobs.append(('midcurve53', row))
    jobs.sort(key=lambda x:(x[1]['timestamp'][:8], x[0]), reverse=True)
    if args.limit: jobs = jobs[:args.limit]
    results = []
    manifest = ROOT/('midcurve_call_replay_manifest.csv' if args.calls_near_puts else 'midcurve_download_manifest.csv')
    previous = {r['file']:r for r in csv.DictReader(manifest.open())} if manifest.exists() else {}
    for i, job in enumerate(jobs, 1):
        row = source.fetch(job)
        row['requested_timestamp'] = job[1]['timestamp']
        row['lookup_basis'] = 'nearest replay to put capture; match printed dates only' if args.calls_near_puts else 'CDX index'
        if args.calls_near_puts:
            if row['file'] in previous:
                row['effective_url'] = previous[row['file']]['effective_url']
            match = re.search(r'/web/(\d{14})', row['effective_url'])
            row['capture_timestamp'] = match.group(1) if match else ''
        results.append(row)
        previous[row['file']] = row
        with manifest.open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=source.FIELDS+['requested_timestamp','lookup_basis'])
            writer.writeheader(); writer.writerows(previous.values())
        if i % 10 == 0 or row['error'] or i == len(jobs):
            print(f'{i}/{len(jobs)} PDFs; failures {sum(bool(r["error"]) for r in results)}; latest {row.get("trade_date")}', flush=True)
        if row['error'] and not args.continue_after_error:
            print('Stopped after retries; rerun to resume missing downloads.', flush=True)
            break

if __name__ == '__main__': main()

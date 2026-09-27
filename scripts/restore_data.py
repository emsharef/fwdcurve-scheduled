"""Restore successful recorded source downloads without rewriting the manifests."""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT/'papers/identification/data'


def entries():
    rows = []
    for name in ['download_manifest.csv','midcurve_download_manifest.csv','midcurve_call_replay_manifest.csv']:
        with (DATA/name).open() as f:
            rows.extend(csv.DictReader(f))
    rows.extend(json.loads((DATA/'free_supplement_manifest.json').read_text()).values())
    unique = {}
    for row in rows:
        if row.get('error') or not row.get('sha256'):
            continue
        path = Path(row['file'])
        if path.is_absolute() or '..' in path.parts or path.parts[0]!='raw':
            raise ValueError(f'Unsafe manifest path: {path}')
        url = row.get('effective_url') or row.get('archive_url') or row.get('url')
        if not url or not url.startswith('https://'):
            raise ValueError(f'Missing HTTPS source: {path}')
        item = {'file':str(path), 'url':url, 'sha256':row['sha256']}
        if str(path) in unique and unique[str(path)]['sha256']!=item['sha256']:
            raise ValueError(f'Conflicting hashes: {path}')
        unique[str(path)] = item
    return list(unique.values())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('--list', action='store_true')
    group.add_argument('--download', action='store_true')
    p.add_argument('--limit', type=int, help='retrieve at most this many source entries')
    a = p.parse_args()
    rows = entries()
    if a.limit is not None:
        if a.limit<1:
            p.error('--limit must be positive')
        rows = rows[:a.limit]
    for i, row in enumerate(rows,1):
        target = DATA/row['file']
        print(f'{i}/{len(rows)} {row["file"]}',flush=True)
        if a.list:
            continue
        if target.exists():
            if digest(target)!=row['sha256']:
                raise ValueError(f'Existing file differs from recorded hash: {target}')
            continue
        target.parent.mkdir(parents=True,exist_ok=True)
        tmp = target.with_suffix(target.suffix+'.part')
        subprocess.run(['curl','--fail','--location','--silent','--show-error',
                        '--proto','=https','--proto-redir','=https','--max-time','90',
                        '--retry','2','--retry-delay','5',row['url'],'--output',str(tmp)],check=True)
        if digest(tmp)!=row['sha256']:
            raise ValueError(f'Response differs from recorded hash: {row["url"]}; retained as {tmp}')
        tmp.replace(target)
        time.sleep(1)
    aliases = DATA/'source_aliases.json'
    if a.download and aliases.exists():
        for dest, source in json.loads(aliases.read_text()).items():
            if (DATA/source).exists():
                (DATA/dest).write_bytes((DATA/source).read_bytes())
    print('Listed' if a.list else 'Verified/restored',len(rows),'source entries.')


if __name__=='__main__':
    main()

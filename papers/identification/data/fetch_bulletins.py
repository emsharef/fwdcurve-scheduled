"""Download the already discovered 2026 Wayback CME bulletins; no lab tools.
Resume-safe, one worker, validated PDF headers, checksums, capture and trade dates.
"""
from pathlib import Path
import concurrent.futures, csv, hashlib, json, re, subprocess, time, argparse
from datetime import datetime, timezone
import pymupdf
ROOT=Path(__file__).resolve().parent
RAW=ROOT/'raw'/'wayback'; RAW.mkdir(parents=True,exist_ok=True)
FIELDS=['kind','capture_timestamp','trade_date','publication_status','bulletin_number','pages','bytes','sha256','archive_url','effective_url','file','checked_utc','error']
def inspect(path):
    raw=path.read_bytes()
    if not raw.startswith(b'%PDF'):raise ValueError('response is not a PDF')
    with pymupdf.open(path) as doc:
        text=doc[0].get_text()
        match=re.search(r'(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun),\s+([A-Z][a-z]{2})\s+(\d{1,2}),\s+(20\d\d)',text)
        if not match:raise ValueError('printed trade date not found')
        trade=datetime.strptime(' '.join(match.groups()),'%b %d %Y').date().isoformat()
        status='PRELIMINARY' if 'PRELIMINARY' in text else 'FINAL' if re.search(r'\bFINAL\b',text) else 'UNKNOWN'
        bn=re.search(r'BULLETIN\s*#\s*(\d+)',text)
        return dict(trade_date=trade,publication_status=status,bulletin_number=bn.group(1) if bn else '',pages=len(doc),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def fetch(item):
    kind,row=item; stamp=row['timestamp']; url=f"https://web.archive.org/web/{stamp}id_/{row['original']}"
    target=RAW/f'{kind}_{stamp}.pdf'; r=dict(kind=kind,capture_timestamp=stamp,archive_url=url,file=str(target.relative_to(ROOT)),checked_utc=datetime.now(timezone.utc).isoformat(),effective_url=url,error='')
    try:
        if not target.exists():
            temp=target.with_suffix('.part')
            for attempt in range(3):
                time.sleep(2 if attempt==0 else 20*attempt)
                result=subprocess.run(['curl','-L','--fail','--silent','--show-error','--max-time','35','--connect-timeout','12',url,'-o',str(temp),'-w','%{url_effective}'],capture_output=True,text=True)
                if result.returncode==0:
                    if not result.stdout.startswith('https://web.archive.org/web/'):raise ValueError('unexpected redirect outside Wayback')
                    inspect(temp);temp.replace(target);r['effective_url']=result.stdout;break
                if attempt==2:raise RuntimeError(result.stderr.strip())
        r.update(inspect(target))
    except Exception as e:r['error']=str(e)
    return r
if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--limit',type=int); args=parser.parse_args()
    jobs=[]
    for kind in ['calls','puts']:
        rows=json.loads((ROOT/'raw'/f'wayback_{kind}_2026_index.json').read_text())
        jobs.extend((kind,dict(zip(rows[0],r))) for r in rows[1:])
    # Interleave sides to obtain matched dates early; newest dates first.
    jobs.sort(key=lambda x:(x[1]['timestamp'][:8],x[0]),reverse=True)
    if args.limit: jobs=jobs[:args.limit]
    done=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
        for result in pool.map(fetch,jobs):
            done.append(result)
            with (ROOT/'download_manifest.csv').open('w',newline='') as f:
                writer=csv.DictWriter(f,fieldnames=FIELDS);writer.writeheader();writer.writerows(done)
            if len(done)%10==0 or result['error'] or len(done)==len(jobs):
                print(f"{len(done)}/{len(jobs)} processed; {sum(bool(x['error']) for x in done)} failures; latest {result['kind']} {result.get('trade_date','?')} {result.get('publication_status','?')}",flush=True)
    print('Download manifest:',ROOT/'download_manifest.csv',flush=True)

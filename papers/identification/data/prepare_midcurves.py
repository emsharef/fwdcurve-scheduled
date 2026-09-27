"""Extract midcurve quotes with source coordinates; do not guess weekly mappings.

Monthly S0/S2/S3 mappings follow [cme2026sr3options], Rule 460A01.D.3-5.
Weekly rows remain unmapped because month-only labels do not identify the week.
"""
from pathlib import Path
from collections import Counter, defaultdict
from datetime import date
import csv, json, re
import pymupdf
from fetch_bulletins import inspect
from prepare_bulletins import row_at, cell, number, FRACTIONS, write, metadata, third_wed

ROOT = Path(__file__).resolve().parent

def extract(path, info):
    rows, totals = [], []
    product = contract = None
    block = 0
    with pymupdf.open(path) as doc:
        for pi, page in enumerate(doc):
            words = page.get_text('words')
            for anchor in sorted([w for w in words if w[0] < 50 and w[1] > 105], key=lambda w:(w[1],w[0])):
                text, y = anchor[4], anchor[1]
                rr = row_at(words, y); joined = ' '.join(w[4] for w in rr)
                if anchor[0] < 25 and re.fullmatch(r'S[02345]W?', text) and 'OPT' in joined:
                    if product != text: product, contract = text, None
                if anchor[0] < 25 and re.fullmatch(r'(JAN|FEB|MAR|APR|MAY|JUN|JUL|AUG|SEP|OCT|NOV|DEC)\d{2}', text):
                    match = re.search(r'\b(S[02345]W?) OPT\b', joined)
                    if match:
                        new = (match.group(1), text)
                        if new != (product, contract): block += 1
                        product, contract = new
                if text == 'TOTAL' and product and contract:
                    tr = row_at(words, y + 1.75)
                    vol, oi = number(cell(tr,425,459)), number(cell(tr,459,492))
                    cr = [r for r in rows if r['block'] == block]
                    totals.append(dict(source_file=info['file'], source_page=pi+1,
                        product=product, contract_label=contract, block=block,
                        reported_volume=vol, parsed_volume=sum(r['volume'] or 0 for r in cr),
                        reported_open_interest=oi, parsed_open_interest=sum(r['open_interest'] or 0 for r in cr)))
                if not (product and contract and 25 < anchor[0] < 40 and re.fullmatch(r'\d{4,5}', text)): continue
                code = int(text); assert code%100 in FRACTIONS, (path, joined)
                raw = cell(rr,300,337); settle = number(raw)
                rows.append(dict(trade_date=info['trade_date'], publication_status=info['publication_status'],
                    option_type='call' if info['kind']=='midcurve53' else 'put',
                    product=product, contract_label=contract, block=block,
                    strike_code=code, strike_index=code//100+FRACTIONS[code%100],
                    settlement_index=settle, settlement_raw=raw,
                    quote_status='cabinet' if 'CAB' in raw else 'numeric' if settle is not None else 'missing',
                    volume=number(cell(rr,425,459)), open_interest=number(cell(rr,459,492)),
                    reported_delta=number(cell(rr,370,401)), source_file=info['file'],
                    source_page=pi+1, source_y=round(y,3)))
    for t in totals:
        t['volume_matches'] = t['reported_volume']==t['parsed_volume']
        t['open_interest_matches'] = t['reported_open_interest']==t['parsed_open_interest']
    return rows, totals

def main():
    transfers = {}
    for name in ['midcurve_download_manifest.csv','midcurve_call_replay_manifest.csv']:
        path = ROOT/name
        if path.exists():
            for row in csv.DictReader(path.open()):
                if not row['error']: transfers[row['file']] = row
    files = list((ROOT/'raw'/'midcurves').glob('*.pdf'))
    files += list((ROOT/'raw').glob('midcurve5[34]_sample.pdf'))
    sources, selected = [], {}
    for path in files:
        info = inspect(path)
        info.update(kind=path.name.split('_')[0], file=str(path.relative_to(ROOT)))
        transfer = transfers.get(info['file'])
        if transfer is None:
            transfer = next((r for r in transfers.values() if r['sha256']==info['sha256']), None)
        if transfer:
            assert transfer['sha256']==info['sha256']
            info.update(capture_timestamp=transfer['capture_timestamp'], source_url=transfer['effective_url'])
        else:
            info.update(capture_timestamp='',source_url='')
        sources.append(info)
        key = (info['trade_date'],info['kind'])
        # Prefer final, then timestamp-named downloads over the manual samples.
        score = (info['publication_status']=='FINAL', info['capture_timestamp'], 'sample' not in path.name, path.name)
        if key not in selected or score > selected[key][0]: selected[key] = (score,path,info)
    rows, totals = [], []
    for _, path, info in sorted(selected.values(), key=lambda x:(x[2]['trade_date'],x[2]['kind'])):
        a,b = extract(path,info); rows.extend(a); totals.extend(b)
    write('midcurve_source_manifest.csv', sources)
    write('midcurve_quotes_unmapped.csv', rows)
    write('midcurve_contract_total_checks.csv', totals)
    assert all(r['settlement_index'] is None or r['settlement_index']>=0 for r in rows)
    assert all(abs((r['settlement_index'] or 0)*400-round((r['settlement_index'] or 0)*400))<1e-7 for r in rows)
    futures = {(r['trade_date'],r['contract_month']):r for r in
        csv.DictReader((ROOT/'processed'/'futures_all.csv').open())
        if r['product']=='SR3' and r['publication_status']=='FINAL'}
    groups = defaultdict(dict)
    for r in rows:
        if r['publication_status']!='FINAL' or r['quote_status']!='numeric' or r['product'] not in ['S0','S2','S3']: continue
        key = (r['trade_date'],r['product'],r['contract_label'],r['strike_index'])
        assert r['option_type'] not in groups[key], ('duplicate monthly strike',key)
        groups[key][r['option_type']] = r
    panel = []
    for (d,p,c,k), sides in sorted(groups.items()):
        if set(sides)!= {'call','put'}: continue
        meta = metadata(c)
        if meta['option_expiry']<=d: continue
        yy, mm = map(int,meta['underlying_month'].split('-'))
        yy += {'S0':1,'S2':2,'S3':3}[p]
        a = third_wed(yy,mm); b = third_wed(yy+1,3) if mm==12 else third_wed(yy,mm+3)
        underlying = f'{yy}-{mm:02d}'
        future = futures.get((d,underlying))
        if future is None: continue
        call, put = sides['call'], sides['put']; F=float(future['settlement_index'])
        panel.append(dict(trade_date=d,product=p,contract_label=c,option_expiry=meta['option_expiry'],
            underlying_month=underlying,accrual_start=a.isoformat(),accrual_end=b.isoformat(),
            accrual_act360=(b-a).days/360,strike_index=k,futures_index=F,
            call_index=call['settlement_index'],put_index=put['settlement_index'],
            moneyness_rate_bp=round((F-k)*100,8),call_volume=call['volume'],put_volume=put['volume'],
            call_open_interest=call['open_interest'],put_open_interest=put['open_interest'],
            call_file=call['source_file'],call_page=call['source_page'],
            put_file=put['source_file'],put_page=put['source_page'],
            futures_file=future['source_file'],futures_page=future['source_page'],
            mapping_basis='[cme2026sr3options] Rule 460A01.D.3-5; expiry rule-derived'))
    write('midcurve_monthly_panel.csv',panel)
    dates = {r['trade_date'] for r in rows}
    pairs = {d for d in dates if {r['option_type'] for r in rows if r['trade_date']==d and r['publication_status']=='FINAL'}=={'call','put'}}
    coverage = []
    for d in sorted(dates):
        dr = [r for r in rows if r['trade_date']==d]
        coverage.append(dict(trade_date=d,
            call_status=';'.join(sorted({r['publication_status'] for r in dr if r['option_type']=='call'})) or 'MISSING',
            put_status=';'.join(sorted({r['publication_status'] for r in dr if r['option_type']=='put'})) or 'MISSING',
            call_rows=sum(r['option_type']=='call' for r in dr),put_rows=sum(r['option_type']=='put' for r in dr),
            matched_monthly_strikes=sum(r['trade_date']==d for r in panel)))
    write('midcurve_date_coverage.csv',coverage)
    summary = dict(raw_pdfs=len(sources), selected_editions=len(selected),
        printed_dates=len(dates), final_call_put_dates=len(pairs),
        first_trade_date=min(dates), last_trade_date=max(dates), rows=len(rows),
        numeric_rows=sum(r['quote_status']=='numeric' for r in rows),
        weekly_rows=sum(r['product'].endswith('W') for r in rows),
        monthly_matched_pairs=len(panel),monthly_matched_dates=len({r['trade_date'] for r in panel}),
        products=dict(Counter(r['product'] for r in rows)),
        contract_total_checks=len(totals),
        contract_total_mismatches=sum(not r['volume_matches'] or not r['open_interest_matches'] for r in totals))
    (ROOT/'processed'/'midcurve_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()

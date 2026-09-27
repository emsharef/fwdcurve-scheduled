"""Extract standard SR3 option settlements and SR1/SR3 futures from source PDFs.
Uses page coordinates, not text-order guesses. Keeps source page, raw cells and flags.
Excludes FLEX and mid-curve products rather than guessing their contract mappings.
"""
from pathlib import Path
from datetime import date,datetime,timedelta
from collections import defaultdict,Counter
import csv,json,re,hashlib
import pymupdf
from fetch_bulletins import inspect
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'processed'; OUT.mkdir(exist_ok=True)
MON={m:i for i,m in enumerate('JAN FEB MAR APR MAY JUN JUL AUG SEP OCT NOV DEC'.split(),1)}
FRACTIONS={v:i/16 for i,v in enumerate([0,6,12,18,25,31,37,43,50,56,62,68,75,81,87,93])}
def write(name,rows,fields=None):
    if fields is None:fields=list(rows[0]) if rows else []
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
def number(raw):
    m=re.match(r'^([+-]?(?:\d+(?:\.\d*)?|\.\d+))',raw)
    return float(m.group(1)) if m else None
def month(code):return 2000+int(code[3:]),MON[code[:3]]
def third_wed(y,m):
    d=date(y,m,1);return d+timedelta(days=(2-d.weekday())%7+14)
def easter(y):
    a=y%19;b=y//100;c=y%100;d=b//4;e=b%4;f=(b+8)//25;g=(b-f+1)//3;h=(19*a+b-d-g+15)%30;i=c//4;k=c%4;l=(32+2*e+2*i-h-k)%7;m=(a+11*h+22*l)//451
    mm=(h+l-7*m+114)//31;dd=(h+l-7*m+114)%31+1;return date(y,mm,dd)
def metadata(code):
    y,m=month(code);expiry=third_wed(y,m)-timedelta(days=5)
    if expiry==easter(y)-timedelta(days=2):expiry-=timedelta(days=1)
    qm=((m+2)//3)*3;a=third_wed(y,qm);by,bm=(y+1,3) if qm==12 else (y,qm+3);b=third_wed(by,bm)
    return dict(option_expiry=expiry.isoformat(),underlying_month=f'{y}-{qm:02d}',accrual_start=a.isoformat(),accrual_end=b.isoformat(),accrual_act360=(b-a).days/360)
def row_at(words,y):return sorted([w for w in words if abs(w[1]-y)<1.15],key=lambda w:w[0])
def cell(words,lo,hi):return ' '.join(w[4] for w in words if lo<=w[0]<hi)
def extract(path,info):
    opts=[];futs=[];issues=[];totals=[];mode=None;contract=None;flex=False
    with pymupdf.open(path) as doc:
        for pi,page in enumerate(doc):
            words=page.get_text('words')
            # The leftmost table labels and strike cells anchor rows.
            anchors=sorted([w for w in words if w[0]<50 and w[1]>105],key=lambda w:(w[1],w[0]))
            # FLEX section titles can start near the page centre.
            flex_y=min([w[1] for w in words if w[4] in ('FLEX',"EOO'S")]+[1e10])
            for anchor in anchors:
                text=anchor[4];y=anchor[1]
                if y>=flex_y:flex=True
                if flex:continue
                rr=row_at(words,y);joined=' '.join(w[4] for w in rr)
                if text=='TOTAL' and mode=='SR3_OPT' and contract:
                    tr=row_at(words,y+1.75)
                    reported_vol=number(cell(tr,425,459));reported_oi=number(cell(tr,459,492))
                    cr=[r for r in opts if r['contract_label']==contract]
                    parsed_vol=sum(r['volume'] or 0 for r in cr);parsed_oi=sum(r['open_interest'] or 0 for r in cr)
                    totals.append(dict(source_file=info['file'],page=pi+1,contract_label=contract,rows=len(cr),reported_volume=reported_vol,parsed_volume=parsed_vol,reported_open_interest=reported_oi,parsed_open_interest=parsed_oi,volume_matches=reported_vol==parsed_vol,open_interest_matches=reported_oi==parsed_oi))
                if text in ('SR1','SR3') and anchor[0]<25:
                    if 'TOTAL' in joined:continue
                    if re.search(r'\bFUT\b',joined):mode=text+'_FUT';contract=None
                    elif re.search(r'\bOPT\b',joined):mode=text+'_OPT'
                if re.fullmatch(r'(JAN|FEB|MAR|APR|MAY|JUN|JUL|AUG|SEP|OCT|NOV|DEC)\d{2}',text) and anchor[0]<25:
                    if 'SR3 OPT' in joined:
                        mode='SR3_OPT';contract=text
                    elif mode in ('SR1_FUT','SR3_FUT'):
                        raw=cell(rr,280,328);settle=number(raw)
                        if settle is None:issues.append(dict(file=info['file'],page=pi+1,reason='missing futures settlement',raw=joined));continue
                        yy,mm=month(text)
                        futs.append(dict(trade_date=info['trade_date'],publication_status=info['publication_status'],product=mode[:3],contract_month=f'{yy}-{mm:02d}',settlement_index=settle,settlement_raw=raw,volume_raw=cell(rr,425,459),open_interest_raw=cell(rr,459,490),source_file=info['file'],source_page=pi+1,capture_timestamp=info['capture_timestamp']))
                    elif mode=='SR3_OPT':
                        # Date labels on an option continuation page still carry SR3 OPT.
                        issues.append(dict(file=info['file'],page=pi+1,reason='unmapped option month label',raw=joined))
                if not(mode=='SR3_OPT' and contract and re.fullmatch(r'\d{4,5}',text) and 25<anchor[0]<40):continue
                code=int(text);frac=code%100
                if frac not in FRACTIONS:
                    issues.append(dict(file=info['file'],page=pi+1,reason='unknown strike encoding',raw=joined));continue
                strike=code//100+FRACTIONS[frac];raw=cell(rr,300,337);settle=number(raw)
                # CAB is retained as a textual cabinet quote, never guessed as zero or a tick.
                quality='cabinet' if 'CAB' in raw else 'numeric' if settle is not None else 'missing'
                if quality=='missing':issues.append(dict(file=info['file'],page=pi+1,reason='missing option settlement',raw=joined))
                volume_raw=cell(rr,425,459);oi_raw=cell(rr,459,492)
                opts.append(dict(trade_date=info['trade_date'],publication_status=info['publication_status'],option_type='call' if info['kind']=='calls' else 'put',contract_label=contract,**metadata(contract),strike_code=code,strike_index=strike,settlement_index=settle,settlement_rate_bp=None if settle is None else round(settle*100,8),settlement_raw=raw,quote_status=quality,volume=number(volume_raw),volume_raw=volume_raw,open_interest=number(oi_raw),open_interest_raw=oi_raw,reported_delta=number(cell(rr,370,401)),source_file=info['file'],source_page=pi+1,source_y=round(y,3),capture_timestamp=info['capture_timestamp']))
    return opts,futs,issues,totals

def main():
    manifest=[]
    for kind in ['calls','puts']:
        index=json.loads((ROOT/'raw'/f'wayback_{kind}_2026_index.json').read_text());header=index[0]
        for vals in index[1:]:
            entry=dict(zip(header,vals));stamp=entry['timestamp'];path=ROOT/'raw'/'wayback'/f'{kind}_{stamp}.pdf'
            if not path.exists():continue
            info=inspect(path);info.update(kind=kind,capture_timestamp=stamp,file=str(path.relative_to(ROOT)),archive_url=f"https://web.archive.org/web/{stamp}id_/{entry['original']}")
            manifest.append(info)
    # Prefer FINAL then latest archived capture within each printed-date/side group.
    selected={}
    for row in manifest:
        key=(row['trade_date'],row['kind']);score=(row['publication_status']=='FINAL',row['capture_timestamp'])
        if key not in selected or score>(selected[key]['publication_status']=='FINAL',selected[key]['capture_timestamp']):selected[key]=row
    opts=[];futs=[];issues=[];totals=[]
    for row in sorted(selected.values(),key=lambda x:(x['trade_date'],x['kind'])):
        a,b,c,d=extract(ROOT/row['file'],row);opts.extend(a);futs.extend(b);issues.extend(c);totals.extend(d)
    write('source_manifest.csv',manifest)
    write('contract_total_checks.csv',totals);write('options_all.csv',opts);write('futures_all.csv',futs);write('parse_issues.csv',issues,['file','page','reason','raw'])
    # Final-only futures, same printed trade date; no interpolation or forward filling.
    fm={(x['trade_date'],x['contract_month']):x for x in futs if x['product']=='SR3' and x['publication_status']=='FINAL'}
    pairs=defaultdict(dict)
    for x in opts:
        if x['publication_status']=='FINAL' and x['quote_status']=='numeric' and x['option_expiry']>x['trade_date']:
            pairs[(x['trade_date'],x['contract_label'],x['strike_index'])][x['option_type']]=x
    joined=[]
    for (d,contract,k),sides in sorted(pairs.items()):
        if len(sides)!=2:continue
        call=sides['call'];put=sides['put'];future=fm.get((d,call['underlying_month']))
        if future is None:continue
        F=future['settlement_index'];parity=(call['settlement_index']-put['settlement_index']-(F-k))*100
        joined.append(dict(trade_date=d,contract_label=contract,**metadata(contract),strike_index=k,futures_index=F,call_index=call['settlement_index'],put_index=put['settlement_index'],call_rate_bp=call['settlement_rate_bp'],put_rate_bp=put['settlement_rate_bp'],moneyness_rate_bp=round((F-k)*100,8),undiscounted_parity_residual_bp=round(parity,8),call_volume=call['volume'],put_volume=put['volume'],call_open_interest=call['open_interest'],put_open_interest=put['open_interest'],call_file=call['source_file'],call_page=call['source_page'],put_file=put['source_file'],put_page=put['source_page'],futures_file=future['source_file'],futures_page=future['source_page']))
    write('calibration_panel.csv',joined)
    near=[r for r in joined if abs(r['moneyness_rate_bp'])<=50 and r['option_expiry']<='2027-12-31']
    write('calibration_near_money.csv',near)
    coverage=[]
    all_dates=sorted(set(r['trade_date'] for r in manifest))
    for d in all_dates:
        rows=[r for r in joined if r['trade_date']==d];num_exp=len(set(r['option_expiry'] for r in rows))
        cs=selected.get((d,'calls'),{}).get('publication_status','MISSING');ps=selected.get((d,'puts'),{}).get('publication_status','MISSING')
        coverage.append(dict(trade_date=d,call_status=cs,put_status=ps,matched_numeric_strikes=len(rows),matched_expiries=num_exp))
    write('date_coverage.csv',coverage)
    # Checks against preserved manual rows, where a matching source date exists.
    manual=list(csv.DictReader((ROOT/'cme_2026-09-24.csv').open()))
    checked=0
    for row in manual:
        for side in ['call','put']:
            candidates=[o for o in opts if o['trade_date']=='2026-09-24' and o['option_expiry']==row['expiry'] and o['strike_index']==float(row['strike']) and o['option_type']==side]
            if candidates:
                assert len(candidates)==1 and abs(candidates[0]['settlement_index']-float(row[side]))<1e-9,(row,candidates)
                checked+=1
    unique=[(r['trade_date'],r['option_type'],r['contract_label'],r['strike_index']) for r in opts]
    assert len(unique)==len(set(unique)),'duplicate option rows'
    assert all(r['settlement_index'] is None or r['settlement_index']>=0 for r in opts)
    assert all(abs((r['settlement_index'] or 0)*400-round((r['settlement_index'] or 0)*400))<1e-7 for r in opts),'settlement off 0.0025 grid'
    summary=dict(near_money_strikes=len(near),contract_total_checks=len(totals),contract_total_mismatches=sum(not r['volume_matches'] or not r['open_interest_matches'] for r in totals),downloaded_pdfs=len(manifest),selected_pdfs=len(selected),first_trade_date=min(all_dates),last_trade_date=max(all_dates),trading_dates=len(all_dates),final_call_put_dates=sum(x['call_status']==x['put_status']=='FINAL' for x in coverage),calibration_dates=sum(x['matched_numeric_strikes']>0 for x in coverage),option_rows=len(opts),numeric_option_rows=sum(r['quote_status']=='numeric' for r in opts),cabinet_rows=sum(r['quote_status']=='cabinet' for r in opts),futures_rows=len(futs),matched_call_put_strikes=len(joined),manual_values_checked=checked,parse_issues=len(issues),publication_status_counts=dict(Counter(x['publication_status'] for x in manifest)),archive_bytes=sum(x['bytes'] for x in manifest))
    rates_path=ROOT/'raw'/'nyfed_sofr_2026.json'
    if rates_path.exists():
        rates=json.loads(rates_path.read_text())['refRates']
        write('sofr_fixings.csv',sorted(rates,key=lambda r:r['effectiveDate']))
        summary['sofr_fixings']=len(rates)
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()

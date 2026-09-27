"""Offline empirical analysis for paper_pub3; no lab or network operations.

Fixed protocol: FINAL paired settlements, 7--365 calendar days to expiry,
|moneyness| <=25 rate bp, >=3 strikes straddling the future in each chain.
Select the out-of-money side at each strike. Pricing is a discounted European
normal diagnostic with futures mean fixed; it is NOT the paper's exact cash
model or an American option pricer. All variances below are in rate bp squared.
"""
from pathlib import Path
from datetime import date
from collections import defaultdict
import csv, json, math, os, hashlib
os.environ.setdefault('MPLCONFIGDIR','/tmp/paper_pub3_matplotlib')
import numpy as np
from scipy.special import ndtr
from scipy.optimize import linprog
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

ROOT=Path(__file__).resolve().parents[1]; OUT=ROOT/'analysis'; FIG=ROOT/'figures'
DATA=ROOT/'data'/'processed'
BLUE='#24567A'; ORANGE='#C27536'; GREEN='#378477'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,
 'axes.spines.right':False,'savefig.bbox':'tight','pdf.fonttype':42})

def load(name): return list(csv.DictReader((DATA/name).open()))
def write(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]) if rows else []);w.writeheader();w.writerows(rows)
def dump(name,obj): (OUT/name).write_text(json.dumps(obj,indent=2,allow_nan=False)+'\n')
def days(a,b): return (date.fromisoformat(b)-date.fromisoformat(a)).days
def pdf(x): return np.exp(-np.asarray(x)**2/2)/np.sqrt(2*np.pi)
def price(q,x,D):
    # OTM price: the sign of the selected option has already been absorbed.
    s=np.sqrt(np.maximum(q,0)); d=np.divide(-np.abs(x),s,out=np.full(np.broadcast(s,x).shape,-np.inf),where=s>0)
    return D*(-np.abs(x)*ndtr(d)+s*pdf(d))
def invert(c,x,D):
    c=np.maximum(np.asarray(c,dtype=float),0); x=np.asarray(x);D=np.asarray(D)
    lo=np.zeros_like(c); hi=np.full_like(c,128.**2)
    while np.any(price(hi,x,D)<c): hi*=4
    for _ in range(55):
        mid=(lo+hi)/2; below=price(mid,x,D)<c
        lo=np.where(below,mid,lo);hi=np.where(below,hi,mid)
    return np.where(c==0,0,(lo+hi)/2)
def select(rows):
    groups=defaultdict(list)
    for r in rows:
        d=days(r['trade_date'],r['option_expiry']); x=float(r['moneyness_rate_bp'])
        if not(7<=d<=365 and abs(x)<=25 and r['option_expiry']<r['accrual_start']): continue
        z=dict(r); z['x']=x;z['D']=float(r['discount_to_expiry']);z['S']=d/360
        z['side']='put' if x>=0 else 'call';z['c']=100*float(r[z['side']+'_index'])
        z['volume']=float(r.get(z['side']+'_volume') or 0)
        z['oi']=float(r.get(z['side']+'_open_interest') or 0)
        key=(r['trade_date'],r.get('product','SR3'),r['contract_label'])
        groups[key].append(z)
    result=[]
    for key,rr in sorted(groups.items()):
        if len(rr)<3 or not min(r['x'] for r in rr)<0<max(r['x'] for r in rr): continue
        rr.sort(key=lambda r:float(r['strike_index']))
        q=invert(np.array([r['c'] for r in rr]),np.array([r['x'] for r in rr]),np.array([r['D'] for r in rr]))
        assert np.max(np.abs(price(q,np.array([r['x'] for r in rr]),np.array([r['D'] for r in rr]))-np.array([r['c'] for r in rr])))<1e-8
        for r,v in zip(rr,q):r['Q']=float(v)
        near=min(rr,key=lambda r:(abs(r['x']),float(r['strike_index'])))
        result.append(dict(key=key,rows=rr,near=near,date=key[0],expiry=near['option_expiry'],S=near['S']))
    return result

MEETINGS=[r['meeting_date'] for r in load('fomc_meetings_asof_2026-03-30.csv')]
def design(gs,kind):
    d=gs[0]['date']; S=np.array([g['S'] for g in gs]); end=max(g['expiry'] for g in gs)
    meetings=[m for m in MEETINGS if d<m<=end]; T=np.array([days(d,m)/360 for m in meetings])
    event=(T[None,:]<=S[:,None]).astype(float)
    if kind=='constant':edges=np.array([0,max(S)])
    elif kind=='90day': edges=np.r_[np.arange(0,max(S)*360,90)/360,max(S)]
    elif kind=='gap':edges=np.r_[0,np.unique(S)]
    bg=np.maximum(0,np.minimum(S[:,None],edges[1:])-edges[:-1])
    return np.c_[event,bg],meetings,edges
def intervals(gs,eps,near_only=False):
    lower=[];upper=[]
    for g in gs:
        rr=[g['near']] if near_only else g['rows']
        c=np.array([r['c'] for r in rr]);x=np.array([r['x'] for r in rr]);D=np.array([r['D'] for r in rr])
        lower.append(max(invert(c-eps,x,D)));upper.append(min(invert(c+eps,x,D)))
    return np.array(lower),np.array(upper)
def solve(A,lo,hi,c=None):
    if np.any(lo>hi+1e-8):return None
    res=linprog(np.zeros(A.shape[1]) if c is None else c,A_ub=np.r_[A,-A],b_ub=np.r_[hi,-lo],bounds=(0,None),method='highs')
    if res.status==2:return None
    if not res.success: raise RuntimeError(res.message)
    assert np.max(A@res.x-hi)<2e-5 and np.max(lo-A@res.x)<2e-5
    return res
def minimum_tolerance(gs,A,near_only=False):
    low=0.;high=max(r['c'] for g in gs for r in g['rows'])
    assert solve(A,*intervals(gs,high,near_only)) is not None
    while high-low>0.0001:
        mid=(low+high)/2
        if solve(A,*intervals(gs,mid,near_only)) is None:low=mid
        else:high=mid
    lo,hi=intervals(gs,high,near_only);res=solve(A,lo,hi)
    assert res is not None
    for q,g in zip(A@res.x,gs):
        for r in ([g['near']] if near_only else g['rows']):
            assert abs(float(price(q,r['x'],r['D']))-r['c']) <= high+1e-5
    return high
def extremes(A,lo,hi,target):
    l=solve(A,lo,hi,target);h=solve(A,lo,hi,-target)
    if l is None:return None
    assert h is not None
    return max(0,float(l.fun)),max(0,float(-h.fun))

def main():
    stdrows=load('calibration_panel_with_discount.csv'); midrows=load('midcurve_monthly_panel_with_discount.csv')
    groups=select(stdrows);midgroups=select(midrows)
    bydate=defaultdict(list)
    for g in groups:bydate[g['date']].append(g)
    dates=sorted(bydate);calendar=[];fits=[];ranges=[];held=[];chains=[]
    for g in groups:
        rr=g['rows']; q=g['near']['Q']; errors=[float(price(q,r['x'],r['D'])-r['c']) for r in rr if r is not g['near']]
        chains.append(dict(trade_date=g['date'],expiry=g['expiry'],contract=g['key'][2],strikes=len(rr),
            nearest_Q=q,nearest_sd=math.sqrt(q),max_held_strike_error=max(map(abs,errors)),
            mean_abs_held_strike_error=float(np.mean(np.abs(errors))),
            smile_min_tolerance=minimum_tolerance([g],np.ones((1,1))),
            discount_effect_near_bp=(1/g['near']['D']-1)*g['near']['c']))
    for n,d in enumerate(dates):
        gs=sorted(bydate[d],key=lambda g:g['expiry']); cache={}
        for kind in ['constant','90day','gap']:
            A,meetings,edges=design(gs,kind); lo,hi=intervals(gs,.5)
            rank=int(np.linalg.matrix_rank(A));nmeet=len(meetings)
            individually=[]
            for j in range(nmeet):
                c=np.eye(A.shape[1])[j]
                individually.append(np.linalg.matrix_rank(np.vstack([A,c]))==rank)
            calendar.append(dict(trade_date=d,background=kind,expiries=len(gs),meetings=nmeet,
                background_parameters=len(edges)-1,rank=rank,parameters=A.shape[1],
                identified_meetings=sum(individually),full_rank=rank==A.shape[1]))
            eps=minimum_tolerance(gs,A);epsnear=minimum_tolerance(gs,A,True)
            fits.append(dict(trade_date=d,background=kind,min_tolerance_bp=eps,
                nearest_strike_min_tolerance_bp=epsnear,
                feasible_025=eps<=.2501,feasible_050=eps<=.5001,feasible_100=eps<=1.0001))
            cache[kind]=(A,meetings,edges,eps)
            for tol in [.5,1.]:
                lo,hi=intervals(gs,tol)
                if solve(A,lo,hi) is None:continue
                targets=[(m,np.eye(A.shape[1])[j]) for j,m in enumerate(meetings)]
                targets.append(('all_meetings',np.r_[np.ones(nmeet),np.zeros(len(edges)-1)]))
                for label,c in targets:
                    lower,upper=extremes(A,lo,hi,c)
                    ranges.append(dict(trade_date=d,background=kind,tolerance_bp=tol,target=label,
                        lower_variance_bp2=lower,upper_variance_bp2=upper,width_bp2=upper-lower))
        # Hold out the entire second expiry, fixed before seeing its prices.
        A,meetings,edges,eps=cache['constant'];j=1
        train=[g for k,g in enumerate(gs) if k!=j];At=np.delete(A,j,axis=0)
        for tol in [.5,1.]:
            lo,hi=intervals(train,tol)
            fit=solve(At,lo,hi)
            record=dict(trade_date=d,tolerance_bp=tol,held_expiry=gs[j]['expiry'],
                training_feasible=fit is not None,observed_bp=gs[j]['near']['c'],lower_bp='',upper_bp='',outside_bp='')
            if fit is not None:
                lower,upper=extremes(At,lo,hi,A[j]);r=gs[j]['near']
                a=float(price(lower,r['x'],r['D']));b=float(price(upper,r['x'],r['D']))
                # Compare the held quote interval, not just its centre, to the prediction.
                gap=max(a-(r['c']+tol), (r['c']-tol)-b,0)
                record.update(lower_bp=a,upper_bp=b,outside_bp=gap)
            held.append(record)
        if (n+1)%10==0: print(f'{n+1}/{len(dates)} dates analyzed',flush=True)
    write('calendar.csv',calendar);write('fit_tolerances.csv',fits);write('risk_ranges.csv',ranges)
    write('held_expiry.csv',held);write('chain_diagnostics.csv',chains)
    # Sensitivity to a simple activity screen, without calling it executable liquidity.
    activity=[]
    for d in dates:
        gs=[]
        for g in bydate[d]:
            rr=[r for r in g['rows'] if r['volume']>0 and r['oi']>=100]
            if len(rr)>=3 and min(r['x'] for r in rr)<0<max(r['x'] for r in rr):
                z=dict(g);z['rows']=rr;z['near']=min(rr,key=lambda r:(abs(r['x']),float(r['strike_index'])));gs.append(z)
        if len(gs)<2:continue
        gs.sort(key=lambda g:g['expiry']);A,_,_=design(gs,'constant')
        activity.append(dict(trade_date=d,expiries=len(gs),strikes=sum(len(g['rows']) for g in gs),
            min_tolerance_bp=minimum_tolerance(gs,A)))
    write('activity_screen.csv',activity)
    # Transport the standard option's nearest-strike variance to a same-expiry midcurve.
    lookup={(g['date'],g['expiry']):g for g in groups};transport=[]
    for g in midgroups:
        base=lookup.get((g['date'],g['expiry']))
        if base is None:continue
        r=g['near'];q=base['near']['Q'];pred=float(price(q,r['x'],r['D']))
        transport.append(dict(trade_date=g['date'],expiry=g['expiry'],product=g['key'][1],
            standard_sd=math.sqrt(q),midcurve_sd=math.sqrt(r['Q']),
            observed_bp=r['c'],predicted_bp=pred,residual_bp=pred-r['c'],
            standard_underlying=base['near']['underlying_month'],midcurve_underlying=r['underlying_month']))
    write('midcurve_transport.csv',transport)
    # Same-window futures/OIS-forward rate gap; no claim of independent executable quotes.
    forward=[];seen=set()
    for r in stdrows:
        if not 7<=days(r['trade_date'],r['option_expiry'])<=365:continue
        key=(r['trade_date'],r['underlying_month'])
        if key in seen:continue
        seen.add(key)
        delta=float(r['accrual_act360']);ratio=float(r['discount_to_accrual_start'])/float(r['discount_to_accrual_end'])
        fut=(100-float(r['futures_index']))/100;ois=(ratio-1)/delta
        forward.append(dict(trade_date=key[0],underlying_month=key[1],accrual_start=r['accrual_start'],accrual_end=r['accrual_end'],
            start_years=days(key[0],r['accrual_start'])/360,futures_rate_bp=fut*1e4,
            curve_forward_rate_bp=ois*1e4,gap_bp=(fut-ois)*1e4,
            implied_p=math.log1p(delta*fut)-math.log(ratio)))
    write('futures_curve_gaps.csv',forward)
    # Local background-neutral option example, fixed date and first two expiries.
    chosen='2026-09-14' if '2026-09-14' in bydate else dates[-1]
    gs=sorted(bydate[chosen],key=lambda g:g['expiry'])[:2]
    hedge={}
    if len(gs)==2:
        r1,r2=[g['near'] for g in gs];sd1,sd2=np.sqrt([r1['Q'],r2['Q']])
        h1=r1['D']*pdf(r1['x']/sd1)/sd1;h2=r2['D']*pdf(r2['x']/sd2)/sd2 # straddle derivative wrt Q
        w=-h2*r2['S']/(h1*r1['S']); delta1=r1['D']*(2*ndtr(r1['x']/sd1)-1);delta2=r2['D']*(2*ndtr(r2['x']/sd2)-1)
        assert abs(w*h1*r1['S']+h2*r2['S'])<1e-12
        # Independent finite-difference check of the straddle's variance sensitivity.
        dq=1e-3
        for r,h in [(r1,h1),(r2,h2)]:
            finite=(2*price(r['Q']+dq,r['x'],r['D'])-2*price(r['Q']-dq,r['x'],r['D']))/(2*dq)
            assert abs(finite-h)<1e-8
        hedge=dict(trade_date=chosen,first_expiry=gs[0]['expiry'],second_expiry=gs[1]['expiry'],
            first_weight=float(w),second_weight=1.,first_strike=r1['strike_index'],second_strike=r2['strike_index'],
            first_underlying=r1['underlying_month'],second_underlying=r2['underlying_month'],
            first_futures_hedge=float(-w*delta1),second_futures_hedge=float(-delta2),
            event_variance_sensitivity=float(h2),
            intervening_meetings=[m for m in MEETINGS if gs[0]['expiry']<m<=gs[1]['expiry']])
    dump('local_hedge_example.json',hedge)
    def quantile(values):
        return dict(zip(['min','q25','median','q75','max'],map(float,np.quantile(values,[0,.25,.5,.75,1]))))
    summary=dict(dates=len(dates),chains=len(groups),selected_strikes=sum(len(g['rows']) for g in groups),
        first_date=dates[0],last_date=dates[-1],chains_per_date=quantile([len(bydate[d]) for d in dates]),
        held_strike_error=quantile([r['max_held_strike_error'] for r in chains]),
        smile_min_tolerance=quantile([r['smile_min_tolerance'] for r in chains]),
        discount_effect=quantile([r['discount_effect_near_bp'] for r in chains]),
        backgrounds={},held_expiry={},activity_screen_dates=len(activity),
        activity_screen_tolerance=quantile([r['min_tolerance_bp'] for r in activity]),
        midcurve_observations=len(transport),midcurve_dates=len({r['trade_date'] for r in transport}),
        midcurve_abs_error=quantile([abs(r['residual_bp']) for r in transport]),
        futures_curve_observations=len(forward),futures_curve_gap=quantile([r['gap_bp'] for r in forward]),
        negative_futures_curve_gaps=sum(r['gap_bp']<0 for r in forward))
    for kind in ['constant','90day','gap']:
        rr=[r for r in fits if r['background']==kind];cc=[r for r in calendar if r['background']==kind]
        summary['backgrounds'][kind]=dict(min_tolerance=quantile([r['min_tolerance_bp'] for r in rr]),
            nearest_min_tolerance=quantile([r['nearest_strike_min_tolerance_bp'] for r in rr]),
            feasible_025=sum(r['feasible_025'] for r in rr),feasible_050=sum(r['feasible_050'] for r in rr),feasible_100=sum(r['feasible_100'] for r in rr),
            full_rank_dates=sum(r['full_rank'] for r in cc),identified_meetings=quantile([r['identified_meetings'] for r in cc]))
    for tol in [.5,1.]:
        rr=[r for r in held if r['tolerance_bp']==tol];ok=[r for r in rr if r['training_feasible']]
        summary['held_expiry'][str(tol)]=dict(training_feasible=len(ok),outside=sum(r['outside_bp']>1e-4 for r in ok),
            max_outside_bp=max([r['outside_bp'] for r in ok],default=0),
            median_prediction_width_bp=float(np.median([r['upper_bp']-r['lower_bp'] for r in ok])) if ok else None)
    summary['midcurve_by_product']={}
    for p in ['S0','S2','S3']:
        rr=[r for r in transport if r['product']==p]
        summary['midcurve_by_product'][p]=dict(chains=len(rr),
            median_sd_ratio=float(np.median([r['midcurve_sd']/r['standard_sd'] for r in rr])),
            median_signed_price_error_bp=float(np.median([r['residual_bp'] for r in rr])))
    # Reproduce exact input versions and the fixed analysis choices.
    manifest={name:hashlib.sha256((DATA/name).read_bytes()).hexdigest() for name in
        ['calibration_panel_with_discount.csv','midcurve_monthly_panel_with_discount.csv','fomc_meetings_asof_2026-03-30.csv']}
    dump('input_hashes.json',manifest);dump('summary.json',summary)
    figures(dates,calendar,fits,ranges,chains,transport,forward,held)
    tables(summary)
    print(json.dumps(summary,indent=2),flush=True)

def figures(dates,calendar,fits,ranges,chains,transport,forward,held):
    ds=[date.fromisoformat(d) for d in dates]
    fig,ax=plt.subplots(2,1,figsize=(8.5,5.2),sharex=True)
    cc=[r for r in calendar if r['background']=='constant']
    ax[0].plot(ds,[r['meetings'] for r in cc],label='Meetings before last expiry',color='gray')
    ax[0].plot(ds,[r['expiries'] for r in cc],label='Observed expiries',color=BLUE)
    ax[0].plot(ds,[r['identified_meetings'] for r in cc],label='Individually identified; constant background',color=ORANGE)
    ax[0].set_ylabel('Count');ax[0].legend(frameon=False,fontsize=8,ncol=1)
    for kind,color,label in [('constant',BLUE,'Constant'),('90day',ORANGE,'90-day cells'),('gap',GREEN,'Each expiry gap')]:
        rr=[r for r in fits if r['background']==kind]
        ax[1].plot(ds,[r['min_tolerance_bp'] for r in rr],'.-',ms=3,lw=.8,color=color,label=label)
    ax[1].axhline(.5,color='gray',ls=':',lw=1);ax[1].set_ylabel('Minimum price tolerance (bp)')
    ax[1].legend(frameon=False,ncol=3,fontsize=8);ax[1].xaxis.set_major_formatter(mdates.DateFormatter('%b'))
    fig.tight_layout();fig.savefig(FIG/'empirical_calendar_fit.pdf');plt.close(fig)
    # Risk ranges: earliest date where all specifications fit at 1 bp; no narrowness selection.
    eligible=[]
    for d in dates:
        if all(any(r['trade_date']==d and r['background']==k and r['tolerance_bp']==1. for r in ranges) for k in ['constant','90day','gap']):eligible.append(d)
    if eligible:
        d=eligible[0];fig,axes=plt.subplots(1,2,figsize=(8.5,3.5),gridspec_kw={'width_ratios':[4,1]})
        targets=sorted({r['target'] for r in ranges if r['trade_date']==d and r['target']!='all_meetings'})+['all_meetings']
        for shift,kind,col in [(-.2,'constant',BLUE),(0,'90day',ORANGE),(.2,'gap',GREEN)]:
            rr={r['target']:r for r in ranges if r['trade_date']==d and r['background']==kind and r['tolerance_bp']==1.}
            for ax,tt in zip(axes,[targets[:-1],targets[-1:]]):
                low=np.array([rr[t]['lower_variance_bp2'] for t in tt]);up=np.array([rr[t]['upper_variance_bp2'] for t in tt]);x=np.arange(len(tt))+shift
                ax.errorbar(x,(low+up)/2,yerr=(up-low)/2,fmt='o',ms=3,capsize=3,color=col,label={'constant':'Constant','90day':'90-day cells','gap':'Expiry gaps'}[kind])
        axes[0].set_xticks(range(len(targets)-1),[date.fromisoformat(t).strftime('%d %b\n%Y') for t in targets[:-1]],rotation=25,fontsize=8)
        axes[1].set_xticks([0],['All meetings']);axes[1].set_xlim(-.5,.5)
        axes[0].set_ylabel('Compatible variance (bp²)');fig.suptitle(f'{d}; ±1 bp premium tolerance')
        axes[0].legend(frameon=False,ncol=3,fontsize=8);fig.tight_layout();fig.savefig(FIG/'empirical_ranges.pdf');plt.close(fig)
        dump('range_figure_date.json',{'date':d})
    fig,ax=plt.subplots(1,2,figsize=(8.5,3.5))
    ax[0].hist([r['max_held_strike_error'] for r in chains],bins=24,color=BLUE)
    ax[0].axvline(.5,color=ORANGE,ls='--');ax[0].set(xlabel='Largest omitted-strike error per chain (bp)',ylabel='Option chains')
    for p,color in [('S0',BLUE),('S2',ORANGE),('S3',GREEN)]:
        rr=[r for r in transport if r['product']==p]
        ax[1].scatter([r['standard_sd'] for r in rr],[r['midcurve_sd'] for r in rr],s=15,alpha=.65,label=p,color=color)
    lim=max([r['standard_sd'] for r in transport]+[r['midcurve_sd'] for r in transport]);ax[1].plot([0,lim],[0,lim],'k:',lw=1)
    ax[1].set(xlabel='Standard-option normal SD (bp)',ylabel='Same-expiry midcurve normal SD (bp)');ax[1].legend(frameon=False,fontsize=8)
    fig.tight_layout();fig.savefig(FIG/'empirical_price_checks.pdf');plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.5,3.0))
    sc=ax.scatter([r['start_years'] for r in forward],[r['gap_bp'] for r in forward],c=[days(dates[0],r['trade_date']) for r in forward],cmap='viridis',s=13,alpha=.7)
    ax.axhline(0,color='gray',lw=1);ax.set(xlabel='Time to underlying accrual start (ACT/360 years)',ylabel='Futures rate − curve forward (bp)')
    fig.colorbar(sc,ax=ax,label='Days since first sample date');fig.tight_layout();fig.savefig(FIG/'empirical_convexity.pdf');plt.close(fig)

def tables(s):
    lines=[r'\begin{tabular}{lrrrr}\toprule Background variance & Median min. error & $\pm0.25$ & $\pm0.5$ & $\pm1$ \\\midrule']
    for k,label in [('constant','Constant'),('90day','90-day cells'),('gap','Each expiry gap')]:
        r=s['backgrounds'][k];lines.append(f"{label} & {r['min_tolerance']['median']:.3f} & {r['feasible_025']} & {r['feasible_050']} & {r['feasible_100']} \\\\")
    lines.append(r'\bottomrule\end{tabular}');(OUT/'fit_table.tex').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':main()

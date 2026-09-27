"""Offline referee extensions: normal-mixture ATM interpolation, calendar LPs,
humped loadings and American normal exercise sensitivity. No lab operations.
All prices in rate bp, variances in bp^2, times ACT/360.
"""
from run_analysis import *
from scipy.optimize import least_squares, nnls

# Equal-weight normal mixture with mean fixed at the observed futures quote.
# In standardized units the component means are +/-d and SDs exp(l1),exp(l2).
def mixture(par,x,D,scale):
    d,l1,l2=par
    sign=np.where(np.asarray(x)<0,1.,-1.)
    # x=F-K in index bp. Selected calls have x<0; puts x>=0.
    def leg(mu,s):
        y=sign*(np.asarray(x)+mu)
        return y*ndtr(y/s)+s*pdf(y/s)
    return D*.5*(leg(d*scale,np.exp(l1)*scale)+leg(-d*scale,np.exp(l2)*scale))

def mixfit(g,omit=None):
    rr=g['rows']; use=[i for i in range(len(rr)) if i!=omit]
    x=np.array([r['x'] for r in rr]);c=np.array([r['c'] for r in rr]);D=rr[0]['D']
    training_near=min((rr[i] for i in use),key=lambda r:(abs(r['x']),float(r['strike_index'])))
    scale=np.sqrt(training_near['Q']);scale=max(scale,1.)
    starts=[[0,0,0],[.5,-.5,.2],[-.5,-.5,.2]]
    fits=[least_squares(lambda p:(mixture(p,x,D,scale)-c)[use],s,
              bounds=([-2.,-3.,-3.],[2.,1.5,1.5]),max_nfev=200,ftol=1e-9,xtol=1e-9,gtol=1e-9) for s in starts]
    f=min(fits,key=lambda f:np.sum(f.fun**2)); fitted=mixture(f.x,x,D,scale)
    atm=float(mixture(f.x,np.array([0.]),D,scale)[0])
    # ATM equivalent-normal variance: deliberately not the mixture second moment.
    vatm=(atm/D*np.sqrt(2*np.pi))**2
    moment=scale**2*(f.x[0]**2+.5*np.exp(2*f.x[1])+.5*np.exp(2*f.x[2]))
    return dict(par=f.x.tolist(),scale=scale,atm=atm,vatm=vatm,moment=moment,
       max_error=float(np.max(abs(fitted-c))),rmse=float(np.sqrt(np.mean((fitted-c)**2))),
       held_error=None if omit is None else float(abs(fitted[omit]-c[omit])),success=bool(f.success))

def vatminterval(gs,fits,eps):
    c=np.array([fits[g['key']]['atm'] for g in gs]);D=np.array([g['near']['D'] for g in gs])
    return 2*np.pi*(np.maximum(c-eps,0)/D)**2,2*np.pi*((c+eps)/D)**2

def atmtolerance(gs,fits,A):
    low=0.;high=20.
    while solve(A,*vatminterval(gs,fits,high)) is None: high*=2
    while high-low>1e-4:
        mid=(low+high)/2
        if solve(A,*vatminterval(gs,fits,mid)) is None: low=mid
        else:high=mid
    return high

# Smooth shape 1+c*k*tau*exp(-k*tau); finite-horizon positive bounded loading.
# Analytical maturity integral, 20-point Gaussian integration over shock time.
GX,GW=np.polynomial.legendre.leggauss(20)
def shape_design(gs,c,k,kind='constant'):
    A,meetings,edges=design(gs,kind);n=len(meetings)
    for l,g in enumerate(gs):
        a=days(g['date'],g['near']['accrual_start'])/360
        b=days(g['date'],g['near']['accrual_end'])/360
        for p,(left,right) in enumerate(zip(edges[:-1],edges[1:])):
            right=min(right,g['S'])
            if right<=left: A[l,n+p]=0;continue
            s=(right+left)/2+(right-left)/2*GX
            primitive=lambda x:-(x+1/k)*np.exp(-k*x)
            beta=1+c*(primitive(b-s)-primitive(a-s))/(b-a)
            A[l,n+p]=(right-left)/2*np.dot(GW,beta**2)
    return A,meetings,edges

def american_normal(q,x,D,n):
    """Recombining trinomial, cash exercise on arithmetic futures martingale.
    Exact one-step variance q/n. Positive probs 1/6,2/3,1/6. Exercise each step.
    Return American and European on SAME lattice to isolate exercise premium.
    """
    h=np.sqrt(3*q/n); j=np.arange(-n,n+1)
    sign=1 if x<0 else -1
    payoff=np.maximum(sign*(x+j*h),0);am=payoff.copy();eu=payoff.copy();disc=D**(1/n)
    for step in range(n-1,-1,-1):
        am=disc*(am[:-2]/6+am[1:-1]*2/3+am[2:]/6)
        eu=disc*(eu[:-2]/6+eu[1:-1]*2/3+eu[2:]/6)
        ex=np.maximum(sign*(x+np.arange(-step,step+1)*h),0)
        am=np.maximum(am,ex)
    return float(am[0]),float(eu[0])

def main():
    import sys
    refit='--refit' in sys.argv
    input_hashes={name:hashlib.sha256((DATA/name).read_bytes()).hexdigest() for name in ['calibration_panel_with_discount.csv','midcurve_monthly_panel_with_discount.csv','fomc_meetings_asof_2026-03-30.csv']}
    expected=json.loads((OUT/'input_hashes.json').read_text())
    assert input_hashes==expected, 'Inputs changed: rerun the baseline before extensions.'
    std=select(load('calibration_panel_with_discount.csv'));mid=select(load('midcurve_monthly_panel_with_discount.csv'))
    allg=std+mid; fits={};out=[]
    cache=OUT/'mixture_chains.json'
    if cache.exists() and not refit:
        saved=json.loads(cache.read_text());fits={tuple(r['key']):r for r in saved}
    else:
        for i,g in enumerate(allg):
            f=mixfit(g); hold=g['rows'].index(g['near'])
            # Leave the closest strike out only with >=5 strikes and both sides left.
            rr=[r for j,r in enumerate(g['rows']) if j!=hold]
            eligible=len(g['rows'])>=5 and min(r['x'] for r in rr)<0<max(r['x'] for r in rr)
            f['held_near_error']=mixfit(g,hold)['held_error'] if eligible else None
            f.update(key=list(g['key']),date=g['date'],expiry=g['expiry'],product=g['key'][1],strikes=len(g['rows']))
            fits[g['key']]=f
            if i%100==0:print('mixtures',i,len(allg),flush=True)
        dump('mixture_chains.json',list(fits.values()))
    bydate=defaultdict(list)
    for g in std:bydate[g['date']].append(g)
    calendars=[];ranges=[]
    for d,gs in sorted(bydate.items()):
        gs.sort(key=lambda g:g['expiry'])
        for kind in ['constant','90day','gap']:
            A,meetings,edges=design(gs,kind);eps=atmtolerance(gs,fits,A)
            calendars.append(dict(date=d,background=kind,min_atm_tolerance=eps))
            if d=='2026-06-18':
                for tol in [.25,.5,1.]:
                    lo,hi=vatminterval(gs,fits,tol)
                    if solve(A,lo,hi) is None: continue
                    for j,m in enumerate(meetings):
                        target=np.eye(A.shape[1])[j];l,h=extremes(A,lo,hi,target)
                        ranges.append(dict(date=d,background=kind,tolerance=tol,meeting=m,lower=l,upper=h))
    write('mixture_calendar.csv',calendars);write('mixture_ranges.csv',ranges)
    # Hump: use standard plus S0/S2 to select a common shape, hold every S3 out.
    overlap=sorted(set(g['date'] for g in mid)&set(bydate))
    panels={d:sorted(bydate[d]+[g for g in mid if g['date']==d],key=lambda g:(g['expiry'],g['key'])) for d in overlap}
    grid=[]
    for k in [.25,.5,.75,1.,1.5,2.,3.]:
        for c in [0.,.5,1.,2.,4.,8.]:
            total=0.;cnt=0;hold=[];training=[]
            for d,gs in panels.items():
                train=[g for g in gs if g['key'][1]!='S3'];test=[g for g in gs if g['key'][1]=='S3']
                A,mm,ee=shape_design(gs,c,k)
                tid=[gs.index(g) for g in train];hid=[gs.index(g) for g in test]
                y=np.array([fits[g['key']]['vatm'] for g in gs]);w=1/(2*np.sqrt(y))
                # Scale columns before NNLS; zeros removed. Minimum-norm is not an identified estimate.
                X=A[tid]*w[tid,None]; yy=y[tid]*w[tid];sc=np.linalg.norm(X,axis=0);act=sc>1e-12
                theta=np.zeros(A.shape[1]);coef,_=nnls(X[:,act]/sc[act],yy,maxiter=1000);theta[act]=coef/sc[act]
                sd_error=np.sqrt(np.maximum(A@theta,0))-np.sqrt(y)
                total+=float(np.sum(sd_error[tid]**2));cnt+=len(tid)
                training.extend(abs(sd_error[tid]).tolist());hold.extend(abs(sd_error[hid]).tolist())
            grid.append(dict(c=c,k=k,train_sd_rmse=np.sqrt(total/cnt),train_n=cnt,
                held_n=len(hold),held_sd_mae=float(np.mean(hold)),held_sd_median=float(np.median(hold))))
    best=min(grid,key=lambda r:r['train_sd_rmse']);write('shape_grid.csv',grid)
    # Independent checks: held-product predictions do not depend on a null-space allocation;
    # quadrature is stable to doubling nodes; mixture nests the normal baseline exactly.
    global GX,GW
    projection=0.;quadrature=0.
    for gs in panels.values():
        A,_,_=shape_design(gs,best['c'],best['k']);train=np.array([g['key'][1]!='S3' for g in gs])
        if (~train).any():projection=max(projection,float(np.max(abs(A[~train]-A[~train]@np.linalg.pinv(A[train])@A[train]))))
        GX,GW=np.polynomial.legendre.leggauss(40);B,_,_=shape_design(gs,best['c'],best['k'])
        quadrature=max(quadrature,float(np.max(abs(A-B))));GX,GW=np.polynomial.legendre.leggauss(20)
    xx=np.linspace(-25,25,101);nested=float(np.max(abs(mixture([0,0,0],xx,.98,30)-price(900,xx,.98))))
    assert projection<1e-10 and quadrature<1e-10 and nested<1e-12
    dump('extensions_checks.json',dict(held_S3_rowspace_max_error=projection,loading_quadrature_20_vs_40_max_error=quadrature,nested_normal_max_error=nested))

    shapecal=[];shaperanges=[];profile=[]
    for d,gs in panels.items():
        for name,c,k in [('parallel',0.,1.),('hump',best['c'],best['k'])]:
            for kind in ['constant','90day','gap']:
                A,mm,ee=shape_design(gs,c,k,kind);tol=atmtolerance(gs,fits,A)
                shapecal.append(dict(date=d,shape=name,background=kind,min_atm_tolerance=tol,
                     rank=int(np.linalg.matrix_rank(A)),parameters=A.shape[1],rows=len(gs)))
                # All date ranges at 1 premium bp on the fitted ATM proxy.
                lo,hi=vatminterval(gs,fits,1.)
                if solve(A,lo,hi) is not None:
                    for j,m in enumerate(mm):
                        l,h=extremes(A,lo,hi,np.eye(A.shape[1])[j]);shaperanges.append(dict(date=d,shape=name,background=kind,meeting=m,lower=l,upper=h))
        # Profile shape uncertainty: union over the prespecified finite grid, not just best shape.
        for row in grid:
            A,mm,ee=shape_design(gs,row['c'],row['k'],'constant');lo,hi=vatminterval(gs,fits,1.)
            if solve(A,lo,hi) is None:continue
            for j,m in enumerate(mm):
                l,h=extremes(A,lo,hi,np.eye(A.shape[1])[j]);profile.append(dict(date=d,c=row['c'],k=row['k'],meeting=m,lower=l,upper=h))
    write('shape_calendars.csv',shapecal);write('shape_ranges.csv',shaperanges);write('shape_profile.csv',profile)
    # Exercise sensitivity on all chains from first/middle/last observation dates.
    chosen=[sorted(bydate)[i] for i in [0,len(bydate)//2,len(bydate)-1]];exercise=[]
    for d in chosen:
        for g in bydate[d]:
            # closest plus each end of strike band
            picks={0,len(g['rows'])-1,g['rows'].index(g['near'])}
            for j in sorted(picks):
                r=g['rows'][j];q=fits[g['key']]['vatm'];values=[]
                for n in [400,800,1600]:
                    am,eu=american_normal(q,r['x'],r['D'],n);values.append(am-eu)
                exercise.append(dict(date=d,expiry=g['expiry'],strike=r['strike_index'],x=r['x'],D=r['D'],q=q,
                  premium400=values[0],premium800=values[1],premium1600=values[2],last_change=abs(values[2]-values[1]),
                  european_error1600=eu-float(price(q,r['x'],r['D']))))
    # At r=0 convex martingale exercise adds no value; same-tree premium exactly zero.
    am,eu=american_normal(900,12.5,1.,400);assert abs(am-eu)<1e-9
    write('exercise_sensitivity.csv',exercise)
    # Gaussian mean effect: bounds on z/delta, conditional on June18 nearest-ATM proxy intervals.
    mean=[];gs=sorted(bydate['2026-06-18'],key=lambda g:g['expiry'])
    for kind in ['constant','90day','gap']:
        A,mm,edges=design(gs,kind);lo,hi=vatminterval(gs,fits,1.)
        if solve(A,lo,hi) is None:continue
        T=np.array([days(gs[0]['date'],m)/360 for m in mm])
        for g in gs:
            S=g['S'];row=np.r_[np.maximum(S-T,0),[(max(S-a,0)**2-max(S-b,0)**2)/2 for a,b in zip(edges[:-1],edges[1:])]]
            l,h=extremes(A,lo,hi,row);delta=float(g['near']['accrual_act360']);G0=1+delta*(100-float(g['near']['futures_index']))/100
            # theta bp² converted to decimal variance; rate mean shift in bp.
            shift=lambda z:G0*(-np.expm1(-delta*z*1e-8))/delta*1e4
            mean.append(dict(background=kind,expiry=g['expiry'],mean_shift_lower_bp=shift(l),mean_shift_upper_bp=shift(h)))
    write('mean_sensitivity.csv',mean)
    fs=[fits[g['key']] for g in std];fm=[fits[g['key']] for g in mid]
    summary=dict(standard_chains=len(fs),midcurve_chains=len(fm),mixture_median_max_error=float(np.median([f['max_error'] for f in fs])),
       mixture_max_error=float(max(f['max_error'] for f in fs)),converged=sum(f['success'] for f in fs),
       held_near_n=sum(f['held_near_error'] is not None for f in fs),
       held_near_median=float(np.median([f['held_near_error'] for f in fs if f['held_near_error'] is not None])),
       held_near_max=float(max(f['held_near_error'] for f in fs if f['held_near_error'] is not None)),
       atm_vs_nearest_sd_median=float(np.median([np.sqrt(fits[g['key']]['vatm'])-np.sqrt(g['near']['Q']) for g in std])),
       calendar={kind:dict(median=float(np.median([r['min_atm_tolerance'] for r in calendars if r['background']==kind])),
          feasible={str(t):sum(r['min_atm_tolerance']<=t for r in calendars if r['background']==kind) for t in [.25,.5,1.]}) for kind in ['constant','90day','gap']},
       shape_best=best,parallel_grid=next(r for r in grid if r['c']==0),shape_dates=len(overlap),
       shape_calendar={name:{kind:dict(median=float(np.median([r['min_atm_tolerance'] for r in shapecal if r['shape']==name and r['background']==kind])),
          feasible_1=sum(r['min_atm_tolerance']<=1 for r in shapecal if r['shape']==name and r['background']==kind)) for kind in ['constant','90day','gap']} for name in ['parallel','hump']},
       profile_dates=len(set(r['date'] for r in profile)),exercise_dates=chosen,exercise_n=len(exercise),
       exercise_median=float(np.median([r['premium1600'] for r in exercise])),exercise_max=float(max(r['premium1600'] for r in exercise)),
       exercise_convergence_max=float(max(r['last_change'] for r in exercise)),
       european_lattice_error_max=float(max(abs(r['european_error1600']) for r in exercise)))
    dump('extensions_summary.json',summary)
    dump('extensions_input_hashes.json',input_hashes)
    from datetime import timedelta
    first=date.fromisoformat(min(bydate));last=date.fromisoformat(max(bydate))
    weekdays=[(first+timedelta(days=i)).isoformat() for i in range((last-first).days+1) if (first+timedelta(days=i)).weekday()<5]
    near=lambda d:min(abs(days(d,m)) for m in MEETINGS)<=3
    dump('coverage_diagnostics.json',dict(near_meeting_calendar_day_radius=3,sample_near=sum(near(d) for d in bydate),sample_dates=len(bydate),weekday_near=sum(near(d) for d in weekdays),weekdays=len(weekdays)))

    fig,ax=plt.subplots(1,2,figsize=(10.2,3.5))
    base=list(csv.DictReader((OUT/'chain_diagnostics.csv').open())) if (OUT/'chain_diagnostics.csv').exists() else []
    ax[0].hist([f['max_error'] for f in fs],bins=25,color=BLUE,alpha=.8);ax[0].axvline(.25,color=ORANGE,ls='--');ax[0].set(xlabel='Mixture maximum strike error (premium bp)',ylabel='Standard chains')
    tau=np.linspace(0,5,300);ax[1].plot(tau,1+best['c']*best['k']*tau*np.exp(-best['k']*tau),color=BLUE);ax[1].axhline(1,color=ORANGE,ls='--');ax[1].set(xlabel='Forward maturity minus shock time (years)',ylabel='Fitted background loading')
    fig.tight_layout();fig.savefig(FIG/'empirical_extensions.pdf');plt.close(fig)
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()

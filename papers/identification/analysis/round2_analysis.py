"""Offline second-round sensitivity calculations; no lab, network or new inputs.
Keeps the original smile fits and never uses S3 to choose a loading shape.
"""
from extend_empirics import *
from math import comb


def robustness(std,fits):
    gs=sorted([g for g in std if g['date']=='2026-06-18'],key=lambda g:g['expiry'])
    # Common envelope: maximum mean bound across the three 1-bp seed feasible sets.
    # Verify that the widened boxes stay inside those seed boxes: no circular bound.
    upper=np.zeros(len(gs));means=[]
    for kind in ['constant','90day','gap']:
        A,mm,edges=design(gs,kind);lo,hi=vatminterval(gs,fits,1.)
        assert solve(A,lo,hi) is not None
        T=np.array([days(gs[0]['date'],m)/360 for m in mm])
        for l,g in enumerate(gs):
            S=g['S'];row=np.r_[np.maximum(S-T,0),[(max(S-a,0)**2-max(S-b,0)**2)/2 for a,b in zip(edges[:-1],edges[1:])]]
            _,h=extremes(A,lo,hi,row);delta=float(g['near']['accrual_act360'])
            G0=1+delta*(100-float(g['near']['futures_index']))/100
            shift=G0*(-np.expm1(-delta*h*1e-8))/delta*1e4
            upper[l]=max(upper[l],shift)
            means.append(dict(background=kind,expiry=g['expiry'],upper_mean_shift_bp=shift))
    allowances=[];eps=[]
    for l,g in enumerate(gs):
        D=g['near']['D'];q=fits[g['key']]['vatm'];values=[]
        for n in [800,1600]:
            am,eu=american_normal(q,0.,D,n);values.append(am-eu)
        allowance=.25+values[-1]+D*upper[l];eps.append(allowance)
        allowances.append(dict(date=g['date'],expiry=g['expiry'],atm_variance=q,discount=D,base_allowance=.25,
            exercise_premium=values[-1],exercise_800_1600_change=abs(values[-1]-values[0]),
            upper_mean_shift_bp=upper[l],discounted_mean_bound=D*upper[l],total_allowance=allowance))
    eps=np.array(eps);assert np.all(eps<1.),'Seed envelopes would not bound the widened sets.'
    ranges=[]
    for kind in ['constant','90day','gap']:
        A,mm,edges=design(gs,kind);lo,hi=vatminterval(gs,fits,eps)
        assert solve(A,lo,hi) is not None
        for j,m in enumerate(mm):
            l,h=extremes(A,lo,hi,np.eye(A.shape[1])[j])
            ranges.append(dict(date=gs[0]['date'],background=kind,meeting=m,lower=l,upper=h))
    write('round2_allowances.csv',allowances);write('round2_robust_ranges.csv',ranges)
    return dict(min_allowance=min(eps),max_allowance=max(eps),seed_allowance=1.,
                seed_containment_verified=bool(np.all(eps<1.)),exercise_convergence_max=max(r['exercise_800_1600_change'] for r in allowances),
                headline_ranges=[r for r in ranges if r['meeting'] in ['2026-09-16','2027-01-27']])


def loading_blocks(panels,k):
    """Integrate (1+chi1 B+chi2 C)^2 by its six coefficients, per contract."""
    blocks={}
    for d,gs in panels.items():
        A,_,_=design(gs,'constant');S=np.array([g['S'] for g in gs]);ss=(GX[None,:]+1)*S[:,None]/2
        a=np.array([days(d,g['near']['accrual_start'])/360 for g in gs])[:,None]
        b=np.array([days(d,g['near']['accrual_end'])/360 for g in gs])[:,None]
        primitive=lambda x:-(x+1/k)*np.exp(-k*x)
        B=(primitive(b-ss)-primitive(a-ss))/(b-a)
        C=1-(np.exp(-k*(a-ss))-np.exp(-k*(b-ss)))/(k*(b-a))
        integ=lambda v:(v@GW)*S/2
        coeff=np.array([S,2*integ(B),integ(B*B),2*integ(C),2*integ(B*C),integ(C*C)])
        blocks[d]=(A,coeff)
    return blocks


def fit_shape(panels,fits,blocks,c1,c2,k,save=False):
    total=0.;cnt=0;held=[];predictions=[];projection=0.
    for d,gs in panels.items():
        A,coeff=blocks[d];A=A.copy();A[:,-1]=np.array([1,c1,c1*c1,c2,c1*c2,c2*c2])@coeff
        train=np.array([g['key'][1]!='S3' for g in gs]);y=np.array([fits[g['key']]['vatm'] for g in gs]);w=1/(2*np.sqrt(y))
        X=A[train]*w[train,None];yy=y[train]*w[train];sc=np.linalg.norm(X,axis=0);act=sc>1e-12
        theta=np.zeros(A.shape[1]);coef,_=nnls(X[:,act]/sc[act],yy,maxiter=1000);theta[act]=coef/sc[act]
        prediction=np.sqrt(np.maximum(A@theta,0));err=prediction-np.sqrt(y)
        total+=float(np.sum(err[train]**2));cnt+=sum(train);held.extend(abs(err[~train]).tolist())
        if save:
            if (~train).any():projection=max(projection,float(np.max(abs(A[~train]-A[~train]@np.linalg.pinv(A[train])@A[train]))))
            for i,g in enumerate(gs):predictions.append(dict(date=d,product=g['key'][1],expiry=g['expiry'],held_out=not bool(train[i]),observed_sd=float(np.sqrt(y[i])),predicted_sd=float(prediction[i]),error_sd=float(err[i])))
    result=dict(chi1=c1,chi2=c2,kappa=k,train_n=int(cnt),train_sd_rmse=float(np.sqrt(total/cnt)),held_n=len(held),held_sd_mae=float(np.mean(held)),held_sd_median=float(np.median(held)))
    return (result,predictions,projection) if save else result


def loadings(std,mid,fits):
    overlap=sorted(set(g['date'] for g in mid)&set(g['date'] for g in std))
    panels={d:sorted([g for g in std+mid if g['date']==d],key=lambda g:(g['expiry'],g['key'])) for d in overlap}
    kappas=[.25,.5,.75,1.,1.25,1.5,2.,3.,4.]
    amplitudes=[0.,.5,1.,2.,4.,8.,12.,16.];levels=[0.,.25,.5,1.,2.,4.,8.]
    grid=[];cache={}
    for k in kappas:
        cache[k]=loading_blocks(panels,k)
        for c1 in amplitudes:
            for c2 in levels:
                # The flat shape is independent of kappa; retain it only once.
                if c1==0 and c2==0 and k!=kappas[0]:continue
                grid.append(fit_shape(panels,fits,cache[k],c1,c2,k))
        print('loading kappa',k,flush=True)
    best=min(grid,key=lambda r:r['train_sd_rmse'])
    pure=min((r for r in grid if r['chi2']==0),key=lambda r:r['train_sd_rmse'])
    baseline=next(r for r in grid if r['chi1']==r['chi2']==0)
    write('round2_loading_grid.csv',grid)
    # Training-only boundary check: enlarge amplitude limits before evaluating its S3 result.
    boundary=[]
    if best['chi1']==max(amplitudes) or best['chi2']==max(levels):
        for k in kappas:
            for c1 in [0.,1.,2.,4.,8.,12.,16.,24.,32.,48.,64.]:
                for c2 in [0.,1.,2.,4.,8.,12.,16.,24.,32.,48.,64.]:
                    if c1==0 and c2==0 and k!=kappas[0]:continue
                    boundary.append(fit_shape(panels,fits,cache[k],c1,c2,k))
    enlarged=min(boundary,key=lambda r:r['train_sd_rmse']) if boundary else best
    if boundary:write('round2_loading_boundary.csv',boundary)
    result,pred,proj=fit_shape(panels,fits,cache[best['kappa']],best['chi1'],best['chi2'],best['kappa'],True)
    assert proj<1e-10
    write('round2_loading_predictions.csv',pred)
    # Window bands: cross-sectional IQR of accrual midpoints relative to midpoint shock time.
    # Full range of T-s is disclosed separately; bands are descriptive, not new fitting data.
    bands=[]
    for prod in ['S0','S2','S3']:
        gg=[g for gs in panels.values() for g in gs if g['key'][1]==prod]
        centres=[(days(g['date'],g['near']['accrual_start'])+days(g['date'],g['near']['accrual_end']))/720-g['S']/2 for g in gg]
        bands.append(dict(product=prod,n=len(gg),q25=float(np.quantile(centres,.25)),q75=float(np.quantile(centres,.75)),
                          min_distance=min(days(g['date'],g['near']['accrual_start'])/360-g['S'] for g in gg),
                          max_distance=max(days(g['date'],g['near']['accrual_end'])/360 for g in gg)))
    write('round2_window_bands.csv',bands)
    fig,ax=plt.subplots(1,2,figsize=(10.2,3.5));fs=[fits[g['key']] for g in std]
    ax[0].hist([f['max_error'] for f in fs],bins=25,color=BLUE,alpha=.8);ax[0].axvline(.25,color=ORANGE,ls='--');ax[0].set(xlabel='Mixture maximum strike error (premium bp)',ylabel='Standard chains')
    tau=np.linspace(0,5,300);shape=lambda r:1+r['chi1']*r['kappa']*tau*np.exp(-r['kappa']*tau)+r['chi2']*(1-np.exp(-r['kappa']*tau))
    original=1+4*.75*tau*np.exp(-.75*tau);norm0=1+4*.75*np.exp(-.75)
    norm1=1+best['chi1']*best['kappa']*np.exp(-best['kappa'])+best['chi2']*(1-np.exp(-best['kappa']))
    ax[1].plot(tau,original/norm0,color=BLUE,label='Original hump');ax[1].plot(tau,shape(best)/norm1,color=ORANGE,label='Free long-end level');ax[1].axhline(1,color='grey',ls=':',lw=.8)
    for b,col in zip(bands,[BLUE,GREEN,'#8D6BA6']):
        ax[1].axvspan(b['q25'],b['q75'],color=col,alpha=.12);ax[1].text((b['q25']+b['q75'])/2,.04,b['product'],transform=ax[1].get_xaxis_transform(),ha='center',fontsize=8,color=col)
    ax[1].set(xlabel='Forward maturity minus shock time (years)',ylabel='Loading relative to one year');ax[1].legend(frameon=False,fontsize=8,loc='upper right')
    fig.tight_layout();fig.savefig(FIG/'empirical_extensions.pdf');plt.close(fig)
    return dict(grid_points=len(grid),pure_distinct_shapes=sum(r['chi2']==0 for r in grid),best=best,expanded_pure=pure,parallel=baseline,held_rowspan_error=proj,window_bands=bands,
                selection_used_S3=False,boundary_check=enlarged,boundary_grid_points=len(boundary))


def additivity():
    rows=[];dt=1/8;a=25.;r=.04
    for sigma in [0.,25.,50.,100.]:
        old=0.;first=None
        for n in range(1,9):
            sd=sigma*np.sqrt(n*dt);mu=a*(2*np.arange(n+1)-n);weights=np.array([comb(n,k)/2**n for k in range(n+1)])
            calls=np.maximum(mu,0) if sd==0 else mu*ndtr(mu/sd)+sd*pdf(mu/sd)
            call=float(weights@calls);proxy=2*np.pi*call**2;D=np.exp(-r*n*dt)
            if first is None:first=proxy
            add=n*first;gauss_true=a*a*n+sigma*sigma*n*dt
            err=D*(np.sqrt(add/(2*np.pi))-call)
            rows.append(dict(background_vol=sigma,meetings=n,expiry=n*dt,discount=D,true_variance=gauss_true,
               atm_proxy=proxy,additive_one_increment_proxy=add,true_atm_premium=D*call,
               additive_proxy_premium=D*np.sqrt(add/(2*np.pi)),premium_error=err,
               inferred_meeting_variance=proxy-old-sigma*sigma*dt,true_meeting_variance=a*a))
            old=proxy
    write('round2_atm_additivity.csv',rows)
    # Equal-variance Gaussian increments are additive exactly; binary no-background closed forms.
    assert abs(rows[0]['atm_proxy']-np.pi/2*a*a)<1e-10
    assert abs(rows[1]['atm_proxy']-rows[0]['atm_proxy'])<1e-10
    fig,ax=plt.subplots(1,2,figsize=(10.2,3.3))
    for sigma,col in [(0.,'#8D6BA6'),(25.,BLUE),(50.,ORANGE),(100.,GREEN)]:
        rr=[r for r in rows if r['background_vol']==sigma]
        ax[0].plot([r['meetings'] for r in rr],[r['premium_error'] for r in rr],'.-',label=f'{sigma:g} bp/year½',color=col)
        if sigma in [0.,50.]:ax[1].plot([r['meetings'] for r in rr],[r['inferred_meeting_variance'] for r in rr],'.-',label=f'{sigma:g} bp/year½',color=col)
    ax[0].axhline(.25,color='grey',ls=':',lw=.8);ax[0].set(xlabel='Independent ±25 bp meetings',ylabel='ATM price error (premium bp)');ax[0].legend(frameon=False,fontsize=8)
    ax[1].axhline(625,color='grey',ls=':',lw=.8,label='True meeting variance');ax[1].set(xlabel='Meeting index',ylabel='Inferred meeting variance (bp²)');ax[1].legend(frameon=False,fontsize=8)
    fig.tight_layout();fig.savefig(FIG/'atm_additivity.pdf');plt.close(fig)
    return dict(dt=dt,jump_size=a,discount_rate=r,scenarios=[dict(background_vol=sigma,max_price_error=max(abs(r['premium_error']) for r in rows if r['background_vol']==sigma),
        inferred_variance_min=min(r['inferred_meeting_variance'] for r in rows if r['background_vol']==sigma),inferred_variance_max=max(r['inferred_meeting_variance'] for r in rows if r['background_vol']==sigma)) for sigma in [0.,25.,50.,100.]])


def verify_round2(std,mid):
    """Independent quadrature and Gaussian controls for the new calculations."""
    global GX,GW
    from scipy.integrate import quad
    overlap=sorted(set(g['date'] for g in mid)&set(g['date'] for g in std))
    panels={d:sorted([g for g in std+mid if g['date']==d],key=lambda g:(g['expiry'],g['key'])) for d in overlap}
    blocks=loading_blocks(panels,1.5)
    gx,gw=GX,GW
    GX,GW=np.polynomial.legendre.leggauss(40)
    refined=loading_blocks(panels,1.5)
    GX,GW=gx,gw
    multiplier=np.array([1,12,144,8,96,64])
    quadrature=max(float(np.max(abs(multiplier@(blocks[d][1]-refined[d][1])))) for d in panels)
    pure=loading_blocks(panels,.75)
    nested=max(float(np.max(abs(np.array([1,4,16,0,0,0])@pure[d][1]-shape_design(gs,4,.75)[0][:,-1]))) for d,gs in panels.items())
    numerical=0.
    for d in [overlap[0],overlap[-1]]:
        gs=panels[d]
        for idx in [0,len(gs)//2,len(gs)-1]:
            g=gs[idx];a=days(d,g['near']['accrual_start'])/360;b=days(d,g['near']['accrual_end'])/360
            beta=lambda t:quad(lambda T:1+12*1.5*(T-t)*np.exp(-1.5*(T-t))+8*(1-np.exp(-1.5*(T-t))),a,b,epsabs=1e-11)[0]/(b-a)
            direct=quad(lambda t:beta(t)**2,0,g['S'],epsabs=1e-10)[0]
            numerical=max(numerical,abs(direct-(multiplier@blocks[d][1])[idx]))
    # Integrate the positive payoff under equal-variance Gaussian controls.
    gaussian=0.
    for sigma in [0.,25.,50.,100.]:
        for n in [1,2,8]:
            v=n*(625+sigma*sigma/8);sd=np.sqrt(v)
            c=quad(lambda z:sd*z*np.exp(-z*z/2)/np.sqrt(2*np.pi),0,np.inf)[0]
            gaussian=max(gaussian,abs(2*np.pi*c*c-v))
    assert quadrature<1e-9 and nested<1e-9 and numerical<1e-9 and gaussian<1e-7
    result=dict(quadrature20_40_exposure_error=quadrature,nested_original_hump_exposure_error=nested,
                independent_double_quadrature_error=numerical,gaussian_control_variance_error=gaussian)
    dump('round2_checks.json',result)
    return result


def main():
    expected=json.loads((OUT/'extensions_input_hashes.json').read_text())
    assert all(hashlib.sha256((DATA/k).read_bytes()).hexdigest()==v for k,v in expected.items())
    fits={tuple(r['key']):r for r in json.loads((OUT/'mixture_chains.json').read_text())}
    std=select(load('calibration_panel_with_discount.csv'));mid=select(load('midcurve_monthly_panel_with_discount.csv'))
    summary=dict(robustness=robustness(std,fits),loadings=loadings(std,mid,fits),additivity=additivity())
    verify_round2(std,mid)
    dump('round2_summary.json',summary);print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()

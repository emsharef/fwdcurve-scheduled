"""Offline final-revision sensitivities using saved fits and existing data only."""
from round2_analysis import *
from scipy.integrate import quad


def moments(std,fits):
    gs=sorted([g for g in std if g['date']=='2026-06-18'],key=lambda g:g['expiry'])
    allowances={r['expiry']:float(r['total_allowance']) for r in csv.DictReader((OUT/'round2_allowances.csv').open())}
    M=np.array([fits[g['key']]['moment'] for g in gs]);c=np.array([fits[g['key']]['atm'] for g in gs])
    eps=np.array([allowances[g['expiry']] for g in gs])
    # Scaling the whole centered mixture by lambda scales ATM price by lambda
    # and variance by lambda^2. Additional relative bands are sensitivity choices.
    base_lo=M*np.maximum(1-eps/c,0)**2;base_hi=M*(1+eps/c)**2
    obs=[];scale_error=0.
    for i,g in enumerate(gs):
        f=fits[g['key']];d,l1,l2=f['par'];sc=f['scale']
        assert abs(M[i]-sc**2*(d*d+.5*np.exp(2*l1)+.5*np.exp(2*l2)))<1e-8
        for lam in [max(1-eps[i]/c[i],0),1+eps[i]/c[i]]:
            actual=float(mixture(f['par'],np.array([0.]),g['near']['D'],sc*lam)[0])
            scale_error=max(scale_error,abs(actual-lam*c[i]))
        obs.append(dict(expiry=g['expiry'],atm_variance=f['vatm'],mixture_variance=M[i],ratio=M[i]/f['vatm'],
                        atm_price=c[i],allowance=eps[i],base_lower=base_lo[i],base_upper=base_hi[i]))
    results=[];checks=[]
    for eta in [0.,.1,.25,.5]:
        lo=(1-eta)*base_lo;hi=(1+eta)*base_hi
        for kind in ['constant','90day','gap']:
            A,mm,edges=design(gs,kind);feasible=solve(A,lo,hi) is not None
            for j,m in enumerate(mm):
                l,h=extremes(A,lo,hi,np.eye(A.shape[1])[j]) if feasible else (None,None)
                results.append(dict(eta=eta,background=kind,meeting=m,feasible=feasible,lower=l,upper=h))
            checks.append(dict(eta=eta,background=kind,feasible=feasible))
    assert scale_error<1e-10
    for kind in ['constant','90day','gap']:
        for meeting in {r['meeting'] for r in results}:
            rr=[r for r in results if r['background']==kind and r['meeting']==meeting and r['feasible']]
            assert all(b['lower']<=a['lower']+1e-6 and b['upper']>=a['upper']-1e-6 for a,b in zip(rr[:-1],rr[1:]))
    write('round3_moment_observations.csv',obs);write('round3_moment_ranges.csv',results)
    return dict(atm_scaling_error=scale_error,nested_ranges_checked=True,ratio_min=float(min(M/np.array([fits[g['key']]['vatm'] for g in gs]))),
                ratio_max=float(max(M/np.array([fits[g['key']]['vatm'] for g in gs]))),feasibility=checks,
                headline_ranges=[r for r in results if r['meeting'] in ['2026-09-16','2027-01-27']])


def front_design(gs,cut,order=20):
    """Clamp loading to phi(cut) for maturity distances below cut; retain tail.
    Integrate maturity analytically, splitting time at the clamping boundaries.
    Normalize all shapes at distance one year for a comparable matrix scale.
    """
    A,mm,edges=design(gs,'gap');k=1.5
    phi=lambda x:1+12*k*x*np.exp(-k*x)+8*(1-np.exp(-k*x))
    primitive=lambda x:9*x-12*(x+1/k)*np.exp(-k*x)+(8/k)*np.exp(-k*x)
    F=lambda x:np.where(x<cut,phi(cut)*(x-cut),primitive(x)-primitive(cut))
    norm=phi(max(1.,cut));xx,ww=np.polynomial.legendre.leggauss(order)
    for l,g in enumerate(gs):
        a=days(g['date'],g['near']['accrual_start'])/360;b=days(g['date'],g['near']['accrual_end'])/360
        for j,(left,right) in enumerate(zip(edges[:-1],edges[1:])):
            right=min(right,g['S'])
            if right<=left:A[l,len(mm)+j]=0;continue
            pieces=sorted(set([left,right]+[q for q in [a-cut,b-cut] if left<q<right]))
            val=0.
            for t0,t1 in zip(pieces[:-1],pieces[1:]):
                tt=(t0+t1)/2+(t1-t0)/2*xx
                beta=(F(b-tt)-F(a-tt))/(b-a)/norm
                val+=(t1-t0)/2*np.dot(ww,beta**2)
            A[l,len(mm)+j]=val
    return A


def front(std,mid):
    gs=sorted([g for g in std+mid if g['date']=='2026-07-22'],key=lambda g:(g['expiry'],g['key']))
    rows=[];err=0.
    _,mm,_=design(gs,'gap')
    _,coef=loading_blocks({'2026-07-22':gs},1.5)['2026-07-22']
    norm=1+18*np.exp(-1.5)+8*(1-np.exp(-1.5))
    original=np.array([1,12,144,8,96,64])@coef/norm**2
    original_error=float(np.max(abs(front_design(gs,0.)[:,len(mm):].sum(axis=1)-original)))
    assert original_error<1e-10
    for cut in [0.,.5,1.,1.5,4.]:
        A=front_design(gs,cut);B=front_design(gs,cut,40);err=max(err,float(np.max(abs(A-B))))
        sv=np.linalg.svd(A,compute_uv=False)
        rank=int(np.sum(sv>1e-10*sv[0]));kept=sv[:rank]
        assert all(int(np.sum(sv>tol*sv[0]))==rank for tol in [1e-8,1e-12])
        rows.append(dict(flatten_through_years=cut,rows=A.shape[0],columns=A.shape[1],rank=rank,
                         smallest_nonzero_singular=float(kept[-1]),largest_singular=float(sv[0]),ratio=float(kept[-1]/sv[0])))
    A,_,_=design(gs,'gap')
    assert np.max(abs(front_design(gs,4.)-A))<1e-10
    assert err<1e-10
    phi=lambda x:1+18*x*np.exp(-1.5*x)+8*(1-np.exp(-1.5*x))
    write('round3_front_sensitivity.csv',rows)
    return dict(normalized_at_zero=float(phi(0)/phi(1)),normalized_at_half=float(phi(.5)/phi(1)),
                quadrature_error=err,original_loading_exposure_error=original_error,parallel_control_rank=int(np.linalg.matrix_rank(A)),results=rows)


def main():
    expected=json.loads((OUT/'extensions_input_hashes.json').read_text())
    assert all(hashlib.sha256((DATA/k).read_bytes()).hexdigest()==v for k,v in expected.items())
    fits={tuple(r['key']):r for r in json.loads((OUT/'mixture_chains.json').read_text())}
    std=select(load('calibration_panel_with_discount.csv'));mid=select(load('midcurve_monthly_panel_with_discount.csv'))
    out=dict(moments=moments(std,fits),front=front(std,mid))
    dump('round3_summary.json',out)
    inputs=[*(DATA/k for k in expected),OUT/'mixture_chains.json',OUT/'round2_allowances.csv']
    dump('round3_input_hashes.json',{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs})
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()

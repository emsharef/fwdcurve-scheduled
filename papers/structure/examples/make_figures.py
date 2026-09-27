"""Deterministic synthetic illustrations; no lab, market data, or simulation."""
from pathlib import Path
import os
ROOT = Path(__file__).resolve().parents[1]
os.environ.setdefault('MPLCONFIGDIR', str(ROOT / 'build' / 'mpl'))
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from numpy.polynomial.legendre import leggauss

plt.rcParams.update({'font.family': 'serif', 'font.size': 10, 'axes.spines.top': False,
                     'axes.spines.right': False, 'savefig.bbox': 'tight'})
FIG = ROOT / 'figures'
FIG.mkdir(exist_ok=True)

def save(fig, name):
    fig.savefig(FIG / (name + '.pdf'))
    fig.savefig(FIG / (name + '.png'), dpi=170)
    plt.close(fig)

# Evaluate the tiny difference with a series, avoiding cancellation.
tau = np.linspace(0, 1, 301)
delta = .0025
z = delta * tau / 2
gap = delta / 2 * (z**3/3 - 2*z**5/15 + 17*z**7/315)
assert np.all(gap <= delta**4*tau**3/48 + 1e-25)
fig, ax = plt.subplots(1, 2, figsize=(10, 3.4), layout="constrained")
ax[0].plot(tau, 1e4*delta/2*np.tanh(z), label='Two-point law')
ax[0].plot(tau, 1e4*delta**2*tau/4, '--', label='Gaussian tangent')
ax[0].set(xlabel='Years after announcement', ylabel='Profile change from origin (bp)')
ax[0].legend()
ax[1].plot(tau, gap*1e4/1e-9)
ax[1].set(xlabel='Years after announcement', ylabel='Profile gap ($10^{-9}$ bp)')
save(fig, 'jump_profiles')

idx = np.arange(33)
a = np.r_[0., np.cumsum(1/np.arange(1, 33))]
rec = 1-.7**idx
matidx = np.add.outer(np.arange(16), np.arange(16))
svh = np.linalg.svd(a[matidx], compute_uv=False)
svr = np.linalg.svd(rec[matidx], compute_uv=False)
fig, ax = plt.subplots(1, 2, figsize=(10, 3.4), layout="constrained")
ax[0].plot(idx, a, label='Harmonic cumulative')
ax[0].plot(idx, rec, label=r'$1-0.7^i$')
ax[0].set(xlabel='Meeting index', ylabel='Loading')
ax[0].legend()
ax[1].semilogy(np.arange(1,17), np.maximum(svh/svh[0],1e-17), 'o-', label='Harmonic cumulative')
ax[1].semilogy(np.arange(1,17), np.maximum(svr/svr[0],1e-17), 's--', label='Recurrent, exact rank 2')
ax[1].axhline(np.finfo(float).eps, color='gray', lw=.8, label='Machine precision')
ax[1].set(xlabel='Singular value index', ylabel='Normalized singular value')
ax[1].legend(fontsize=8)
save(fig, 'hankel')

H, t, T, eta, kappa = 4., 2., 4., .0025, .35
meetings = np.linspace(0, H, 34)[1:-1]
def approximate(p):
    x, w = leggauss(p)
    x, w = (x+1)/2, w/2
    return np.sum((w/(1-x))[:, None]*(1-x[:,None]**idx[None,:]), axis=0)
def integrate_nodes(n):
    edges = np.r_[0., meetings[meetings<t], t]
    x,w=leggauss(n)
    return np.concatenate([(lo+hi)/2+(hi-lo)/2*x for lo,hi in zip(edges[:-1],edges[1:])]), np.concatenate([(hi-lo)/2*w for lo,hi in zip(edges[:-1],edges[1:])])
def sig(s, maturity, loads):
    count=np.count_nonzero((meetings>s)&(meetings<=maturity))
    return eta*loads[count]*np.exp(-kappa*(maturity-s))
def primitive(s, maturity, loads):
    edges=np.r_[s,meetings[(meetings>s)&(meetings<maturity)],maturity]
    lo,hi=edges[:-1],edges[1:]
    return np.sum(eta*loads[np.arange(len(lo))]*(np.exp(-kappa*(lo-s))-np.exp(-kappa*(hi-s)))/kappa)
def errors(loads, n):
    ss, ww=integrate_nodes(n)
    def coeff(ls):
        st=np.array([primitive(s,t,ls) for s in ss])
        sT=np.array([primitive(s,T,ls) for s in ss])
        vol=np.array([sig(s,T,ls) for s in ss])
        return vol,vol*sT,sT-st,-.5*np.dot(ww,sT*sT-st*st)
    v,dr,u,mu=coeff(a)
    vt,drt,ut,mut=coeff(loads)
    fmse=np.dot(ww,dr-drt)**2+np.dot(ww,(v-vt)**2)
    vd=np.dot(ww,(u-ut)**2)
    cov=np.dot(ww,(u-ut)*ut)
    b=mu-mut+.5*vd+2*cov
    bmse=np.exp(2*mut+2*np.dot(ww,ut*ut))*(np.expm1(b)**2+np.exp(2*b)*np.expm1(vd))
    return np.array([fmse,bmse])
rows=[]
for p in [1,2,3,4,6,8,12]:
    loads=approximate(p)
    eps=np.max(np.abs(a-loads)); abar=max(np.max(np.abs(a)),np.max(np.abs(loads)))
    exact=errors(loads,12); refined=errors(loads,24)
    assert np.allclose(exact,refined,rtol=2e-7,atol=1e-27), (p,exact,refined)
    cb=eta**2*t+4*abar**2*eta**4*(t*T-t*t/2)**2
    log_bound=eta**2*t*(T-t)**2+abar**2*eta**4*t*t*T*T*(T-t)**2
    moment_exponent=abar**2*eta**2*(t*T*(T-t)+4*t*(T-t)**2)
    cp=np.sqrt(6)*np.exp(moment_exponent)*log_bound
    bounds=eps**2*np.array([cb,cp])
    assert np.all(exact<=bounds*(1+1e-10))
    rows.append(dict(nodes=p,order=p+1,epsilon=float(eps),forward_rmse_bp=float(1e4*np.sqrt(exact[0])),forward_bound_bp=float(1e4*np.sqrt(bounds[0])),bond_rmse_bp=float(1e4*np.sqrt(exact[1])),bond_bound_bp=float(1e4*np.sqrt(bounds[1]))))
fig,ax=plt.subplots(1,2,figsize=(10,3.4),layout="constrained")
for p in [2,4,8]:
    err=np.abs(a-approximate(p))[1:]
    ax[0].semilogy(idx[1:], np.where(err>1e-14,err,np.nan),label=f'Order {p+1}')
ax[0].axhline(1e-14,color='gray',ls=':',lw=1,label='Numerical display threshold')
ax[0].set(xlabel='Meeting index',ylabel='Absolute loading error')
ax[0].legend(loc='lower left', bbox_to_anchor=(0, 1.02), fontsize=8, ncol=2, borderaxespad=0)
orders=[r['order'] for r in rows]
for name,label,style in [('forward_rmse_bp','Forward RMSE','o-'),('forward_bound_bp','Forward bound','o--'),('bond_rmse_bp','Bond RMSE','s-'),('bond_bound_bp','Bond bound','s--')]:
    ax[1].semilogy(orders,[r[name] for r in rows],style,label=label)
ax[1].set(xlabel='Recurrence order (upper bound)',ylabel='Error in bp of rate / unit price')
ax[1].legend(fontsize=8)
save(fig,'approximation')

# An incompatible one-step correlation: adjacent analytic cross-term difference.
meeting, obs, decay, blocknoise, step, rho = 1., .5, .6, .008, .007, .6
maturity=np.linspace(meeting,3,301)
C=rho*blocknoise*step*np.expm1(decay*obs)/decay
J=C*np.exp(-decay*maturity)*(maturity-meeting-1/decay)+rho*blocknoise*step*obs/decay
J0=-C*np.exp(-decay*meeting)/decay+rho*blocknoise*step*obs/decay
Jprime=2*C*np.exp(-decay*meeting)
remainder=J-J0-Jprime*(maturity-meeting)
fig,ax=plt.subplots(1,2,figsize=(10,3.4),layout="constrained")
ax[0].plot(maturity,J*1e4,label='Integrated cross-term difference')
ax[0].plot(maturity,(J0+Jprime*(maturity-meeting))*1e4,'--',label='Affine tangent')
ax[0].set(xlabel='Maturity (years)',ylabel='Cumulative drift contribution (bp)')
ax[0].legend(fontsize=8)
ax[1].plot(maturity,remainder*1e4,label=r'$\rho=0.6$')
ax[1].axhline(0,color='gray',ls='--',label=r'$\rho=0$')
ax[1].set(xlabel='Maturity (years)',ylabel='Non-affine remainder (bp)')
ax[1].legend()
save(fig,'splice_correlation')

(ROOT/'examples'/'results.json').write_text(json.dumps({'parameters':dict(H=H,t=t,T=T,meetings=32,eta=eta,kappa=kappa,initial_curve=0),'jump_gap_bp':float(gap[-1]*1e4),'approximation':rows,'checks':['12 versus 24 point quadrature on each time interval','All numerical errors below theorem bounds','Two-point profile gap bound']},indent=2)+'\n')
with (ROOT/'examples'/'results.tex').open('w') as f:
    f.write('% Generated by examples/make_figures.py\n')
    for r in rows:
        f.write(f"{r['order']} & {r['epsilon']:.2e} & {r['forward_rmse_bp']:.3g} & {r['forward_bound_bp']:.3g} & {r['bond_rmse_bp']:.3g} & {r['bond_bound_bp']:.3g} \\\\\n")
print('Created four quantitative figures and seven approximation comparisons; all checks passed.')

# Geometry only: distinguish a break across maturities from a jump through time.
fig, ax = plt.subplots(1, 2, figsize=(9, 3.2))
ax[0].plot([.25, 1], [3., 3.], color='C0', lw=2)
ax[0].plot([1, 2.5], [3.25, 3.25], color='C0', lw=2)
ax[0].scatter([1], [3.], facecolor='white', edgecolor='C0', zorder=3)
ax[0].scatter([1], [3.25], color='C0', zorder=3)
ax[0].axvline(1, color='gray', ls=':', lw=1)
ax[0].text(1.05, 2.96, 'Meeting date', fontsize=9)
ax[0].set(xlabel=r'Maturity $T$ (years)', ylabel='Forward rate (%)',
          title=r'One curve observed at $t=0.25$', ylim=(2.9,3.6), xlim=(.2,2.5))
ax[1].plot([0,1], [3.2,3.25], color='C1', lw=2)
ax[1].plot([1,1.75], [3.5,3.53], color='C1', lw=2)
ax[1].scatter([1],[3.25],facecolor='white',edgecolor='C1',zorder=3)
ax[1].scatter([1],[3.5],color='C1',zorder=3)
ax[1].axvline(1,color='gray',ls=':',lw=1)
ax[1].annotate('',xy=(1.08,3.5),xytext=(1.08,3.25),arrowprops=dict(arrowstyle='<->',color='black'))
ax[1].text(1.14,3.365,r'$\xi_1(2)$',fontsize=11)
ax[1].set(xlabel=r'Observation time $t$ (years)',ylabel='Forward rate (%)',
          title=r'One maturity $T=2$ followed through time',ylim=(2.9,3.6),xlim=(0,1.75))
fig.tight_layout()
save(fig,'two_discontinuities')
print('Created the introductory schematic distinguishing time and maturity.')

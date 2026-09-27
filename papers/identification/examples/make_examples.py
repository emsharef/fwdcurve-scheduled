"""Reproduce the paper's deterministic figures, tables and pricing diagnostics.
No lab, network, market-data credentials or random simulation is used.
"""
from pathlib import Path
import csv, json, os
from datetime import date
import numpy as np
from scipy.special import ndtr, ndtri
from scipy.optimize import linprog, brentq, lsq_linear
os.environ.setdefault('MPLCONFIGDIR', '/tmp/paper_pub3_matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[1]
FIG=ROOT/'figures'; OUT=ROOT/'examples'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'savefig.bbox':'tight','pdf.fonttype':42})
BLUE='#24567A'; ORANGE='#C27536'; GREEN='#378477'
phi=lambda x: np.exp(-np.asarray(x)**2/2)/np.sqrt(2*np.pi)
def bounds(A,lo,hi,c=None):
    A=np.asarray(A); lo=np.asarray(lo); hi=np.asarray(hi)
    targets=np.eye(A.shape[1]) if c is None else np.atleast_2d(c)
    result=[]
    for v in targets:
        low=linprog(v,A_ub=np.r_[A,-A],b_ub=np.r_[hi,-lo],bounds=(0,None),method='highs')
        high=linprog(-v,A_ub=np.r_[A,-A],b_ub=np.r_[hi,-lo],bounds=(0,None),method='highs')
        if not low.success or not high.success:
            raise RuntimeError((low.message,high.message))
        assert np.max(A@low.x-hi)<1e-6 and np.max(lo-A@low.x)<1e-6
        assert np.max(A@high.x-hi)<1e-6 and np.max(lo-A@high.x)<1e-6
        result.append([low.fun,-high.fun])
    return np.array(result)
# Figure 1: identical aggregate risks, different allocations.
t=np.arange(1,4); a=np.array([200,300,200]); b=np.array([300,100,300])
assert a.sum()==b.sum() and t@a==t@b
fig,axs=plt.subplots(1,2,figsize=(9,3.1))
axs[0].bar(t-.17,a,.34,label='Allocation A',color=BLUE); axs[0].bar(t+.17,b,.34,label='Allocation B',color=ORANGE)
axs[0].set(xticks=t,xticklabels=['Meeting 1','Meeting 2','Meeting 3'],ylabel='Meeting variance (bp²)'); axs[0].legend(frameon=False,fontsize=8,loc='upper left',ncol=2,bbox_to_anchor=(0,1.13)); axs[0].set_ylim(0,350)
x=np.linspace(0,350,100); axs[1].plot(x,700-2*x,color=BLUE,lw=2)
axs[1].scatter([200,300],[300,100],c=[BLUE,ORANGE],s=55,zorder=3)
axs[1].set(xlabel='First meeting variance (bp²)',ylabel='Second meeting variance (bp²)',xlim=(-10,360),ylim=(-20,720))
axs[1].text(18,85,'Third meeting variance = first\nTotal = 700 bp²',fontsize=9)
fig.tight_layout(); fig.savefig(FIG/'aggregation.pdf'); plt.close(fig)
# Synthetic exact European ATM inversion, conditional on known discount and mean.
S=np.array([.05,.15,.25,.35,.45,.55]); T=np.array([.10,.20,.30,.40,.50]); delta=.25
A=np.c_[(T[None,:]<=S[:,None]).astype(float),S]
theta=np.r_[np.full(5,100.),2500.]; Q=A@theta
# m and discount from a flat 4% initial curve, accrual [1,1.25], full variance schedule.
p=(delta*(1.25-T))@theta[:5]*1e-8 + theta[-1]*1e-8*(delta*(1.25*1.0-1.0**2/2)+delta**3/3) # exact integral of h through b
m=np.exp(.04*delta+p-delta*((np.maximum(S[:,None]-T,0)@theta[:5])+theta[-1]*S*S/2)*1e-8)
disc=np.exp(-.04*S)
prem=disc*m/delta*(2*ndtr(delta*np.sqrt(Q)*1e-4/2)-1)*1e4
# premium is in rate-basis-point units, Q in bp².
def invert_atm(c):
    y=np.clip(np.asarray(c)*1e-4*delta/(disc*m),0,1-1e-14)
    return (2*ndtri((1+y)/2)/delta*1e4)**2
intervals={}
for eps in [.25,.5,1.]:
    lo=invert_atm(np.maximum(prem-eps,0)); hi=invert_atm(prem+eps)
    intervals[str(eps)]=bounds(A,lo,hi)
assert np.max(np.abs(invert_atm(prem)-Q))<1e-7
fig,axs=plt.subplots(1,2,figsize=(9,3.3))
for off,eps,color in [(-.09,.25,BLUE),(.09,.5,ORANGE)]:
    B=intervals[str(eps)][:5]; center=B.mean(axis=1)
    axs[0].errorbar(np.arange(1,6)+off,center,yerr=(B[:,1]-B[:,0])/2,fmt='o',capsize=4,color=color,label=f'±{eps:g} bp premium')
axs[0].axhline(100,color='black',ls=':',lw=1); axs[0].set(xlabel='Meeting',ylabel='Compatible variance (bp²)',xticks=range(1,6)); axs[0].legend(frameon=False,fontsize=9)
axs[1].plot(S,np.sqrt(Q),'-o',color=BLUE,label='Total standard deviation')
axs[1].plot(S,np.sqrt(theta[-1]*S),'--',color=GREEN,label='Background component')
axs[1].set(xlabel='Option expiry (years)',ylabel='Standard deviation (bp)'); axs[1].legend(frameon=False,fontsize=9)
fig.tight_layout(); fig.savefig(FIG/'precision.pdf'); plt.close(fig)
# Synthetic row dependence: three meetings share a gap and a flexible background masks them.
C=np.c_[(np.array([.10,.20,.30])[None,:]<=np.array([.05,.35])[:,None]).astype(float),[.05,.35]]
assert np.linalg.matrix_rank(C)==2
summary={'synthetic':{'true_parameter':theta.tolist(),'Q':Q.tolist(),'premium_bp':prem.tolist(),'bounds':{k:v.tolist() for k,v in intervals.items()}}}
(OUT/'results.json').write_text(json.dumps(summary,indent=2)+'\n')

# Calendar visual and independent consistency checks for the worked examples.
fig,axs=plt.subplots(2,1,figsize=(9,3.5),sharex=True)
for j,(exp,label) in enumerate([([.05,.35], 'Two expiries: background and one three-meeting total'),([.05,.15,.25,.35], 'Four expiries: background and each meeting')]):
    ax=axs[j]; ax.axhline(0,color='gray',lw=.8); ax.axvspan(0,.05,color=BLUE,alpha=.07)
    ax.scatter([.10,.20,.30],[0,0,0],marker='^',s=65,color=ORANGE,zorder=3,label='Meeting')
    for n,t in enumerate([.10,.20,.30],1):ax.text(t,-.32,f'M{n}',ha='center',fontsize=9)
    ax.vlines(exp,-.15,.15,color=BLUE,lw=2,label='Observed expiry')
    for t in exp:ax.text(t,.22,f'{t:.2f}',ha='center',fontsize=9,color=BLUE)
    ax.set(ylim=(-.65,.6),yticks=[],title=label); ax.spines['left'].set_visible(False)
    ax.spines['bottom'].set_visible(False); ax.tick_params(bottom=False,labelbottom=False)
axs[0].legend(frameon=False,ncol=2,loc='lower center',fontsize=8)
axs[1].set_xlim(-.01,.37)
fig.tight_layout();fig.savefig(FIG/'calendar.pdf');plt.close(fig)
# The two allocations agree in p,z,q for later options and futures, not just Q.
meet=np.arange(1,4)/12
for Scheck,acheck,bcheck in [(.30,.5,.75),(.4,.75,1.0),(.5,1.,1.25)]:
    dt=bcheck-acheck
    vals=[]
    for alloc in [a,b]:
        vv=alloc*1e-8
        vals.append([dt*((bcheck-meet)@vv),dt*((Scheck-meet)@vv),dt**2*vv.sum()])
    assert np.allclose(vals[0],vals[1],rtol=1e-12,atol=1e-15)
Afull=np.c_[(np.array([.10,.20,.30])[None,:]<=np.array([.05,.15,.25,.35])[:,None]).astype(float),[.05,.15,.25,.35]]
assert np.linalg.matrix_rank(Afull)==4
# Strict interval feasibility is verified at both optimizing endpoints above.
for B in intervals.values():
    assert np.all(B[:,0]<=theta+1e-6) and np.all(theta<=B[:,1]+1e-6)
print('Checks passed: price inversion, exact aggregate equality, calendar ranks, both LP endpoints, synthetic truth coverage.')

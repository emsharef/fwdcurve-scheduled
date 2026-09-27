"""Offline reproduction of lab calendar examples; does not execute lab checks."""
from run_analysis import *
from scipy.optimize import brentq
D=lambda s:date.fromisoformat(s)
t0=D('2026-01-02');time=lambda d:(d-t0).days/360
meeting_dates=[D(s) for s in MEETINGS if s>='2026-01-02']
# The data vintage used for the price sample starts in March; include Jan explicitly.
if D('2026-01-28') not in meeting_dates:meeting_dates.insert(0,D('2026-01-28'))
if D('2026-03-18') not in meeting_dates:meeting_dates.append(D('2026-03-18'));meeting_dates.sort()
T=np.array([time(d) for d in meeting_dates])
expiry_days=[[16,13,13,10,15,12,10,14,11,16,13,11],[15,12,12,16,14,11,16,13,10,15,12,10]]
expiries=[date(2026+y,m+1,d) for y,ds in enumerate(expiry_days) for m,d in enumerate(ds)]
S=np.array([time(d) for d in expiries]);event=(T[None,:]<=S[:,None]).astype(float)
starts=[D(s) for s in ['2026-03-18','2026-06-17','2026-09-16','2026-12-16','2027-03-17','2027-06-16','2027-09-15','2027-12-15']]
a=np.repeat([time(d) for d in starts],3);delta=91/360
cuts=np.array([0]+[time(D(s)) for s in ['2026-01-28','2026-03-18','2026-06-17','2026-09-16','2027-01-27','2027-03-17','2027-07-28']]+[S[-1]])
cnt=np.array([sum(left<Ti<=right for Ti in T) for left,right in zip(np.r_[0,S[:-1]],S)])
free=cnt==0

def exposure(edges,k=0):
    lo=edges[:-1][None,:];hi=np.minimum(S[:,None],edges[1:][None,:]);length=np.maximum(hi-lo,0)
    if not k:return length
    g=((-np.expm1(-k*delta))/(k*delta))**2
    return np.where(hi>lo,g*np.exp(-2*k*(a[:,None]-hi))*(-np.expm1(-2*k*length))/(2*k),0)

def meanrows(edges):
    eventz=np.maximum(S[:,None]-T[None,:],0)
    bgz=(np.maximum(S[:,None]-edges[:-1],0)**2-np.maximum(S[:,None]-edges[1:],0)**2)/2
    return np.c_[eventz,bgz]
F=lambda k:np.exp(-122*k/360)-np.exp(-364*k/360)-np.exp(-10*k/360)+np.exp(-182*k/360)
kstar=brentq(F,.828,.864,xtol=1e-14)
ks=np.unique(np.r_[np.linspace(.05,2,300),kstar+np.array([-1e-5,0,1e-5])]);out=[]
for k in ks:
    bg=exposure(cuts,k);diff=np.diff(np.r_[np.zeros((1,8)),bg],axis=0)[free]
    diag=np.diag(diff);analytic=((-np.expm1(-k*delta))/(k*delta))**2/(2*k)*F(k)
    assert abs(diag[4]-analytic)<1e-14 and abs(diag[6]-analytic)<1e-14
    norm=np.linalg.norm(diff,axis=0);sv=np.linalg.svd(diff/norm,compute_uv=False)
    out.append(dict(kappa=k,change_diagonal=analytic,min_singular=sv[-1]))
write('critical_shape.csv',out)
quarters=np.array([0]+[time(date(y,m,1)) for y in [2026,2027] for m in [1,4,7,10] if date(y,m,1)>t0]+[S[-1]])
partmeet=np.r_[0,T,S[-1]];gap=np.r_[0,S]
ranks={}
for name,edges in [('eight_cells',cuts),('quarters',quarters),('meeting_dates',partmeet),('expiry_gaps',gap)]:
    A=np.c_[event,exposure(edges)];Z=meanrows(edges)
    ranks[name]=dict(variance_rank=int(np.linalg.matrix_rank(A)),stacked_rank=int(np.linalg.matrix_rank(np.r_[A,Z])),columns=A.shape[1])
A=np.c_[event,exposure(partmeet)];Z=meanrows(partmeet)
direction=np.zeros(A.shape[1]);i=meeting_dates.index(D('2026-03-18'));j=meeting_dates.index(D('2026-04-29'))
direction[i]=-23;direction[j]=-19;direction[len(T)+i+1]=360
assert np.max(abs(A@direction))<1e-10
max_z=float(np.max(abs(delta*Z@direction))*1e-8)
listed=[0,1,2,3,4,5,8,11,14,17,20,23]
AL=np.c_[event,S][listed];assert np.linalg.matrix_rank(AL)==10
summary=dict(kappa_star=kstar,rank_examples=ranks,max_z_change=max_z,listed_rank=10,listed_columns=17)
# Certify the parallel-calendar ranks over rational numbers, independently of SVD.
from fractions import Fraction
# Fraction Gaussian elimination: exact finite matrix certificate, no symbolic dependency.
def exact_rank(rows):
    mat=[[Fraction(x) for x in row] for row in rows];nr=len(mat);nc=len(mat[0]);rank=0
    for col in range(nc):
        pivot=next((j for j in range(rank,nr) if mat[j][col]),None)
        if pivot is None:continue
        mat[rank],mat[pivot]=mat[pivot],mat[rank]
        p=mat[rank][col];mat[rank]=[x/p for x in mat[rank]]
        for j in range(rank+1,nr):
            p=mat[j][col]
            if p:mat[j]=[x-p*y for x,y in zip(mat[j],mat[rank])]
        rank+=1
        if rank==nr:break
    return rank
Sd=np.rint(360*S).astype(int);Td=np.rint(360*T).astype(int)
for name,edges in [('eight_cells',cuts),('quarters',quarters),('meeting_dates',partmeet),('expiry_gaps',gap)]:
    ed=np.rint(360*edges).astype(int)
    exactA=[[int(t<=s) for t in Td]+[int(max(0,min(s,b)-a)) for a,b in zip(ed[:-1],ed[1:])] for s in Sd]
    exactZ=[[int(max(0,s-t)) for t in Td]+[Fraction(int(max(0,s-a)**2-max(0,s-b)**2),2) for a,b in zip(ed[:-1],ed[1:])] for s in Sd]
    assert exact_rank(exactA)==ranks[name]['variance_rank']
    assert exact_rank(exactA+exactZ)==ranks[name]['stacked_rank']
summary['parallel_ranks_checked_with_exact_rationals']=True
dump('calendar_examples.json',summary)
fig,ax=plt.subplots(1,2,figsize=(10.2,3.2));ax[0].plot(ks,[r['change_diagonal'] for r in out],color=BLUE);ax[1].semilogy(ks,[max(r['min_singular'],1e-16) for r in out],color=BLUE)
for aax in ax:aax.axvline(kstar,color=ORANGE,ls=':');aax.set_xlabel('Decay rate (per year)')
ax[0].axhline(0,color='grey',lw=.7);ax[0].set_ylabel('Window-change diagonal (years)');ax[1].set_ylabel('Smallest singular value');ax[1].set_ylim(1e-16,1)
fig.tight_layout();fig.savefig(FIG/'critical_shape.pdf');plt.close(fig)
print(json.dumps(summary,indent=2))

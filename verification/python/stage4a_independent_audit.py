from fractions import Fraction as Q
from itertools import product
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq
# No imports from Stage 4 code. Partition by all pairwise equidistance points, then choose nearest from full set.
def partition(pos):
    points={Q(0),Q(1)}
    for a in pos.values():
        points.update([a,(a+Q(1,2))%1])
    for a in pos.values():
        for b in pos.values():
            if a!=b: points.update([((a+b)/2)%1,((a+b)/2+Q(1,2))%1])
    pts=sorted(points)
    def dist(x,y):
        d=abs(x-y);return min(d,1-d)
    for l,r in zip(pts,pts[1:]):
        mid=(l+r)/2; ds={i:dist(mid,z) for i,z in pos.items()}; best=min(ds.values()); ids=[i for i,d in ds.items() if d==best]
        yield l,r,ids,dist(l,pos[ids[0]]),dist(r,pos[ids[0]])
def exact(pos):
    shares={i:Q(0) for i in pos}; T=Q(0)
    if not pos:return shares,None
    for l,r,ids,dl,dr in partition(pos):
        for i in ids: shares[i]+=(r-l)/len(ids)
        T+=(r-l)*(dl+dr)/2
    return shares,T
# S03: direct payoffs for all subsets, no gap functions.
Z=dict(zip('ABCDE',map(Q,['0','.12','.24','.62','.63'])))
sets=[frozenset(i for i,k in zip(Z,bits) if k) for bits in product([0,1],repeat=5)]
alloc={S:exact({i:Z[i] for i in S}) for S in sets}
F=Q('.005'); v=Q(2)
cost={S: F*len(S)+alloc[S][1] if S else v for S in sets}
def name(S):return ''.join(sorted(S)) or 'empty'
# threshold policy: q-threshold, half of Stage 4 theta
interval={S:(max([2*alloc[S|{j}][0][j] for j in Z if j not in S],default=None),min([2*alloc[S][0][j] for j in S],default=None)) for S in sets}
def admissible(S):
    lo,hi=interval[S]; return lo is None or hi is None or lo<=hi
feas=sorted([S for S in sets if admissible(S)],key=cost.get)
order=sorted(sets,key=cost.get)
print('S03 all sets in cost order; admissible interval (theta):')
for S in order:print(name(S),str(cost[S]),float(cost[S]),interval[S],admissible(S))
assert name(order[0])=='ABCD' and cost[order[0]]<cost[order[1]]
assert name(feas[0])=='ACD' and len(feas[0])==3
best4=min((S for S in feas if len(S)==4),key=cost.get);print('best4',name(best4),cost[best4]);assert name(best4)=='ACDE'
# Compare exact direct deviation test with intervals at all payoff thresholds, midpoints and tails
edges=sorted({x for lo,hi in interval.values() for x in (lo,hi) if x is not None}); grid=[edges[0]-1,*edges,*[(a+b)/2 for a,b in zip(edges,edges[1:])],edges[-1]+1];counts=[]
for th in grid:
    eq=[]
    for S in sets:
        actual=all(2*alloc[S][0][j]>=th if j in S else 2*alloc[S|{j}][0][j]<=th for j in Z)
        lo,hi=interval[S]; assert actual==((lo is None or lo<=th) and (hi is None or th<=hi))
        if actual:eq.append(S)
    counts.append(len(eq))
print('S03 thresholds',len(grid),'checks',len(grid)*len(sets),'eq counts',min(counts),max(counts),'multi',sum(c>1 for c in counts),'no pure',sum(c==0 for c in counts))
# exact thresholds / ties at benchmark
for th in map(Q,['.24','.30','.38']):print('theta',th,[name(S) for S in sets if all(2*alloc[S][0][j]>=th if j in S else 2*alloc[S|{j}][0][j]<=th for j in Z)])
# mixed equilibrium: unique first best implies deterministic actions; quantitative bound from necessary B/E incentives
r=1/(1-Q('.12')+Q('.19')); gap=cost[order[1]]-cost[order[0]]; print('mixed bound P(first best)<=',r,'loss >=',gap*(1-r),float(gap*(1-r)))
# S01 independent evaluator uses direct exact partition of all choice boundaries then antiderivative of density; quadrature for welfare.
P=dict(zip('ABCD',map(Q,['0','.25','.5','.75'])))
def direct(P,eps,with_welfare=False):
    q={i:0. for i in P}; T=0.;h=.05
    def integ(x):return x+eps/(2*np.pi)*np.sin(2*np.pi*(x-h))
    for l,r,ids,dl,dr in partition(P):
        a,b=float(l),float(r);mass=integ(b)-integ(a)
        for i in ids:q[i]+=mass/len(ids)
        if with_welfare:
            slope=float((dr-dl)/(r-l)); intercept=float(dl)-slope*a
            T+=quad(lambda x:(slope*x+intercept)*(1+eps*np.cos(2*np.pi*(x-h))),a,b,epsabs=1e-13)[0]
    return q,T
# symbolic antiderivative and welfare identity
x,z,e,h,d=sp.symbols('x z e h d', real=True)
assert sp.simplify(sp.diff(x+e*sp.sin(2*sp.pi*(x-h))/(2*sp.pi),x)-(1+e*sp.cos(2*sp.pi*(x-h))))==0
assert sp.expand(((d+z)**2+(d-z)**2-2*d*d)/4-z*z/2)==0
# analytic root candidates for A tie: q_A on either side monotone as entry gap changes.
for eps in [0.,1e-6,.001,.01]:
    target=Q(1,10); targetq,targetT=direct({**{i:z for i,z in P.items() if i!='A'},'E':target},eps,True); q0,T0=direct(P,eps,True)
    print('eps',eps,'target profit',.5*targetq['E']-.107,'delta W',.003-(targetT-T0),'A before',.5*q0['A']-.11)
    # enumerate every incumbent action at all locations, including colocations and immediately adjacent
    zs=sorted(set([Q(i,400) for i in range(400)]+[(k+off)%1 for k in P.values() for off in [Q(-1,1000000),Q(1,1000000)]]))
    maxprofit=-1; maxloc=[]; count=0; min_margin=1; multiple=0;unresolved=0
    for zz in zs:
        qAll,_=direct({**P,'E':zz},eps); min_margin=min(min_margin,*(.5*qAll[i]-.05 for i in 'BCD'))
        # dominance proven analytically, so only A decisions remain. enumerate both and mix at ties
        piA=.5*qAll['A']-.11; choices=[keep for keep in [False,True] if (piA>=-1e-12 if keep else piA<=1e-12)]
        if not choices:unresolved+=1
        if len(choices)>1:multiple+=1
        for keep in choices:
            q,_=direct({**{i:z for i,z in P.items() if keep or i!='A'},'E':zz},eps);pi=.5*q['E']-.107;count+=1
            if pi>maxprofit+1e-13:maxprofit=pi;maxloc=[zz]
            elif abs(pi-maxprofit)<=1e-13:maxloc.append(zz)
    print('grid',len(zs),'continuations',count,'ties',multiple,'unresolved',unresolved,'minBCD',min_margin,'best',maxprofit,'argmax count',len(maxloc),'first',maxloc[:3]);assert maxprofit<=.5*targetq['E']-.107+1e-12
    # analytically determined tie neighborhoods; solve monotone q_A on each side; mixed payoff is convex combo of two values
    for lo,hi in [(1e-9,.249999999),(.750000001,.999999999)]:
        def A(zz):return .5*direct({**P,'E':Q(str(zz))},eps)[0]['A']-.11
        root=brentq(A,lo,hi,xtol=1e-14); qq=Q(str(root)); co=direct({**P,'E':qq},eps)[0]['E']; ex=direct({**{i:z for i,z in P.items() if i!='A'},'E':qq},eps)[0]['E'];print('tie z',root,'piE co/exit',.5*co-.107,.5*ex-.107);assert .5*max(co,ex)-.107<=.5*targetq['E']-.107+1e-12
print('PASS: independent numerical checks; proof and scope separate')

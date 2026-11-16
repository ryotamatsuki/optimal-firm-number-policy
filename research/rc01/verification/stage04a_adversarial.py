from fractions import Fraction as Q
from itertools import combinations
from collections import Counter
from random import Random
from functools import lru_cache
from math import gcd
import sys

# Clean implementation: unfolded labelled Voronoi intervals, not production gap solver.
# Unit margin, t=1, v-c=2; normalized threshold x=2(F-s)/m.
def positions(d):
    z=[Q(0)]
    for a in d[:-1]: z.append(z[-1]+a)
    return tuple(z)
def subsets(n): return range(1<<n)
def bits(s,n): return tuple(i for i in range(n) if s>>i&1)
@lru_cache(None)
def alloc(z,s):
    n=len(z); q=[Q(0)]*n; cost=Q(0)
    if not s:return tuple(q),cost
    images=sorted((z[i]+offset,i) for i in bits(s,n) for offset in (-1,0,1))
    for j,(y,i) in enumerate(images):
        l=max(Q(0),(images[j-1][0]+y)/2) if j else Q(0)
        r=min(Q(1),(images[j+1][0]+y)/2) if j+1<len(images) else Q(1)
        if r<=l:continue
        q[i]+=r-l
        # integral |x-y| dx on clipped interval
        cost+=((r-y)*abs(r-y)-(l-y)*abs(l-y))/2
    assert sum(q)==1 and all(q[i]>0 for i in bits(s,n))
    return tuple(q),cost

def game(d):
    z=positions(d); n=len(z); A={s:alloc(z,s) for s in subsets(n)}
    # actual active payoff (q_i - theta/2) versus 0 after switching action.
    # double shares at the active profile for each binary deviation
    D={s:tuple((s>>i&1, 2*A[s|(1<<i)][0][i]) for i in range(n)) for s in A}
    return A,D

def equilibrium(D,x):
    return [s for s,row in D.items() if all(x<=v if active else x>=v for active,v in row)]
def partition(*Ds):
    pts=sorted({v for D in Ds for row in D.values() for _,v in row})
    return sorted(set(pts+[pts[0]-1,pts[-1]+1]+[(x+y)/2 for x,y in zip(pts,pts[1:])]))
def signals(A,E): return {(s,A[s][0]) for s in E}
def C(A,s,F):return F*s.bit_count()+A[s][1] if s else Q(2)
def comp(n,total):
    for cuts in combinations(range(1,total),n-1):
        p=(0,)+cuts+(total,)
        yield tuple(Q(b-a,total) for a,b in zip(p,p[1:]))

cnt=Counter(); rng=Random(41701)
for n in range(3,9):
    # full small ordered integer compositions, severe near-contact, equal/tied shares
    worlds=list(comp(n,n+2))
    worlds += [tuple(Q(w,sum(ws)) for w in ws) for ws in ([rng.randint(1,40) for _ in range(n)] for __ in range(6))]
    worlds += [tuple(Q(w,sum(ws)) for w in ws) for ws in ([1 if i==j else 1000+i for i in range(n)] for j in (0,n-1))]
    if n%2==0:worlds += [(a,Q(2,n)-a)*(n//2) for a in (Q(1,n),Q(1,10000*n),Q(1,3*n))]
    for d in worlds:
        A,D=game(d); allmask=(1<<n)-1; q=A[allmask][0]; H=min(2*x for x in q); cnt['worlds']+=1;cnt['profiles']+=len(A)
        # All finite deviations, all profiles, partition by every payoff-indifference threshold.
        for x in partition(D):
            E=equilibrium(D,x); assert E; cnt['regimes']+=1;cnt['pure_NE']+=len(E);cnt['multiple']+=len(E)>1
            cnt['deviation_inequalities']+=n*len(D)
            for s in E:
                for i,(active,v) in enumerate(D[s]):
                    if x==v:
                        other=s^(1<<i);cnt['indifferent_flips']+=1
                        # recompute ALL players after switching, rather than infer equivalence
                        feasible=all(x<=w if act else x>=w for act,w in D[other]);cnt['flipped_still_NE']+=feasible
            # Independent existence proof witness: smallest cardinality no-entry set.
            s=min((s for s,row in D.items() if all(active or x>=v for active,v in row)),key=lambda s:(s.bit_count(),s))
            assert s in E
        assert equilibrium(D,Q(0))==[allmask]
        if n%2:continue
        # two points on same full-signal fiber; alternate shift both directions, positive.
        e=tuple(a+(-1)**i*(min(d[1::2])/3) for i,a in enumerate(d));B,J=game(e);assert B[allmask][0]==q
        uniform=len(set(q))==1
        for x in partition(D,J):
            eq1,eq2=equilibrium(D,x),equilibrium(J,x)
            overlap=signals(A,eq1)&signals(B,eq2)
            cnt['paired_regimes']+=1
            if uniform:assert overlap
        if uniform:cnt['uniform_pairs']+=1
        else:
            eps=min(min(d),min(e),min(2*v-H for v in q if 2*v>H),1-H)/3
            x=H+eps;E=equilibrium(D,x);K=equilibrium(J,x)
            assert E and K and not signals(A,E)&signals(B,K)
            # Stronger: no retained signal matches ANY compatible alternative at same S,
            # even if alternative S is not an equilibrium.
            assert all(A[s][0]!=B[s][0] for s in E)
            cnt['nonuniform_pairs']+=1
            if q.count(min(q))==1:
                x=(H+min(2*v for v in q if 2*v>H))/2
                assert equilibrium(D,x)==[allmask^(1<<q.index(min(q)))];cnt['unique_min']+=1
    alloc.cache_clear()
print('EXACT adversarial enumeration',dict(cnt))
# Welfare attack, all pure equilibria under all policy regimes, near both strict bounds.
wc=Counter()
for n in (4,6,8,10):
    u=(Q(1,n),)*n; A,D=game(u); full=(1<<n)-1;H=Q(2,n)
    for a in (Q(1,10000*n), Q(1,20*n),Q(1,10*n)):
        b=Q(2,n)-a;c=(a,b)*(n//2);B,J=game(c);lo=a*b/2;hi=Q(1,4*n*(n-1))
        if lo>=hi:continue
        for F in (lo+(hi-lo)/100, (lo+hi)/2, hi-(hi-lo)/100):
            gam=hi-F;delta=F-lo
            assert min(C(A,s,F)-C(A,full,F) for s in A if s!=full)>=gam
            vals=[(max(C(B,s,F) for s in equilibrium(J,x)),x) for x in partition(J)];rstar=min(v for v,x in vals)
            assert rstar<= C(B,full,F)-delta
            assert all(v-rstar>=delta for v,x in vals if x<=H)
            assert all(max(C(A,s,F) for s in equilibrium(D,x))-C(A,full,F)>=gam for x in partition(D) if x>H)
            x=H+min(a,b)/3; E=equilibrium(J,x)
            assert all(C(B,full,F)-C(B,s,F)==(n-s.bit_count())*delta for s in E)
            wc['welfare_cases']+=1;wc['paired_policy_regimes']+=len(vals)
print('WELFARE',dict(wc))
# permanent counterexample to whole-correspondence equivalence; equality threshold reveals.
u=(Q(1,4),)*4;c=(Q(1,20),Q(9,20))*2;A,D=game(u);B,J=game(c)
for x in (Q(1,2),Q(3,5)):
    E=equilibrium(D,x);K=equilibrium(J,x)
    assert signals(A,E)!=signals(B,K) and signals(A,E)&signals(B,K)
    print('REGRESSION theta',x,'U',list(map(lambda s:bits(s,4),E)),'C',list(map(lambda s:bits(s,4),K)))
# An actual indifferent action changes other firms' best responses; do not identify toggled profile with NE by assumption.
assert 15 in equilibrium(D,Q(1,2)) and 14 in equilibrium(D,Q(1,2));assert A[15]!=A[14]
print('PASS Python',sys.version.split()[0])

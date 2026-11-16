from fractions import Fraction as Q
from itertools import combinations, product
from random import Random
from collections import Counter
import sympy as sp
import sys

def allsets(n):
    return [s for k in range(n+1) for s in combinations(range(n),k)]
def pos(d):
    z=[Q(0)]
    for x in d[:-1]:z.append(z[-1]+x)
    return z
def geo(z,S):
    if not S:return (),Q(0)
    g=[z[b]-z[a] for a,b in zip(S,S[1:])]+[1+z[S[0]]-z[S[-1]]]
    return tuple((g[j-1]+g[j])/2 for j in range(len(g))),sum(x*x/4 for x in g)
def direct(z,S):
    if not S:return (),Q(0)
    def dist(x,y):return min(abs(x-y),1-abs(x-y))
    b={Q(0),Q(1)}
    for i in S:b.update([z[i],(z[i]+Q(1,2))%1])
    for i,j in combinations(S,2):
        x=(z[i]+z[j])/2;b.update([x,(x+Q(1,2))%1])
    b=sorted(b);q={i:Q(0) for i in S};T=Q(0)
    for l,r in zip(b,b[1:]):
        x=(l+r)/2;i=min(S,key=lambda i:dist(x,z[i]));q[i]+=r-l
        T+=(r-l)*(dist(l,z[i])+dist(r,z[i]))/2
    return tuple(q[i] for i in S),T

def table(d,direct_check=False):
    n=len(d);z=pos(d);ss=allsets(n);D={s:geo(z,s) for s in ss}
    if direct_check:
        for s in ss:assert direct(z,s)==D[s]
    I={}
    for s,(q,T) in D.items():
        vals=[]
        for i in range(n):
            if i not in s:
                S=tuple(sorted(s+(i,)));vals.append(2*D[S][0][S.index(i)])
        I[s]=(max(vals,default=None),min((2*x for x in q),default=None))
    return D,I

def ne(I,x):return [s for s,(l,h) in I.items() if (l is None or l<=x) and (h is None or x<=h)]
def deletion(d,x,start=None):
    z=pos(d);n=len(d);s=tuple(range(n)) if start is None else start
    while s:
        q,_=geo(z,s);bad=[i for i,qi in zip(s,q) if 2*qi<x]
        if not bad:break
        s=tuple(i for i in s if i!=bad[0])
    return s

def loss(d,S,F):return F*len(S)+geo(pos(d),S)[1] if S else Q(2)
def probes(*tables):
    t=sorted({x for I in tables for l,h in I.values() for x in (l,h) if x is not None});return [t[0]-1,*t,*[(a+b)/2 for a,b in zip(t,t[1:])],t[-1]+1]

# Algebra checks.
a,b,F,t,n,k=sp.symbols('a b F t n k',positive=True)
assert sp.simplify(t*((a+b)**2-a*a-b*b)/4-t*a*b/2)==0
assert sp.simplify(k*F+t/(4*k)-(n*F+t/(4*n))-(n-k)*(t/(4*k*n)-F))==0
for N in range(3,17):
    M=sp.Matrix(N,N,lambda i,j:int(j==i or j==(i-1)%N));assert M.rank()==N-(N%2==0)
    if N%2==0:assert M*sp.Matrix([(-1)**i for i in range(N)])==sp.zeros(N,1)
print('symbolic identities, rank N=3..16 PASS')
# Exhaustive bounded integer composition grids; arbitrary policy boundaries/midpoints;
# independently integrate wages/quantities in selected computationally smaller worlds.
counts=Counter();rng=Random(20261117)
for N in range(3,9):
    # all positive ordered length compositions total N+3; plus random exact unequal geometry and ties
    grid=[]
    for bars in combinations(range(1,N+3),N-1):
        z=(0,)+bars+(N+3,);grid.append(tuple(Q(z[i+1]-z[i],N+3) for i in range(N)))
    for j in range(12):
        w=[rng.randrange(1,51) for i in range(N)];grid.append(tuple(Q(x,sum(w)) for x in w))
    if N%2==0:
        for j in range(1,5):
            a=Q(j,5*N);grid.append((a,Q(2,N)-a)*(N//2))
    for ind,d in enumerate(grid):
        check=ind<2
        D,I=table(d,check);counts['markets']+=1;counts['direct subsets']+=len(D) if check else 0
        s0=tuple(range(N));q0=D[s0][0];H=2*min(q0);assert ne(I,Q(0))==[s0]
        for x in probes(I):
            E=ne(I,x);assert E;assert deletion(d,x) in E;counts['policy regimes']+=1;counts['NE checks']+=len(E)
        if N%2:continue
        delta=min(d[1::2])/2;e=tuple(v+(-1)**i*delta for i,v in enumerate(d));B,J=table(e);assert B[s0][0]==q0
        eq=len(set(q0))==1
        if eq:
            for x in probes(I,J):
                s=s0 if x<=H else deletion(d,x,tuple(range(0,N,2)))
                assert s in ne(I,x) and s in ne(J,x) and D[s][0]==B[s][0];counts['common selector checks']+=1
        else:
            eps=min(min(d),min(e),min(2*q-H for q in q0 if 2*q>H),1-H)/2;x=H+eps
            A=ne(I,x);K=ne(J,x);assert A and K
            assert all(D[s][0]!=B[s][0] for s in A)
            assert not {(s,D[s][0]) for s in A}&{(s,B[s][0]) for s in K}
            # Adaptive first revealing assortment, without using unknown d in chosen sequence.
            for j in range(1,100):
                x=H+Q(1,2**j);E=ne(I,x)
                if all(D[s][0]!=B[s][0] for s in E):break
            else:raise AssertionError('probe limit')
            counts['max halvings']=max(counts['max halvings'],j)
            counts['unequal pair checks']+=1
            # if unique min, midpoint between first two distinct constraints suffices
            if q0.count(min(q0))==1:
                x=(H+min(2*q for q in q0 if 2*q>H))/2
                assert ne(I,x)==[tuple(i for i in s0 if q0[i]>min(q0))];counts['unique min checks']+=1
print('grid audit',dict(counts))
# Welfare: compare uniform vs paired, conditions, pure-selection-robust improvement.
for N in (4,6,8,10):
    u=(Q(1,N),)*N;a=Q(1,100*N*N);b=Q(2,N)-a;c=(a,b)*(N//2);F=Q(1,8*N*(N-1));H=Q(2,N);theta=H+a/2
    assert a*b/2<F<Q(1,4*N*(N-1));U,I=table(u);C,J=table(c);s0=tuple(range(N))
    gamma=Q(1,4*N*(N-1))-F;Delta=F-a*b/2
    assert all(loss(u,s,F)-loss(u,s0,F)>=gamma for s in U if s!=s0)
    E=ne(J,theta); assert E
    for s in E:
        r=N-len(s); assert r>0 and all(not(i not in s and (i+1)%N not in s) for i in range(N)); assert loss(c,s0,F)-loss(c,s,F)==r*Delta
    print('welfare N',N,'gamma',gamma,'Delta',Delta,'paired NE',len(E),'minimum improvement',min(loss(c,s0,F)-loss(c,s,F) for s in E))
# N=4 exact inherited result; preserves known-state fixed-site optima.
u=(Q(1,4),)*4;c=(Q(1,20),Q(9,20))*2;F=Q(1,50)
U,I=table(u,True);C,J=table(c,True)
for d,D in [(u,U),(c,C)]:print('baseline minimum',min((loss(d,s,F),s) for s in D))
print('PASS',sys.version.split()[0],sp.__version__)

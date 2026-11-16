"""Exploratory exact enumeration; no Stage 4 or novelty certification."""
from fractions import Fraction as Q
from itertools import combinations
from random import Random
from math import sqrt
from sympy import Matrix

def states(n):
    return [s for k in range(n+1) for s in combinations(range(n),k)]

def gaps(z,s):
    if len(s)==1:return [Q(1)]
    return [(z[s[(k+1)%len(s)]]-z[i])%1 for k,i in enumerate(s)]

def shares(z,s):
    if not s:return {}
    d=gaps(z,s)
    return {i:(d[k-1]+d[k])/2 for k,i in enumerate(s)}

def interval(z,s):
    if not s:return Q(2),None
    q=shares(z,s)
    return max((2*shares(z,tuple(sorted((*s,i))))[i] for i in range(len(z)) if i not in s),default=None),2*min(q.values())

def eq(z,s,x):
    lo,hi=interval(z,s)
    return (lo is None or lo<=x) and (hi is None or x<=hi)

def cost(z,s,f):
    return f*len(s)+sum((d*d/4 for d in gaps(z,s)),Q(0)) if s else Q(2)

# C01: full firm-level observations under common pure selection, plus optima.
f=Q(1,50); u=tuple(map(Q,['0','.25','.50','.75'])); c=tuple(map(Q,['0','.05','.50','.55'])); ss=states(4)
for z in [u,c]:
    val=min(cost(z,s,f) for s in ss)
    print('C01',z,'optimum',val,[s for s in ss if cost(z,s,f)==val])
    for s in [(0,1,2,3),(0,2),(0,),()]:print(s,interval(z,s),shares(z,s),cost(z,s,f))
    assert shares(z,(0,1,2,3))=={i:Q(1,4) for i in range(4)}
    for x,s in [(Q(0),(0,1,2,3)),(Q(1,2),(0,1,2,3)),(Q(3,4),(0,2)),(Q(1),(0,2)),(Q(3,2),(0,)),(Q(2),(0,)),(Q(3),())]:assert eq(z,s,x)
    print('forced B closure:',shares(z,(0,2,3)))
for n in range(3,11):
    M=Matrix(n,n,lambda i,j:int(j==i or j==(i-1)%n)); print('rank',n,M.rank()); assert M.rank()==n-(n%2==0)
# A01: theta rational, F=theta^2/8, t=1, no empty planner optimum.
rng=Random(20261117); count=0; maxratio=0; cases=0
for n in range(2,10):
    for _ in range(120):
        z=tuple([Q(0)]+[Q(i,100) for i in sorted(rng.sample(range(1,100),n-1))]); ss=states(n)
        theta=Q(rng.randint(1,99),100); f=theta*theta/8
        opt=min(cost(z,s,f) for s in ss); es=[s for s in ss if eq(z,s,theta)]; assert es
        for s in es:
            ratio=cost(z,s,f)/opt; count+=1; maxratio=max(maxratio,float(ratio)); assert float(ratio)<=1+1/sqrt(2)+1e-12
        # deletion construction, strict unprofitable departure
        s=tuple(range(n))
        while s and min(shares(z,s).values())<theta/2:
            j=min(shares(z,s),key=shares(z,s).get);s=tuple(i for i in s if i!=j)
        assert eq(z,s,theta);cases+=1
print('A01 cases',cases,'equilibria checked',count,'max observed ratio',maxratio,'bound',1+1/sqrt(2))
# A02 family sufficient condition: exact five-site cases.
count=0
for a0 in range(5,17):
    a=Q(a0,100);b=Q(1,2)-a
    for e0 in range(1,8):
        e=Q(e0,1000);lo=e*(b-e)/2;hi=a*a/2
        if not (e<a and lo<hi):continue
        f=(lo+hi)/2;z=(Q(0),a,2*a,2*a+b,2*a+b+e);ss=states(5)
        assert min(ss,key=lambda s:cost(z,s,f))==(0,1,2,3)
        assert interval(z,(0,1,2,3))[0]>interval(z,(0,1,2,3))[1]
        count+=1
print('A02 nonimplementation family checks',count)
# A02 strengthened count-mismatch/maximin conjectured family, independent exact test.
count=0
for a0 in range(5,17):
    a=Q(a0,100); b=Q(1,2)-a
    for e0 in range(1,8):
        e=Q(e0,1000); lo=(a*a+e*(b-e))/4; hi=a*a/2
        if not (0<e<a and lo<hi):continue
        f=(lo+hi)/2; z=(Q(0),a,2*a,2*a+b,2*a+b+e);ss=states(5)
        feasible=[s for s in ss if (lambda l,h:l is None or h is None or l<=h)(*interval(z,s))]
        best=min(cost(z,s,f) for s in feasible)
        assert [s for s in feasible if cost(z,s,f)==best]==[(0,2,3)]
        theta=b+min(e,a-e)/2; assert [s for s in ss if eq(z,s,theta)]==[(0,2,3)]
        # dominance: all three strictly profitable even when all five stay;
        # B and E strictly unprofitable facing the three remaining firms.
        q=shares(z,tuple(range(5))); assert all(2*q[i]>theta for i in (0,2,3))
        assert all(2*shares(z,tuple(sorted((0,2,3,i))))[i]<theta for i in (1,4))
        count+=1
print('A02 strengthened family checks',count)
# C01: common selection path minimax regret, and pure policy optimum of clustered market.
for x in [Q(51,100),Q(525,1000),Q(54,100)]:
    assert [s for s in states(4) if eq(c,s,x)]==[(0,2),(1,3)]
u_loss=cost(u,(0,2),Q(1,50))-cost(u,(0,1,2,3),Q(1,50))
c_loss=cost(c,(0,1,2,3),Q(1,50))-cost(c,(0,2),Q(1,50))
print('C01 regrets: 2 vs 4 (uniform), 4 vs 2 (cluster)',u_loss,c_loss,'randomized lower bound',u_loss*c_loss/(u_loss+c_loss))

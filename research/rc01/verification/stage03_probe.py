from fractions import Fraction as Q
from itertools import combinations
from random import Random
from collections import Counter
from math import inf

# Exact rational diagnostic of Stage-3 structural hypothesis.
def observations(d):
    n=len(d); allidx=tuple(range(n)); z=[Q(0)]
    for x in d[:-1]: z.append(z[-1]+x)
    data={}
    for k in range(n+1):
        for S in combinations(allidx,k):
            if not S: data[S]=((),Q(2),None); continue
            g=[z[b]-z[a] for a,b in zip(S,S[1:])]+[1+z[S[0]]-z[S[-1]]]
            h=tuple(g[j-1]+g[j] for j in range(k))
            # inactive candidates enter with 2q equal to the length of their containing gap
            steps=[(S[(j+1)%k]-S[j])%n or n for j in range(k)]
            lo=max((g[j] for j in range(k) if steps[j]>1),default=None)
            data[S]=(h,lo,min(h))
    return data

def maxlo(a,b):return max([v for v in (a,b) if v is not None],default=-inf)
def minhi(a,b):return min([v for v in (a,b) if v is not None],default=inf)
def cover(intervals):
    end=-inf
    for l,h in sorted(intervals):
        if l>end:return False
        end=max(end,h)
    return end==inf

def common(a,b):
    return [(l,h,S) for S,(q,lo,hi) in a.items() if q==b[S][0] for l,h in [(maxlo(lo,b[S][1]),minhi(hi,b[S][2]))] if l<=h]

def valid(x,r):
    _,l,h=r;return (l is None or l<=x) and (h is None or x<=h)

def revealing(S,n):
    if not S:return False
    # At near-first departure, a proper subset with both odd/even gaps reveals.
    steps=[(S[(j+1)%len(S)]-S[j])%n or n for j in range(len(S))]
    diff=[sum((-1)**(i%n) for i in range(S[j],S[j]+k)) for j,k in enumerate(steps)]
    return any(diff[j-1]+diff[j] for j in range(len(S)))

rng=Random(20261117); counts=Counter(); subset_tests=0
for n in (4,6,8,10):
    for j in range(24):
        if j<6:
            a=Q(j+1, 8*n); d=tuple(a if i%2==0 else Q(2,n)-a for i in range(n)); label='equal'
        else:
            weights=[rng.randint(1,25) for _ in range(n)]; d=tuple(Q(w,sum(weights)) for w in weights); label='unequal' if len(set(d[i-1]+d[i] for i in range(n)))>1 else 'equal'
        delta=min(d[1::2])/2
        e=tuple(x+(-1)**i*delta for i,x in enumerate(d)); assert min(e)>0
        a,b=observations(d),observations(e); I=tuple(range(n)); assert a[I][0]==b[I][0]
        intervals=common(a,b); assert cover([(l,h) for l,h,S in intervals])==(label=='equal')
        for S in a:
            if S:assert (a[S][0]!=b[S][0])==revealing(S,n)
            subset_tests+=1
        if label=='unequal':
            H=a[I][2]; others=[v-H for v in a[I][0] if v>H]; theta=H+min(min(d),min(others))/2
            eqs=[S for S,r in a.items() if valid(theta,r)]; assert eqs and all(revealing(S,n) for S in eqs)
            assert not any(l<=theta<=h for l,h,S in intervals)
        counts[n,label]+=1
print('pairwise rational tests:',dict(counts)); print('active-subset signal checks:',subset_tests)
print('All-interval cover matches equal shares; unequal shares have a revealing first-exit regime.')
# A concrete unequal 4-site pair: alternating shifts, unequal shares, different cost of all-active.
d=tuple(map(Q,('0.1','0.2','0.3','0.4'))); e=tuple(x+(-1)**i*Q(1,20) for i,x in enumerate(d)); a,b=observations(d),observations(e)
for x in (Q(0),Q(7,20)):
    print('theta',x,'left',[(S,r[0]) for S,r in a.items() if valid(x,r)],'right',[(S,r[0]) for S,r in b.items() if valid(x,r)])
# Secondary economic target: even n with uniform-vs-paired markets, same F.
def realcost(d,S,F):
    if not S:return Q(2)
    n=len(d); g=[sum(d[i%n] for i in range(S[j],S[j]+((S[(j+1)%len(S)]-S[j])%n or n))) for j in range(len(S))]
    return F*len(S)+sum(x*x/4 for x in g)
for n in (4,6,8,10):
    F=Q(1,8*n*(n-1)); a=Q(1,100*n*n); b=Q(2,n)-a
    u=(Q(1,n),)*n; c=(a,b)*(n//2); U=observations(u); C=observations(c); I=tuple(range(n))
    assert a*b/2<F<Q(1,4*n*(n-1))
    assert all(realcost(u,S,F)>realcost(u,I,F) for S in U if S!=I)
    theta=Q(2,n)+a/2; eqs=[S for S,r in C.items() if valid(theta,r)]; assert eqs and all(realcost(c,S,F)<realcost(c,I,F) for S in eqs)
    print('welfare diagnostic',n,'F',F,'probe',theta,'NE',len(eqs),'smallest improvement',min(realcost(c,I,F)-realcost(c,S,F) for S in eqs))

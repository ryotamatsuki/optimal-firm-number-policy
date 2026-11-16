from fractions import Fraction as Q
from itertools import combinations
from sympy import symbols, expand, simplify, Matrix
from math import comb
Z={'U':tuple(map(Q,('0','.25','.5','.75'))),'C':tuple(map(Q,('0','.05','.5','.55')))}
I=tuple(range(4)); sets=[s for k in range(5) for s in combinations(I,k)]
F=Q(1,50); V=Q(2)
def name(s): return ''.join('ABCD'[i] for i in s) or 'empty'
def dist(x,y):
    a=abs(x-y)%1; return min(a,1-a)
def alloc(z,S):
    if not S:return {},Q(0)
    b={Q(0),Q(1)}
    for i in S:b.update((z[i],(z[i]+Q(1,2))%1))
    for i,j in combinations(S,2):
        m=(z[i]+z[j])/2;b.update((m,(m+Q(1,2))%1))
    b=sorted(b); q={i:Q(0) for i in S}; T=Q(0)
    for l,r in zip(b,b[1:]):
        x=(l+r)/2; i=min(S,key=lambda i:dist(x,z[i]))
        assert sum(dist(x,z[j])==dist(x,z[i]) for j in S)==1
        q[i]+=r-l;T+=(r-l)*(dist(l,z[i])+dist(r,z[i]))/2
    assert sum(q.values())==1
    gaps=[(z[S[(k+1)%len(S)]]-z[i])%1 for k,i in enumerate(S)] if len(S)>1 else [Q(1)]
    assert T==sum(d*d/4 for d in gaps)
    assert all(q[i]==(gaps[k-1]+gaps[k])/2 for k,i in enumerate(S))
    return q,T
D={h:{S:alloc(z,S) for S in sets} for h,z in Z.items()}
def cost(h,S):return len(S)*F+D[h][S][1] if S else V
def bounds(h,S):
    q=D[h][S][0]; entry=[2*D[h][tuple(sorted(S+(i,)))][0][i] for i in I if i not in S]
    return max(entry,default=None),min((2*x for x in q.values()),default=None)
def ne(h,x):return [S for S in sets if all(2*D[h][S][0][i]>=x for i in S) and all(2*D[h][tuple(sorted(S+(i,)))][0][i]<=x for i in I if i not in S)]
def select(x):return I if x<=Q(1,2) else (0,2) if x<=1 else (0,) if x<=2 else ()
for h in Z:
    for S in sets:print(h,name(S),bounds(h,S),cost(h,S),D[h][S][0])
    opt=min(cost(h,S) for S in sets);print('OPT',h,opt,[name(S) for S in sets if cost(h,S)==opt])
pts=sorted({x for h in Z for S in sets for x in bounds(h,S) if x is not None}); probe=[pts[0]-1]+pts+[(a+b)/2 for a,b in zip(pts,pts[1:])]+[pts[-1]+1]
for x in sorted(probe):
    s=select(x);a=ne('U',x);b=ne('C',x)
    assert s in a and s in b and D['U'][s][0]==D['C'][s][0]
    print('REGIME',x,','.join(map(name,a)),','.join(map(name,b)),'shared',name(s))
# Robust terminal actions under all pure selections.
assert ne('U',Q(49,100))==ne('C',Q(49,100))==[I]
for h in Z:assert set(ne(h,Q(21,40)))=={(0,2),(1,3)}
opt={h:min(cost(h,S) for S in sets) for h in Z}
a=cost('U',(0,2))-opt['U'];b=cost('C',I)-opt['C'];p=a/(a+b);r=a*b/(a+b)
assert all(cost(h,S)>=cost(h,(0,2)) for h in Z for S in [(0,),()])
assert a*(1-p)==b*p==r
print('REGRET',a,b,p,r,'det',min(a,b))
# Conditional expected demand in symmetric independent mixing.
x=symbols('x'); expected=0
for h in Z:
    for i in I:
        f=0
        for k in range(4):
            for J in combinations(tuple(j for j in I if j!=i),k):
                S=tuple(sorted(J+(i,))); f+=D[h][S][0][i]*x**k*(1-x)**(3-k)
        assert simplify(f-(1-Q(3,2)*x+x*x-Q(1,4)*x**3))==0
        expected=expand(f)
print('SYMMETRIC MIXED conditional share',expected)
for n in range(3,13):
    M=Matrix(n,n,lambda i,j:int(j==i or j==(i-1)%n));assert M.rank()==n-(n%2==0)
print('RANK n=3..12 verified')
print('FORCED B REMOVAL',D['U'][(0,2,3)][0],D['C'][(0,2,3)][0])
print('ALL CHECKS PASS')
# Same antipodal family, fixed-cost sensitivity (diagnostic; not generic geometry).
a,f,t=symbols('a f t', positive=True)
T2=t/8; T3=t*(a**2+(Q(1,2)-a)**2+Q(1,4))/4; T4=t*(a**2+(Q(1,2)-a)**2)/2
assert simplify(T2-T3-t*a*(Q(1,2)-a)/2)==0
assert simplify(T3-T4-t*a*(Q(1,2)-a)/2)==0
for k in (Q(1,4),Q(1,20)):
    print('F/t cutoff at a=',k,':',k*(Q(1,2)-k)/2)
# Symbolic transfer cancellation for fully covered markets.
v,p0,c0,F0,s0,N,T=symbols('v p c F s N T')
assert simplify((v-p0-T)+(p0-c0-N*F0+N*s0)-N*s0-(v-c0-N*F0-T))==0
print('FAMILY AND TRANSFER CHECKS PASS')

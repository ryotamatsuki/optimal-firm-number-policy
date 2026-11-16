from fractions import Fraction as Q
from itertools import combinations
import sympy as sp
z=tuple(map(Q,['0','.12','.24','.62','.63'])); F=Q('.005'); v=Q(2)
sets=[s for k in range(6) for s in combinations(range(5),k)]
name=lambda s: ''.join('ABCDE'[i] for i in s) or 'empty'
def gaps(s):
    if len(s)==1:return [Q(1)]
    return [(z[s[(i+1)%len(s)]]-z[j])%1 for i,j in enumerate(s)]
def demand(i,s):
    s=tuple(sorted(s)); g=gaps(s); k=s.index(i)
    return (g[k-1]+g[k])/2
def cost(s):return F*len(s)+sum(x*x for x in gaps(s))/4 if s else v
def interval(s):
    g=max((2*demand(j,s+(j,)) for j in range(5) if j not in s),default=None)
    h=min((2*demand(i,s) for i in s),default=None)
    return g,h
def eq(s,t):
    return all((2*demand(i,s)>=t if i in s else 2*demand(i,s+(i,))<=t) for i in range(5))
feasible=lambda s: (lambda a,b:a is None or b is None or a<=b)(*interval(s))
# Independent exact nearest-facility allocation by integrating on breakpoints of all piecewise-linear distances.
def direct(s):
    if not s:return {},v
    breaks={Q(0),Q(1)}|{z[i] for i in s}|{(z[i]+Q(1,2))%1 for i in s}
    dist=lambda x,i:min(abs(x-z[i]),1-abs(x-z[i]))
    bs=sorted(breaks)
    for a,b in zip(bs,bs[1:]):
        for i,j in combinations(s,2):
            da=dist(a,i)-dist(a,j);db=dist(b,i)-dist(b,j)
            if da*db<0:breaks.add(a+(b-a)*da/(da-db))
    bs=sorted(breaks);qs={i:Q(0) for i in s};T=Q(0)
    for a,b in zip(bs,bs[1:]):
        mid=(a+b)/2;i=min(s,key=lambda j:dist(mid,j));qs[i]+=b-a
        T+=(b-a)*(dist(a,i)+dist(b,i))/2
    return qs,T+F*len(s)
for s in sets:
    qs,C=direct(s); assert C==cost(s); assert all(q==demand(i,s) for i,q in qs.items())
print('Independent exact direct allocation:',len(sets),'sets, all match')
for n in range(6):
    ss=[s for s in sets if len(s)==n]; fb=min(ss,key=cost); fs=[s for s in ss if feasible(s)]; sb=min(fs,key=cost) if fs else None
    print('count',n,'unrestricted',name(fb),cost(fb),'implementable',name(sb) if sb is not None else None,cost(sb) if sb is not None else None)
print('all four-set intervals:')
for s in sets:
    if len(s)==4:print(name(s),interval(s),cost(s))
bounds=sorted({x for s in sets for x in interval(s) if x is not None}); samples=[bounds[0]-1,bounds[-1]+1]+bounds+[(a+b)/2 for a,b in zip(bounds,bounds[1:])]
assert all(any(eq(s,t) for s in sets) for t in samples)
print('all threshold regimes covered:',len(samples))
for t in map(Q,['.23','.24','.30','.38','.385','.39','.40','.49','.50','.51','.62','1','2']):
    es=[s for s in sets if eq(s,t)]; print('theta',t,[(name(s),str(cost(s))) for s in es])
for t in [Q('.30'),Q('.385')]:
    # iterated strict dominance: scan every remaining possible action profile
    fixed={};changed=True
    while changed:
        changed=False
        for i in range(5):
            if i in fixed:continue
            others=[j for j in range(5) if j!=i and j not in fixed];base=tuple(j for j,x in fixed.items() if x)+(i,)
            vals=[2*demand(i,base+ss)-t for k in range(len(others)+1) for ss in combinations(others,k)]
            if min(vals)>0 or max(vals)<0:
                fixed[i]=min(vals)>0;changed=True; print('dominance',t,'ABCDE'[i],fixed[i],min(vals),max(vals))
    assert len(fixed)==5
    print('unique including mixed',t,name(tuple(sorted(j for j,x in fixed.items() if x))))
fb=min(sets,key=cost); feasible_sets=[s for s in sets if feasible(s)]; sb=min(feasible_sets,key=cost)
print('FB/SB gap',cost(sb)-cost(fb),'cost pct',(cost(sb)/cost(fb)-1)*100)
print('four vs three gain',cost((0,2,3,4))-cost(sb))
p,c,T,k,symF,symS,V=sp.symbols('p c T k F s v'); cs=V-p-T; ps=p-c-k*symF+k*symS;gov=-k*symS
assert sp.simplify(cs+ps+gov-(V-c-T-k*symF))==0
print('symbolic welfare identity PASS')
# Exact fixed-cost intervals (holding t=1 and comparing all nonempty sets; empty benchmark v=2).
def optimal_F_interval(target, candidates):
    low=Q(0);high=None
    n=len(target);T=cost(target)-F*n
    for s in candidates:
        m=len(s);U=cost(s)-F*m
        if n==m:
            assert T<=U
        elif n>m:
            u=(U-T)/(n-m);high=u if high is None else min(high,u)
        else:low=max(low,(T-U)/(m-n))
    return low,high
print('fixed cost FB interval',optimal_F_interval(fb,sets))
print('fixed cost robust SB interval',optimal_F_interval(sb,feasible_sets))

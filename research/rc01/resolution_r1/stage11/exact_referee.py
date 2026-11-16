"""Stage 11 critical re-enumeration from periodic clipped Voronoi cells.
New implementation; no imports from Stage 4/9/10B solvers.
All costs exact Fraction; t=1, v-c=2 in numerical illustration.
"""
from fractions import Fraction as Q
import random

def direct(d):
    n=len(d); z=[Q(0)]
    for a in d[:-1]: z.append(z[-1]+a)
    out={}
    for mask in range(1<<n):
        S=tuple(i for i in range(n) if mask>>i&1)
        if not S: out[S]=((),Q(0)); continue
        copies=sorted((z[i]+k,i) for i in S for k in range(-2,3))
        q={i:Q(0) for i in S}; dist=Q(0)
        for j in range(1,len(copies)-1):
            x,i=copies[j]; l=max(Q(0),(copies[j-1][0]+x)/2); r=min(Q(1),(x+copies[j+1][0])/2)
            if r>l:
                q[i]+=r-l
                dist+=((r-x)*abs(r-x)-(l-x)*abs(l-x))/2
        assert sum(q.values())==1
        out[S]=(tuple(q[i] for i in S),dist)
    return out

def intervals(out,n):
    I={}
    for S,(v,dist) in out.items():
        if not S: I[S]=(Q(2),None); continue
        ent=[]
        for j in set(range(n))-set(S):
            A=tuple(sorted(S+(j,))); ent.append(2*out[A][0][A.index(j)])
        I[S]=(max(ent) if ent else None,min(2*x for x in v))
    return I

def eq(I,x):
    return [S for S,(l,u) in I.items() if (l is None or x>=l) and (u is None or x<=u)]
def sig(out,I,x): return {(S,out[S][0]) for S in eq(I,x)}
def htk(d):
    n=len(d); h=[d[i-1]+d[i] for i in range(n)]
    return min(h),min(max(h[::2]),max(h[1::2])),min(sum(d[(i+j)%n] for j in range(3)) for i in range(n))
def qs(s):return tuple(map(Q,s.split()))
for d in [qs(".1 .2 .3 .4"),qs(".15 .15 .35 .35")]:
    o=direct(d); I=intervals(o,4)
    print('example',d,htk(d),[(x,[(tuple(i+1 for i in S),v) for S,v in sorted(sig(o,I,x))]) for x in map(Q,['.2','.4','.6'])])
d,e=qs(".252 .249 .250 .249"),qs(".052 .449 .050 .449")
o,p=direct(d),direct(e); I,J=intervals(o,4),intervals(p,4)
A=[Q(0)]+[Q(2*j+1,40) for j in range(41)]
F=Q('.02')
def robust(out,I,x,F=F,vc=Q(2)):
    return max(len(S)*F+out[S][1] if S else vc for S in eq(I,x))
u=[robust(o,I,x) for x in A]; c=[robust(p,J,x) for x in A]; mu,mc=min(u),min(c)
reg=list(zip(A,[i-mu for i in u],[i-mc for i in c]))
bestdet=min(max(a,b) for _,a,b in reg)
bestmix=(bestdet,None)
for x,a,b in reg:
    for y,g,h in reg:
        denom=(a-b)-(g-h)
        if denom:
            prob=(h-g)/denom
            if 0<=prob<=1:
                val=max(prob*a+(1-prob)*g,prob*b+(1-prob)*h)
                if val<bestmix[0]:bestmix=(val,(x,y,prob))
print('welfare',mu,mc,bestdet,bestmix,all(sig(o,I,x)&sig(p,J,x) for x in A),not(sig(o,I,Q('.5'))&sig(p,J,Q('.5'))))
random.seed(20261117)
counts={'pairs':0,'thresholds':0,'exists':0,'outside_common':0,'local_disjoint':0,'qualifying_window_disjoint':0,'uniform_pairs':0}
for n,B in [(4,36),(6,24),(8,8)]:
    for j in range(B):
        raw=[random.randint(2,35) for _ in range(n)] if j else [10]*n
        total=sum(raw); delta=Q(random.randint(1,min(raw)-1),total)
        d0=tuple(Q(a,total) for a in raw); e0=tuple(a+(-1)**i*delta for i,a in enumerate(d0))
        H,T,K=htk(d0); _,_,K2=htk(e0); counts['pairs']+=1;counts['uniform_pairs']+=H==T
        o0,p0=direct(d0),direct(e0); I0,J0=intervals(o0,n),intervals(p0,n)
        endpoints=sorted(set([Q(-1),Q(3),H,T,K,K2]+[v for z in [I0,J0] for lim in z.values() for v in lim if v is not None]))
        X=sorted(set(endpoints+[(a+b)/2 for a,b in zip(endpoints,endpoints[1:])]))
        for x in X:
            a,b=sig(o0,I0,x),sig(p0,J0,x);counts['thresholds']+=1;assert a and b;counts['exists']+=1
            if x<=H or x>=T:
                assert a&b; counts['outside_common']+=1
            if H<x<min(T,max(K,K2)):
                assert not a&b;counts['local_disjoint']+=1
            if max(K,K2)>=T and H<x<T:
                assert not a&b;counts['qualifying_window_disjoint']+=1
print(counts)
print('best U',[x for x in A if robust(o,I,x)==mu])
print('best C',[x for x in A if robust(p,J,x)==mc])
print('best det',[x for x,a,b in reg if max(a,b)==bestdet])
for x in [Q(0),Q(19,40),Q(1,2),Q(21,40),Q(3)]:
    print(x,'U',robust(o,I,x),'C',robust(p,J,x))
x,y=qs(".7 .1 .1 .1"),qs(".72 .08 .12 .08")
xo,yo=direct(x),direct(y); xi,yi=intervals(xo,4),intervals(yo,4)
print('interior overlap',[(tuple(i+1 for i in S),v) for S,v in sig(xo,xi,Q('.4'))&sig(yo,yi,Q('.4'))])
print('blind menu costs',[(t,robust(o,I,t),robust(p,J,t)) for t in [Q(0),Q(3)]])
print('strict witness',Q(1,2)*(Q(1,4)-Q(".005"))**2-Q(".02"),Q(".02")-Q(1,2)*(Q(".05")+Q(".005"))*(Q(".45")+Q(".005")))

def alt_cost_shares(d, S, power=1, density=False):
    z=[Q(0)]
    for a in d[:-1]: z.append(z[-1]+a)
    copies=sorted((z[i]+k,i) for i in S for k in range(-2,3))
    q={i:Q(0) for i in S}; dist=Q(0)
    for j in range(1,len(copies)-1):
        x,i=copies[j]; l=max(Q(0),(copies[j-1][0]+x)/2); r=min(Q(1),(x+copies[j+1][0])/2)
        if r>l:
            q[i]+=(r-l if not density else (r-l)/2+(r*r-l*l)/2)
            dist+=((r-x)*abs(r-x)**power-(l-x)*abs(l-x)**power)/(power+1)
    assert sum(q.values())==1
    return tuple(q[i] for i in S),dist
def robust_quad(d,I,x):
    return max(len(S)*F+alt_cost_shares(d,S,2)[1] if S else Q(2) for S in eq(I,x))
quad_u=[robust_quad(d,I,x) for x in A]; quad_c=[robust_quad(e,J,x) for x in A]
print('quad_opt_U',[x for x,v in zip(A,quad_u) if v==min(quad_u)])
print('quad_opt_C',[x for x,v in zip(A,quad_c) if v==min(quad_c)])
print('common optimum',set(x for x,v in zip(A,quad_u) if v==min(quad_u))&set(x for x,v in zip(A,quad_c) if v==min(quad_c)))
print('nonuniform shares',alt_cost_shares(d,tuple(range(4)),density=True)[0],alt_cost_shares(e,tuple(range(4)),density=True)[0])

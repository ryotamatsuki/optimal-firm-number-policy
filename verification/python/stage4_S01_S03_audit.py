from fractions import Fraction as Q
from itertools import combinations,product
import sympy as s
import numpy as np
from scipy.integrate import quad
z=list(map(Q,['0','.12','.24','.62','.63'])); F=Q('.005'); m=Q('.1'); t=Q(1); v=Q(2)
def gaps(S):
 p=sorted(z[i] for i in S); return [p[j+1]-p[j] for j in range(len(p)-1)]+[1+p[0]-p[-1]] if p else []
def share(i,S):
 if len(S)==1:return Q(1)
 p=sorted(S,key=lambda i:z[i]); g=gaps(p); j=p.index(i);return (g[j-1]+g[j])/2
def cost(S):return F*len(S)+sum(d*d for d in gaps(S))/4 if S else v
def bounds(S):
 if not S:return Q(2),None
 H=min(2*share(i,S) for i in S)
 G=max((2*share(i,S|{i}) for i in range(5) if i not in S),default=None)
 return G,H
sets=[frozenset(i for i in range(5) if mask>>i&1) for mask in range(32)]
for S in sorted(sets,key=cost)[:10]: print(''.join('ABCDE'[i] for i in sorted(S)),float(cost(S)),bounds(S))
for theta in [Q('.3'),Q('.24'),Q('.38')]:
 ne=[S for S in sets if all((m*share(i,S)>=m*theta/2 if i in S else m*share(i,S|{i})<=m*theta/2) for i in range(5))]; print('theta',theta,[( ''.join('ABCDE'[i] for i in sorted(S)),float(cost(S))) for S in ne])
# verify threshold conditions all sets, all relevant breakpoints and between
bs=sorted({Q(0),Q(3)}|{2*share(i,S|{i}) for S in sets for i in range(5)}); th=bs+[(a+b)/2 for a,b in zip(bs,bs[1:])]
for S in sets:
 G,H=bounds(S)
 for theta in th:
  a=all((2*share(i,S)>=theta if i in S else 2*share(i,S|{i})<=theta) for i in range(5)); b=(G is None or G<=theta) and (H is None or theta<=H); assert a==b
print('S03 tests',len(sets)*len(th),'theta count',len(th)); print('best implementable',[( ''.join('ABCDE'[i] for i in sorted(S)),float(cost(S)),bounds(S)) for S in sorted(sets,key=cost) if (lambda b:b[0] is None or b[1] is None or b[0]<=b[1])(bounds(S))][:5])
# S01 direct integration using assignment nearest; points break at all pairwise arc midpoints (including opposite)
def rho(x,y):return abs((x-y+.5)%1-.5)
def direct(P,eps=.01,h=.05):
 pts={0.,1.}; p=list(P.values())
 for i,a in enumerate(p):
  pts.add(a);pts.add((a+.5)%1)
  for b in p[i+1:]:pts.add(((a+b)/2)%1);pts.add(((a+b)/2+.5)%1)
 pts=sorted(pts); q=dict.fromkeys(P,0.); T=0.
 f=lambda x:1+eps*np.cos(2*np.pi*(x-h))
 for a,b in zip(pts,pts[1:]):
  if b-a<1e-13:continue
  ds={i:rho((a+b)/2,y) for i,y in P.items()}; best=min(ds.values()); ids=[i for i,d in ds.items() if abs(d-best)<1e-10]; mass=quad(f,a,b)[0]
  for i in ids:q[i]+=mass/len(ids)
  T+=quad(lambda x: f(x)*rho(x,P[ids[0]]),a,b)[0]
 return q,T
P=dict(A=0,B=.25,C=.5,D=.75); QP=dict(P,E=.1); XP={i:y for i,y in QP.items() if i!='A'}
for PP in [P,QP,XP]: print('S01',PP,direct(PP))
q0,T0=direct(P);q1,T1=direct(XP);print('delta W',.003-T1+T0)
# global grid on incumbent continuation with tie allowed; all 4 incumbents sets for 401 locations; direct all assignment for selected corners and grid via gap formulas mass.
def mass(a,b,eps):return b-a+eps/(2*np.pi)*(np.sin(2*np.pi*(b-.05))-np.sin(2*np.pi*(a-.05)))
def qgap(P,eps):
 groups={}
 for i,x in P.items():groups.setdefault(x,[]).append(i)
 loc=sorted(groups); out={};
 if len(loc)==1:return {i:1/len(P) for i in P}
 for j,x in enumerate(loc):
  l=loc[j-1] if j else loc[-1]-1;r=loc[j+1] if j+1<len(loc) else loc[0]+1
  for i in groups[x]:out[i]=mass((l+x)/2,(x+r)/2,eps)/len(groups[x])
 return out
for eps in [0,.000001,.001,.01]:
 best=(-1,None); count=0; multi=0; min_dom=1
 for zz in np.arange(400)/400:
  for a in [0,1]:
   PP={i:x for i,x in P.items() if i!='A' or a}; PP['E']=zz; qq=qgap(PP,eps)
   q_all=qgap(dict(P,E=zz),eps); piA=.5*q_all['A']-.11
   if (a and piA>=-1e-12) or (not a and piA<=1e-12):
    count+=1; pi=.5*qq['E']-.107
    if pi>best[0]+1e-14:best=(pi,zz)
   if abs(piA)<1e-12 and a:multi+=1
   min_dom=min(min_dom,min(.5*q_all[i]-.05 for i in 'BCD'))
  if zz in [0,.1,.25,.5,.75]:
   for a in [0,1]:
    PP={i:x for i,x in P.items() if i!='A' or a};PP['E']=zz
    assert all(abs(qgap(PP,eps)[i]-direct(PP,eps)[0][i])<1e-9 for i in PP)
 print('grid eps',eps,'best',best,'cont',count,'multi',multi,'min_dom',min_dom)
# symbolic identities
D,e,d,h=s.symbols('D e d h',real=True);print('sym',s.simplify(((d+D)**2+(d-D)**2-2*d*d)/4-D**2/2));print('mass',s.trigsimp(s.expand_trig(s.sin(2*s.pi*((D+d)/2-h))-s.sin(2*s.pi*((D-d)/2-h))-2*s.sin(s.pi*d)*s.cos(s.pi*D-2*s.pi*h))))
# Expected-welfare upper bound for any independently mixed Nash profile with positive target probability.
# Conditional on the other players choosing their target actions, B earns share .12, E .19.
# Since conditional target probabilities are >= r=P(target), q_B<=1-.88r and q_E>=.19r.
rmax=1/(1-Q('.12')+Q('.19')); gap=cost(frozenset([0,1,2,4]))-cost(frozenset([0,1,2,3])); print('mixed target prob bound',rmax,float(rmax),'expected loss lower bound',gap*(1-rmax),float(gap*(1-rmax)))
# Welfare loss bound for the entire epsilon interval (density perturbation bound)
print('S01 worst loss bound',Q('.003')-Q('.005')+Q('.01')*(Q('.0625')+Q('.0675')))
print('Pure second best incremental cost',Q('.1016')-Q('.0994'))

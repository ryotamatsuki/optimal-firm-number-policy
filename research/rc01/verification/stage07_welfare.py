from fractions import Fraction as Q
from itertools import combinations
from sympy import symbols,simplify
from math import inf

def model(d,F,V=Q(2)):
 n=len(d); z=[Q(0)]
 for g in d[:-1]:z.append(z[-1]+g)
 subsets=[s for k in range(n+1) for s in combinations(range(n),k)]
 def qs(s):
  if not s:return {},Q(0)
  g=[z[b]-z[a] for a,b in zip(s,s[1:])]+[1+z[s[0]]-z[s[-1]]]
  return {i:(g[j-1]+g[j])/2 for j,i in enumerate(s)},sum(x*x/4 for x in g)
 data={s:qs(s) for s in subsets}; bounds={}; cost={}
 for s,(q,T) in data.items():
  entry=[2*data[tuple(sorted(s+(i,)))][0][i] for i in range(n) if i not in s]
  bounds[s]=(max(entry,default=-inf),min((2*x for x in q.values()),default=inf))
  cost[s]=F*len(s)+T if s else V
 return bounds,cost,data

def audit(n,a,F):
 U=model((Q(1,n),)*n,F); C=model((a,Q(2,n)-a)*(n//2),F)
 pts=sorted({x for B,_,_ in [U,C] for l,h in B.values() for x in (l,h) if x not in (-inf,inf)})
 probes=sorted(pts+[pts[0]-1,pts[-1]+1]+[(x+y)/2 for x,y in zip(pts,pts[1:])])
 rows=[];allcost=[]
 for B,c,D in [U,C]:
  allcost.append([(min(c[s] for s,(l,h) in B.items() if l<=x<=h),max(c[s] for s,(l,h) in B.items() if l<=x<=h),tuple(s for s,(l,h) in B.items() if l<=x<=h)) for x in probes])
 rstar=[min(y[1] for y in A) for A in allcost]; planner=[min(M[1].values()) for M in [U,C]]
 full=[M[1][tuple(range(n))] for M in [U,C]]
 gamma=Q(1,4*n*(n-1))-F;delta=F-a*(Q(2,n)-a)/2
 for j,x in enumerate(probes):
  r=tuple(allcost[i][j][1]-rstar[i] for i in range(2)); rows.append((x,*r)); assert r[0]>=gamma if x>Q(2,n) else r[1]>=delta
 det=min(max(r,s) for _,r,s in rows)
 # convex hull in R^2: maximum of two losses along any line segment, enumerate pairs (2-state minimax diagnostic)
 best=min((max(r,s),x,x,Q(1)) for x,r,s in rows)
 for x,r,s in rows:
  for y,u,v in rows:
   denom=(r-s)-(u-v)
   if denom:
    p=(v-u)/denom
    if 0<=p<=1:
     val=max(p*r+(1-p)*u,p*s+(1-p)*v)
     best=min(best,(val,x,y,p))
 print('N',n,'a',a,'F',F,'probes',len(probes),'planner',planner,'robust',rstar,'full',full,'gamma',gamma,'delta',delta)
 print('det',det,'randomized',best,'lower',min(gamma,delta),gamma*delta/(gamma+delta),'random% U optimum',float(best[0]/rstar[0])*100)
 print('policies attaining Rstar (theta, number of pure NE)',[[(probes[j],len(allcost[i][j][2])) for j in range(len(probes)) if allcost[i][j][1]==rstar[i]] for i in range(2)])
 if n==4:
  for j,x in enumerate(probes):print('regime',x,'U',allcost[0][j][:2],'C',allcost[1][j][:2])
 return len(probes)

if __name__=='__main__':
 v,p,c,t,F,s,k,T=symbols('v p c t F s k T')
 assert simplify((v-p-T)+(p-c-k*F+k*s)-k*s-(v-c-k*F-T))==0
 assert simplify(t*((symbols('a')+symbols('b'))**2-symbols('a')**2-symbols('b')**2)/4-t*symbols('a')*symbols('b')/2)==0
 print('Symbolic accounting and local loss PASS')
 count=audit(4,Q(1,20),Q(1,50))
 for n in (6,8,10):
  a=Q(1,100*n*n);b=Q(2,n)-a;F=Q(1,8*n*(n-1));count+=audit(n,a,F)
 print('total paired policy regimes:',count)

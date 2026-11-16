from fractions import Fraction as Q
from itertools import combinations
Zs={'U':tuple(map(Q,['0','.25','.5','.75'])),'C':tuple(map(Q,['0','.05','.5','.55']))}
F=Q(1,50)
sets=[s for k in range(5) for s in combinations(range(4),k)]
def gap(z,S):
    a=[z[i] for i in S]
    return [b-a for a,b in zip(a,a[1:]+[a[0]+1])] if a else []
def q(z,S,i):
    g=gap(z,S); k=S.index(i)
    return (g[k-1]+g[k])/2
def cost(z,S):
    return F*len(S)+sum(x*x/4 for x in gap(z,S)) if S else Q(2)
def bounds(z,S):
    l=max([2*q(z,tuple(sorted(S+(i,))),i) for i in range(4) if i not in S],default=None)
    h=min([2*q(z,S,i) for i in S],default=None)
    return l,h
def ne(z,theta):
    return [S for S in sets if all(q(z,S,i)>=theta/2 for i in S) and all(q(z,tuple(sorted(S+(i,))),i)<=theta/2 for i in range(4) if i not in S)]
def nm(S):return ''.join('ABCD'[i] for i in S) or 'empty'
for k,z in Zs.items():
    print(k)
    for n in range(5):
        m=min(cost(z,S) for S in sets if len(S)==n)
        print(n,m,[nm(S) for S in sets if len(S)==n and cost(z,S)==m])
    for S in [tuple(range(4)),(0,2),(0,),()]:
        print(nm(S),bounds(z,S),[q(z,S,i) for i in S],cost(z,S))
    print('NE theta=.6',list(map(nm,ne(z,Q(3,5)))))
    print('NE theta=.525',list(map(nm,ne(z,Q(21,40)))))
    print('remove B',[(nm((i,)),q(z,(0,2,3),i)) for i in (0,2,3)])
u=Q(33,200)-Q(57,400); c=Q(73,400)-Q(33,200)
print('loss',u,c,'p four',u/(u+c),'regret',u*c/(u+c))

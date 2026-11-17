"""Recreate manuscript exhibits by independent exact enumeration of four sites."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

BUILD = Path(__file__).resolve().parents[1] / 'build'
BUILD.mkdir(exist_ok=True)
F, V = Q(1,50), Q(2)

def geometry(d, S):
    if not S:
        return (), V
    g = tuple(sum(d[(i+r)%4] for r in range((j-i)%4 or 4))
              for i,j in zip(S,S[1:]+S[:1]))
    q = tuple((g[k-1]+g[k])/2 for k in range(len(g)))
    return q, len(S)*F+sum(x*x for x in g)/4

def equilibria(d, theta):
    out = {}
    for k in range(5):
        for S in combinations(range(4), k):
            q,c = geometry(d,S)
            if any(2*x<theta for x in q):
                continue
            if any(2*geometry(d,tuple(sorted(S+(j,))))[0][tuple(sorted(S+(j,))).index(j)]>theta
                   for j in range(4) if j not in S):
                continue
            out[(S,q)] = c
    assert out
    return out

def bounds(d):
    h = tuple(d[i-1]+d[i] for i in range(4))
    return min(h),min(max(h[::2]),max(h[1::2])),min(sum(d[(i+j)%4] for j in range(3)) for i in range(4))

a,b = tuple(map(Q,('.1','.2','.3','.4'))),tuple(map(Q,('.15','.15','.35','.35')))
full=(0,1,2,3); middle=(0,2,3); high=(1,3)
assert bounds(a)==(Q('.3'),Q('.5'),Q('.6'))
assert bounds(b)==(Q('.3'),Q('.5'),Q('.65'))
shared=tuple(map(Q,('.25','.15','.25','.35')))
for d in (a,b):
    assert list(equilibria(d,Q('.2')))==[(full,shared)]
    assert (high,(Q('.5'),Q('.5'))) in equilibria(d,Q('.6'))
assert list(equilibria(a,Q('.4')))==[(middle,tuple(map(Q,('.35','.30','.35'))))]
assert list(equilibria(b,Q('.4')))==[(middle,tuple(map(Q,('.325','.325','.35'))))]
u,c=tuple(map(Q,('.252','.249','.250','.249'))),tuple(map(Q,('.052','.449','.050','.449')))
A=[Q(0)]+[Q(2*j+1,40) for j in range(41)]
assert bounds(u)[:2]==bounds(c)[:2]==(Q('.499'),Q('.501'))
assert all(equilibria(u,x).keys() & equilibria(c,x).keys() for x in A)
assert not (equilibria(u,Q('.5')).keys() & equilibria(c,Q('.5')).keys())
rows=[(max(equilibria(u,x).values()),max(equilibria(c,x).values())) for x in A]
U,C=map(min,zip(*rows)); r=[(x-U,y-C) for x,y in rows]
det=min(max(x,y) for x,y in r)
mix=det
for (x,y),(z,w) in combinations(r,2):
    den=x-y-z+w
    if den:
        p=(w-z)/den
        if 0<=p<=1: mix=min(mix,max(p*x+(1-p)*z,p*y+(1-p)*w))
assert (U,C,det,mix)==(Q(285003,2000000),Q(330001,2000000),Q(17101,1000000),Q(384755399,39600000000))
# Frozen negative examples: interior overlap without the sufficient condition;
# blind menu with a shared robust optimum. Also check the strict P5 witness.
pair=tuple(tuple(map(Q,d)) for d in (('.7','.1','.1','.1'),('.72','.08','.12','.08')))
assert bounds(pair[0])[:2]==(Q('.2'),Q('.8'))
assert equilibria(pair[0],Q('.4')).keys() & equilibria(pair[1],Q('.4')).keys()
assert all(max(equilibria(d,Q(0)).values())<max(equilibria(d,Q(3)).values()) for d in (a,b))
for x in map(Q,('.3','.5','1','2','2.1')):
    assert equilibria(a,x).keys() & equilibria(b,x).keys()
gamma=Q(1,2)*(Q(1,4)-Q('.005'))**2-F
Delta=F-Q(1,2)*(Q('.05')+Q('.005'))*(Q('.45')+Q('.005'))
assert (gamma,Delta,gamma*Delta/(gamma+Delta))==(Q(801,80000),Q(599,80000),Q(479799,112000000))
print('Exact profile checks and finite-menu regret PASS:',U,C,det,mix)
print('Negative examples and strict P5 witness PASS:',gamma,Delta,gamma*Delta/(gamma+Delta))
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'pdf.fonttype':42})
fig,axs=plt.subplots(2,3,figsize=(6.5,4.1))
for i,d in enumerate((a,b)):
    for j,(S,th) in enumerate(zip((full,middle,high),('0.2','0.4','0.6'))):
        ax=axs[i,j]; ax.set_aspect('equal'); ax.axis('off')
        ax.add_patch(plt.Circle((0,0),1,fill=False,color='#555555',lw=1.1))
        for k in range(4):
            z=math.pi/2-2*math.pi*float(sum(d[:k])); X,Y=math.cos(z),math.sin(z)
            ax.scatter(X,Y,s=48,facecolor='#222222' if k in S else 'white',edgecolor='#222222' if k in S else '#444444',zorder=3)
            ax.text(X*1.24,Y*1.24,str(k+1),ha='center',va='center',fontsize=9)
        ax.set(xlim=(-1.6,1.6),ylim=(-1.48,1.48))
        q,_=geometry(d,S)
        ax.text(0,-1.46,'shares: '+', '.join(f'{float(x):.3f}'.rstrip('0').rstrip('.') for x in q),ha='center',va='top',fontsize=9)
        if i==0: ax.set_title(r'$\theta='+th+'$',pad=1,fontsize=11)
        if j==0: ax.text(-1.55,0,'A' if i==0 else 'B',ha='center',va='center',weight='bold')
fig.subplots_adjust(left=.02,right=.98,top=.94,bottom=.1,wspace=.08,hspace=.3)
fig.text(.5,.018,'Filled: active site     Open: inactive candidate     Shares in increasing label order',ha='center',fontsize=9)
fig.savefig(BUILD/'Fig1.pdf',metadata={'CreationDate':None,'ModDate':None});plt.close(fig)
fig,ax=plt.subplots(figsize=(6.5,1.85));ax.axvspan(.499,.501,facecolor='0.87',edgecolor='0.45',hatch='////',linewidth=.5)
ax.scatter([.475,.525],[0,0],color='#222222',s=40,zorder=3);ax.scatter([.5],[0],marker='x',s=55,color='#333333',zorder=3)
ax.text(.475,.13,'Available',ha='center');ax.text(.525,.13,'Available',ha='center');ax.text(.5,.13,'Additional',ha='center')
ax.text(.5,.35,'Window (.499, .501)',ha='center',va='center',bbox={'facecolor':'white','edgecolor':'none','pad':1.5})
ax.set(xlim=(.45,.55),ylim=(-.2,.46),yticks=[],xticks=[.475,.5,.525],xlabel=r'Participation threshold $\theta$')
ax.set_xticklabels(['.475','.500','.525']);ax.spines[['top','left','right']].set_visible(False)
fig.tight_layout(pad=.35);fig.savefig(BUILD/'Fig2.pdf',metadata={'CreationDate':None,'ModDate':None});plt.close(fig)
summary=[('Known-state optimum (U)',U),('Known-state optimum (C)',C),('Deterministic regret',det),('Randomized regret',mix)]
(BUILD/'summary.tex').write_text('\\begin{tabular}{lrr}\\toprule\nQuantity & Exact value & Decimal \\\\\\midrule\n'+''.join(f'{n} & ${v.numerator}/{v.denominator}$ & {float(v):.7f} \\\\\n' for n,v in summary)+'\\bottomrule\\end{tabular}\n')

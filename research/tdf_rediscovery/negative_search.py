"""Reproduce the two preliminary strict-interior randomized counterexample searches.
These are negative diagnostics only, not proofs of monotonicity.
Requires NumPy. Each search resets its RNG.
"""
import numpy as np

def search(access=False):
    rng=np.random.default_rng(170326)
    for n in range(5 if access else 4,9):
        sets=[tuple(i for i in range(n) if s>>i&1) for s in range(1<<n)]
        found=None
        for _ in range(1500 if access else 1000):
            z=np.r_[0,np.sort(rng.choice(np.arange(1,100),n-1,replace=False))/100]
            lo=[];hi=[];T=[]
            for S in sets:
                if not S:lo.append(2);hi.append(3);T.append(2);continue
                g=np.diff(np.r_[z[list(S)],z[S[0]]+1])
                hi.append(min(g+np.roll(g,1)))
                lo.append(max([g[(np.searchsorted(S,j)-1)%len(S)] for j in range(n) if j not in S],default=-1))
                T.append(sum(g*g)/4)
            thresholds=sorted(set(np.round(lo+hi,8)))
            mids=[(a+b)/2 for a,b in zip(thresholds,thresholds[1:])]
            eqs=[[j for j,(l,h) in enumerate(zip(lo,hi)) if l<x<h] for x in mids]
            for i,(x,es) in enumerate(zip(mids,eqs)):
                if not es:continue
                for y,es2 in zip(mids[i+1:],eqs[i+1:]):
                    if not es2:continue
                    if access:
                        test=min(len(sets[j]) for j in es)>max(len(sets[j]) for j in es2) and min(T[j] for j in es)>max(T[j] for j in es2)+1e-8
                    else:
                        test=max(len(sets[j]) for j in es)<min(len(sets[j]) for j in es2)
                    if test:found=(z,x,[sets[j] for j in es],y,[sets[j] for j in es2]);break
                if found:break
            if found:break
        print(n,'strict all-pure access reversal' if access else 'strict all-pure count reversal',found,flush=True)
        if found:break

if __name__=='__main__':
    search(False)
    search(True)

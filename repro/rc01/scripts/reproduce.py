"""Frozen RC01-R1 reproducibility driver, exact arithmetic via archived originals."""
import csv, hashlib, importlib.util, pathlib, subprocess, sys, zipfile, os
from fractions import Fraction as Q
ROOT=pathlib.Path(__file__).resolve().parents[1]
BUILD=ROOT/'build'; BUILD.mkdir(exist_ok=True)
EXPECTED={'stage04.py':'09041b87e28adc5f770755670fc4dfe9d365d159','stage04.txt':'605b6ff682b38f16d6de813dd75ec4c8d736bcc3','stage04a.py':'cc14df8f4b87827e3c2b9a4be473aa02d28f86e1','stage04a.txt':'57d0a38c8e44fbce9b2d551125eec88f5d33299b','portability.py':'86aa20d15134cc5c7ef065ffb6772d53c6af12c5','portability.txt':'d348b223792fc3efb2321f942c9025c525b5ebb1'}
def gh(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def extract():
    archive=ROOT/'originals.zip'; dest=BUILD/'originals'; dest.mkdir(exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        for name,expected in EXPECTED.items():
            data=z.read('r1/'+name); assert gh(data)==expected,name
            (dest/name).write_bytes(data)
    return dest
def module(path):
    spec=importlib.util.spec_from_file_location('frozen_solver',path); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
def run_exact(src,log,dest):
    out=subprocess.check_output([sys.executable,str(src)],cwd=src.parent)
    dest.write_bytes(out); assert out==log.read_bytes(),f'Log differs: {src.name}'
    print('EXACT LOG MATCH',src.name,gh(out),flush=True)
def main():
    assert sys.version_info[:3]==(3,13,5),sys.version
    import sympy,matplotlib
    assert sympy.__version__=='1.14.0'; assert matplotlib.__version__=='3.10.8'
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib import rcParams
    rcParams.update({'pdf.fonttype':42,'font.family':'DejaVu Sans','font.size':10})
    dest=extract()
    for name in ('stage04','stage04a','portability'):
        run_exact(dest/(name+'.py'),dest/(name+'.txt'),BUILD/(name+'.rerun.txt'))
    m=module(dest/'stage04.py'); F=Q(1,50)
    d=tuple(map(Q,('.252','.249','.250','.249'))); e=tuple(map(Q,('.052','.449','.050','.449')))
    D,I=m.table(d,F); E,J=m.table(e,F); full=tuple(range(4)); assert D[full][0]==E[full][0]
    H,T,K=m.limits(d); assert (H,T)==(Q(499,1000),Q(501,1000))
    rows=[]
    for x in m.A:
        s=m.ne(I,x); r=m.ne(J,x); assert s and r
        common=bool({(a,D[a][0]) for a in s}&{(a,E[a][0]) for a in r}); assert common
        rows.append((x,max(D[a][1] for a in s),max(E[a][1] for a in r),common))
    u=min(r[1] for r in rows); c=min(r[2] for r in rows)
    regrets=[(x,a-u,b-c) for x,a,b,_ in rows]; det=min(max(a,b) for _,a,b in regrets); mix=m.mixopt(regrets)[0]
    assert (u,c,det,mix)==(Q(285003,2000000),Q(330001,2000000),Q(17101,1000000),Q(384755399,39600000000))
    with (BUILD/'welfare.csv').open('w',newline='') as f:
        w=csv.writer(f); w.writerow(['theta','worst_U','worst_C','common_signal']); w.writerows(rows)
    summary=[('H',H),('T',T),('Known-state optimum U',u),('Known-state optimum C',c),('Deterministic regret',det),('Randomized regret',mix)]
    (BUILD/'summary.tex').write_text('\\begin{tabular}{lr}\\hline\nQuantity & Exact value \\\\\n\\hline\n'+''.join(f'{n} & ${v.numerator}/{v.denominator}$ \\\\\n' for n,v in summary)+'\\hline\\end{tabular}\n')
    fig,ax=plt.subplots(figsize=(6,1.8)); ax.axvspan(float(H),float(T),alpha=.3,color='#286b60',label='Identification window'); ax.scatter([float(x) for x in m.A if Q(45,100)<=x<=Q(55,100)],[0]*sum(Q(45,100)<=x<=Q(55,100) for x in m.A),marker='o',label='Feasible thresholds'); ax.scatter([.5],[0],marker='x',color='black',label='Additional revealing threshold'); ax.set(xlim=(.45,.55),ylim=(-.3,.6),yticks=[],xlabel='Policy threshold'); ax.legend(loc='upper center',fontsize=8,frameon=False,ncol=2); fig.tight_layout(); fig.savefig(BUILD/'window.pdf',metadata={'CreationDate':None,'ModDate':None}); plt.close(fig)
    # Additional freeze illustration: correct one-based label output, all pure profiles.
    a=tuple(map(Q,('.1','.2','.3','.4'))); b=tuple(map(Q,('.15','.15','.35','.35')))
    X,IX=m.table(a,F); Y,IY=m.table(b,F); assert X[full][0]==Y[full][0]==tuple(map(Q,('.25','.15','.25','.35')))
    assert m.ne(IX,Q(2,5))==m.ne(IY,Q(2,5))==[(0,2,3)]
    assert X[(0,2,3)][0]==tuple(map(Q,('.35','.30','.35'))); assert Y[(0,2,3)][0]==tuple(map(Q,('.325','.325','.35')))
    assert (1,3) in m.ne(IX,Q(3,5)) and (1,3) in m.ne(IY,Q(3,5))
    print('FROZEN OUTPUTS PASS',det,mix,flush=True)
if __name__=='__main__': main()

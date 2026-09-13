"""Exact projective-chart/Hermite verification of the extracted 4x4 pencil.

A success is a proof; a timeout or non-zero-dimensional chart is NOT evidence
for or against admissibility. Uses rational arithmetic only.
"""
from __future__ import annotations
from pathlib import Path
from itertools import combinations
import argparse,json,time
import sympy as s
ROOT=Path(__file__).resolve().parents[1]

def inertia(H):
    H=s.MutableDenseMatrix(H); pos=neg=zero=0; steps=[]
    while H.rows:
        n=H.rows
        choices=[i for i in range(n) if H[i,i]]
        if choices:
            i=choices[0]; p=H[i,i]; order=[i]+[j for j in range(n) if j!=i]
            H=H.extract(order,order); v=H[1:,0]; p=H[0,0]
            pos+=(1 if p>0 else 0); neg+=(1 if p<0 else 0)
            steps.append({'kind':'one','pivot':str(p),'permutation':order})
            H=H[1:,1:]-v*v.T/p
        else:
            pairs=[(i,j) for i in range(n) for j in range(i+1,n) if H[i,j]]
            if not pairs:
                zero+=n; break
            i,j=pairs[0]; order=[i,j]+[a for a in range(n) if a not in (i,j)]
            H=H.extract(order,order); b=H[0,1]; C=H[2:,:2]
            steps.append({'kind':'two','off_diagonal':str(b),'permutation':order})
            H=H[2:,2:]-C*s.Matrix([[0,1/b],[1/b,0]])*C.T
            pos+=1;neg+=1
    return {'positive':pos,'negative':neg,'zero':zero,'signature':pos-neg,'congruence_steps':steps}

def monomial(xs,e):
    return s.prod(x**a for x,a in zip(xs,e))

def chart(idx):
    started=time.monotonic(); data=json.loads((ROOT/'data/interrupted_pencil.json').read_text())
    xs=s.symbols('x0:5'); Bs=[s.Matrix([[s.Rational(v) for v in row] for row in B]) for B in data['basis']]
    A=sum((x*B for x,B in zip(xs,Bs)),s.zeros(4)); subs={xs[j]:0 for j in range(idx)};subs[xs[idx]]=1
    ys=xs[idx+1:]; M=A.subs(subs)
    equations=list({s.expand(M.extract(I,J).det()) for I in combinations(range(4),3) for J in combinations(range(4),3)})
    equations=[f for f in equations if f!=0]
    result={'chart':idx,'normalization':{str(k):str(v) for k,v in subs.items()},'variables':list(map(str,ys))}
    if not ys:
        result.update({'certified_no_real_points':bool(equations),'reason':'nonzero constant minor' if equations else 'explicit rank-at-most-two point'})
    else:
        G=s.groebner(equations,*ys,order='grevlex',domain=s.QQ)
        result['groebner_basis']=list(map(str,G.polys))
        if any(p.as_expr()==1 for p in G.polys):
            result.update({'certified_no_real_points':True,'reason':'unit ideal'})
        elif not G.is_zero_dimensional:
            result.update({'certified_no_real_points':False,'reason':'method inconclusive: positive-dimensional complex chart'})
        else:
            leading=[p.LM(order=G.order).exponents for p in G.polys]
            def standard(e):return not any(all(a>=b for a,b in zip(e,l)) for l in leading)
            zero=(0,)*len(ys); frontier=[zero]; seen={zero}; exps=[]
            while frontier:
                e=frontier.pop();exps.append(e)
                for j in range(len(ys)):
                    ee=list(e);ee[j]+=1;ee=tuple(ee)
                    if ee not in seen and standard(ee):seen.add(ee);frontier.append(ee)
            exps.sort(key=lambda e:(sum(e),e)); ids={e:i for i,e in enumerate(exps)}; q=len(exps)
            assert q<1000, 'unexpectedly large algebra'
            operators=[]
            for y in ys:
                T=s.zeros(q)
                for j,e in enumerate(exps):
                    rem=G.reduce(y*monomial(ys,e))[1]
                    for f,c in s.Poly(rem,*ys,domain=s.QQ).terms():
                        if c:T[ids[f],j]=c
                operators.append(T)
            mon_ops=[]
            for e in exps:
                T=s.eye(q)
                for U,a in zip(operators,e):
                    if a:T=T*U**a
                mon_ops.append(T)
            H=s.zeros(q)
            for i in range(q):
                for j in range(i,q):
                    v=sum(mon_ops[i][a,b]*mon_ops[j][b,a] for a in range(q) for b in range(q))
                    H[i,j]=H[j,i]=v
            sig=inertia(H)
            result.update({'reason':'Hermite trace-form signature','quotient_dimension':q,
              'standard_monomials':exps,'multiplication_matrices':[[[str(v) for v in U.row(i)] for i in range(q)] for U in operators],
              'trace_form':[[str(v) for v in H.row(i)] for i in range(q)],'inertia':sig,
              'certified_no_real_points':sig['signature']==0})
    result['elapsed_seconds']=time.monotonic()-started
    out=ROOT/f'data/pencil_chart_{idx}.json';out.write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('trace_form','multiplication_matrices','groebner_basis')},indent=2))
    return result['certified_no_real_points']

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--chart',type=int,choices=range(5),required=True); a=p.parse_args()
    raise SystemExit(0 if chart(a.chart) else 2)

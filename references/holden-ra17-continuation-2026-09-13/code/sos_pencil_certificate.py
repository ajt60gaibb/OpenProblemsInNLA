"""Find and then EXACTLY verify a positive Gram-form in the minor ideal.

The numerical SDP only proposes a certificate. The saved certificate is accepted
only after rational ideal-membership and positive-definiteness checks.
"""
from __future__ import annotations
from pathlib import Path
from itertools import combinations,combinations_with_replacement
import argparse,json,time
import sympy as s
ROOT=Path(__file__).resolve().parents[1]

def exponents(n,k):
    out=[]
    for c in combinations_with_replacement(range(n),k):
        v=[0]*n
        for i in c:v[i]+=1
        out.append(tuple(v))
    return out

def monomial(xs,e):return s.prod(x**a for x,a in zip(xs,e))

def positive_definite(G):
    H=s.Matrix(G);piv=[]
    while H.rows:
        p=H[0,0]
        if p<=0:return False,piv
        piv.append(p);v=H[1:,0];H=H[1:,1:]-v*v.T/p
    return True,piv

def input_pencil():
    D=json.loads((ROOT/'data/interrupted_pencil.json').read_text());xs=s.symbols('x0:5')
    Bs=[s.Matrix([[s.Rational(v) for v in row] for row in B]) for B in D['basis']]
    A=sum((x*B for x,B in zip(xs,Bs)),s.zeros(4))
    ijs=list((I,J) for I in combinations(range(4),3) for J in combinations(range(4),3))
    fs=[s.expand(A.extract(I,J).det()) for I,J in ijs]
    return D,xs,A,ijs,fs

def verify(path):
    _,xs,A,ijs,fs=input_pencil();D=json.loads(Path(path).read_text())
    es=[tuple(e) for e in D['monomials']];z=s.Matrix([monomial(xs,e) for e in es])
    G=s.Matrix([[s.Rational(v) for v in row] for row in D['gram']])
    assert G==G.T
    hs=[s.sympify(h,locals={str(x):x for x in xs}) for h in D['multipliers']]
    assert len(hs)==len(fs)
    assert s.expand((z.T*G*z)[0]-sum(h*f for h,f in zip(hs,fs)))==0
    ok,piv=positive_definite(G);assert ok
    assert all(tuple(D['minor_indices'][i][0])==I and tuple(D['minor_indices'][i][1])==J for i,(I,J) in enumerate(ijs))
    return {'status':'EXACTLY_VERIFIED','degree':D['degree'],'gram_dimension':len(es),'positive_pivots':list(map(str,piv))}

def search(degree):
    import numpy as np
    import cvxpy as cp
    start=time.monotonic();_,xs,A,ijs,fs=input_pencil();half=degree//2
    ze=exponents(5,half);oe=exponents(5,degree);me=exponents(5,degree-3);rows={e:i for i,e in enumerate(oe)}
    W=s.zeros(len(oe),len(fs)*len(me))
    for i,f in enumerate(fs):
        terms=s.Poly(f,*xs).terms()
        for j,e in enumerate(me):
            for u,c in terms:
                if c:W[rows[tuple(a+b for a,b in zip(e,u))],i*len(me)+j]+=c
    null=W.T.nullspace();L=s.Matrix.hstack(*null).T if null else s.zeros(0,len(oe))
    pairs=[(i,j) for i in range(len(ze)) for j in range(i,len(ze))]
    Q=s.zeros(len(oe),len(pairs))
    for k,(i,j) in enumerate(pairs):Q[rows[tuple(a+b for a,b in zip(ze[i],ze[j]))],k]=1 if i==j else 2
    D=L*Q; R,piv=D.rref(); free=[j for j in range(len(pairs)) if j not in piv]
    H=cp.Variable((len(ze),len(ze)),symmetric=True);gv=cp.hstack([H[i,j] for i,j in pairs])
    constraints=[H-np.eye(len(ze)) >> 0]
    if D.rows:
        Df=np.asarray(D,dtype=float);Df=Df/np.maximum(np.max(np.abs(Df),axis=1,keepdims=True),1)
        constraints.append(Df@gv==0)
    prob=cp.Problem(cp.Minimize(cp.trace(H)),constraints)
    solvers=cp.installed_solvers();done=False
    for solver in ('CLARABEL','CVXOPT','SCS'):
        if solver not in solvers:continue
        try:
            kw={'solver':solver}
            if solver=='SCS':kw.update({'eps':1e-8,'max_iters':15000})
            if solver=='CLARABEL':kw.update({'time_limit':20.0,'max_iter':200})
            prob.solve(**kw)
            if H.value is not None and prob.status in ('optimal','optimal_inaccurate'):done=True;break
        except Exception:continue
    if not done:raise RuntimeError(f'No candidate Gram matrix; SDP status {prob.status}')
    vals=[float(H.value[i,j]) for i,j in pairs]
    for digits in (6,9,12,15):
        den=10**digits;g=[s.Rational(round(v*den),den) for v in vals]
        for i,p in enumerate(piv):g[p]=-sum(R[i,j]*g[j] for j in free)
        G=s.zeros(len(ze))
        for v,(i,j) in zip(g,pairs):G[i,j]=G[j,i]=v
        ok,_=positive_definite(G)
        if ok:break
    if not ok:raise RuntimeError('Rational recovery did not produce a positive-definite Gram matrix')
    q=Q*s.Matrix(g);_,cols=W.rref();U=W[:,list(cols)]
    alpha,params=U.gauss_jordan_solve(q);assert not params.rows
    full=s.zeros(W.cols,1)
    for j,v in zip(cols,alpha):full[j]=v
    hs=[s.expand(sum(full[i*len(me)+j]*monomial(xs,e) for j,e in enumerate(me))) for i in range(len(fs))]
    obj={'degree':degree,'monomials':ze,'gram':[[str(v) for v in G.row(i)] for i in range(G.rows)],
         'minor_indices':ijs,'multipliers':list(map(str,hs)), 'note':'All final coefficients are rational. SDP output is not itself a certificate.'}
    out=ROOT/f'data/pencil_sos_degree_{degree}.json';out.write_text(json.dumps(obj,indent=2))
    res=verify(out);res['elapsed_seconds']=time.monotonic()-start
    (ROOT/f'data/pencil_sos_degree_{degree}_verified.json').write_text(json.dumps(res,indent=2))
    print(json.dumps(res,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--degree',type=int,choices=(4,6,8),default=4);p.add_argument('--verify')
    a=p.parse_args()
    if a.verify:print(json.dumps(verify(a.verify),indent=2))
    else:search(a.degree)

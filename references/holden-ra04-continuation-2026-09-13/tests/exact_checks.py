#!/usr/bin/env python3
"""Finite rational-arithmetic checks; these are not substitutes for the proofs."""
from __future__ import annotations
import argparse, itertools, json, math
from fractions import Fraction as Q
from pathlib import Path

def eye(n): return [[Q(i==j) for j in range(n)] for i in range(n)]
def transpose(A): return [list(x) for x in zip(*A)]
def mm(A,B):
    BT=transpose(B)
    return [[sum((x*y for x,y in zip(a,b)),Q(0)) for b in BT] for a in A]
def sub(A,B): return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]
def norm2(A): return sum((x*x for a in A for x in a),Q(0))
def rank(A):
    A=[[Q(x) for x in row] for row in A]
    nr=len(A); nc=len(A[0]) if nr else 0; rr=0
    for col in range(nc):
        pivot=next((i for i in range(rr,nr) if A[i][col]),None)
        if pivot is None: continue
        A[rr],A[pivot]=A[pivot],A[rr]
        z=A[rr][col]; A[rr]=[x/z for x in A[rr]]
        for i in range(rr+1,nr):
            z=A[i][col]
            if z: A[i]=[x-z*y for x,y in zip(A[i],A[rr])]
        rr+=1
        if rr==nr: break
    return rr

def inv(A):
    n=len(A); B=[[Q(x) for x in A[i]]+eye(n)[i] for i in range(n)]
    for c in range(n):
        p=next((i for i in range(c,n) if B[i][c]),None)
        if p is None: raise ArithmeticError('singular matrix')
        B[c],B[p]=B[p],B[c]
        z=B[c][c]; B[c]=[x/z for x in B[c]]
        for i in range(n):
            if i!=c:
                z=B[i][c]
                if z: B[i]=[x-z*y for x,y in zip(B[i],B[c])]
    return [row[n:] for row in B]

def krylov(nodes,H,q):
    return [[Q(h)*(Q(x)**j) for j in range(q) for h in row]
            for x,row in zip(nodes,H)]
def product(xs):
    v=Q(1)
    for x in xs:v*=x
    return v

def coloring_checks():
    count=0
    for b in range(1,5):
        for ng in range(1,5):
            for mult in itertools.product(range(1,b+1),repeat=ng):
                rho=sum(mult)
                if rho>12: continue
                loads=[0]*b; nodes=[]; H=[]
                for s,d in enumerate(mult):
                    colors=sorted(range(b),key=lambda j:(loads[j],j))[:d]
                    assert len(set(colors))==d
                    for c in colors:
                        loads[c]+=1; nodes.append(Q(s+1)); H.append([Q(j==c) for j in range(b)])
                    assert max(loads)-min(loads)<=1
                q=(rho+b-1)//b
                assert max(loads)<=q
                assert rank(krylov(nodes,H,q))==rho
                count+=1
    return count

def barycentric_checks():
    examples=[]
    for centers in ([Q(4),Q(1)],[Q(16),Q(4),Q(1)],[Q(10000),Q(100),Q(1)]):
        r=len(centers); b=2; m=r*b; w=Q(1,10**7)
        beta=min(1-centers[s+1]/centers[s] for s in range(r-1))
        nodes=[c*(1+sign*w) for c in centers for sign in (1,-1)]
        baseblocks=[[[1,2],[3,1]],[[2,1],[1,-1]],[[1,3],[2,1]]]
        H=[[Q(x) for x in row] for block in baseblocks[:r] for row in block]
        ds=[product(c-centers[j] for j in range(r) if j!=s) for s,c in enumerate(centers)]
        p=lambda j,x:product(x-centers[l] for l in range(r) if l!=j)
        C=[]; C0=[]
        for i,(x,h) in enumerate(zip(nodes,H)):
            s=i//b; values=[p(j,x)/ds[s] for j in range(r)]
            assert sum((values[j]-Q(j==s))**2 for j in range(r)) <= (2*r*w/beta)**2
            C.append([values[j]*h[a] for j in range(r) for a in range(b)])
            C0.append([Q(j==s)*h[a] for j in range(r) for a in range(b)])
        E=sub(C,C0); R0=inv(C0)
        assert norm2(E)*norm2(R0)<=Q(1,4)
        IR=mm(E,R0)
        J=[[IR[i][j]+Q(i==j) for j in range(m)] for i in range(m)]
        R=mm(R0,inv(J))
        assert mm(C,R)==eye(m)
        Dinv=[[Q(i==j)/ds[i//b] for j in range(m)] for i in range(m)]
        RR=mm(R,Dinv)
        Raw=[[C[i][j]*ds[i//b] for j in range(m)] for i in range(m)]
        assert mm(Raw,RR)==eye(m)
        tailnodes=[Q(1,2),Q(0)]; T=[[Q(1),Q(1)],[Q(2),Q(-1)]]
        Tail=[[p(j,x)*h[a] for j in range(r) for a in range(b)] for x,h in zip(tailnodes,T)]
        F=mm(Tail,RR)
        B=((1+w)/beta)**(r-1)
        for x in (Q(0),Q(1,2),nodes[-1],(1+w)*centers[-1]):
            assert max(abs(p(j,x)) for j in range(r))/min(abs(z) for z in ds)<=B
        rhs=4*r*B**2*norm2(R0)*norm2(T)
        assert norm2(F)<=rhs
        examples.append({'r':r,'b':b,'center_condition_ratio':str(centers[0]/centers[-1]),
                         'width':str(w),'neumann_frobenius_product_squared':str(norm2(E)*norm2(R0)),
                         'graph_frobenius_squared':str(norm2(F)),
                         'deterministic_bound_squared':str(rhs)})
    return examples

def boundary_check():
    nodes=[5,4,3,2,2,2]
    H=[[1,0],[0,1],[1,1],[1,0],[0,1],[1,-1]]
    K2=krylov(nodes,H,2); K3=krylov(nodes,H,3)
    assert rank(K2)==4
    assert rank(K2[3:])==2
    assert rank(K2)-rank(K2[3:])==2
    assert rank(K3)==5
    return {'eigenvalues':nodes,'b':2,'k':4,'rank_K2':4,'rank_K3':5,
            'dimension_K2_intersection_above_cutoff':2,'required_above_cutoff':3}

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default='results/exact_checks.json');args=p.parse_args()
    result={'status':'PASS','arithmetic':'fractions.Fraction',
            'balanced_coloring_cases':coloring_checks(),
            'barycentric_graph_examples':barycentric_checks(),
            'boundary_example':boundary_check(),
            'limits':'Finite checks only; not a proof of unrestricted RA-04.'}
    out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'balanced_coloring_cases':result['balanced_coloring_cases'],
                      'barycentric_graph_examples':len(result['barycentric_graph_examples'])},indent=2))
if __name__=='__main__':main()

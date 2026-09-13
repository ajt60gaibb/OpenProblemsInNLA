#!/usr/bin/env python3
"""Exact Toeplitz Böttcher--Wenzel SOS certificate checker (stdlib only).

No numerical eigensolver, SDP solver, floating-point arithmetic, or optimizer
is used by this verifier. It expands the canonical quartic independently,
checks the polynomial identity, checks exact nullspace identities, and proves
positive semidefiniteness by a rational congruence to a strictly diagonally
dominant positive-diagonal matrix.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import hashlib
import json
import time


def add_product(poly, a: int, b: int, c: int, d: int, value: int) -> None:
    """Add value*x_a*y_b*x_c*y_d to a sparse quartic."""
    if value:
        key = tuple(sorted((a, c))) + tuple(sorted((b, d)))
        poly[key] += value


def add_wedge_product(poly, p, q, value: int) -> None:
    a,b=p; c,d=q
    add_product(poly,a,b,c,d,value)
    add_product(poly,a,b,d,c,-value)
    add_product(poly,b,a,c,d,-value)
    add_product(poly,b,a,d,c,value)


def canonical_polynomial(n: int):
    """Expand 2||X||²||Y||²-2<tr X^T Y>²-||XY-YX||² directly."""
    labels=list(range(1-n,n)); w={a:n-abs(a) for a in labels}
    p=defaultdict(int)
    for a in labels:
        for b in labels:
            add_product(p,a,b,a,b,2*w[a]*w[b])
            add_product(p,a,a,b,b,-2*w[a]*w[b])
    for i in range(n):
        for j in range(n):
            comm=defaultdict(int)
            for k in range(n):
                comm[i-k,k-j]+=1
                comm[k-j,i-k]-=1
            terms=[(a,b,c) for (a,b),c in comm.items() if c]
            for a,b,c in terms:
                for d,e,f in terms:
                    add_product(p,a,b,d,e,-c*f)
    return {key:v for key,v in p.items() if v}


def gram_from_certificate(data):
    n=data['n']; D=data['gram_denominator']
    assert isinstance(n,int) and n>=2
    assert isinstance(D,int) and D>0
    labels=[a for a in range(1-n,n) if a]
    pairs=list(combinations(labels,2)); position={p:i for i,p in enumerate(pairs)}
    size=len(pairs)
    Q=[[0]*size for _ in range(size)]
    for h,(a,b) in enumerate(pairs):
        Q[h][h]=2*(n-abs(a))*(n-abs(b))*D
    # Independently assemble the commutator's linear map in wedge coordinates.
    for i in range(n):
        for j in range(n):
            c=defaultdict(int)
            for k in range(n):
                a,b=i-k,k-j
                if a and b and a!=b:
                    if a<b:c[position[a,b]]+=1
                    else:c[position[b,a]]-=1
            c={h:v for h,v in c.items() if v}
            for h,v in c.items():
                for l,w in c.items():Q[h][l]-=D*v*w
    seen=set()
    for a,b,c,d,t in data['plucker_coefficients']:
        assert a<b<c<d and all(v in labels for v in (a,b,c,d))
        assert (a,b,c,d) not in seen
        seen.add((a,b,c,d))
        assert isinstance(t,int)
        for p,q,s in [((a,b),(c,d),1),((a,c),(b,d),-1),((a,d),(b,c),1)]:
            h,l=position[p],position[q]
            Q[h][l]+=s*t;Q[l][h]+=s*t
    assert all(Q[i][j]==Q[j][i] for i in range(size) for j in range(size))
    return pairs,Q


def check_polynomial(n: int,D: int,pairs,Q):
    represented=defaultdict(int)
    # Restore the central-coordinate squares omitted from the Gram matrix.
    for a in range(1-n,n):
        if a:add_wedge_product(represented,(0,a),(0,a),2*n*(n-abs(a))*D)
    for i,p in enumerate(pairs):
        for j,q in enumerate(pairs):
            if Q[i][j]:add_wedge_product(represented,p,q,Q[i][j])
    represented={k:v for k,v in represented.items() if v}
    target={k:D*v for k,v in canonical_polynomial(n).items()}
    if represented!=target:
        keys=represented.keys()|target.keys()
        bad=[(k,represented.get(k,0)-target.get(k,0)) for k in keys
             if represented.get(k,0)!=target.get(k,0)]
        raise AssertionError(f'Canonical coefficient mismatch: {bad[:5]}')
    return len(target)


def check_psd(data,pairs,Q):
    n=data['n'];size=len(pairs);covered=set();columns=[];groups=[]
    for k in range(n-1):
        group=[i for i,(a,b) in enumerate(pairs) if b-a==2*(n-1)-k]
        assert group
        groups.append(group);covered.update(group)
        # Q times the indicator of this group must be exactly zero.
        assert all(sum(Q[i][j] for j in group)==0 for i in range(size)), 'kernel identity'
        for i in group[1:]:columns.append([(i,1),(group[0],-1)])
    for i in range(size):
        if i not in covered:columns.append([(i,1)])
    h=len(columns)
    assert h==data['complement_dimension']==size-(n-1)
    # These difference vectors plus the disjoint group indicators span R^size.
    G=[[sum(si*sj*Q[a][b] for a,si in ci for b,sj in cj)
        for cj in columns] for ci in columns]
    T=data['congruence_numerators']
    assert isinstance(data['congruence_denominator'],int) and data['congruence_denominator']>0
    assert len(T)==h and all(len(row)==h for row in T)
    assert all(isinstance(v,int) for row in T for v in row)
    tcols=[[(k,T[k][j]) for k in range(h) if T[k][j]] for j in range(h)]
    GT=[[sum(G[i][k]*v for k,v in col) for col in tcols] for i in range(h)]
    H=[[sum(v*GT[k][j] for k,v in col) for j in range(h)] for col in tcols]
    assert all(H[i][j]==H[j][i] for i in range(h) for j in range(h))
    margins=[H[i][i]-sum(abs(H[i][j]) for j in range(h) if j!=i) for i in range(h)]
    assert min(margins)>0, 'strict diagonal dominance'
    assert min(margins)==int(data['integer_diagonal_dominance_minimum'])
    return h,min(margins)


def verify(path:Path):
    start=time.perf_counter();raw=path.read_bytes();data=json.loads(raw)
    assert data['schema']=='toeplitz-bw-sos-rational-v1'
    pairs,Q=gram_from_certificate(data)
    count=check_polynomial(data['n'],data['gram_denominator'],pairs,Q)
    rank,margin=check_psd(data,pairs,Q)
    return {'n':data['n'],'result':'PASS','exact_quartic_monomials':count,
            'noncentral_gram_dimension':len(pairs),'noncentral_gram_rank':rank,
            'positive_integer_margin':str(margin),'sha256':hashlib.sha256(raw).hexdigest(),
            'elapsed_seconds':round(time.perf_counter()-start,4)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificates',nargs='*',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    paths=args.certificates or sorted((Path(__file__).parent/'certificates').glob('n*.json'))
    if not paths:parser.error('No certificate files supplied or found.')
    results=[]
    for path in paths:
        result=verify(path);results.append(result);print(json.dumps(result),flush=True)
    if args.output:args.output.write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()

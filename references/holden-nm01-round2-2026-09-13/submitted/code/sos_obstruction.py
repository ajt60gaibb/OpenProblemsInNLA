#!/usr/bin/env python3
"""Exact rational certificates obstructing bounded-degree SOS preorderings.

No numerical optimization is used. This does NOT solve NM-01. It checks a
separating linear functional for one explicitly specified relaxation.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from math import prod
from typing import Any
import argparse, json, time
from exact_baseline import inverse, determinant, matmul, matrix, transpose, rank, rational


def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), F(0))


def rational_contact(t: F) -> list[F]:
    den=t*t-t+1
    return [(t*t-t)/den,t/den,(1-t)/den]


def contact_family(count: int) -> list[list[F]]:
    if count < 4:
        raise ValueError('At least four contacts are required.')
    extra=count-3
    vs=[[F(i==j) for i in range(3)] for j in range(3)]
    vs += [rational_contact(F(1,3)+F(j,3*(extra+1)))
           for j in range(1,extra+1)]
    return vs


def primal_vertices(normals: list[list[F]]) -> list[list[F]]:
    """Return columns as a list of vectors; rank-three polytope only."""
    out=[]
    for a,b in combinations(normals,2):
        A=[[F(1)]*3,a,b]
        if determinant(A)==0:
            continue
        x=[row[0] for row in inverse(A)]
        if all(dot(v,x)>=0 for v in normals) and x not in out:
            out.append(x)
    if not out or rank(transpose(out)) != 3:
        raise ValueError('Degenerate primal polytope.')
    return out


def quotient_basis(point: list[F], k: int) -> list[F]:
    """Basis 1,x,...,x^k,y,xy,...,x^(k-1)y on a nondegenerate circle."""
    x,y=point[:2]
    return [x**j for j in range(k+1)]+[x**j*y for j in range(k)]


def pd_pivots(a: list[list[F]]) -> list[F]:
    """Exact LDL pivots: successful return certifies positive definiteness."""
    if any(len(row)!=len(a) for row in a):
        raise ValueError('Square matrix required.')
    if any(a[i][j]!=a[j][i] for i in range(len(a)) for j in range(len(a))):
        raise ValueError('Symmetry check failed.')
    b=[row[:] for row in a]; piv=[]
    for i in range(len(b)):
        p=b[i][i]
        if p<=0:
            raise ValueError(f'Nonpositive LDL pivot {i}: {p}')
        piv.append(p)
        for j in range(i+1,len(b)):
            for k in range(j,len(b)):
                b[j][k]-=b[j][i]*b[i][k]/p
                b[k][j]=b[j][k]
    return piv


def rational_json(x: Any):
    if isinstance(x,F): return str(x)
    if isinstance(x,list): return [rational_json(v) for v in x]
    if isinstance(x,tuple): return [rational_json(v) for v in x]
    if isinstance(x,dict): return {str(k):rational_json(v) for k,v in x.items()}
    return x


def make_instance(degree: int=4, eta: F=F(1,2**32), epsilon: F=F(1,2**40)):
    if not isinstance(degree,int) or isinstance(degree,bool) or degree<2:
        raise ValueError('Integer degree at least two required.')
    if not F(0)<eta<1 or not F(0)<=epsilon<1:
        raise ValueError('Require 0<eta<1 and 0<=epsilon<1.')
    vs=contact_family(2*degree+1)
    c=[F(1,3)]*3
    normals=vs[:3]+[[(1-epsilon)*x+epsilon*y for x,y in zip(v,c)] for v in vs[3:]]
    hs=primal_vertices(normals)
    ys=[[a+(1+eta)*(b-a) for a,b in zip(c,v)] for v in vs]
    return {'schema':'nm01-sos-obstruction-v1','degree':degree,
            'eta':eta,'epsilon':epsilon,'contacts':vs,
            'dual_vertices':normals,'H':transpose(hs),
            'evaluation_points':ys,'weights':[F(1,len(vs))]*len(vs)}


def verify_certificate(data: dict[str,Any], include_pivots: bool=False) -> dict:
    degree=data['degree']
    if not isinstance(degree,int) or isinstance(degree,bool) or not 2<=degree<=8:
        raise ValueError('Verifier supports integer degree 2 through 8.')
    eta=rational(data['eta']); epsilon=rational(data['epsilon'])
    expected=make_instance(degree,eta,epsilon)
    for key in ('contacts','dual_vertices','H','evaluation_points'):
        if matrix(data[key])!=expected[key]:
            raise ValueError(f'Incorrect {key}.')
    weights=[rational(v) for v in data['weights']]
    if weights!=expected['weights']:
        raise ValueError('Incorrect weights.')
    vs=expected['contacts']; ns=expected['dual_vertices']; hs=transpose(expected['H'])
    ys=expected['evaluation_points']; M=len(vs); n=len(hs)
    if M!=2*degree+1 or n!=M:
        raise ValueError('Unexpected contact or facet count.')
    if any(sum(h)!=1 or min(h)<0 for h in hs):
        raise ValueError('H is not normalized and nonnegative.')
    if any(sum(q)!=1 or dot(q,q)!=1 for q in vs):
        raise ValueError('Bad sphere contacts.')
    if len({tuple(q) for q in vs})!=M:
        raise ValueError('Repeated contacts.')
    if epsilon>0 and any(dot(q,q)>=1 for q in ns[3:]):
        raise ValueError('Extra vertices are not strictly interior to the ball.')
    # Every dual vertex is exposed: its active input columns span rank 2.
    for q in ns:
        tight=[h for h in hs if dot(q,h)==0]
        if len(tight)!=2 or rank(tight)!=2 or any(dot(q,h)<0 for h in hs):
            raise ValueError('Dual vertex/facet incidence check failed.')
    c=[F(1,3)]*3
    radius2=F(2,3)*(1+eta)**2
    if any(sum(y)!=1 or dot([y[i]-c[i] for i in range(3)],
                           [y[i]-c[i] for i in range(3)])!=radius2 for y in ys):
        raise ValueError('Expanded-circle identity failed.')
    lf=sum((w*(1-dot(y,y)) for w,y in zip(weights,ys)),F(0))
    if lf>=0:
        raise ValueError('The functional does not separate the target.')
    slack=[[dot(h,y) for h in hs] for y in ys]
    basis={k:[quotient_basis(y,k) for y in ys] for k in range(degree//2+1)}
    count=0; least=None; details=[]
    for t in range(min(degree,n)+1):
        k=(degree-t)//2; b=basis[k]; dim=2*k+1
        for ids in combinations(range(n),t):
            w=[weights[i]*prod(slack[i][j] for j in ids) for i in range(M)]
            gram=[[sum((w[l]*b[l][i]*b[l][j] for l in range(M)),F(0))
                   for j in range(dim)] for i in range(dim)]
            try:
                piv=pd_pivots(gram)
            except ValueError as exc:
                raise ValueError(f'Localizing matrix {ids}: {exc}') from exc
            least=min(piv) if least is None else min(least,*piv)
            if include_pivots:
                details.append({'subset':list(ids),'basis_degree':k,
                                'ldl_pivots':piv})
            count+=1
    result={'accepted':True,'total_degree':degree,'rank':3,'columns':n,
            'ssc_convention':'strong' if epsilon>0 else 'weak',
            'localizing_matrices_checked':count,'functional_target_value':lf,
            'smallest_ldl_pivot':least,
            'claim':'No degree-D full-preordering certificate for 1-||q||^2 using the H-column inequalities.'}
    if include_pivots: result['localizing_checks']=details
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--degree',type=int,default=4)
    p.add_argument('--eta-bits',type=int,default=32)
    p.add_argument('--epsilon-bits',type=int,default=40)
    p.add_argument('--generate',type=Path)
    p.add_argument('--verify',type=Path)
    p.add_argument('--report',type=Path)
    p.add_argument('--pivots',action='store_true')
    args=p.parse_args(); start=time.monotonic()
    if args.verify:
        data=json.loads(args.verify.read_text())
    else:
        data=make_instance(args.degree,F(1,2**args.eta_bits),F(1,2**args.epsilon_bits))
    report=verify_certificate(data,args.pivots)
    report['elapsed_seconds']=round(time.monotonic()-start,3)
    if args.generate:
        args.generate.write_text(json.dumps(rational_json(data),indent=2)+'\n')
    if args.report:
        args.report.write_text(json.dumps(rational_json(report),indent=2)+'\n')
    brief={k:v for k,v in report.items() if k!='localizing_checks'}
    print(json.dumps(rational_json(brief),indent=2))

if __name__=='__main__': main()

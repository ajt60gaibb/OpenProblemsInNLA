#!/usr/bin/env python3
"""Exact finite-case spread certificates after the signed-threshold reduction.

Float eigensolvers suggest rational bounds only; integer coefficient tests certify
those bounds. Every enumerated characteristic polynomial is computed using exact
int64 arithmetic under a checked overflow bound. The verifier regenerates the full
candidate family, not just a random sample.
"""
from __future__ import annotations
import argparse, hashlib, json, math, time
from pathlib import Path
import numpy as np


def integer_safety_bound(n: int, max_entry: int) -> int:
    # Newton-identity sums: |c_{k-i} tr(A^i)| <=
    # n * binom(n,k-i) * (n*b)^k; k<=n.
    return n * (2**n) * (n * max_entry)**n


def patterns(n: int, low: int, high: int, batch: int = 2048):
    """S_ij = d_i d_j eps_min(i,j), with d_0=1, including all eps,d."""
    total = 1 << (2*n-1)
    idx = np.minimum.outer(np.arange(n), np.arange(n))
    shifts = np.arange(n, dtype=np.uint64)
    for start in range(0, total, batch):
        ids = np.arange(start, min(start+batch,total), dtype=np.uint64)
        ecode = ids >> np.uint64(n-1)
        eps = 1 - 2*((ecode[:, None] >> shifts) & 1).astype(np.int64)
        d = np.ones((len(ids),n), dtype=np.int64)
        if n>1:
            d[:,1:] = 1-2*((ids[:,None] >> shifts[:n-1]) & 1).astype(np.int64)
        S=eps[:,idx]*d[:,:,None]*d[:,None,:]
        A=np.where(S>0,high,low).astype(np.int64)
        yield ids,A


def charpolys(A: np.ndarray) -> np.ndarray:
    """Newton identities for det(xI-A), in descending coefficient order."""
    count,n,_=A.shape
    C=np.zeros((count,n+1),dtype=np.int64); C[:,0]=1
    traces=np.empty((count,n),dtype=np.int64)
    power=A.copy()
    for k in range(1,n+1):
        traces[:,k-1]=np.trace(power,axis1=1,axis2=2)
        sums=np.zeros(count,dtype=np.int64)
        for i in range(1,k+1):
            sums += C[:,k-i]*traces[:,i-1]
        if np.any(sums % k):
            raise ArithmeticError('Newton identity divisibility failure')
        C[:,k]=-(sums//k)
        if k<n: power=power@A
    return C


def direct_charpoly(A: list[list[int]]) -> tuple[int,...]:
    """Independent scalar Python-integer Faddeev-LeVerrier implementation."""
    n=len(A)
    B=[[int(i==j) for j in range(n)] for i in range(n)]
    cs=[1]
    for k in range(1,n+1):
        AB=[[sum(A[i][r]*B[r][j] for r in range(n)) for j in range(n)] for i in range(n)]
        trace=sum(AB[i][i] for i in range(n))
        if trace % k: raise ArithmeticError('nonintegral characteristic coefficient')
        c=-trace//k;cs.append(c)
        for i in range(n):AB[i][i]+=c
        B=AB
    return tuple(cs)


def shifted_nonnegative(c: tuple[int,...], h: int, q: int) -> bool:
    """All coefficients of q^n p((x+h)/q) are nonnegative.

    The leading coefficient is 1, so the polynomial is strictly positive for
    x>0. Consequently p has no real root larger than h/q.
    """
    if q<=0 or c[0]!=1: raise ValueError('invalid certificate')
    b=[1];qpow=1
    for cj in c[1:]:
        qpow*=q
        new=[h*b[0]+cj*qpow]
        for j in range(1,len(b)):new.append(h*b[j]+b[j-1])
        new.append(b[-1]);b=new
    return all(x>=0 for x in b)


def negated_polynomial(c: tuple[int,...]) -> tuple[int,...]:
    return tuple((-1)**j*x for j,x in enumerate(c))


def polynomial_digest(coeffs):
    h=hashlib.sha256()
    for c in sorted(coeffs):h.update((','.join(map(str,c))+'\n').encode())
    return h.hexdigest()


def enumerate_polynomials(n, low, high, batch=2048, verbose=True):
    bound=integer_safety_bound(n,max(abs(low),abs(high)))
    if bound>=2**63:raise ValueError(f'Overflow not excluded: {bound}')
    data={}; start_time=time.monotonic();checked=0
    for ids,A in patterns(n,low,high,batch):
        C=charpolys(A)
        for j,row in enumerate(C):
            c=tuple(map(int,row))
            if c not in data:data[c]=(int(ids[j]),A[j].copy())
        # Every batch gets an independent arbitrary-precision scalar cross-check.
        j=(int(ids[0])//batch) % len(ids)
        if direct_charpoly(A[j].tolist())!=tuple(map(int,C[j])):
            raise ArithmeticError('Independent characteristic polynomial mismatch')
        checked+=len(ids)
        if verbose and (checked % (batch*32)==0 or checked==(1<<(2*n-1))):
            print(f'n={n}: {checked} patterns; {len(data)} distinct polynomials; '
                  f'{time.monotonic()-start_time:.1f}s',flush=True)
    return data,bound


def generate(n,low,high,out):
    if n < 2 or high <= 0 or low >= high:
        raise ValueError("Require n>=2 and integer endpoints low<high with high>0")
    start=time.monotonic()
    # low/high specifies an integer scaling of the normalized interval.
    # Candidate has k low rows in its upper-left block, all other entries high.
    best=-1; bestk=[]
    for k in range(1,n):
        F=(low*k-high*(n-k))**2+4*high**2*k*(n-k)
        if F>best: best=F;bestk=[k]
        elif F==best:bestk.append(k)
    data,bound=enumerate_polynomials(n,low,high)
    certificates=[];failures=[];counts={'rank_two':0,'rational_enclosure':0}
    for c,(pid,A) in sorted(data.items()):
        # Exactly two nonzero roots of opposite sign, and n-2 roots at zero.
        if all(x==0 for x in c[3:]) and c[2]<0:
            g2=c[1]**2-4*c[2]
            if g2<=best:
                certificates.append({'coefficients':c,'pattern':pid,'kind':'rank_two','gap_squared':g2})
                counts['rank_two']+=1
                continue
        eig=np.linalg.eigvalsh(A.astype(float))
        ok=False
        for q in (10**4,10**6,10**8,10**10):
            upper=math.ceil(float(eig[-1])*q)+3
            negupper=math.ceil(float(-eig[0])*q)+3
            width=upper+negupper
            if width<0 or width*width>best*q*q:continue
            if shifted_nonnegative(c,upper,q) and shifted_nonnegative(negated_polynomial(c),negupper,q):
                certificates.append({'coefficients':c,'pattern':pid,'kind':'rational_enclosure',
                    'q':q,'upper':upper,'negative_upper':negupper})
                counts['rational_enclosure']+=1;ok=True;break
        if not ok:failures.append({'coefficients':c,'pattern':pid,'numerical_gap':float(eig[-1]-eig[0])})
    payload={'schema':'spread-exact-v1','n':n,'low':low,'high':high,
        'pattern_count':1<<(2*n-1),'distinct_polynomial_count':len(data),
        'polynomial_sha256':polynomial_digest(data),'integer_safety_bound':bound,
        'maximum_spread_squared':best,'maximizing_block_sizes':bestk,
        'certificate_counts':counts,'certificates':certificates,'failures':failures,
        'generation_seconds':time.monotonic()-start,
        'claim':'EXACT_FINITE_CASE' if not failures else 'INCOMPLETE_DO_NOT_CLAIM_PROOF'}
    Path(out).parent.mkdir(parents=True,exist_ok=True)
    Path(out).write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('certificates','failures')},indent=2))
    print('failures:',len(failures),flush=True)
    return not failures


def verify(path, coverage=True):
    p=json.loads(Path(path).read_text())
    if p['schema']!='spread-exact-v1' or p['failures'] or p['claim']!='EXACT_FINITE_CASE':
        raise ValueError('Incomplete or unknown certificate')
    n,lo,hi=p['n'],p['low'],p['high'];best=p['maximum_spread_squared']
    if n < 2 or hi <= 0 or lo >= hi:
        raise ValueError('Invalid case parameters')
    best_actual=max((lo*k-hi*(n-k))**2+4*hi*hi*k*(n-k) for k in range(1,n))
    if best!=best_actual:raise ValueError('Candidate bound mismatch')
    seen=set()
    for item in p['certificates']:
        c=tuple(item['coefficients'])
        if len(c)!=n+1 or c[0]!=1 or c in seen:raise ValueError('Bad polynomial')
        seen.add(c)
        if item['kind']=='rank_two':
            if not(all(v==0 for v in c[3:]) and c[2]<0):raise ValueError('Not two opposite roots')
            if c[1]**2-4*c[2]>best:raise ValueError('Too-large quadratic spread')
            if item['gap_squared']!=c[1]**2-4*c[2]:raise ValueError('Quadratic metadata mismatch')
        elif item['kind']=='rational_enclosure':
            q=item['q'];u=item['upper'];v=item['negative_upper']
            if q<=0 or u+v<0 or (u+v)**2>best*q*q:raise ValueError('Bad width')
            if not shifted_nonnegative(c,u,q):raise ValueError('Upper-root certificate failure')
            if not shifted_nonnegative(negated_polynomial(c),v,q):raise ValueError('Lower-root certificate failure')
        else:raise ValueError('Unknown certificate kind')
    if len(seen)!=p['distinct_polynomial_count'] or polynomial_digest(seen)!=p['polynomial_sha256']:
        raise ValueError('Certificate index mismatch')
    if coverage:
        actual,bound=enumerate_polynomials(n,lo,hi)
        if p['pattern_count']!=1<<(2*n-1) or set(actual)!=seen:
            raise ValueError('Coverage mismatch')
        if bound!=p['integer_safety_bound']:raise ValueError('Overflow-bound mismatch')
    print(f'PASS: n={n}, entries={{{lo},{hi}}}, {len(seen)} polynomials, '
          f'{p["pattern_count"]} patterns, spread^2 <= {best}; '
          f'full coverage={coverage}',flush=True)


def main():
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='command',required=True)
    g=sub.add_parser('generate');g.add_argument('--n',type=int,required=True)
    g.add_argument('--low',type=int,required=True);g.add_argument('--high',type=int,required=True)
    g.add_argument('--out',required=True)
    v=sub.add_parser('verify');v.add_argument('path');v.add_argument('--certificates-only',action='store_true')
    args=ap.parse_args()
    if args.command=='generate':
        if not generate(args.n,args.low,args.high,args.out):raise SystemExit(2)
    else:verify(args.path,not args.certificates_only)

if __name__=='__main__':main()

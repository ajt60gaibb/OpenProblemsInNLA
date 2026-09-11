"""Exploratory exact search for IV-01; no resolution is asserted.

Searches boundary strata of sign-regular 5x5 matrices and tests sparse
checkerboard directions. Every reported counterexample is rechecked by
all minors at both checkerboard corners and at a violating box member.
This is exploratory code, not part of the seven proof certificates.
"""
from __future__ import annotations
import argparse, datetime, itertools, json, math, random, time
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
N=5
SUBSETS={k:list(itertools.combinations(range(N),k)) for k in range(N+1)}
INDICES=[(I,J) for k in range(N+1) for I in SUBSETS[k] for J in SUBSETS[k]]


def determinant(A):
    n=len(A)
    if n==0:return 1
    B=[list(r) for r in A]; sign=1; prior=1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if B[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:B[k],B[pivot]=B[pivot],B[k];sign=-sign
        p=B[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                value=B[i][j]*p-B[i][k]*B[k][j]
                assert value%prior==0
                B[i][j]=value//prior
            B[i][k]=0
        prior=p
    return sign*B[-1][-1]


def minors(A):
    return {(I,J):determinant([[A[i][j] for j in J] for i in I])
            for I,J in INDICES}


def signature(data):
    result=[]
    for k in range(1,N+1):
        ss={1 if data[I,J]>0 else -1 for I in SUBSETS[k] for J in SUBSETS[k]
            if data[I,J]!=0}
        if len(ss)!=1:return None
        result.append(next(iter(ss)))
    return tuple(result)


def gradient(data,I,J,i,j):
    if i not in I or j not in J:return 0
    r,c=I.index(i),J.index(j)
    return (-1)**(r+c)*data[I[:r]+I[r+1:],J[:c]+J[c+1:]]


def normalize(A):
    g=0
    for row in A:
        for a in row:g=math.gcd(g,abs(a))
    return [[a//max(g,1) for a in row] for row in A]


def shifted(A,position,t):
    i,j=position
    B=[[a*t.denominator for a in row] for row in A]
    B[i][j]+=t.numerator
    return normalize(B)


def boundaries(A,data,sig):
    candidates=[]
    for i in range(N):
        for j in range(N):
            lower=upper=None
            for I,J in INDICES:
                if not I:continue
                a=sig[len(I)-1]*data[I,J]
                b=sig[len(I)-1]*gradient(data,I,J,i,j)
                if b>0:
                    bound=F(-a,b)
                    lower=bound if lower is None else max(lower,bound)
                elif b<0:
                    bound=F(-a,b)
                    upper=bound if upper is None else min(upper,bound)
            for t in [lower,upper]:
                if t is not None and t!=0:
                    B=shifted(A,(i,j),t)
                    if determinant(B):candidates.append(B)
    return candidates


def sparse_counterexample(A,data,sig):
    zeros=[(I,J) for I,J in INDICES if I and data[I,J]==0]
    if not zeros:return None
    pos=[(i,j) for i in range(N) for j in range(N)]
    grads={p:[(-1)**sum(p)*gradient(data,I,J,*p) for I,J in zeros] for p in pos}
    for p,q in itertools.combinations(pos,2):
        gp,gq=grads[p],grads[q]
        witness=next((k for k,(a,b) in enumerate(zip(gp,gq)) if a*b<0),None)
        if witness is None:continue
        wp,wq=abs(gq[witness]),abs(gp[witness])
        g=math.gcd(wp,wq);wp//=g;wq//=g
        if any(a*wp+b*wq for a,b in zip(gp,gq)):continue
        E=[[0]*N for _ in range(N)]
        E[p[0]][p[1]]=(-1)**sum(p)*wp
        E[q[0]][q[1]]=(-1)**sum(q)*wq
        B=[[A[i][j]+E[i][j] for j in range(N)] for i in range(N)]
        one=minors(B)
        if any(sig[len(I)-1]*one[I,J]<0 for I,J in zeros):continue
        # For two uncertain entries, each minor is quadratic at most.
        # First derivative is zero on every currently zero minor.
        # Choose a sufficiently small exact step and recheck all minors.
        scale=max(abs(z) for row in E for z in row)
        for power in range(1,100):
            den=(2**power)*max(scale,1)
            plus=[[den*A[i][j]+E[i][j] for j in range(N)] for i in range(N)]
            minus=[[den*A[i][j]-E[i][j] for j in range(N)] for i in range(N)]
            if signature(minors(plus))!=sig or signature(minors(minus))!=sig:continue
            for s,t in itertools.product([-1,1],repeat=2):
                inside=[[den*a for a in row] for row in A]
                inside[p[0]][p[1]]+=s*abs(E[p[0]][p[1]])
                inside[q[0]][q[1]]+=t*abs(E[q[0]][q[1]])
                md=minors(inside)
                bad=[{'rows':I,'columns':J,'determinant':md[I,J]}
                     for I,J in INDICES if I and sig[len(I)-1]*md[I,J]<0]
                if bad:
                    return {'signature':sig,'checkerboard_corner_minus':minus,
                            'checkerboard_corner_plus':plus,'violating_member':inside,
                            'bad_minors':bad,'all_minor_checks':'exact integer'}
            break
    return None



def sparse_three_counterexample(A,data,sig):
    zeros=[(I,J) for I,J in INDICES if I and data[I,J]==0]
    if len(zeros)<2:return None
    pos=[(i,j) for i in range(N) for j in range(N)]
    grads={p:[(-1)**sum(p)*gradient(data,I,J,*p) for I,J in zeros] for p in pos}
    for support in itertools.combinations(pos,3):
        rows=[tuple(grads[p][k] for p in support) for k in range(len(zeros))]
        first=next((v for v in rows if any(v)),None)
        if first is None:continue
        weights=None
        for second in rows:
            cross=(first[1]*second[2]-first[2]*second[1],
                   first[2]*second[0]-first[0]*second[2],
                   first[0]*second[1]-first[1]*second[0])
            if any(cross):weights=cross;break
        if weights is None:continue
        if all(w<0 for w in weights):weights=tuple(-w for w in weights)
        if not all(w>0 for w in weights):continue
        if any(sum(a*w for a,w in zip(row,weights)) for row in rows):continue
        g=math.gcd(*weights);weights=tuple(w//g for w in weights)
        E=[[0]*N for _ in range(N)]
        for p,w in zip(support,weights):E[p[0]][p[1]]=(-1)**sum(p)*w
        Bp=[[A[i][j]+E[i][j] for j in range(N)] for i in range(N)]
        Bm=[[A[i][j]-E[i][j] for j in range(N)] for i in range(N)]
        dp,dm=minors(Bp),minors(Bm)
        valid=True
        for I,J in zeros:
            even=dp[I,J]+dm[I,J];odd=dp[I,J]-dm[I,J]
            if sig[len(I)-1]*even<0 or (even==0 and odd!=0):valid=False;break
        if not valid:continue
        I,J=next((I,J) for I,J in zeros
                 if any(gradient(data,I,J,*p) for p in support))
        for power in range(1,301):
            den=2**power*max(weights)
            plus=[[den*A[i][j]+E[i][j] for j in range(N)] for i in range(N)]
            minus=[[den*A[i][j]-E[i][j] for j in range(N)] for i in range(N)]
            if signature(minors(plus))!=sig or signature(minors(minus))!=sig:continue
            inside=[[den*a for a in row] for row in A]
            for p,w in zip(support,weights):
                derivative=sig[len(I)-1]*gradient(data,I,J,*p)
                direction=-1 if derivative>0 else 1
                inside[p[0]][p[1]]+=direction*w
            md=minors(inside)
            bad=[{'rows':II,'columns':JJ,'determinant':md[II,JJ]}
                 for II,JJ in INDICES if II and sig[len(II)-1]*md[II,JJ]<0]
            if bad:
                return {'signature':sig,'checkerboard_corner_minus':minus,
                        'checkerboard_corner_plus':plus,'violating_member':inside,
                        'bad_minors':bad,'all_minor_checks':'exact integer',
                        'uncertain_entry_count':3}
    return None


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--states',type=int,default=200)
    parser.add_argument('--until-utc',default=None)
    parser.add_argument('--seed',type=int,default=2026091101)
    args=parser.parse_args()
    deadline=None
    if args.until_utc:
        deadline=datetime.datetime.fromisoformat(args.until_utc.replace('Z','+00:00'))
    rng=random.Random(args.seed)
    start=time.monotonic(); count=0; boundary_count=0; result=None
    status={'status':'running','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'no_solution_claimed':True,'method':'exact boundary-stratum and sparse-direction search'}
    out=ROOT/'verification'/'IV-01_exploratory_search.json'
    A=None; depth=0
    while count<args.states or (deadline is not None and datetime.datetime.now(datetime.timezone.utc)<deadline):
        if A is None or depth>=6:
            M=rng.choice([1000000,10000000,100000000])
            coeff=[M**4,M**3,rng.choice([-1,1])*M**2,rng.choice([-1,1])*M,rng.choice([-1,1])]
            xs=sorted(rng.sample(range(13),5)); ys=sorted(rng.sample(range(13),5))
            A=[[sum(coeff[k]*(i*j)**k for k in range(5)) for j in ys] for i in xs]
            A=normalize(A);depth=0
        data=minors(A);sig=signature(data)
        assert sig is not None and data[tuple(range(N)),tuple(range(N))]!=0
        if any(v==0 for (I,J),v in data.items() if I):boundary_count+=1
        result=sparse_counterexample(A,data,sig)
        if result is None:
            result=sparse_three_counterexample(A,data,sig)
        count+=1
        if result:
            status['status']='counterexample_found';status['certificate']=result
            status['no_solution_claimed']=False
            break
        candidates=boundaries(A,data,sig)
        if candidates:
            A=rng.choice(candidates);depth+=1
        else:A=None
        if count%10==0:
            status.update(states_checked=count,boundary_states=boundary_count,
                          elapsed_seconds=time.monotonic()-start,
                          last_update_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
            out.write_text(json.dumps(status,indent=2))
            print(count,status['elapsed_seconds'],flush=True)
    if not result:status['status']='no_counterexample_found'
    status.update(states_checked=count,boundary_states=boundary_count,
                  elapsed_seconds=time.monotonic()-start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    out.write_text(json.dumps(status,indent=2))
    print(json.dumps(status,indent=2))

if __name__=='__main__':main()

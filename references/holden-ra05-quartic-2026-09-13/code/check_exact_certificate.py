"""Standard-library-only check of the full-rank quartic witness certificate."""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Verification requires assertions: run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from pathlib import Path
import json
import sys


def mm(A, B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]


def rational_rank(A):
    """Gaussian elimination over fractions, with no floating-point tolerance."""
    B = [[F(x) for x in row] for row in A]
    r = 0
    for j in range(len(B[0])):
        pivot = next((i for i in range(r, len(B)) if B[i][j]), None)
        if pivot is None:
            continue
        B[r], B[pivot] = B[pivot], B[r]
        scale = B[r][j]
        B[r] = [x / scale for x in B[r]]
        for i in range(r+1, len(B)):
            scale = B[i][j]
            B[i] = [x - scale*y for x,y in zip(B[i], B[r])]
        r += 1
        if r == len(B):
            break
    return r


def check(path: Path) -> dict:
    data=json.loads(path.read_text())
    A=data['rows']; w=list(map(F,data['weights'])); k,N,R=data['k'],data['N'],data['R']
    n,d=len(A),len(A[0])
    assert n==2*k*N and d==k+k*N
    expected=[]
    for j in range(k):
        for t in range(N):
            for s in (1,-1):
                row=[0]*d; row[j]=R; row[k+j*N+t]=s; expected.append(row)
    assert A==expected
    input_rank = rational_rank(A)
    assert input_rank == d > k+1
    assert N>k and R*R*(N-k)>=1
    assert all(x>=0 for x in w)
    output=[]
    for q in data['queries']:
        den=q['denominator']; Z=q['projector_numerator']
        assert Z==list(map(list,zip(*Z)))
        assert mm(Z,Z)==[[den*z for z in row] for row in Z]
        assert sum(Z[i][i] for i in range(d))==k*den
        P=[[F(z,den) for z in row] for row in Z]
        rowcost=[]
        for row in A:
            projected=[sum(P[i][j]*row[j] for j in range(d)) for i in range(d)]
            dist2=sum((F(row[i])-projected[i])**2 for i in range(d))
            rowcost.append(dist2**2)
        orig=sum(rowcost,F(0)); weighted=sum((wi*c for wi,c in zip(w,rowcost)),F(0))
        rel=abs(weighted-orig)/orig
        assert orig==F(q['original_cost'])
        assert weighted==F(q['weighted_cost'])
        assert rel==F(q['relative_error'])
        assert rel>F(data['epsilon'])
        output.append({'label':q['label'],'original_cost':str(orig),'weighted_cost':str(weighted),'relative_error':str(rel)})
    # Check the supplied head projector's cost exactly as well.
    opt=sum(F(sum(x*x for x in row[k:]))**2 for row in A)
    assert opt==2*k*N==F(data['optimal_cost'])
    # Global optimality is proved in the manuscript, not inferred from sampling.
    return {'passed':True,'rows':n,'ambient_dimension':d,'input_rank':input_rank,'query_rank':k,
            'retained_rows':sum(x!=0 for x in w),'head_cost':str(opt),
            'optimality_parameter_inequality':R*R*(N-k), 'queries':output,
            'scope':'Exact finite matrix/projector/cost checks; global optimality uses the manuscript lemma.'}

if __name__=='__main__':
    default=Path(__file__).resolve().parents[1]/'results'/'exact_full_rank_certificate.json'
    result=check(Path(sys.argv[1]) if len(sys.argv)>1 else default)
    print(json.dumps(result,indent=2))

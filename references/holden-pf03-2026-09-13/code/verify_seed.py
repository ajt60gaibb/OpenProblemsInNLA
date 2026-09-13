"""Independent, standard-library-only verification of the algebraic seed."""
from pathlib import Path
import json,time
from fractions import Fraction as F
from field3 import *

def verify_seed(path: Path, verbose=True):
    t0=time.monotonic()
    d=json.loads(path.read_text())
    n=d['rank']
    assert n == 7
    assert d['field_polynomial']=='t^3-2'
    I=identity(n)
    O=mat_decode(d['orthogonal_matrix'])
    Qp=mat_decode(d['Qprime']);Q=mat_decode(d['Q'])
    Bs=[mat_decode(x) for x in d['coefficient_matrices']]
    C=[[ALPHA*d['S'][i][j]+ALPHA**2*d['T'][i][j] for j in range(n)] for i in range(n)]
    assert transpose(C)==[[-x for x in row] for row in C]
    assert multiply(add(I,C),O)==subtract(I,C)
    assert multiply(O,transpose(O))==I
    assert multiply(transpose(O),O)==I
    assert Qp==transpose(Qp) and Q==transpose(Q)
    assert Q==multiply(multiply(O,Qp),transpose(O))
    assert sum((Q[i][i] for i in range(n)),ZERO)==ZERO
    for i in range(n):
        assert Qp[i][i]==ZERO
        for j in range(n):
            assert O[i][j]==sum((ALPHA**k*Bs[k][i][j] for k in range(3)),ZERO)
            for k in range(3):
                Bs[k][i][j].rational()
    interval=isolate_alpha(40)
    positive_lower=[]
    for i in range(n):
        for j in range(i+1,n):
            low,high=Qp[i][j].interval(interval)
            assert low>0,('nonpositive cross term',i,j)
            positive_lower.append(low)
    assert min(positive_lower)>F(17391,10**6)
    expected_local=[(1016353,444291),(1150668,687760),(380276,104352),(242452,30000),(3486402,4967538),(424643,91575),(1071944,579814)]
    Cs=[];Hlist=[];local_bounds=[]
    for j in range(n):
        U=[[Bs[k][i][j] for k in range(3)] for i in range(n)]
        assert rational_rank([[x.rational() for x in row] for row in U])==3
        H=multiply(multiply(transpose(U),Q),U)
        assert H==mat_decode(d['restricted_gram'][j])
        assert H==transpose(H)
        assert multiply(H,[[ONE],[ALPHA],[ALPHA**2]])==[[ZERO] for _ in range(3)]
        # Positive upper-left block + the displayed kernel proves PSD rank two.
        h=H[0][0]
        det=H[0][0]*H[1][1]-H[0][1]**2
        assert positive(h,interval),('local diagonal',j)
        assert positive(det,interval),('local determinant',j)
        assert h.interval(interval)[0]>F(expected_local[j][0],10**6)
        assert det.interval(interval)[0]>F(expected_local[j][1],10**6)
        local_bounds.append((h.interval(interval)[0],det.interval(interval)[0]))
        Cs.append(U);Hlist.append(H)
    if verbose:
        print('PASS: Cayley identity and both orthogonality identities (exact).')
        print('PASS: Q=O Qprime O^T, symmetry, trace(Q)=0 (exact).')
        print('PASS: all 21 off-diagonal Qprime entries strictly positive (rational intervals).')
        print('PASS: all 7 rational coefficient matrices have rank three.')
        print('PASS: all 7 local forms PSD of rank two, with exact specified kernel.')
        print('Isolation interval:',str(interval[0]),str(interval[1]))
        print('Strict cross-term lower bound >', min(positive_lower).numerator//(min(positive_lower).denominator//10**6+1),'/ 1000000 [conservative display]')
        print('Elapsed:',round(time.monotonic()-t0,3),'seconds')
    return d,O,Qp,Q,Bs,Cs,Hlist,interval

if __name__=='__main__':
    verify_seed(Path(__file__).resolve().parent.parent/'data'/'exact_algebraic_certificate.json')

"""Construct 21 rational rays surrounding the seven algebraic zero rays."""
from pathlib import Path
import json
from fractions import Fraction as F
from field3 import *
from verify_seed import verify_seed

HERE=Path(__file__).resolve().parent.parent/'data'

def round_fraction(x:F, denominator:int)->F:
    return F((2*x.numerator*denominator+x.denominator)//(2*x.denominator),denominator)

def generate():
    d,O,Qp,Q,Bs,Cs,Hs,iso=verify_seed(HERE/'exact_algebraic_certificate.json',False)
    ac=round_fraction(sum(iso)/2,10**20)
    b_interval=(ALPHA**2).interval(iso)
    bc=round_fraction(sum(b_interval)/2,10**20)
    delta=F(1,10000)
    attempts=0
    while True:
        attempts+=1
        W=[[ONE,ONE,ONE],
           [E(ac+delta),E(ac),E(ac-delta)],
           [E(bc),E(bc+delta),E(bc-delta)]]
        blocks=[multiply(U,W) for U in Cs]
        V=[[blocks[j][i][k] for j in range(7) for k in range(3)] for i in range(7)]
        Z=multiply(multiply(transpose(V),Q),V)
        lows=[]
        for i in range(21):
            for j in range(i+1,21):
                if i//3 != j//3:
                    lows.append(Z[i][j].interval(iso)[0])
        if min(lows)>0:
            break
        delta/=2
        if attempts>50:
            raise ArithmeticError('Failed to obtain certified positive cross terms')
    dx=(ALPHA-ac)/delta
    dy=(ALPHA**2-bc)/delta
    lam=[(ONE+2*dx-dy)/3,(ONE-dx+2*dy)/3,(ONE-dx-dy)/3]
    assert all(positive(x,iso) for x in lam)
    assert multiply(W,[[x] for x in lam])==[[ONE],[ALPHA],[ALPHA**2]]
    h=[]
    for row in O:
        value=sum(row,ZERO)
        lb,ub=value.interval(iso)
        h.append(round_fraction((lb+ub)/2,10**8))
    Vr=[[x.rational() for x in row] for row in V]
    hd=[sum(h[i]*Vr[i][j] for i in range(7)) for j in range(21)]
    assert min(hd)>0
    assert rational_rank(Vr)==7
    out={
        'description':'Rational 7 by 21 generator matrix, three columns per cone.',
        'center':[str(ac),str(bc)],'delta':str(delta),
        'coefficient_triangle':[[str(x.rational()) for x in row] for row in W],
        'barycentric_coefficients':[x.encode() for x in lam],
        'generators':[[str(x) for x in row] for row in Vr],
        'positive_slice_functional':[str(x) for x in h],
        'isolation_interval':[str(x) for x in iso],
        'cross_lower_bound':str(min(lows)),
    }
    (HERE/'rational_cone_certificate.json').write_text(json.dumps(out,indent=2))
    print('All 189 cross-block generator pairings certified positive.')
    print('delta =',delta,'; exact 20-decimal centers:',ac,bc)
    print('All three barycentric coefficients certified positive.')
    print('Exact rational rank of generator matrix: 7.')
    print('Common rational functional strictly positive on all 21 generators.')
    print('Cross pairing lower bound exceeds 17/1000:',min(lows)>F(17,1000))
    print('Largest generator coefficient string length:',max(len(str(x)) for r in Vr for x in r))

if __name__=='__main__':
    generate()

"""Independent exact first-order polynomial check of the supplied model.

This is a diagnostic, not the universal contraction proof. It uses direct
truncated-polynomial multiplication, not the verifier's sparse derivative loop.
"""
import importlib.util
import json
from fractions import Fraction as Q
from pathlib import Path

SOURCE = Path(__file__).resolve().parent / 'submitted-code/verify_conference.py'
spec = importlib.util.spec_from_file_location('supplied_verifier', SOURCE)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def mul(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])


def conj(x):
    return (x[0], -x[1])


ZERO = (Q(0), Q(0))
ONE = (Q(1), Q(0))


def check(d):
    h, n = (d-1)//2, d-1
    ps = [2*j-5 for j in range(h+d-1)]
    selected = list(range(n))
    cert = dict(dimension=d, anchor_half_angle_numerators=ps,
                anchor_half_angle_denominator=7, selected_variables=selected,
                inverse_numerators=[[int(i==j) for j in range(n)] for i in range(n)],
                inverse_denominator=1, verification_bits=160)
    grid, f_intervals, j_intervals = module.exact_model(cert)
    anchors = [(Q(49-p*p,49+p*p), Q(14*p,49+p*p)) for p in ps]
    a, b = [ZERO]*d, [ONE]+anchors[h:]
    for j in range(1,h+1):
        a[j],a[d-j] = anchors[j-1],conj(anchors[j-1])
    if d%2==0:
        a[d//2]=ONE
    checks=0
    for v in [-1]+selected:
        da,db=[ZERO]*d,[ZERO]*d
        if 0<=v<h:
            da[v+1]=mul((Q(0),Q(2)),a[v+1])
            da[d-v-1]=conj(da[v+1])
        elif v>=h:
            j=v-h+1
            db[j]=mul((Q(0),Q(2)),b[j])
        values=[]
        for s in range(1,d//2+1):
            total=ZERO
            for seq,der in ((a,da),(b,db)):
                for j in range(d):
                    k=(j+s)%d
                    term=mul(seq[j],conj(seq[k])) if v<0 else add(
                        mul(der[j],conj(seq[k])),mul(seq[j],conj(der[k])))
                    total=add(total,term)
            values.extend(total if 2*s!=d else total[:1])
        bounds=f_intervals if v<0 else j_intervals[selected.index(v)]
        assert len(values)==len(bounds)==n
        for value,(lo,hi) in zip(values,bounds):
            assert Q(lo,grid.S)<=value<=Q(hi,grid.S), (d,v,value,lo,hi)
            checks+=1
    return dict(dimension=d, exact_value_and_derivative_enclosures_checked=checks,
                passed=True)


if __name__=='__main__':
    print(json.dumps([check(d) for d in (3,4,5,6,7,8)],indent=2))

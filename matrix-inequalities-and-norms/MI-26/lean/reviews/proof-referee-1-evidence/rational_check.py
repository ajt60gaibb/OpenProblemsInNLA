"""Independent exact rational and polynomial reconstruction; not a Lean proof."""
from fractions import Fraction as F
from pathlib import Path
import json

def mat(rows):
    return [[F(x) for x in row] for row in rows]

def transpose(a):
    return list(map(list, zip(*a)))

def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]

def scale(c, a):
    return [[c * x for x in row] for row in a]

def mul(a, b):
    return [[sum(x * y for x, y in zip(ar, bc)) for bc in transpose(b)] for ar in a]

def outer(v):
    return [[x * y for y in v] for x in v]

def matrix_function(a):
    return add(a, scale(-1, mul(a, a)))

P = mat([[1, 0], [0, 0]])
v = [F(3, 5), F(4, 5)]
Q = outer(v)
assert sum(x*x for x in v) == 1
assert Q == mat([['9/25', '12/25'], ['12/25', '16/25']])
assert P == outer([F(1), F(0)])
assert P == transpose(P) and Q == transpose(Q)
assert mul(P, P) == P and mul(Q, Q) == Q
S = add(P, Q)
S2 = mul(S, S)
assert S == scale(F(1, 25), mat([[34, 12], [12, 16]]))
assert S2 == scale(F(1, 25), mat([[52, 24], [24, 16]]))
zero = mat([[0, 0], [0, 0]])
assert matrix_function(P) == zero and matrix_function(Q) == zero
image = matrix_function(S)
assert image == scale(F(1, 25), mat([[-18, -12], [-12, 0]]))
w = [F(1), F(-2)]
Fw = [sum(a*b for a,b in zip(row,w)) for row in image]
assert Fw == [F(6,25), F(-12,25)]
quadratic = sum(a*b for a,b in zip(w,Fw))
assert quadratic == F(6,5) and quadratic > 0
assert F(0)-F(0)**2 == 0 and F(2)-F(2)**2 == -2

# Independent multivariate rational expansion in (theta, x, y).
def padd(a, b):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}

def pscale(c, a):
    return {key: c*value for key,value in a.items() if c*value}

def pmul(a, b):
    out = {}
    for ka,va in a.items():
        for kb,vb in b.items():
            key = tuple(x+y for x,y in zip(ka,kb))
            out[key] = out.get(key,F(0))+va*vb
    return {key:value for key,value in out.items() if value}

def pf(a):
    return padd(a, pscale(-1, pmul(a,a)))

one = {(0,0,0):F(1)}
theta = {(1,0,0):F(1)}
x = {(0,1,0):F(1)}
y = {(0,0,1):F(1)}
other = padd(one, pscale(-1,theta))
z = padd(pmul(theta,x),pmul(other,y))
gap = padd(padd(pf(z),pscale(-1,pmul(theta,pf(x)))),pscale(-1,pmul(other,pf(y))))
xy = padd(x,pscale(-1,y))
factored = pmul(pmul(theta,other),pmul(xy,xy))
assert gap == factored

out = {'scope':'Independent supplementary exact arithmetic and polynomial identity; not a Lean proof or CFC/PSD certificate.',
       'P':P,'Q':Q,'Q_positive_outer_vector':v,'P_squared':mul(P,P),'Q_squared':mul(Q,Q),
       'sum':S,'sum_squared':S2,'matrix_polynomial_image':image,'w':w,'image_times_w':Fw,
       'quadratic_form':quadratic,'strict_positive_gap':quadratic,
       'concavity_gap_factorization':'theta*(1-theta)*(x-y)^2',
       'concavity_gap_coefficients':{str(key):value for key,value in gap.items()},
       'all_exact_checks_pass':True}
Path(__file__).with_name('rational-check.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
print('PASS: exact PSD outer-product witnesses, projections, matrix polynomial, quadratic form 6/5, and full symbolic concavity factorization.')

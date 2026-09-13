"""Independent exact statement diagnostics; no author checker import or proof oracle."""
from fractions import Fraction as F
from pathlib import Path
import json

class Poly:
    def __init__(self, terms):
        self.t = {k:F(v) for k,v in terms.items() if v}
    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly({(0,0):F(x)})
    def __add__(self, other):
        q = self.coerce(other); t = self.t.copy()
        for k,v in q.t.items(): t[k] = t.get(k, F(0)) + v
        return Poly(t)
    __radd__ = __add__
    def __neg__(self): return Poly({k:-v for k,v in self.t.items()})
    def __sub__(self, other): return self + -self.coerce(other)
    def __rsub__(self, other): return self.coerce(other) + -self
    def __mul__(self, other):
        q = self.coerce(other); t = {}
        for (i,j),a in self.t.items():
            for (k,l),b in q.t.items():
                e = (i+k,j+l); t[e] = t.get(e,F(0)) + a*b
        return Poly(t)
    __rmul__ = __mul__
    def __pow__(self, n):
        out = self.coerce(1)
        for _ in range(n): out = out*self
        return out
    def __eq__(self, other): return self.t == self.coerce(other).t

d,z = Poly({(1,0):1}), Poly({(0,1):1})
Q = 2*(d+1)*z**2-(2*d+1)*z+d
assert Q == 2*(d-1)*(z-F(1,2))**2+(d-1)*F(1,2)+4*(z-F(3,8))**2+F(7,16)
for G, rhs in [
    (2*d**2*z, (d-1)*Q),
    (2*d**2, (d-z)*(2*z+d-1)),
    (2*d*z, (d-1)*(z-d)*(2*z-1))
]:
    # Multiply by z>0, with no change of sign, before exact coefficient comparison.
    assert z*(G-2*z-d**2+1)-d*(d-1)*(z-1) == rhs

def mat(rows): return [[F(x) for x in row] for row in rows]
def diag(v): return [[F(x) if i==j else F(0) for j in range(len(v))] for i,x in enumerate(v)]
def mul(A,B): return [[sum((a*b for a,b in zip(row,col)),F(0)) for col in zip(*B)] for row in A]
def sub(A,B): return [[a-b for a,b in zip(r,s)] for r,s in zip(A,B)]
def scale(c,A): return [[c*x for x in row] for row in A]
def outer(v): return [[x*y for y in v] for x in v]
def fsq(A): return sum((x*x for row in A for x in row),F(0))
def tr(A): return sum((A[i][i] for i in range(len(A))),F(0))

A = diag([5,3,1]); v = [F(3,5),F(4,5),F(0)]; B = outer(v)
assert mul(A,B) != mul(B,A)
assert fsq(B) == 1
TA = F(10); eps = F(12,5)
deficit = fsq(A)-fsq(B); residual = fsq(sub(A,B)); cross = tr(mul(B,sub(A,B)))
assert deficit == (1+eps)*TA == 34
assert cross == F(68,25) and residual == deficit-2*cross == F(714,25)
# Actual finite spectral function f(x)=x+1: C is its selected rank-one truncation.
fA = diag([6,4,2]); C = scale(F(2),B); Tf=F(20)
assert fsq(sub(fA,C)) == F(1028,25) <= (1+eps)*Tf
assert C != [[B[i][j]+(1 if i==j else 0) for j in range(3)] for i in range(3)]

# A=Ahat, n=3, k=2, f(0)=1, two different selected null-space directions.
Z = diag([2,0,0]); fZ = diag([3,1,1]); C1 = diag([3,1,0])
w = [F(0),F(3,5),F(4,5)]; C2 = outer(w); C2[0][0] = F(3)
assert C1 != C2 and fsq(sub(fZ,C1)) == fsq(sub(fZ,C2)) == 1
assert fsq(Z)-fsq(Z) == 0

# The exact diagonal harmonic test includes a zero spectral coordinate.
a = [F(0),F(2),F(8)]; vv = [F(0),F(3,5),F(4,5)]; b=F(3)
zz = [vi/ai if ai else F(0) for ai,vi in zip(a,vv)]
H = sum((vi*vi/ai if ai else F(0) for ai,vi in zip(a,vv)),F(0))
D = sub(diag(a),scale(b,outer(vv)))
quad = sum((zz[i]*D[i][j]*zz[j] for i in range(3) for j in range(3)),F(0))
assert H == F(13,50) and quad == H-b*H*H and b*H <= 1
assert D[1][1] > 0 and D[1][1]*D[2][2]-D[1][2]**2 > 0

out = {
    'status':'PASS independent exact statement diagnostics, not universal Lean proofs',
    'universal_coefficient_identities':['SOS for branchQuadratic','first factor after multiplication by z','second factor after multiplication by z','third factor after multiplication by z'],
    'noncommuting_affine_function_example':{'dimension':3,'rank':1,'f':'x+1','epsilon':str(eps),'actual_trace_deficit':str(deficit),'actual_residual':str(residual),'cross_trace':str(cross),'actual_function_error':str(fsq(sub(fA,C))),'function_tail':str(Tf),'function_truncation_differs_from_full_f_B':True},
    'positive_f0_zero_tail':{'dimension':3,'rank':2,'f0':1,'different_selected_null_space_truncations':True,'both_actual_errors':'1=(n-k)*f(0)^2'},
    'harmonic_zero_coordinate_example':{'H':str(H),'b_times_H':str(b*H),'actual_quadratic':str(quad),'equals_H_minus_b_H_squared':True},
    'review_limits':'The ordered scalar inequality still needs proof from actual admissibility; harmonic/overlap/order/CFC/Frobenius bridges and the universal final statement are unproved Challenge obligations. No finite sample replaces them.'
}
(Path(__file__).parent/'reconstruction.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

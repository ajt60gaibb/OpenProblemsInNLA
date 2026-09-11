"""Independent rational-interval audit of the additional SPD word-equation roots.

Uses fractions.Fraction endpoints with no fixed-point rounding and evaluates
X^12 by the Cayley--Hamilton recurrence on det(X)=3, rather than multiplying
all letters of the word. Derivatives use interval dual numbers. No third-party
package or floating-point number participates in the proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
import sys

@dataclass(frozen=True)
class Interval:
    lower: Q
    upper: Q
    def __post_init__(self):
        if self.lower > self.upper: raise ValueError('Reversed interval')
    @staticmethod
    def point(value) -> 'Interval':
        value = Q(value)
        return Interval(value, value)
    def __add__(self, other):
        if not isinstance(other, Interval): other = Interval.point(other)
        return Interval(self.lower+other.lower, self.upper+other.upper)
    __radd__ = __add__
    def __neg__(self): return Interval(-self.upper, -self.lower)
    def __sub__(self, other): return self + (-other if isinstance(other, Interval) else -Q(other))
    def __rsub__(self, other): return Interval.point(other)-self
    def __mul__(self, other):
        if not isinstance(other, Interval): other = Interval.point(other)
        values = [x*y for x in (self.lower, self.upper) for y in (other.lower, other.upper)]
        return Interval(min(values), max(values))
    __rmul__ = __mul__
    def inverse(self):
        if self.lower <= 0 <= self.upper: raise ZeroDivisionError('Interval contains zero')
        return Interval(1/self.upper, 1/self.lower)
    def __truediv__(self, other):
        if not isinstance(other, Interval): other = Interval.point(other)
        return self*other.inverse()
    def magnitude(self): return max(abs(self.lower), abs(self.upper))

ZERO = Interval.point(0)
ONE = Interval.point(1)

@dataclass(frozen=True)
class Dual:
    value: Interval
    grad: tuple[Interval, Interval]
    @staticmethod
    def constant(value):
        return Dual(Interval.point(value), (ZERO, ZERO))
    def __add__(self, other):
        if not isinstance(other, Dual): other = Dual.constant(other)
        return Dual(self.value+other.value, tuple(a+b for a,b in zip(self.grad, other.grad)))
    __radd__ = __add__
    def __neg__(self): return Dual(-self.value, tuple(-v for v in self.grad))
    def __sub__(self, other): return self+(-other if isinstance(other, Dual) else -Q(other))
    def __rsub__(self, other): return Dual.constant(other)-self
    def __mul__(self, other):
        if not isinstance(other, Dual): other = Dual.constant(other)
        return Dual(self.value*other.value, tuple(a*other.value+self.value*b for a,b in zip(self.grad,other.grad)))
    __rmul__ = __mul__
    def inverse(self):
        reciprocal = self.value.inverse()
        return Dual(reciprocal, tuple(-g*reciprocal*reciprocal for g in self.grad))
    def __truediv__(self, other):
        if not isinstance(other, Dual): other = Dual.constant(other)
        return self*other.inverse()

def matmul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]

def evaluate(x: Interval, y: Interval):
    x = Dual(x, (ONE,ZERO)); y = Dual(y,(ZERO,ONE))
    z = (3+y*y)/x
    X = [[x,y],[y,z]]
    B = [[Dual.constant(1),Dual.constant(4)],[Dual.constant(4),Dual.constant(17)]]
    trace = x+z
    # X^r = u_r X - 3 u_(r-1) I, with u_0=0, u_1=1.
    previous, current = Dual.constant(0), Dual.constant(1)
    for _ in range(1,12):
        previous, current = current, trace*current-3*previous
    central = [[current*X[i][j] - (3*previous if i==j else 0) for j in range(2)] for i in range(2)]
    XB = matmul(X,B)
    BX = matmul(B,X)
    value = matmul(matmul(XB,central),BX)
    residual = [value[0][0]-4783113, value[0][1]-6377496]
    return [r.value for r in residual], [list(r.grad) for r in residual]

def ceil_to(q: Q, places: int = 80) -> str:
    scale=10**places
    numerator = -((-q.numerator*scale)//q.denominator)
    return str(Q(numerator,scale))

def audit(path: Path):
    cert=json.loads(path.read_text())
    if cert['B'] != [[1,4],[4,17]] or cert['P'] != [[4783113,6377496],[6377496,8503345]]:
        raise ValueError('Unexpected equation')
    reports=[]; xboxes=[]
    for block in cert['certificates']:
        center=[Q(v) for v in block['center']]
        radius=Q(block['radius'])
        if radius<=0 or center[0]<=radius: raise ValueError('Box is not in x>0')
        box=[Interval(c-radius,c+radius) for c in center]
        fcenter,Jcenter=evaluate(*[Interval.point(v) for v in center])
        if any(v.lower != v.upper for row in Jcenter for v in row):
            raise ArithmeticError('Center derivative is not exact')
        a,b=Jcenter[0][0].lower,Jcenter[0][1].lower
        c,d=Jcenter[1][0].lower,Jcenter[1][1].lower
        determinant=a*d-b*c
        if determinant==0: raise ArithmeticError('Singular center Jacobian')
        inverse=[[d/determinant,-b/determinant],[-c/determinant,a/determinant]]
        _,Jbox=evaluate(*box)
        defect=[[Interval.point(int(i==j))-sum(inverse[i][k]*Jbox[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        displacement=Interval(-radius,radius)
        image=[Interval.point(center[i])-sum(inverse[i][j]*fcenter[j] for j in range(2))
               +sum(defect[i][j]*displacement for j in range(2)) for i in range(2)]
        if not all(box[i].lower<image[i].lower<=image[i].upper<box[i].upper for i in range(2)):
            raise ArithmeticError('Strict inclusion failed')
        contraction=max(sum(e.magnitude() for e in row) for row in defect)
        if contraction>=Q(1,10**20): raise ArithmeticError('Contraction is not below 1e-20')
        if box[0].lower<=3<=box[0].upper and box[1].lower<=0<=box[1].upper:
            raise ArithmeticError('Box includes the known root')
        xboxes.append(box[0])
        image_displacement=max((image[i]-center[i]).magnitude() for i in range(2))
        reports.append({'center':block['center'],'radius':block['radius'],
                        'contraction_norm_upper_rounded_outward':ceil_to(contraction),
                        'image_displacement_upper_rounded_outward':ceil_to(image_displacement),
                        'strict_inclusion':True, 'positive_definite_by_determinant_3':True})
    if len(xboxes)!=2 or xboxes[0].upper>=xboxes[1].lower:
        raise ArithmeticError('Expected two separated root boxes')
    return {'arithmetic':'exact rational endpoints; Cayley--Hamilton polynomial recurrence; interval dual numbers',
            'certificate':path.name,'certificates':reports,'passed':True}

def main():
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    result=audit(args.certificate)
    if args.verify:
        if args.output is None or json.loads(args.output.read_text())!=result:
            raise ArithmeticError('Stored independent report differs')
    elif args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: independent Fraction/Cayley--Hamilton interval proof of two additional SPD roots.')

if __name__=='__main__':main()

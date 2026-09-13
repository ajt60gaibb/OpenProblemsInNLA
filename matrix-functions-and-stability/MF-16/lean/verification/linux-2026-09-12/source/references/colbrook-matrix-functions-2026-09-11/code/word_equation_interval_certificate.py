"""Exact fixed-point interval certificates for two additional SPD roots.

No floating point is used. Every interval arithmetic operation rounds outwards
using Python integers. Brouwer's fixed-point theorem applied to c-C*f maps a
certified box into itself. The checked derivative norm also gives uniqueness
inside each box. This is independent of the Armstrong--Hillar degree argument.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse, json

PRECISION = 110
SCALE = 10**PRECISION

def ceildiv(a: int, b: int) -> int:
    return -((-a)//b)

@dataclass(frozen=True)
class IV:
    lo: int
    hi: int
    def __post_init__(self):
        if self.lo > self.hi: raise ValueError('Invalid interval')
    @staticmethod
    def of(v: int | F | str) -> 'IV':
        q=F(v); return IV((q.numerator*SCALE)//q.denominator,
                          ceildiv(q.numerator*SCALE,q.denominator))
    def __add__(self, other):
        if not isinstance(other,IV):other=IV.of(other)
        return IV(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return IV(-self.hi,-self.lo)
    def __sub__(self, other):return self+(-other if isinstance(other,IV) else -F(other))
    def __rsub__(self, other):return IV.of(other)-self
    def __mul__(self,other):
        if not isinstance(other,IV):other=IV.of(other)
        p=(self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi)
        return IV(min(p)//SCALE,ceildiv(max(p),SCALE))
    __rmul__=__mul__
    def reciprocal(self):
        if self.lo <= 0 <= self.hi:raise ZeroDivisionError('Interval contains zero')
        # Reciprocal is decreasing on either connected half-axis.
        vals=(F(SCALE*SCALE,self.lo),F(SCALE*SCALE,self.hi))
        low=min(vals);high=max(vals)
        return IV(low.numerator//low.denominator,ceildiv(high.numerator,high.denominator))
    def __truediv__(self,other):
        if not isinstance(other,IV):other=IV.of(other)
        return self*other.reciprocal()
    def mid(self)->F:return F(self.lo+self.hi,2*SCALE)
    def abs_bound(self)->F:return F(max(abs(self.lo),abs(self.hi)),SCALE)
    def bounds(self)->list[str]:return [str(F(self.lo,SCALE)),str(F(self.hi,SCALE))]

Z=IV.of(0);O=IV.of(1)
I=(O,Z,Z,O); ZERO=(Z,Z,Z,Z)
B=tuple(IV.of(v) for v in (1,4,4,17))
P=(4783113,6377496,6377496,8503345)

def madd(a,b):return tuple(v+w for v,w in zip(a,b))
def mmul(a,b):
    return (a[0]*b[0]+a[1]*b[2], a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2], a[2]*b[1]+a[3]*b[3])

def evaluate(x: IV, y: IV):
    z=(3+y*y)/x
    X=(x,y,y,z)
    DX=((O,Z,Z,-z/x),(Z,O,O,2*y/x))
    W=I; DW=[ZERO,ZERO]
    for letter in 'XB'+'X'*12+'BX':
        M=X if letter=='X' else B
        DM=DX if letter=='X' else (ZERO,ZERO)
        DW=[madd(mmul(d,M),mmul(W,e)) for d,e in zip(DW,DM)]
        W=mmul(W,M)
    f=(W[0]-P[0],W[1]-P[1])
    J=[[d[k] for d in DW] for k in (0,1)]
    return f,J

def certify(center: list[str], radius: str):
    c=[F(v) for v in center];rad=F(radius)
    if rad<=0 or c[0]<=rad:raise ValueError('Box must have positive x')
    box=[IV.of(v)+IV.of(rad)*IV(-SCALE,SCALE) for v in c]
    fc,Jc=evaluate(*[IV.of(v) for v in c])
    Jmid=[[v.mid() for v in row] for row in Jc]
    a,b=Jmid[0];d,e=Jmid[1];det=a*e-b*d
    if det==0:raise ArithmeticError('Singular midpoint Jacobian')
    C=[[e/det,-b/det],[-d/det,a/det]]
    _,Jbox=evaluate(*box)
    E=[[IV.of(int(i==j))-sum(C[i][k]*Jbox[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    K=[IV.of(c[i])-sum(C[i][j]*fc[j] for j in range(2))+sum(E[i][j]*IV.of(rad)*IV(-SCALE,SCALE) for j in range(2)) for i in range(2)]
    if not all(box[i].lo<K[i].lo<=K[i].hi<box[i].hi for i in range(2)):
        raise ArithmeticError('Krawczyk / fixed-point inclusion failed')
    norm=max(sum(v.abs_bound() for v in row) for row in E)
    if not norm<1:raise ArithmeticError('Contraction check failed')
    # Neither box contains the exactly known solution (x,y)=(3,0).
    if box[0].lo<=3*SCALE<=box[0].hi and box[1].lo<=0<=box[1].hi:
        raise ArithmeticError('Box contains the already known root')
    return {'center':center,'radius':radius,'box':[v.bounds() for v in box],
            'image':[v.bounds() for v in K], 'contraction_norm_upper':str(norm),
            'contraction_norm_below_1e_minus_20':norm<F(1,10**20),
            'strict_inclusion':True, 'positive_definite_by_determinant_3':True}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);ap.add_argument('--verify',action='store_true');args=ap.parse_args()
    centers=[
        ['2.97299380819299117758493389609784495774741397155657886187361411',
         '0.018911273654278090444181424461238260981382296167953064916080803049'],
        ['3.4943451066391805475573214719294212038451031732609896449235575995',
         '-0.33048510081376612951233228934416138546417449676247029490553199728']]
    result={'arithmetic':'integer fixed-point, rigorous outward rounding',
            'decimal_places':PRECISION,'word':'X B X^12 B X',
            'B':[[1,4],[4,17]],'P':[[P[0],P[1]],[P[2],P[3]]],
            'known_root':[[3,0],[0,1]],
            'coordinate_parameterization':'X(x,y)=[[x,y],[y,(3+y^2)/x]]',
            'certificates':[certify(c,'1e-40') for c in centers]}
    # Disjoint x intervals certify distinct additional roots.
    first=result['certificates'][0]['box'][0]
    second=result['certificates'][1]['box'][0]
    if not F(first[1])<F(second[0]):raise ArithmeticError('Boxes not disjoint')
    if args.verify:
        if json.loads(args.output.read_text())!=result:raise ArithmeticError('Stored certificate differs from regenerated certificate')
    else:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: two disjoint positive-definite root boxes, each a strict contraction; together with diag(3,1), at least three exact SPD solutions.')
    for c in result['certificates']:
        print('Center:',c['center'],'radius',c['radius'],'contraction norm < 1e-20:',c['contraction_norm_below_1e_minus_20'])

if __name__=='__main__':main()

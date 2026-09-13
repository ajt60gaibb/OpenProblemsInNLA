"""Exact exploratory MF-16 polynomial Krawczyk data; not a Lean proof.

Independent Fraction arithmetic, three polynomial coordinates, no inverse Expr.
The adapted root is Colbrook's second additional solution. Arithmetic operations
mirror LeanCert's rational-interval const/var/add/mul/neg AD fragment and its
strong norm-form image enclosure. No numerical result is an assumed theorem.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import math

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q
    def __post_init__(self): assert self.lo <= self.hi
    @staticmethod
    def point(a): return Interval(Q(a), Q(a))
    def __add__(self, b):
        if not isinstance(b, Interval): b = Interval.point(b)
        return Interval(self.lo + b.lo, self.hi + b.hi)
    __radd__ = __add__
    def __neg__(self): return Interval(-self.hi, -self.lo)
    def __sub__(self, b): return self + (-b if isinstance(b, Interval) else -Q(b))
    def __rsub__(self, a): return Interval.point(a) - self
    def __mul__(self, b):
        if not isinstance(b, Interval): b = Interval.point(b)
        v = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Interval(min(v), max(v))
    __rmul__ = __mul__
    def mag(self): return max(abs(self.lo), abs(self.hi))

def const(a): return ('c', Q(a))
def var(i): return ('v', i)
def add(a,b): return ('a',a,b)
def neg(a): return ('n',a)
def sub(a,b): return add(a,neg(b))
def mul(a,b): return ('m',a,b)
def scale(a,b): return mul(const(a),b)

def system():
    x,y,z = [var(i) for i in range(3)]
    s=add(x,z); s2=mul(s,s)
    u=mul(s,sub(mul(s2,add(mul(s2,sub(mul(s2,add(mul(s2,sub(s2,const(30))),const(324))),const(1512))),const(2835))),const(1458)))
    v=scale(3,sub(mul(s2,add(mul(s2,sub(mul(s2,add(mul(s2,sub(s2,const(27))),const(252))),const(945))),const(1215))),const(243)))
    a=add(x,scale(4,y)); b=add(scale(4,x),scale(17,y))
    c=add(y,scale(4,z)); d=add(scale(4,y),scale(17,z))
    aa=mul(a,a); bb=mul(b,b); ac=mul(a,c); bd=mul(b,d)
    cubic11=add(add(mul(x,aa),scale(2,mul(y,mul(a,b)))),mul(z,bb))
    cubic12=add(add(mul(x,ac),mul(y,add(mul(a,d),mul(b,c)))),mul(z,bd))
    return (sub(sub(mul(x,z),mul(y,y)),const(3)),
            sub(sub(mul(u,cubic11),mul(v,add(aa,bb))),const(4783113)),
            sub(sub(mul(u,cubic12),mul(v,add(ac,bd))),const(6377496)))

def evaluate(F, box):
    zero=Interval.point(0); one=Interval.point(1)
    @lru_cache(None)
    def run(e):
        op=e[0]
        if op=='c': return Interval.point(e[1]),(zero,)*3
        if op=='v': return box[e[1]],tuple(one if j==e[1] else zero for j in range(3))
        a,da=run(e[1])
        if op=='n': return -a,tuple(-g for g in da)
        b,db=run(e[2])
        if op=='a': return a+b,tuple(da[j]+db[j] for j in range(3))
        assert op=='m'
        return a*b,tuple(da[j]*b+a*db[j] for j in range(3))
    out=[run(e) for e in F]
    return [v for v,d in out],[list(d) for v,d in out]

def inverse(A):
    n=len(A); M=[list(row)+[Q(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
    for k in range(n):
        pivot=next(i for i in range(k,n) if M[i][k]);M[k],M[pivot]=M[pivot],M[k]
        d=M[k][k];M[k]=[a/d for a in M[k]]
        for i in range(n):
            if i!=k:
                c=M[i][k];M[i]=[a-c*b for a,b in zip(M[i],M[k])]
    return [row[n:] for row in M]

def determinant(A):
    a,b,c=A[0];d,e,f=A[1];g,h,i=A[2]
    return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def round_to(x,digits):
    s=10**digits
    return Q(math.floor(x*s+Q(1,2)),s)

def check(F,center,radius,C):
    box=[Interval(c-radius,c+radius) for c in center]
    fc,jc=evaluate(F,[Interval.point(c) for c in center])
    _,J=evaluate(F,box)
    defect=[[Interval.point(int(i==j))-sum((C[i][k]*J[k][j] for k in range(3)),Interval.point(0)) for j in range(3)] for i in range(3)]
    q=max(sum(e.mag() for e in row) for row in defect)
    displacement=[-sum((C[i][j]*fc[j] for j in range(3)),Interval.point(0)) for i in range(3)]
    worst=max(d.mag() for d in displacement)
    image=[Interval.point(center[i])+displacement[i]+Interval(-q*radius,q*radius) for i in range(3)]
    strict=all(box[i].lo<image[i].lo and image[i].hi<box[i].hi for i in range(3))
    return {'pass': determinant(C)!=0 and q<1 and strict,
            'center':center,'radius':radius,'preconditioner':C,'det_preconditioner':determinant(C),
            'contraction':q,'center_displacement':worst,'image_radius_bound':worst+q*radius,
            'strict_inclusion':strict,'margin':radius-worst-q*radius,
            'box':box,'center_residual':fc,'center_jacobian':jc}

def json_value(v):
    if isinstance(v,Q): return str(v)
    if isinstance(v,Interval): return [str(v.lo),str(v.hi)]
    if isinstance(v,(list,tuple)):return [json_value(x) for x in v]
    if isinstance(v,dict): return {k:json_value(x) for k,x in v.items()}
    return v

def main():
    F=system()
    x=Q('3.4943451066391805475573214719294212038451031732609896449235575995')
    y=Q('-0.33048510081376612951233228934416138546417449676247029490553199728')
    z=(3+y*y)/x
    attempts=[]; selected=None
    for digits in (10,12,14):
        center=[round_to(c,digits) for c in (x,y,z)]
        _,jc=evaluate(F,[Interval.point(c) for c in center])
        exact_inverse=inverse([[j.lo for j in row] for row in jc])
        for cdigits in (10,12,14):
            C=[[round_to(c,cdigits) for c in row] for row in exact_inverse]
            for rexp in (6,7,8,9):
                result=check(F,center,Q(1,10**rexp),C)
                attempts.append({'center_digits':digits,'C_digits':cdigits,'radius_power':rexp,
                    'pass':result['pass'],'q_float_diagnostic':float(result['contraction']),
                    'displacement_float_diagnostic':float(result['center_displacement'])})
                if result['pass'] and result['contraction'] < Q(1,10) and result['margin']>result['radius']/2:
                    selected=result;break
            if selected:break
        if selected:break
    print(json.dumps({'attempts':attempts,'selected':json_value(selected)},indent=2))
    assert selected

if __name__=='__main__':main()

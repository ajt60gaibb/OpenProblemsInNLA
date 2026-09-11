#!/usr/bin/env python3
"""Exact rational/interval examples for the GDN critical-exponent lower bound.

This verifies finite illustrative examples, not the all-dimensions asymptotic
proof in the manuscript. Only Python's standard library is required.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)

@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self):
        require(self.lo <= self.hi, 'reversed interval')
    @staticmethod
    def val(x):
        return x if isinstance(x,I) else I(F(x),F(x))
    def __add__(self, other):
        o=I.val(other); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self, other): return self+-I.val(other)
    def __rsub__(self, other): return I.val(other)+-self
    def __mul__(self, other):
        o=I.val(other); v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self, other):
        o=I.val(other);require(o.lo*o.hi>0,'division interval contains zero')
        return self*I(1/o.hi,1/o.lo)
    def __pow__(self, n: int):
        require(isinstance(n,int) and n>=0,'nonnegative integer power required')
        r=I.val(1);b=self
        while n:
            if n%2:r=r*b
            b=b*b;n//=2
        return r
    def sqrt(self, bits: int=512):
        require(self.lo>0,'positive interval required for square root')
        scale=1<<bits
        a=isqrt((self.lo.numerator*scale*scale)//self.lo.denominator)
        b=isqrt((self.hi.numerator*scale*scale)//self.hi.denominator)+1
        return I(F(a,scale),F(b,scale))
    def round_out(self, places: int=80):
        scale=10**places
        lo=(self.lo.numerator*scale)//self.lo.denominator
        hi=-((-self.hi.numerator*scale)//self.hi.denominator)
        return I(F(lo,scale),F(hi,scale))
    def dump(self):return [str(self.lo),str(self.hi)]


def q(x, e: F, m: int):
    out=1
    for i in range(1,m+1):out=out*(x-i*e)
    return out

def dq(x,e: F,m: int):
    out=0
    for j in range(1,m+1):
        t=1
        for i in range(1,m+1):
            if i!=j:t=t*(x-i*e)
        out=out+t
    return out

def p(x,e: F,m: int):return q(x,e,m)*(x-1)*(x-2)-F(1,4)*e**m

def dp(x,e: F,m: int):return dq(x,e,m)*(x-1)*(x-2)+q(x,e,m)*(2*x-3)

def isolate(lo: F,hi: F,e: F,m: int,steps: int=200):
    plo=p(lo,e,m);phi=p(hi,e,m)
    require(plo*phi<0,'initial endpoints do not bracket a root')
    for _ in range(steps):
        mid=(lo+hi)/2;pm=p(mid,e,m)
        if pm==0:
            # Retain a nondegenerate sign-changing interval around a rational root.
            lo=(lo+mid)/2;hi=(mid+hi)/2;plo=p(lo,e,m);phi=p(hi,e,m)
        elif pm*plo<0:hi=mid;phi=pm
        else:lo=mid;plo=pm
    require(p(lo,e,m)*p(hi,e,m)<0,'root isolation failed')
    return I(lo,hi)

def evaluate(n: int,e: F,roots: list[I]):
    m=n-2
    require(3<=n<=40,'unsupported example order')
    require(0<e<=F(1,8*(m+1)),'epsilon outside proven GDN range')
    require(len(roots)==n,'wrong root count')
    for j,r in enumerate(roots):
        require(r.lo>0,'root interval not positive')
        require(p(r.lo,e,m)*p(r.hi,e,m)<0,'no sign-changing root bracket')
        if j:require(roots[j-1].hi<r.lo,'overlapping root intervals')
    total=I.val(0)
    for r in roots:
        # alpha = 2m - 1/2. Use the root identity to avoid cancellation
        # in the small product (lambda-1)(lambda-2).
        term=(r**(2*m-1))*r.sqrt()/(q(r,e,m)*dp(r,e,m))
        total=(total+F(1,4)*term).round_out()
    require(total.hi<0,'negativity was not certified')
    return total

def create():
    examples=[]
    for n in range(3,11):
        m=n-2;e=F(1,10**(6*m))
        initial=[(e*(F(j)-F(1,4)),e*(F(j)+F(1,4))) for j in range(1,m+1)]
        initial += [(F(3,4),F(1)),(F(2),F(9,4))]
        roots=[isolate(a,b,e,m) for a,b in initial]
        value=evaluate(n,e,roots)
        examples.append(dict(n=n,epsilon=str(e),alpha=str(F(4*m-1,2)),
            root_intervals=[r.dump() for r in roots],
            normalized_entry_interval=value.dump()))
        print('certified n=',n,'alpha=',F(4*m-1,2),'normalized entry',float(value.lo),float(value.hi))
    return dict(schema='gdn-critical-exponent-examples-v1',kappa='1/4',examples=examples)

def verify(data):
    require(data.get('schema')=='gdn-critical-exponent-examples-v1','unknown schema')
    require(F(data['kappa'])==F(1,4),'wrong kappa')
    require([d['n'] for d in data['examples']]==list(range(3,11)),'missing examples')
    for d in data['examples']:
        n=d['n'];m=n-2
        require(F(d['alpha'])==F(4*m-1,2),'wrong exponent')
        roots=[I(F(a),F(b)) for a,b in d['root_intervals']]
        out=evaluate(n,F(d['epsilon']),roots)
        require(out.dump()==d['normalized_entry_interval'],'stored interval mismatch')
    print('PASS: eight exact GDN examples with a certified negative noninteger power entry.')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    if args.verify:verify(json.loads(args.certificate.read_text()))
    else:
        data=create();args.certificate.parent.mkdir(parents=True,exist_ok=True)
        args.certificate.write_text(json.dumps(data,indent=2)+'\n');verify(data)

if __name__=='__main__':main()

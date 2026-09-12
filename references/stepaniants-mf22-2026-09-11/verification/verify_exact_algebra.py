#!/usr/bin/env python3
"""Exact Gaussian-integer polynomial checks for the MF-22 proof.
All polynomials are in r and use integer coefficients; no float arithmetic.
"""
import json
from pathlib import Path
from hashlib import sha256
class G:
 def __init__(self,a=0,b=0): self.a,self.b=a,b
 def __add__(self,o):
  if not isinstance(o,G): o=G(o)
  return G(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self): return G(-self.a,-self.b)
 def __sub__(self,o): return self+-o
 def __mul__(self,o):
  if not isinstance(o,G): o=G(o)
  return G(self.a*o.a-self.b*o.b,self.a*o.b+self.b*o.a)
 __rmul__=__mul__
 def __eq__(self,o): return isinstance(o,G) and (self.a,self.b)==(o.a,o.b)
 def conj(self):return G(self.a,-self.b)
 def pair(self):return [self.a,self.b]
I=G(0,1)
def poly(*x):return [v if isinstance(v,G) else G(v) for v in x]
def trim(p):
 while len(p)>1 and p[-1]==G():p.pop()
 return p

def add(p,q):
 z=[G() for _ in range(max(len(p),len(q)))];
 for j,x in enumerate(p): z[j]=z[j]+x
 for j,x in enumerate(q): z[j]=z[j]+x
 return trim(z)
def neg(p):return [-x for x in p]
def sub(p,q):return add(p,neg(q))
def mul(p,q):
 z=[G() for _ in range(len(p)+len(q)-1)]
 for j,x in enumerate(p):
  for k,y in enumerate(q):z[j+k]=z[j+k]+x*y
 return trim(z)
def scale(p,k):return [k*x for x in p]
def conj(p):return [x.conj() for x in p]
def zprod(p,q):
 z=[poly(0) for _ in range(len(p)+len(q)-1)]
 for j,x in enumerate(p):
  for k,y in enumerate(q):z[j+k]=add(z[j+k],mul(x,y))
 return z
A=poly(-6*I,-1);B=poly(-30*I,-7);C=poly(-30*I,7)
D=poly(-30*I,-25);E=poly(-6*I,1);F=poly(-30*I,25)
a=poly(30,-10*I,-1);b=poly(-240,80*I,24);c=poly(420,0,-46)
alpha=[A,poly(0,-24),F];h=[B,poly(96*I),C];ell=[D,poly(0,24),E]
den=[sub(x,y) for x,y in zip(zprod(alpha,ell),zprod(h,h))]
assert den==[scale(x,24) for x in [a,b,c,conj(b),conj(a)]]
N=[a,poly(-120,22*I,-1),poly(36,0,2)]
assert [sub(mul(A,x),mul(B,y)) for x,y in zip(ell,h)]==[scale(x,24) for x in N]
AhBalpha=[sub(mul(A,x),mul(B,y)) for x,y in zip(h,alpha)]
assert AhBalpha==[poly(0),scale(poly(24,-34*I,-7),24),scale(poly(30,22*I,7),24)]
# resultant of h(z), ell(z)
u=sub(mul(C,D),mul(B,E))
v=sub(mul(C,poly(0,24)),mul(poly(96*I),E))
w=sub(mul(poly(96*I),D),mul(B,poly(0,24)))
res=sub(mul(u,u),mul(v,w))
assert res==poly(2177280,622080*I,946944,241920*I)
W=poly(-24,34*I,7);V=poly(30,22*I,7)
num=add(add(mul(N[0],mul(V,V)),mul(N[1],mul(W,V))),mul(N[2],mul(W,W)))
assert num==poly(134136,-103032*I,32436,-40632*I,-10404,840*I)
R=poly(134136,32436,-10404);J=poly(-103032,-40632,840)
assert add(scale(R,70),scale(J,867))==poly(-79939224,-32957424)
assert 3337**2-4*120*34200==-5280431
# Cubic discriminant b²c²−4ac³−4b³d−27a²d²+18abcd.
ra=poly(-60,0,6);rb=poly(0,25);rc=poly(-30,0,5);rd=poly(0,15)
disc=mul(mul(rb,rb),mul(rc,rc))
disc=add(disc,scale(mul(ra,mul(rc,mul(rc,rc))),-4))
disc=add(disc,scale(mul(mul(rb,mul(rb,rb)),rd),-4))
disc=add(disc,scale(mul(mul(ra,ra),mul(rd,rd)),-27))
disc=add(disc,scale(mul(mul(ra,rb),mul(rc,rd)),18))
assert disc==poly(-6480000,0,-5269500,0,-855000,0,83425,0,-3000)
report={'verdict':'PASS','arithmetic':'Gaussian integer polynomial arithmetic, no floating point','checks':['quartic denominator','quadratic numerator','common-root elimination','quadratic resultant','rational-root substitution','positive-parameter contradiction','discriminant and positivity constants'],'source_sha256':sha256(Path(__file__).with_name('reviewed-proof.md').read_bytes()).hexdigest()}
Path(__file__).with_name('exact-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

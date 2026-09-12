"""Separate-method exact author-independent coefficient check; standard library only.
Polynomials in (r,z) over Gaussian integers; no floating-point arithmetic.
"""
from dataclasses import dataclass
from pathlib import Path
import hashlib,json

@dataclass
class P:
    c: dict
    def __post_init__(self): self.c={k:v for k,v in self.c.items() if v!=(0,0)}
    @staticmethod
    def cast(q): return q if isinstance(q,P) else P({(0,0):(q,0)})
    def __add__(a,b):
        b=P.cast(b); d=a.c.copy()
        for k,v in b.c.items():
            t=d.get(k,(0,0)); d[k]=(t[0]+v[0],t[1]+v[1])
        return P(d)
    __radd__=__add__
    def __neg__(a): return P({k:(-v[0],-v[1]) for k,v in a.c.items()})
    def __sub__(a,b): return a+-P.cast(b)
    def __rsub__(a,b): return P.cast(b)+-a
    def __mul__(a,b):
        b=P.cast(b); d={}
        for (r,z),(u,v) in a.c.items():
            for (s,t),(x,y) in b.c.items():
                k=(r+s,z+t); h=d.get(k,(0,0)); d[k]=(h[0]+u*x-v*y,h[1]+u*y+v*x)
        return P(d)
    __rmul__=__mul__
    def __pow__(a,n):
        assert isinstance(n,int) and n>=0
        b=P.cast(1)
        for _ in range(n): b=b*a
        return b
    def conj(a):return P({k:(v[0],-v[1]) for k,v in a.c.items()})
    def at_z(a,z):
        out=P.cast(0)
        for (j,k),(re,im) in a.c.items():out+=P({(j,0):(re,im)})*z**k
        return out

def check(a,b,name):
    assert (a-P.cast(b)).c=={},(name,(a-P.cast(b)).c)
    passed.append(name)

passed=[]
r=P({(1,0):(1,0)});z=P({(0,1):(1,0)});I=P({(0,0):(0,1)})
A=-r-6*I;B=-7*r-30*I;C=7*r-30*I;D=-25*r-30*I;E=r-6*I;F=25*r-30*I
a=30-r*r-10*I*r;b=24*r*r+80*I*r-240;c=420-46*r*r
al=A-24*r*z+F*z*z;h=B+96*I*z+C*z*z;ell=D+24*r*z+E*z*z
N=a+(-120-r*r+22*I*r)*z+2*(r*r+18)*z*z
d=a+b*z+c*z*z+b.conj()*z**3+a.conj()*z**4
check(A*D-B*B,24*a,'invertible two-by-two transfer coefficient')
check(A*ell-B*h,24*N,'generating numerator')
check(al*ell-h*h,24*d,'generating denominator')
res=(C*D-B*E)**2-(C*24*r-96*I*E)*(96*I*D-B*24*r)
check(res,2177280+946944*r*r+I*(622080*r+241920*r**3),'quadratic resultant')
check(A*h-B*al,24*z*(24-7*r*r-34*I*r+(7*r*r+30+22*I*r)*z),'coprimality elimination')
num=7*r*r-24+34*I*r;den=7*r*r+30+22*I*r
R=134136+32436*r*r-10404*r**4;Ip=-103032-40632*r*r+840*r**4
check(a*den**2+(-120-r*r+22*I*r)*num*den+2*(r*r+18)*num**2,R+I*r*Ip,'rational-root substitution')
check(70*R+867*Ip,-79939224-32957424*r*r,'positive-parameter exclusion')
p=a*z**4+b*z**3+c*z*z+b.conj()*z+a.conj()
q=a*z**3+(a+b)*z*z-(a.conj()+b.conj())*z-a.conj()
check(p,(z-1)*q,'simple unit root factorization')
check(q.at_z(P.cast(1)),120*I*r,'q(1)')
check(q.at_z(P.cast(-1)),48*(r*r-10),'q(-1)')
RR=6*(r*r-10)*z**3+25*r*z*z+5*(r*r-6)*z+15*r
plus=1+I*z;minus=1-I*z
check(a*plus**3+(a+b)*plus**2*minus-(a.conj()+b.conj())*plus*minus**2-a.conj()*minus**3,8*I*RR,'Cayley homogeneous cubic')
check(RR.at_z(-I),-I*a,'Cayley pole exclusion at -i')
check(RR.at_z(I),I*a.conj(),'Cayley zero exclusion at i')
u=6*(r*r-10);v=25*r;w=5*(r*r-6);t=15*r
Disc=v*v*w*w-4*u*w**3-4*v**3*t-27*u*u*t*t+18*u*v*w*t
check(Disc,-25*r**4*(120*r**4-3337*r*r+34200)-5269500*r*r-6480000,'cubic discriminant')
# Companion-block determinant: det(z^2 L-z K1-K2)=det(L) det(z I-T).
q11=z*z*A-z*24*r+F;q12=z*z*B+z*96*I+C
q22=z*z*D+z*24*r+E
check(q11*q22-q12*q12,24*p,'direct four-by-four characteristic polynomial')
# Check each scalar coefficient in the finite recurrence against the canonical blocks.
rawB={-1:[[-1,0],[-5,0]],0:[[0,-5],[16,-5]],1:[[-5,16],[-5,0]],2:[[0,-5],[0,-1]]}
rawC={-1:[[1,0],[7,0]],0:[[24,7],[0,25]],1:[[-25,0],[-7,-24]],2:[[0,-7],[0,-1]]}
expected={-1:[[A,0],[B,0]],0:[[-24*r,B],[96*I,D]],1:[[F,96*I],[C,24*r]],2:[[0,C],[0,E]]}
for k in rawB:
    for j in range(2):
        for l in range(2):check(6*I*rawB[k][j][l]-r*rawC[k][j][l],expected[k][j][l],f'canonical coefficient {k},{j},{l}')
source=Path(__file__).with_name('reviewed-proof.md')
result={'outcome':'PASS','arithmetic':'Gaussian-integer bivariate polynomial ring; no floating point','checks':passed,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
out=Path(__file__).with_name('exact_identity_check.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'outcome':'PASS','checks':len(passed),'source_sha256':result['source_sha256']}))

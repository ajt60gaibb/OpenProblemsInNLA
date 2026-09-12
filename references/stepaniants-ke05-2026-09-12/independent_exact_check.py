"""Independent standard-library symbolic check of the literal KE-05 recurrence.
No author checker, partition-scan implementation, or numerical library is imported.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

class Poly:
    """Sparse polynomial over Q in (e,a,b,c,d)."""
    def __init__(self,x=0):
        if isinstance(x,Poly):self.t=dict(x.t)
        elif isinstance(x,dict):self.t={k:F(v) for k,v in x.items() if v}
        else:self.t={(0,0,0,0,0):F(x)} if x else {}
    def __add__(self,other):
        other=Poly(other);out=dict(self.t)
        for k,v in other.t.items():out[k]=out.get(k,F(0))+v
        return Poly(out)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.t.items()})
    def __sub__(self,other):return self+-Poly(other)
    def __rsub__(self,other):return Poly(other)+-self
    def __mul__(self,other):
        other=Poly(other);out={}
        for k,v in self.t.items():
            for l,w in other.t.items():
                h=tuple(x+y for x,y in zip(k,l));out[h]=out.get(h,F(0))+v*w
        return Poly(out)
    __rmul__=__mul__
    def __eq__(self,other):return self.t==Poly(other).t
    def div_e(self):
        assert all(k[0]>=1 for k in self.t)
        return Poly({(k[0]-1,)+k[1:]:v for k,v in self.t.items()})
    def at_e0(self):return Poly({k:v for k,v in self.t.items() if k[0]==0})

def var(i):
    k=[0]*5;k[i]=1;return Poly({tuple(k):1})
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def sub(A,B):return [[A[i][j]-B[i][j] for j in range(2)] for i in range(2)]
def scale(t,A):return [[t*v for v in row] for row in A]
def det(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def adj(A):return [[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]]
def inv(A):
    z=det(A);assert z
    return [[v/z for v in row] for row in adj(A)]
def eq(A,B):return all(A[i][j]==B[i][j] for i in range(2) for j in range(2))
def serial(A):return [[str(v) for v in row] for row in A]

# Universal conjugated-basis identity, not merely a finite sample.
e,a,b,c,d=[var(i) for i in range(5)]
Ip=[[Poly(1),Poly(0)],[Poly(0),Poly(1)]]
Pp=[[Poly(0),Poly(0)],[Poly(0),Poly(1)]]
C=[[a,b],[c,d]];T=sub(scale(e,C),Pp);D=det(T)
assert D==e*(e*det(C)-a)
U=mul(mul(adj(T),scale(e,C)),T)
U1=[[v.div_e() for v in row] for row in U]
U0=[[v.at_e0() for v in row] for row in U1]
assert eq(U0,mul(mul(sub(Ip,Pp),C),Pp))
assert eq(U0,[[Poly(0),b],[Poly(0),Poly(0)]])
Rnum=sub(scale(2*D,Ip),U)
assert det(Rnum)==D*D*det(sub(scale(2,Ip),scale(e,C)))
# Therefore H=U/D has limit [[0,-b/a],[0,0]] when a!=0;
# det((2I-H)(2I-P))=2 det(2I-eC), before imposing trace C=3, det C=2.

# Exact nonorthogonal witness and literal reorders at rational parameters.
I=[[F(1),F(0)],[F(0),F(1)]]
C0=[[F(1),F(0)],[F(0),F(2)]];P0=[[F(0),F(0)],[F(0),F(1)]]
O3=[[F(1),F(2)],[F(3),F(5)]];P=mul(mul(inv(O3),P0),O3)
assert eq(P,[[F(6),F(10)],[F(-3),F(-5)]])
Q=mul(mul(sub(I,P),C0),P)
K=mul(sub(I,P),C0);kap=K[0][0]+K[1][1]
assert kap==7;N=scale(-1/kap,Q)
assert eq(N,scale(F(1,7),[[F(-30),F(-50)],[F(18),F(30)]]))
assert det(N)==0 and eq(mul(N,N),[[F(0)]*2 for _ in range(2)])
assert sum(v*v for row in N for v in row)==F(4624,49)
rows=[]
for eps in (F(1,6),F(1,1000),F(1,100000),F(1,10000000)):
    Ls=[scale(F(2),I),scale(eps,C0),P0];Os=[I,I,O3]
    Bs=[mul(mul(inv(Os[j]),Ls[j]),Os[j]) for j in range(3)]
    for k in range(3):
        order=[k]+[i for i in range(3) if i!=k]
        bs=[Bs[j] for j in order];ls=[Ls[j] for j in order];oms=[Os[j] for j in order]
        hats=[None]*3;Ss=[None]*3
        for i in range(2,-1,-1):
            Z=I
            for j in range(i+1,3):Z=sub(mul(bs[i],Z),mul(Z,hats[j]))
            Ss[i]=Z;Ohat=mul(oms[i],Z)
            hats[i]=mul(mul(inv(Ohat),ls[i]),Ohat)
            assert eq(hats[i],mul(mul(inv(Z),bs[i]),Z))
        if k==0:
            assert det(Ss[0])==2*(2-eps)*(2-2*eps)
            explicit=scale(F(1)/(2*eps-7),[[2*eps*eps-7*eps+30,20*eps+50],[3*eps-18,4*eps*eps-14*eps-30]])
            assert eq(hats[1],explicit)
        rows.append({'epsilon':str(eps),'k':k+1,'order':[j+1 for j in order],'S_determinants':[str(det(Z)) for Z in Ss]})
root=Path(__file__).parent
candidate=root/'reviewed-proof.md'
source=candidate.read_bytes();expected='51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f'
assert hashlib.sha256(source).hexdigest()==expected
out={'status':'PASS','scope':'Universal polynomial identities in Q[e,a,b,c,d], exact nonorthogonal witness, and twelve literal reordered rational instances. The full Gaussian argument is independently audited in the review, not proved by finite instances.',
 'reviewed_proof_bytes':len(source),'reviewed_proof_sha256':expected,
 'universal_checks':['det(eC−P)=e(e det C−a) when P=diag(0,1)',
 'lim adj(eC−P)eC(eC−P)/det(eC−P)=[[0,−b/a],[0,0]] for a!=0',
 'det((2I−H)(2I−P))=2 det(2I−eC)'],
 'witness_kappa':str(kap),'witness_limit':serial(N),'witness_limit_spectral_norm':'68/7',
 'exact_reordered_instances':rows,'dependencies':'Python standard library only'}
(root/'independent-exact-output.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

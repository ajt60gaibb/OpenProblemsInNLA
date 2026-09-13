"""Independent exact RA09 statement diagnostics; no universal Lean proof.
Only Python integer/Fraction arithmetic is used. Polynomial identities are
expanded coefficientwise; scalar/matrix instances only test transcription.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
class Poly:
    def __init__(self,x=0): self.v=x if isinstance(x,dict) else ({(0,0):F(x)} if x else {})
    def __add__(self,o):
        o=o if isinstance(o,Poly) else Poly(o);r=self.v.copy()
        for k,v in o.v.items():r[k]=r.get(k,F(0))+v
        return Poly({k:v for k,v in r.items() if v})
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.v.items()})
    def __sub__(self,o):return self+-Poly(o) if not isinstance(o,Poly) else self+-o
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        o=o if isinstance(o,Poly) else Poly(o);r={}
        for a,x in self.v.items():
            for b,y in o.v.items():
                k=(a[0]+b[0],a[1]+b[1]);r[k]=r.get(k,F(0))+x*y
        return Poly({k:v for k,v in r.items() if v})
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly(1)
        for _ in range(n):r=r*self
        return r
    def __truediv__(self,q):return self*F(1,q)
d=Poly({(1,0):F(1)});z=Poly({(0,1):F(1)})
q=2*(d+1)*z**2-(2*d+1)*z+d
sos=2*(d-1)*(z-F(1,2))**2+(d-1)/2+4*(z-F(3,8))**2+F(7,16)
residuals={
 'sum_of_squares':q-sos,
 'branch_below_one':z*(2*d*d*z-2*z-d*d+1)-d*(d-1)*(z-1)-(d-1)*q,
 'branch_middle':z*(2*d*d-2*z-d*d+1)-d*(d-1)*(z-1)-(d-z)*(2*z+d-1),
 'branch_above_d':z*(2*d*z-2*z-d*d+1)-d*(d-1)*(z-1)-(d-1)*(z-d)*(2*z-1)}
assert all(not x.v for x in residuals.values())
coords=list(map(F,[0,F(1,7),F(1,2),1,3,7]));pos=coords[1:]
scalar_count=zero_count=consequence_count=0
for intercept,slope,cap in product(map(F,[0,F(1,3),2]),map(F,[0,F(1,2),1,3]),map(F,[0,F(1,3),2])):
    fn=lambda x:intercept+min(slope*x,cap)
    for tau in pos:
        c=fn(tau)/tau
        for x,y in product(coords,repeat=2):
            if 0<x<=y:assert fn(y)/y<=fn(x)/x
            if x<=tau:assert c*x<=fn(x)
            if tau<=x:assert fn(x)<=c*x
            if x<=y and tau<=y:assert 0<=fn(y)-fn(x)<=c*(y-x)
            if fn(tau)==0:assert fn(x)==0
            consequence_count+=1
        if fn(tau)>0:
            for a,b in product(pos,repeat=2):
                lhs=fn(b)*max(fn(b)-c*b,0)*(1-b/a)
                rhs=max(c*c*a*a-fn(a)**2,0)+2*fn(b)*fn(a)-2*c*c*b*a-fn(b)**2+c*c*b*b
                assert lhs<=rhs,(intercept,slope,cap,tau,a,b,lhs,rhs)
                scalar_count+=1
    for tau in coords:
        c=fn(tau)/tau if tau else F(0)
        aa=list(map(F,[0,F(1,2),7]));pp=[F(1,9),F(4,9),F(4,9)]
        lhs=fn(0)**2-2*fn(0)*sum(p*fn(a) for a,p in zip(aa,pp))
        rhs=sum(p*max(c*c*a*a-fn(a)**2,0) for a,p in zip(aa,pp))
        assert lhs<=rhs;zero_count+=1

def mat(x):return [[F(v) for v in row] for row in x]
def trn(a):return list(map(list,zip(*a)))
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def sub(a,b):return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def diag(v):return [[x if i==j else F(0) for j in range(len(v))] for i,x in enumerate(v)]
def eye(n):return diag([F(1)]*n)
def trace(a):return sum(a[i][i] for i in range(len(a)))
def fsq(a):return sum(x*x for r in a for x in r)
def comb(q,v):return mul(mul(q,diag(v)),trn(q))
def det(a):
    if not a:return F(1)
    return sum((-1)**j*a[0][j]*det([row[:j]+row[j+1:] for row in a[1:]]) for j in range(len(a)))
def principal(a):
    assert a==trn(a)
    r={','.join(map(str,s)):det([[a[i][j] for j in s] for i in s]) for k in range(1,len(a)+1) for s in combinations(range(len(a)),k)}
    assert all(x>=0 for x in r.values()),r
    return r
c,s=F(5,13),F(12,13)
qmat=mat([[c,0,-s],[0,1,0],[s,0,c]])
assert mul(trn(qmat),qmat)==eye(3)==mul(qmat,trn(qmat))
a=list(map(F,[5,3,1]));b=list(map(F,[1,F(1,2),F(1,4)]));A=diag(a);H=comb(qmat,b)
order_principal=principal(sub(A,H));assert mul(A,H)!=mul(H,A)
k=2;B=comb(qmat,b[:k]+[F(0)])
f=lambda x:F(2)+min(x,F(2));FA=diag(list(map(f,a)));C=comb(qmat,list(map(f,b[:k]))+[F(0)])
p=[[x*x for x in row] for row in qmat]
assert all(sum(row[j] for row in p)==1 for j in range(3))
assert all(sum(row[:k])<=1 for row in p)
e=fsq(sub(A,B));ef=fsq(sub(FA,C));tail=sum(x*x for x in a[k:]);ftail=sum(f(x)**2 for x in a[k:])
e_exp=sum(x*x for x in a)+sum(x*x for x in b[:k])-2*sum(b[j]*sum(p[i][j]*a[i] for i in range(3)) for j in range(k))
ef_exp=sum(f(x)**2 for x in a)+sum(f(x)**2 for x in b[:k])-2*sum(f(b[j])*sum(p[i][j]*f(a[i]) for i in range(3)) for j in range(k))
assert e==e_exp and ef==ef_exp
cross=trace(mul(B,sub(A,B)));deficit=fsq(A)-fsq(B)
assert e==deficit-2*cross and 0<cross and e<deficit
scale=f(a[k])/a[k]
assert ef-ftail<=scale**2*(e-tail) and scale**2*tail<=ftail
eps=deficit/tail-1
assert eps>=0 and deficit==(1+eps)*tail and ef<=(1+eps)*ftail
for j in range(3):assert b[j]*sum(p[i][j]/a[i] for i in range(3))<=1
M=mat([[1,-2,3],[4,F(1,2),F(-1,3)]])
U=mat([[F(3,5),F(-4,5)],[F(4,5),F(3,5)]])
assert mul(trn(U),U)==eye(2)
assert fsq(M)==trace(mul(trn(M),M))==fsq(mul(mul(U,M),qmat))

aa=list(map(F,[3,2,0]));v=[F(5,13),F(12,13),F(0)];bb=F(2)
outer=[[bb*x*y for y in v] for x in v]
harmonic_principal=principal(sub(diag(aa),outer))
assert sum(x*x for x in v)==1 and all(x!=0 or w==0 for x,w in zip(aa,v))
harmonic=bb*sum(w*w/x if x else F(0) for x,w in zip(aa,v))
assert harmonic==F(482,507)<1

n=4;k0=2;a0=list(map(F,[4,0,0,0]));A0=diag(a0)
q0=mat([[1,0,0,0],[0,c,0,-s],[0,0,1,0],[0,s,0,c]])
assert mul(trn(q0),q0)==eye(n) and comb(q0,a0)==A0
f0=lambda x:x+3
FA0=diag(list(map(f0,a0)));T1=diag(list(map(f0,a0[:k0]))+[F(0)]*(n-k0))
T2=comb(q0,list(map(f0,a0[:k0]))+[F(0)]*(n-k0))
assert T1!=T2 and T1!=FA0 and T2!=FA0
assert fsq(sub(FA0,T1))==fsq(sub(FA0,T2))==(n-k0)*f0(0)**2==18
assert fsq(A0)-fsq(comb(q0,a0[:k0]+[F(0)]*(n-k0)))==0
record={'scope':'Exact independent diagnostics, not Lean proofs of universal contracts.',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'universal_coefficient_identities':{n:{'residual_coefficients':{}} for n in residuals},
 'scalar_inequality_instances':scalar_count,'scalar_consequence_checks':consequence_count,
 'zero_column_including_zero_cutoff_instances':zero_count,
 'noncommuting_example':{'A':A,'Ahat':H,'A_minus_Ahat_principal_minors':order_principal,
   'k':k,'original_error':e,'trace_deficit':deficit,'cross_trace':cross,
   'function_error':ef,'tail':tail,'function_tail':ftail,'epsilon':eps,
   'overlap_expansions_exact':True,'full_canonical_implication':True},
 'rectangular_Frobenius_invariance':{'matrix':M,'squared_norm':fsq(M),'pass':True},
 'zero_coordinate_harmonic':{'a':aa,'v':v,'b':bb,'principal_minors':harmonic_principal,'harmonic':harmonic},
 'positive_f0_zero_tail':{'n':n,'k':k0,'function_zero':f0(F(0)),
   'two_actual_function_truncations_differ':True,'both_errors':18,
   'function_truncation_is_not_function_of_original_truncation':True},
 'verdict':'PASS'}
(E/'exact-reconstruction.json').write_text(json.dumps(record,indent=2,default=str)+'\n')
print('EXACT DIAGNOSTICS PASS',scalar_count,consequence_count,zero_count)

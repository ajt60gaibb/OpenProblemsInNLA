"""Independent-of-Lean exact diagnostics for the IE23 statement plan.
Standard-library Fraction matrices and a small rational polynomial ring only.
These checks are not universal Lean proof certificates and are not imported by Lean.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

OUT=Path(__file__).resolve().parent
def matrix(rows): return [[F(x) for x in row] for row in rows]
def transpose(a): return [list(row) for row in zip(*a)]
def mul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def scale(c,a): return [[F(c)*x for x in row] for row in a]
def serial(a): return [[str(x) for x in row] for row in a]
A=matrix([[1,1,0],[1,0,1]])
B=scale(F(1,3),matrix([[1,1],[2,-1],[-1,2]]))
X=matrix([[0,0],[1,0],[0,1]])
G=matrix([[2,1],[1,2]])
Gi=scale(F(1,3),matrix([[2,-1],[-1,2]]))
I=matrix([[1,0],[0,1]])
z=matrix([[1],[-1]])
assert mul(A,transpose(A))==G
assert mul(G,Gi)==mul(Gi,G)==I
assert mul(transpose(A),Gi)==B
assert mul(A,B)==mul(A,X)==I and B!=X
assert mul(transpose(B),B)==Gi
assert mul(transpose(X),X)==I
assert mul(B,z)==mul(X,z)==matrix([[0],[1],[-1]])
assert A[0][0]*A[1][1]-A[0][1]*A[1][0]==-1

# Six indeterminates cover real and imaginary parts of u,v,t. This exact
# polynomial ring makes the generic complex identities independently checkable.
N=6; ZERO=(0,)*N
class P:
    def __init__(self,terms):
        if not isinstance(terms,dict):terms={ZERO:F(terms)}
        self.t={e:F(c) for e,c in terms.items() if c}
    def __add__(self,b):
        b=b if isinstance(b,P) else P(b);out=dict(self.t)
        for e,c in b.t.items():out[e]=out.get(e,F(0))+c
        return P(out)
    __radd__=__add__
    def __neg__(self):return P({e:-c for e,c in self.t.items()})
    def __sub__(self,b):return self+-P.coerce(b)
    def __rsub__(self,b):return P.coerce(b)+-self
    def __mul__(self,b):
        b=P.coerce(b);out={}
        for e,c in self.t.items():
            for f,d in b.t.items():
                g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,F(0))+c*d
        return P(out)
    __rmul__=__mul__
    def __truediv__(self,c):return self*F(1,c)
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        r=P(1)
        for _ in range(n):r=r*self
        return r
    @staticmethod
    def coerce(x):return x if isinstance(x,P) else P(x)
    def data(self):return [{'exponent':list(e),'coefficient':str(c)} for e,c in sorted(self.t.items())]
def variable(i):e=[0]*N;e[i]=1;return P({tuple(e):F(1)})
ur,ui,vr,vi,tr,ti=[variable(i) for i in range(N)]
u=(ur,ui);v=(vr,vi);t=(tr,ti)
def cadd(a,b):return(a[0]+b[0],a[1]+b[1])
def cscale(c,a):return(c*a[0],c*a[1])
def ns(a):return a[0]**2+a[1]**2
bu=[cscale(F(1,3),cadd(u,v)),cscale(F(1,3),cadd(cscale(2,u),cscale(-1,v))),
    cscale(F(1,3),cadd(cscale(-1,u),cscale(2,v)))]
identity_B=sum((ns(x) for x in bu),P(0))+ns(cadd(u,v))/3-ns(u)-ns(v)
identity_X=ns((P(0),P(0)))+ns(u)+ns(v)-ns(u)-ns(v)
one_minus_t=(1-tr,-ti);negative_one_minus_t=(-1-tr,-ti)
identity_competitor=ns(t)+ns(one_minus_t)+ns(negative_one_minus_t)-2-3*ns(t)
# Here ur and ui are arbitrary real a,b; no numerical grid is used.
a,b=ur,ui
sos=2*(a**4+b**4)-(a**2+b**2)**2-(a**2-b**2)**2
assert not identity_B.t and not identity_X.t and not identity_competitor.t and not sos.t
result={'status':'PASS','scope':'Exact finite rational and polynomial diagnostics; no Lean proof claim',
        'matrices':{k:serial(val) for k,val in [('A',A),('B',B),('X',X),('Gram',G),('GramInverse',Gi)]},
        'rank_minor_determinant':'-1','Gram_determinant':'3',
        'Bz_and_Xz':serial(mul(B,z)),'output_norm_squared':'2','input_fourth_norm_power':'2',
        'parameter':'4','parameter_strictly_greater_than_2':True,
        'complex_action_B_polynomial_remainder':identity_B.data(),
        'complex_action_X_polynomial_remainder':identity_X.data(),
        'all_complex_competitor_polynomial_remainder':identity_competitor.data(),
        'quartic_sum_of_squares_remainder':sos.data(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','rational_matrix_checks':9,'exact_generic_polynomial_identities':4}),flush=True)

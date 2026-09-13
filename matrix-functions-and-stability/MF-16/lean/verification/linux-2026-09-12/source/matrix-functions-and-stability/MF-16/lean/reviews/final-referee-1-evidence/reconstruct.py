"""Independent MF-16 final-referee arithmetic diagnostics.
No submitted Python verifier or reconstruction module is imported.
Inputs are exact AST and rational interval data emitted by this referee's fresh
Lean inspector. These diagnostics are not a Lean proof oracle.
"""
from pathlib import Path
from fractions import Fraction as Q
from dataclasses import dataclass
from itertools import permutations
import hashlib,json,time
E=Path(__file__).resolve().parent
data=json.loads((E/'actual-numeric.json').read_text())
started=time.monotonic()
@dataclass(frozen=True)
class I:
    lo:Q
    hi:Q
    def __post_init__(self): assert self.lo<=self.hi
    @staticmethod
    def point(x): return I(Q(x),Q(x))
    def __add__(self,x):
        if not isinstance(x,I):x=I.point(x)
        return I(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,x):return self+(-x if isinstance(x,I) else -Q(x))
    def __rsub__(self,x):return I.point(x)-self
    def __mul__(self,x):
        if not isinstance(x,I):x=I.point(x)
        p=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return I(min(p),max(p))
    __rmul__=__mul__
    def mag(self):return max(abs(self.lo),abs(self.hi))
    def dump(self):return [str(self.lo),str(self.hi)]
Z=I.point(0);O=I.point(1)
@dataclass(frozen=True)
class D:
    val:I
    der:tuple
    @staticmethod
    def const(x):return D(I.point(x),(Z,Z,Z))
    def __add__(self,x):
        if not isinstance(x,D):x=D.const(x)
        return D(self.val+x.val,tuple(a+b for a,b in zip(self.der,x.der)))
    __radd__=__add__
    def __neg__(self):return D(-self.val,tuple(-a for a in self.der))
    def __sub__(self,x):return self+(-x if isinstance(x,D) else -Q(x))
    def __rsub__(self,x):return D.const(x)-self
    def __mul__(self,x):
        if not isinstance(x,D):x=D.const(x)
        return D(self.val*x.val,tuple(a*x.val+self.val*b for a,b in zip(self.der,x.der)))
    __rmul__=__mul__
class Poly:
    def __init__(self,x=0):
        if isinstance(x,Poly):self.c=x.c.copy()
        elif isinstance(x,dict):self.c={m:Q(a) for m,a in x.items() if a}
        else:self.c={} if not x else {(0,0,0):Q(x)}
    @staticmethod
    def var(j):return Poly({tuple(int(i==j) for i in range(3)):Q(1)})
    def __add__(self,x):
        x=Poly(x);d=self.c.copy()
        for m,a in x.c.items():d[m]=d.get(m,Q(0))+a
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-a for m,a in self.c.items()})
    def __sub__(self,x):return self+(-Poly(x))
    def __rsub__(self,x):return Poly(x)-self
    def __mul__(self,x):
        x=Poly(x);d={}
        for m,a in self.c.items():
            for n,b in x.c.items():
                k=tuple(i+j for i,j in zip(m,n))
                d[k]=d.get(k,Q(0))+a*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        ans=Poly(1);b=self
        while n:
            if n%2:ans=ans*b
            n//=2
            if n:b=b*b
        return ans
    def __eq__(self,x):return self.c==Poly(x).c
    def moddet(self):
        # Monic reduction x*z -> y^2+3, with the leading x exponent decreasing.
        d={}
        for (a,b,c),v in self.c.items():
            h=min(a,c)
            coeff=Poly(1)
            for _ in range(h):coeff=coeff*(Poly.var(1)**2+3)
            for (i,j,k),w in coeff.c.items():
                m=(a-h+i,b+j,c-h+k)
                d[m]=d.get(m,Q(0))+v*w
        return Poly(d)
    def digest(self):
        return hashlib.sha256(json.dumps([[list(m),str(a)] for m,a in sorted(self.c.items())],separators=(',',':')).encode()).hexdigest()
def eval_ast(node,env,constant):
    op=node[0]
    if op=='const':
        assert len(node)==2
        return constant(Q(node[1]))
    if op=='var':
        assert len(node)==2 and isinstance(node[1],int) and 0<=node[1]<3
        return env[node[1]]
    if op=='neg':
        assert len(node)==2
        return -eval_ast(node[1],env,constant)
    assert op in ('add','mul') and len(node)==3,op
    a=eval_ast(node[1],env,constant);b=eval_ast(node[2],env,constant)
    return a+b if op=='add' else a*b
def det(M):
    n=len(M);r=0
    for p in permutations(range(n)):
        v=1
        for i in range(n):v=v*M[i][p[i]]
        r+=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*v
    return r
def mmul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def ident(n,coerce=lambda x:x):return [[coerce(int(i==j)) for j in range(n)] for i in range(n)]
def mpow(A,n):
    r=ident(len(A));b=A
    while n:
        if n%2:r=mmul(r,b)
        n//=2
        if n:b=mmul(b,b)
    return r
def word(X,B):
    r=ident(2)
    for ch in 'XB'+'X'*12+'BX':r=mmul(r,X if ch=='X' else B)
    return r
center=list(map(Q,data['center']))
box=[I(*map(Q,b)) for b in data['box']]
C=[list(map(Q,row)) for row in data['C']]
radius=Q(1,10**7)
assert len(center)==len(box)==len(C)==len(data['AST'])==3
assert all(len(row)==3 for row in C)
assert all(b.lo==c-radius and b.hi==c+radius for b,c in zip(box,center))
assert box[0].lo>3
actual_det=Q(790668616748253,62500000000000000000000000000)
assert det(C)==actual_det>0
env=[D(b,tuple(O if j==i else Z for j in range(3))) for i,b in enumerate(box)]
evaluated=[eval_ast(a,env,D.const) for a in data['AST']]
J=[e.der for e in evaluated]
claimedJ=[[I(*map(Q,z)) for z in row] for row in data['J']]
assert J==[tuple(row) for row in claimedJ]
defect=[[int(i==j)-sum(C[i][k]*J[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
assert defect==[[I(*map(Q,z)) for z in row] for row in data['I-CJ']]
q=max(sum(z.mag() for z in row) for row in defect)
assert 0<=q<Q(27,1000)<1 and q==Q(data['q'])
assert radius==Q(data['radius'])
fc=[eval_ast(a,[D.const(v) for v in center],D.const).val for a in data['AST']]
assert all(v.lo==v.hi for v in fc)
nc=[center[i]-sum(C[i][j]*fc[j] for j in range(3)) for i in range(3)]
assert nc==[I(*map(Q,v)) for v in data['newton_center']]
image=[z+I(-q*radius,q*radius) for z in nc]
assert image==[I(*map(Q,v)) for v in data['image']]
margins=[min(image[i].lo-box[i].lo,box[i].hi-image[i].hi) for i in range(3)]
assert min(margins)>radius/2
displacement=max((nc[i]-center[i]).mag() for i in range(3))
assert displacement<Q(4,10**11)

x,y,z=[Poly.var(i) for i in range(3)]
S=[[x,y],[y,z]]
B=[[1,4],[4,17]]
X0=[[3,0],[0,1]]
P=[[4783113,6377496],[6377496,8503345]]
assert word(X0,B)==P
assert det(B)==1 and det(X0)==3 and det(P)==3**14
assert P[0][0]>0 and Q(3**14+P[0][1]**2,P[0][0])==P[1][1]
s=x+z;t=s*s
u=s*(t*(t*(t*(t*(t-30)+324)-1512)+2835)-1458)
v=3*(t*(t*(t*(t*(t-27)+252)-945)+1215)-243)
U=[[u*S[i][j]-(v if i==j else 0) for j in range(2)] for i in range(2)]
S12=mpow(S,12)
assert all((S12[i][j]-U[i][j]).moddet()==0 for i in range(2) for j in range(2))
reduced=mmul(mmul(mmul(mmul(S,B),U),B),S)
W=word(S,B)
assert all((W[i][j]-reduced[i][j]).moddet()==0 for i in range(2) for j in range(2))
g=[eval_ast(a,[x,y,z],Poly) for a in data['AST']]
assert g[0]==x*z-y*y-3
assert g[1]==reduced[0][0]-P[0][0]
assert g[2]==reduced[0][1]-P[0][1]
assert (W[0][0]-P[0][0]-g[1]).moddet()==0
assert (W[0][1]-P[0][1]-g[2]).moddet()==0
assert W[0][1]==W[1][0]
assert det(W)==(x*z-y*y)**14
report={
'result':'PASS','scope':'Independent exact arithmetic diagnostics only; the formal proof consumes LeanCert kernel theorems, not this script.',
'input_sha256':hashlib.sha256((E/'actual-numeric.json').read_bytes()).hexdigest(),
'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'center':[str(a) for a in center],'box':[a.dump() for a in box],
'preconditioner_det':str(actual_det),'radius':str(radius),'q':str(q),
'q_display_only':float(q),'center_displacement':str(displacement),
'self_map_margins':[str(a) for a in margins],
'all_J_and_I_minus_CJ_endpoints_exactly_match_actual_Lean':True,
'all_newton_center_and_image_endpoints_exactly_match_actual_Lean':True,
'strict_contraction_and_self_map':True,'x_lower_endpoint_gt_three':True,
'AST_supported_fragment':'const/var012/add/mul/neg only',
'source_matrix_product_and_determinants':True,
'CH12_all_four_entries_mod_determinant':True,
'AST_two_residuals_equal_actual_reduced_word_as_polynomials':True,
'ordinary_word_all_four_entries_mod_determinant':True,
'actual_word_symmetry_and_det_power14':True,
'remaining_entry_recovery_exact':True,
'AST_polynomial_coefficient_hashes':[a.digest() for a in g],
'AST_polynomial_term_counts':[len(a.c) for a in g],
'ordinary_word_term_counts':[[len(a.c) for a in row] for row in W],
'seconds':time.monotonic()-started}
(E/'reconstruction.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'result':'PASS','exact_q_display_only':float(q),'generic_AST_terms':report['AST_polynomial_term_counts'],
'smallest_selfmap_margin_display_only':float(min(margins)),'seconds':report['seconds']}))

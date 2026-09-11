"""Fresh exact checks for PR47/62. Does not import any submitted verifier.
Run with SymPy 1.14 on PYTHONPATH. Mathematical proofs are reviewed separately.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib, json, re, subprocess
import sympy as s

OUT = Path(__file__).resolve().parent
ROOT = OUT.parent
records = {}

def checked(name, value):
    records[name] = value
    print(name, value, flush=True)

# Canonical statements compared directly against published main; no metadata
# or contributor assertion is used to infer preservation.
base = '/private/tmp/nla-review-wave2-20260911'
targets = {}
for pr, category, ids in [
    (47, 'matrix-functions-and-stability', ['MF-03','MF-14','MF-15','MF-16','MF-18','SF-01']),
    (62, 'intervals-and-absolute-value-equations', ['AV-01','AV-02','IV-02','IV-03','IV-04','IV-05','IV-06'])]:
    for ident in ids:
        rel=f'{category}/{ident}/README.md'
        old=subprocess.check_output(['git','show',f'origin/main:{rel}'],cwd=base,text=True)
        new=(ROOT/f'pr-{pr}'/rel).read_text()
        def statement(txt):
            m=re.search(r'^## Problem statement\s*\n(.*?)(?=^## |\Z)',txt,re.M|re.S)
            if not m: raise AssertionError(ident)
            return m[1].strip()
        assert statement(old)==statement(new), ident
        # Include later "Question" sections and all original downstream context.
        suffix_old=old[old.index('## Problem statement'):]
        suffix_new=new[new.index('## Problem statement'):]
        assert suffix_old==suffix_new, ident
        targets[ident]={'path':rel,'statement_identical':True,
                        'entire_original_suffix_identical':True,
                        'statement_sha256':hashlib.sha256(statement(old).encode()).hexdigest()}
checked('canonical_target_preservation',targets)

# MF03: construct Padé pairs afresh from the power series, independently of JSON.
finite=[]
for m in range(1,17):
    a=[s.Rational(1,s.factorial(2*k)) for k in range(2*m+1)]
    T=s.Matrix(m,m,lambda i,j:a[m+i-j])
    q=[s.Integer(1)]+list(T.inv()*s.Matrix([-a[m+i] for i in range(1,m+1)]))
    p=[sum(q[j]*a[k-j] for j in range(k+1)) for k in range(m+1)]
    assert all(sum(q[j]*a[k-j] for j in range(min(m,k)+1))==(p[k] if k<=m else 0)
               for k in range(2*m+1))
    B=sum(abs(q[j])*3**j for j in range(m+1)); N=sum(abs(p[j]-q[j])*3**j for j in range(m+1))
    assert B<2 and N<=2*(2-B)
    if m>=2: assert 20*N<39*(2-B)
    finite.append({'m':m,'bound':str(N/(2-B))})
checked('MF03_fresh_rational_Pade_orders_1_to_16',finite)

# MF16: independently derive the Jacobian from spectral differentiation at diag(t,1).
t,p,g,r,a,b,c=s.symbols('t p g r a b c')
X=s.diag(t,1); B=s.Matrix([[a,b],[b,c]]); Xr=s.diag(p,1)
coords=[s.Matrix([[1,0],[0,0]]),s.Matrix([[0,1],[1,0]]),s.Matrix([[0,0],[0,1]])]
columns=[]
for H in coords:
    dXr=s.Matrix([[r*p/t*H[0,0],g*H[0,1]],[g*H[1,0],r*H[1,1]]])
    D=H*B*Xr*B*X+X*B*Xr*B*H+X*B*dXr*B*X
    columns.append(s.Matrix([D[0,0],D[0,1],D[1,1]]))
J=s.Matrix.hstack(*columns)
Hr=(r+2)*(a*a*p*t+c*c+a*c*g*t)-(r-2)*b*b*(g*t+p+t)
assert s.factor((J.det()-p*t*(r+2)*(a*c-b*b)**2*Hr).subs(p,1+(t-1)*g))==0
vals={t:3,p:3**12,g:(3**12-1)//2,r:12,a:1,b:4,c:17}
assert J.subs(vals).det()==-11785057051824
checked('MF16_symbolic_factorization',{'identity':True,'exact_jacobian':str(J.subs(vals)),
       'determinant':str(J.subs(vals).det())})

# MF15: symbolic determinants and resolvent cofactors for several dimensions.
e,z=s.symbols('e z')
for n in range(3,8):
    m=n-2; A=s.diag(*[i*e for i in range(1,m+1)],1,2)
    for i in range(m): A[i,i+1]=e
    A[m,m+1]=1; A[m+1,0]=s.Rational(1,4)
    M=z*s.eye(n)-A
    expected=s.prod(z-i*e for i in range(1,m+1))*(z-1)*(z-2)-e**m/4
    assert s.expand(M.det()-expected)==0
    # inverse_(1,m) = cofactor_(m,1)/det, one-based manuscript indexing.
    numerator=(-1)**(m-1)*M.minor_submatrix(m-1,0).det()
    assert s.expand(numerator-e**(m-1)*(z-1)*(z-2))==0
checked('MF15_symbolic_charpoly_and_cofactor',{'dimensions':list(range(3,8)),'passed':True})

# MF18: new symbolic rational calculation of the Riccati and Jordan identities.
I=s.I; h=s.Rational(1,2)
A=s.Matrix([[-1,0,-h],[0,0,-h],[h,-h,0]])
Q=s.Matrix([[-2,0,0],[0,0,-1],[0,-1,-1]])
X=s.Matrix([[-1,0,h],[0,0,-h],[h,-h,(-1+I)/2]])
assert s.simplify(X+A.T*X.inv()*A-Q)==s.zeros(3)
S=s.simplify(X.inv()*A)
assert S==s.Matrix([[1,0,1],[0,1,I],[0,0,1]])
H=s.simplify((X-X.conjugate().T)/(2*I));assert H==s.diag(0,0,h)
lam=s.symbols('lam');assert s.factor((lam**2*A.T-lam*Q+A).det())==(lam-1)**6/4
M=A.row_join(s.zeros(3)).col_join(Q.row_join(-s.eye(3)))
L=s.zeros(3).row_join(s.eye(3)).col_join(A.T.row_join(s.zeros(3)))
N=L.inv()*M-s.eye(6)
assert [(N**k).rank() for k in [1,2,3]]==[4,2,0]
checked('MF18_exact_example',{'rank_ImX':H.rank(),'Jordan_nilpotent_ranks':[4,2,0],'passed':True})

# SF01: an exact common-weight comparison test with mixed off-diagonal signs.
A=s.Matrix([[2,3,0],[-1,5,1],[0,-1,3]])
def comparison(X): return s.Matrix(X.rows,X.cols,lambda i,j:abs(X[i,j]) if i==j else -abs(X[i,j]))
C=comparison(A);v=C.inv()*s.ones(3,1);assert all(x>0 for x in v)
for mode in ['Newton','Halley']:
    X=s.eye(3)+2*A
    Y=s.eye(3)+2*C
    for mu in [s.Rational(2),s.Rational(1,3),s.Rational(3,2)]:
        if mode=='Newton':
            X=(mu*X+A*X.inv()/mu)/2;Y=(mu*Y+C*Y.inv()/mu)/2
        else:
            X=mu*X;Y=mu*Y
            X=X*(X**2+3*A)*(3*X**2+A).inv()
            Y=Y*(Y**2+3*C)*(3*Y**2+C).inv()
        assert all(x>=0 for x in comparison(X)-Y)
        assert all(x>0 for x in Y*v)
        assert all(X[i,i]>0 for i in range(3))
checked('SF01_exact_scaled_Newton_Halley',{'steps_each':3,'common_weight':str(v),'passed':True})

# IV06: symbolic determinant plus the four actual eigenvectors and three gaps.
aa,bb=s.symbols('aa bb');M=s.Matrix([[25,aa,bb],[1,-1,0],[1,0,1]])
d1,d2=s.symbols('d1 d2')
assert s.expand((lam*s.eye(3)-M).det().subs({aa:-91+d1,bb:84+d2})-
   ((lam-25)*(lam**2+6)-d1*(lam-1)-d2*(lam+1)))==0
for ev,av,bv,vec in [(-3,-21,154,[-4,2,1]),(0,-16,9,[-1,-1,1]),(3,-146,29,[4,1,2]),(25,-91,84,[312,12,13])]:
    assert M.subs({aa:av,bb:bv})*s.Matrix(vec)==ev*s.Matrix(vec)
gaps={}
for ev in [-1,1,12]:
    ct=(ev-25)*(ev*ev+6);rad=75*(abs(ev-1)+abs(ev+1));gaps[str(ev)]=[ct-rad,ct+rad]
    assert ct+rad<0
checked('IV06_symbolic_counterexample',gaps)

# IV03: fresh generic adjugate/Schur identity (no invertibility of full A needed).
xx=s.symbols('x0:9');M=s.Matrix(3,3,xx)
for i in range(3):
    for j in range(3):
        if i==j:continue
        k=next(k for k in range(3) if k not in [i,j])
        assert s.expand(M.adjugate()[i,j]+M[k,k]*M[i,j]-M[i,k]*M[k,j])==0
checked('IV03_generic_3x3_adjugate_identity',True)

# AV01 exact example independent of supplied orthant enumerator.
M=s.Rational(3,5)*s.Matrix([[1,1],[-1,1]]);rhs=s.Matrix([1,2]);solutions=[]
for signs in product([-1,1],repeat=2):
    root=(M+s.diag(*signs)).inv()*rhs
    assert all(signs[i]*root[i]>0 for i in range(2))
    assert M*root+root.applyfunc(abs)==rhs
    solutions.append([str(x) for x in root])
assert M.applyfunc(abs).eigenvals()=={s.Rational(6,5):1,s.Integer(0):1}
checked('AV01_four_exact_solutions',solutions)

# AV02 full range of integer gap estimates through N=100. These are exact
# squared comparisons and include integral-square threshold boundary cases.
from math import isqrt
count=0
for N in range(3,101):
    for k in range(1,N):
        q=isqrt(144*N*N*k);threshold=8*N**3*q;lead=96*N**4;err=36*N**3
        assert threshold**2<=lead**2*k
        assert threshold>err and (threshold-err)**2>lead**2*(k-1)
        count+=1
checked('AV02_integer_threshold_gaps',{'exact_inequality_pairs':count,'passed':True})

(OUT/'independent-check-results.json').write_text(json.dumps(records,indent=2)+'\n')

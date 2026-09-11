"""Independent exact checks for PR40 and PR54, 2026-09-11.
Run with SymPy 1.14.0; no contributor verifier imported here.
Analytic arguments and scope are recorded in REPORT.md.
"""
from pathlib import Path
import itertools as it
import json
import math
import subprocess
import sympy as s

OUT=Path(__file__).parent
ROOT=OUT.parent
checks={}
def ck(name, truth):
    checks[name]=bool(truth)
    assert truth,name

# Original mathematical text must be retained byte-for-byte except dated
# status and the explicitly delimited new submission block.
for pr,cat,ids,mark in [(40,'nonnegative-and-positive-factorizations',
                        ['NM-03','NM-04','NR-03','NR-04','PF-01','PF-02','PF-05'],'colbrook-factorization'),
                       (54,'frames-and-matrix-designs',
                        ['FR-02','FR-04','FR-09','FR-10','FR-11'],'colbrook-frames')]:
    import re
    def clean(t):
        t=re.sub(r'<!-- '+mark+r' -->.*?<!-- /'+mark+r' -->','',t,flags=re.S)
        t=re.sub(r'^\*\*(Status|Last checked):\*\*.*$','',t,flags=re.M)
        return '\n'.join(z.strip() for z in t.splitlines() if z.strip())
    for id in ids:
        path=f'{cat}/{id}/README.md'
        orig=subprocess.check_output(['git','show','origin/main:'+path],cwd='/private/tmp/nla-review-wave2-20260911',text=True)
        new=(ROOT/f'pr-{pr}'/path).read_text()
        ck('canonical_target_unchanged_'+id,clean(orig)==clean(new))

# NM03: every subset of clauses on four variables, with unused variables removed.
clauses=list(it.combinations(range(4),3))
for mask in range(1,16):
    cc=[c for j,c in enumerate(clauses) if mask>>j&1]
    variables=sorted(set().union(*map(set,cc)))
    n=len(variables);N=n+2
    C=s.Matrix([[int(v in c) for v in variables]+[-1,-2] for c in cc])
    D=s.Matrix.vstack(*(C.row(j) for j in C.T.rref()[1]))
    P=D.T*(D*D.T).inv()*D
    one=s.ones(N,1);delta=s.Rational(1,12*N);eps=delta/(2*N)
    X=s.eye(N)+delta/N*one*one.T-eps*P;r=C.rank()
    tau=N-r-2+r*(1-eps)**2
    ck(f'nm03_projector_{mask}',P*P==P and P.T==P and P*one==s.zeros(N,1))
    ck(f'nm03_positive_{mask}',all(v>0 for v in X))
    ck(f'nm03_threshold_{mask}',s.trace(X*X)-(1+delta)**2-1==tau)
    boolean=[]
    for bits in it.product([0,1],repeat=N):
        chi=s.Matrix(bits)
        if 0<sum(bits)<N and C*chi==s.zeros(C.rows,1):
            boolean.append(bits)
            k=sum(bits)
            Y=s.Matrix(N,N,lambda i,j:delta/N+(s.Rational(1,k) if bits[i]==bits[j]==1 else s.Rational(1,N-k) if bits[i]==bits[j]==0 else 0))
            ck(f'nm03_witness_{mask}_{len(boolean)}',Y.rank()==2 and s.trace((X-Y).T*(X-Y))==tau)
    sat=any(all(sum(bits[variables.index(v)] for v in c)==1 for c in cc) for bits in it.product([0,1],repeat=n))
    ck(f'nm03_boolean_equivalence_{mask}',bool(boolean)==sat)

# NR03: exhaustive positive rectangles with both parities on each side.
C=s.Matrix(8,8,lambda a,b:(1-(int(a)&int(b)).bit_count())**2)
z=s.Matrix([(-1)**a.bit_count() for a in range(8)])
ck('nr03_rank_null',C.rank()==7 and C*z==s.zeros(8,1) and C[:7,:7].det()==-8)
dist={(1<<i,7^(1<<i)) for i in range(3)}|{(7^(1<<i),1<<i) for i in range(3)}|{(7^(1<<i),7^(1<<i)) for i in range(3)}
balanced=[tuple(i for i in range(8) if mask>>i&1) for mask in range(1,256) if len({i.bit_count()%2 for i in range(8) if mask>>i&1})==2]
rectangles=0
for rows,cols in it.product(balanced,repeat=2):
    if all(C[i,j]>0 for i in rows for j in cols):
        rectangles+=1
        ck(f'nr03_rectangle_{rectangles}',sum((i,j) in dist for i in rows for j in cols)<=1)
ck('nr03_89_rectangles',rectangles==89)

# NR04 independent direct certificate.
W=s.zeros(9,7);H=s.zeros(7,9)
for i in range(9):
    t=i-4;W[i,abs(t)]=1;W[i,5]=2*max(t,0);W[i,6]=2*max(-t,0)
    for r in range(5):H[r,i]=(r-abs(t))**2
    H[5,i]=2*max(-t,0);H[6,i]=2*max(t,0)
D9=s.Matrix(9,9,lambda i,j:(i-j)**2)
ck('nr04_integer_factorization',W*H==D9 and D9.rank()==3 and D9[:3,:3].det()==8)

# PF01 independent symbolic generation of the cubic constraints and obstructions.
x=s.symbols('x:5');a=s.symbols('a:5');lam=s.symbols('l')
e3=sum(s.prod(x[i] for i in ids) for ids in it.combinations(range(5),3))
q=2*sum(v*v for v in x)-sum(x)**2
p=lam*e3+q*sum(u*v for u,v in zip(a,x));Hp=s.hessian(p,x)
pair={x[i]:int(i<2) for i in range(5)}
ss=a[0]+a[1]
ck('pf01_hessian_identity',s.expand(Hp.subs(pair).det(method='domain-ge')+96*ss*(2*ss-lam)**2*(4*ss-lam)**2)==0)
mons=[s.prod(x[i] for i in ids) for ids in it.combinations_with_replacement(range(5),3)]
co=s.symbols('c:35');gen=sum(c*m for c,m in zip(co,mons));eq=[]
for i,j in it.combinations(range(5),2):
    pt={x[k]:int(k in (i,j)) for k in range(5)}
    g=[s.diff(gen,v).subs(pt) for v in x];outside=[k for k in range(5) if k not in (i,j)]
    eq.extend([g[i],g[j],g[outside[0]]-g[outside[1]],g[outside[0]]-g[outside[2]]])
ck('pf01_cubic_space_dimension',35-s.linear_eq_to_matrix(eq,co)[0].rank()==6)
R=s.Rational
cases=[(1,[0]*5),(1,[R(1,8)]*5),(1,[R(1,4)]+[0]*4),(1,[-R(1,8)]+[R(1,8)]*4),(-1,[-R(1,4)]*5),(-1,[-R(1,8)]*5),(-1,[0]+[-R(1,4)]*4),(-1,[-R(3,8)]+[-R(1,8)]*4)]
certs={1:((0,1),(0,2,3,4),R(1,4)),2:((0,1),(0,2,3,4),1),3:((1,2),(0,1,3,4),R(9,4)),6:((0,1),(0,2,3,4),-2),7:((1,2),(0,1,3,4),R(1,4))}
for j,(lv,av) in enumerate(cases):
    pp=p.subs({lam:lv,**dict(zip(a,av))});hh=s.hessian(pp,x)
    if j in certs:
        ij,idx,val=certs[j];pt={x[k]:int(k in ij) for k in range(5)}
        ck(f'pf01_obstruction_{j+1}',all(s.diff(pp,v).subs(pt)==0 for v in x) and hh.subs(pt).extract(idx,idx).det()==val)
    elif j in (0,4):
        point=([1,1,1,1,-R(2,3)] if j==0 else [1,1,1,0,5]);pt=dict(zip(x,point))
        ck(f'pf01_obstruction_{j+1}',pp.subs(pt)==0 and hh.subs(pt).det()==(R(256,3) if j==0 else 320))
    else:ck('pf01_obstruction_6',pp.subs(dict.fromkeys(x,1))==-R(5,8))
for n in (5,6):
    ck(f'pf01_incidence_rank_{n}',s.Matrix([[int(i in I) for i in range(n)] for I in it.combinations(range(n),n//2)]).rank()==n)
ck('pf01_two_layer_parameter',s.simplify((3+s.sqrt(5))/2+2/(3+s.sqrt(5)))==3)
for d in range(2,101):
    ck(f'pf01_integer_min_{d}',min(a+b for a in range(1,d+1) for b in range(1,d+1) if a*b>=d)==math.ceil(2*math.sqrt(d)))

# PF02 Gram certificate and orientation for all block sizes 3 through 7.
def basis(k):
    out=[]
    for i in range(k):
        X=2*s.eye(k);X[i,i]+=2;out.append(X)
    for i,j in it.combinations(range(k),2):
        X=2*s.eye(k);X[i,j]=X[j,i]=1;out.append(X)
    return out
for k in range(3,8):
    if k==3:fs=basis(k)
    else:
        fs=[s.diag(f,s.zeros(k-3)) for f in basis(3)]+[s.diag(s.zeros(3),f) for f in basis(k-3)]
        for i in range(3):
            for j in range(3,k):
                X=2*s.eye(k);X[i,j]=X[j,i]=1;fs.append(X)
    hat=[]
    for X in fs:
        Y=X.copy();Y[0,1]=-Y[0,1];Y[1,0]=-Y[1,0];hat.append(Y)
    G=s.Matrix([[s.trace(X*Y) for Y in fs] for X in fs])
    Gh=s.Matrix([[s.trace(X*Y) for Y in hat] for X in hat])
    ck(f'pf02_gram_rank_reflection_{k}',G==Gh and G.rank()==k*(k+1)//2)
    if k==3:ck('pf02_8192',G.det()==8192)
    if k>3:ck(f'pf02_zero_cross_block_{k}',G[:6,6:6+(k-3)*(k-2)//2]==s.zeros(6,(k-3)*(k-2)//2))

# PF05 all key adjoints and square identity with arbitrary real parameters.
aa,bb,cc,dd,ee,ff,al,be,ga,u,t=s.symbols('a b c d e f alpha beta gamma u t',real=True)
A=s.Matrix([[aa,bb],[bb,cc]]);B=s.Matrix([[dd,ee],[ee,ff]])
LA=s.Matrix([[aa+al*bb+be*cc,ga*bb],[ga*bb,cc]])
LB=s.Matrix([[dd,(ee-al*dd/2)/ga],[(ee-al*dd/2)/ga,ff-be*dd]])
ck('pf05_dual_pairing',s.simplify(s.trace(LA*LB)-s.trace(A*B))==0)
sig=ga**2-1;g=ga**2*(u*u-be)-(u-al/2)**2;q0=sig*u*u+al*u-be
ck('pf05_square_identity',s.expand(ga**2*q0-g-(sig*u+al/2)**2)==0)
F=s.Matrix([[sig,-al/2],[-al/2,-be]])
B1=s.Matrix([[1,u],[u,u*u]])
ck('pf05_line_determinant',s.expand((B1+t*F).det()-t*q0-t*t*(-sig*be-al*al/4))==0)

# FR11 derive integral matrices directly from the published quadratics.
xx=s.symbols('X:7',real=True);ii=s.I;b=R(5,12)
a0=5*(xx[0]+ii*xx[1]);a1=12*(xx[2]+ii*xx[3]);a3=12*(xx[4]+ii*xx[5]);a2=(9-2*ii)*xx[6]-(xx[0]+ii*xx[1])-(xx[2]+ii*xx[3])
quadratics=[a0*a0,2*a0*a1+b*s.conjugate(a3)**2,a1*a1+2*a0*a2-s.conjugate(a3)**2,2*(a0*a3+a1*a2),a2*a2+2*a1*a3,2*a2*a3+b*a3*a3]
matrices=[s.hessian(part(s.expand(q)),xx)/2 for q in quadratics for part in (s.re,s.im)]
ck('fr11_integral_symmetric',all(M==M.T and all(v.is_Integer for v in M) for M in matrices))
ck('fr11_entry_bound',max(abs(v) for M in matrices for v in M)==144)
epsilon=R(1,5);rr=R(99,70)
DA=(b+epsilon*b*b)+epsilon*(1+b)+(b+epsilon*b*b)*epsilon*(1+b)
DB=rr*(epsilon*b+b+rr*epsilon*b*b)+epsilon*b*(b+rr*epsilon*b*b)
eta=R(385,144)
ck('fr11_factor_margins',DA==R(7453,8640) and DB==R(230141,282240) and 77-85*DA>eta and 72-85*DB>eta and 77*epsilon*b*b==eta)
ck('fr11_rouche_constants',(b-R(1,100))*(1-b-R(1,100))**4>R(1,25) and 6*R(101,100)**10<9 and R(12,5)<eta)
ck('fr11_coordinate_bound',R(1,25)+(1+R(1,144)+R(1,25))/81==R(15433,291600)<R(1,16))
zz,az,Q2,Q3,Q4,Q5=s.symbols('z a Q2 Q3 Q4 Q5')
A1=(Q2-b*zz)/(2*az);A2=(Q3+zz-A1*A1)/(2*az);A3=(Q4-2*A1*A2)/(2*az)
ck('fr11_quartic_leading',s.expand(A2*A2+2*A1*A3-Q5).coeff(zz,4)==5*b**4/(64*az**6))

# FR02/10 exact rate comparisons; numerical constants are only displays.
ck('sampling_I3_rational_bound',R(40191,482944)<R(1,12))
ck('sampling_I4_rational_bound',R(203,5280)<R(1,24))
ck('sampling_I3_vs_2J',7**7*2**32>3**3*5**20)
ck('sampling_I4_vs_2J',2**24*3**42>5**5*7**28)
def kl(q,p):return q*math.log(q/p)+(1-q)*math.log((1-q)/(1-p))
display={k:(1 if k==2 else 2)*math.log(2)/kl(q,p) for k,q,p in [(2,.75,.5),(3,7/16,.25),(4,3/8,.25)]}

# FR04 derivative and exact weighted-energy identity on a rational example.
qq=s.symbols('q',positive=True)
ck('fr04_convexity_derivative',s.simplify(s.diff(s.acos(1-1/qq),qq,2)-(3*qq-1)/(qq**2*(2*qq-1)**R(3,2)))==0)
Mat=s.Matrix([[1,2,0],[0,1,3],[2,-1,1],[1,0,1],[3,1,2]])
energy=s.trace(Mat.T*Mat);weighted=0;weights=0
for j in range(5):
    v=Mat.row(j);w=(v*v.T)[0];P=s.eye(3)-v.T*v/w
    weighted+=w*s.trace(Mat*P*Mat.T);weights+=w
e2=sum((Mat.T*Mat).extract(I,I).det() for I in it.combinations(range(3),2))
ck('fr04_weighted_energy',weighted/weights==2*e2/energy and weighted/weights<=2*energy/3)

result={'passed':sum(checks.values()),'total':len(checks),'checks':checks,'walsh_constants_display_only':display,'sympy_version':s.__version__}
(OUT/'independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'total':result['total'],'walsh_constants_display_only':display},indent=2))

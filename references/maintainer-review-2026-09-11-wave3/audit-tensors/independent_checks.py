"""Independent exact diagnostics supplementing six analytic tensor reviews.

No submitted verification code is imported. Finite checks do not replace the
uniform analytic proofs or certify global algebraic geometry.
"""
from pathlib import Path
import itertools, json, math, random
import sympy as S

OUT=Path('/private/tmp/nla-review-wave3-artifacts/audit-tensors')
checks={};evidence={}
def ck(name,value):
    checks[name]=bool(value)
    assert checks[name],name

# TR15: enumerate contractions directly from the common Hankel generator.
h=[2,0,1,0,2,0,-1];x=S.symbols('x0:3')
contractions=[S.expand(sum(h[i+j+k]*x[j]*x[k] for j,k in itertools.product(range(3),repeat=2))) for i in range(3)]
ck('TR15_first_contraction_strict_sum_of_squares',S.expand(contractions[0]-(x[0]+x[2])**2-sum(t*t for t in x))==0)
ck('TR15_first_slice_eigenvalues',sorted(S.Matrix(3,3,lambda j,k:h[j+k]).eigenvals().items())==[(S.Integer(1),2),(S.Integer(3),1)])
for i in range(2):
    contraction=sum(h[i+sum(indices)]*math.prod(int(j==1) for j in indices) for indices in itertools.product(range(2),repeat=5))
    ck(f'TR15_negative_eigenpair_coordinate_{i}',contraction==(-1 if i else 0))
t=S.symbols('t');lam=2+2*t+2*t*t
quartic=2*t**4+2*t**3+3*t*t-4*t-1
ck('TR15_nonvacuity_polynomial',S.expand(lam*t*t-contractions[2].subs(dict(zip(x,[1,0,t])))-quartic)==0)
ck('TR15_IVT_signs',quartic.subs(t,0)==-1 and quartic.subs(t,1)==2)
evidence['TR15_contractions']=list(map(str,contractions))

# TR04: exact projector averaging and the parameter-uniform strict coefficient.
for dim in range(2,22):
    for kept in range(1,dim):
        counts=[sum(int(i in {(j+s)%dim for s in range(kept)}) for j in range(dim)) for i in range(dim)]
        ck(f'TR04_cyclic_average_{dim}_{kept}',counts==[kept]*dim)
        ck(f'TR04_strict_average_factor_{dim}_{kept}',S.Rational(kept,dim)<1)
z=S.symbols('z',positive=True)
ck('TR04_limiting_ratio_is_two',S.limit(1+1/(1+z)**2,z,0,dir='+')==2)

# TR13: independently form the original Hankel slices, not the shift model.
certificate_records=[]
for order in [3,5,7,9,13]:
    for n in range(3,10):
        half=(order-1)//2;ell=n-1;a=half*ell+1;s=ell//2;D=order*ell
        generator=[int(i in [a-1,2*a+s-1]) for i in range(D+1)]
        slices=[S.Matrix(a,a,lambda u,v,j=j:generator[u+v+j*s]) for j in range(3)]
        rev=S.Matrix(a,a,lambda u,v:int(u+v==a-1))
        comm=slices[1]*rev*slices[2]-slices[2]*rev*slices[1]
        rank=int(comm.rank())
        r=math.ceil((D+1)/2)
        ck(f'TR13_commutator_rank_{order}_{n}',rank==2*s and 2*a+rank==2*r)
        ck(f'TR13_invertible_first_slice_{order}_{n}',slices[0]==rev and rev*rev==S.eye(a))
        fullrank=None
        if order<=5 and n<=5:
            zero=S.zeros(a)
            K=S.BlockMatrix([[-slices[1],slices[0],zero],[-slices[2],zero,slices[0]],[zero,-slices[2],slices[1]]]).as_explicit()
            fullrank=int(K.rank());ck(f'TR13_full_Koszul_rank_{order}_{n}',fullrank==2*r)
        certificate_records.append({'m':order,'n':n,'a':a,'commutator_rank':rank,'lower_bound':r,'full_Koszul_rank':fullrank})
for order in range(3,24,2):
    half=(order-1)//2
    matrix=S.Matrix(half+1,half+2,lambda i,j:int(i+j==half))
    ck(f'TR13_binary_rank_{order}',matrix.rank()==half+1)
for degree in range(3,16):
    r=math.ceil((degree+1)/2)
    jac=S.Matrix(degree+1,2*r,lambda i,j: (j//2+1)**i if j%2==0 else (i*(j//2+1)**(i-1) if i else 0))
    ck(f'TR13_confluent_moment_Jacobian_{degree}',jac.rank()==degree+1)
evidence['TR13_certificates']=certificate_records

# TR26: exact discriminant factorization along independently chosen pencils.
q=S.symbols('q');rng=random.Random(2026091197);pencils=[]
for d in [2,3]:
    degree=2*d;D=sum(t**(2*j) for j in range(d+1))
    ck(f'TR26_denominator_squarefree_d{d}',S.gcd(D,S.diff(D,t))==1)
    coeff0=[rng.randrange(-9,10) for _ in range(degree+1)]
    coeff1=[rng.randrange(-9,10) for _ in range(degree+1)]
    N=sum((coeff0[j]+q*coeff1[j])*t**j for j in range(degree+1))
    F=S.expand(S.diff(N,t)*D-N*S.diff(D,t))
    disc=S.Poly(S.discriminant(F,t),q)
    iso=S.Poly(S.resultant(D,N,t),q)
    residual,remainder=S.div(disc,iso)
    ck(f'TR26_pencil_total_degree_d{d}',disc.degree()==8*d-6)
    ck(f'TR26_pencil_isotropic_degree_d{d}',iso.degree()==2*d)
    ck(f'TR26_pencil_nonisotropic_degree_d{d}',remainder.is_zero and residual.degree()==6*(d-1))
    ck(f'TR26_pencil_all_components_simple_d{d}',S.gcd(disc,disc.diff()).degree()==0)
    pencils.append({'d':d,'N0':coeff0,'N1':coeff1,'total_degree':disc.degree(),'isotropic_degree':iso.degree(),'nonisotropic_degree':residual.degree(),'squarefree':True})
ck('TR26_degree_two_special_Wronskian',S.expand(S.diff(t**3,t)*(1+t*t+t**4)-t**3*S.diff(1+t*t+t**4,t)-t*t*(3+t*t-t**4))==0)
ck('TR26_degree_two_quartic_has_simple_nonzero_roots',S.gcd(3+t*t-t**4,S.diff(3+t*t-t**4,t))==1 and (3+t*t-t**4).subs(t,0)!=0)
evidence['TR26_independent_pencils']=pencils

# TR20: symbolic in the arbitrary dimension n, plus local crossing/fold algebra.
u,v,n,w=S.symbols('u v n w')
for m in [2,3]:
    formula=(m+n-2-2*m*u-2*n*v+8*u*v)*(1-u)**m/((1-2*u)*(1-2*v)*(1-2*u-2*v)**2)
    coefficient=S.factor(S.diff(formula,u,m-1).subs(u,0)/math.factorial(m-1))
    transformed=S.factor(coefficient.subs(v,w/(1+w))/(1+w)**2)
    numerator=S.Poly(S.cancel(transformed*(1-w)**(3 if m==2 else 5)),w)
    denominator_degree=3 if m==2 else 5
    closed=0
    for (j,),coef in numerator.terms():
        upper=n-1-j+denominator_degree-1
        binomial=S.prod(upper-i for i in range(denominator_degree-1))/math.factorial(denominator_degree-1)
        closed+=coef*binomial
    target=4*n*(n*n-1) if m==2 else 12*n**3*(n-1)
    ck(f'TR20_symbolic_all_n_formula_m{m}',S.expand(closed-target)==0)
A,B,C,beta,parameter=S.symbols('A B C beta parameter')
local=A*u+B*parameter+beta*u*u/2
ck('TR20_single_boundary_fold_equation',S.expand(u*S.diff(local,u)-local)==-B*parameter+beta*u*u/2)
cross=A*u+B*v+C*parameter
equations=S.Matrix([u*S.diff(cross,u)-cross,v*S.diff(cross,v)-cross])
ck('TR20_crossing_unramified_determinant',equations.jacobian([u,v]).det()==-A*B)
ck('TR20_normal_recovery_unique_rank_one_direction',S.Matrix([[A,B],[B,0]]).det()==-B**2)

# TR06: verify the radial exponent and normalization exactly in sample dimensions;
# semialgebraic finite-volume and the graph-area inequality are analytic premises.
rho=S.symbols('rho',positive=True)
for dimension in range(2,10):
    integral=S.integrate(rho**(dimension-2)*S.exp(-rho*rho/2),(rho,0,S.oo))
    gamma=2**S.Rational(dimension-3,2)*S.gamma(S.Rational(dimension-1,2))
    ck(f'TR06_radial_Gamma_identity_k{dimension}',S.simplify(integral-gamma)==0)

result={'passed':sum(checks.values()),'total':len(checks),'checks':checks,'evidence':evidence,'limits':'Exact diagnostics supplement the separately reviewed universal analytic arguments; not proof-assistant certification.'}
(OUT/'independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'total':result['total'],'TR26_pencils':pencils},indent=2))

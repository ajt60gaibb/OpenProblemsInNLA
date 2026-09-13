"""Exact finite checks for the PF-01 second-round structural manuscript.

This is not formal verification or a certificate that PF-01 is solved.
The quartic-kernel result is an exact linear-algebra certificate: AF=0 over
integers and two nonsingular minors modulo a prime establish matching ranks.
"""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math
import platform
import sys
import numpy as np
import sympy as sp
from quartic_kernel import build, family, rank_mod
from pf01 import FactorFactory, distance_matrix

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
P = 1000003

def determinant_mod(matrix: np.ndarray, prime: int=P) -> int:
    a = np.array(matrix, dtype=np.int64, copy=True) % prime
    if a.ndim != 2 or a.shape[0] != a.shape[1]:
        raise ValueError('A square matrix is required')
    ans = 1
    for j in range(a.shape[0]):
        piv = np.flatnonzero(a[j:,j])
        if not len(piv): return 0
        i = j+int(piv[0])
        if i != j:
            a[[j,i]] = a[[i,j]]
            ans = -ans % prime
        value = int(a[j,j]); ans = ans*value % prime
        a[j,j:] = a[j,j:] * pow(value,-1,prime) % prime
        for lo in range(j+1,len(a),64):
            hi = min(lo+64,len(a))
            a[lo:hi,j:] = (a[lo:hi,j:]-a[lo:hi,j,None]*a[None,j,j:]) % prime
    return int(ans)

def certify_rank(a: np.ndarray, expected: int) -> dict:
    rank, rows, cols = rank_mod(a, certificate=True)
    assert rank == expected
    det = determinant_mod(a[np.ix_(rows,cols)])
    assert det != 0
    return {'rank_mod_prime': rank, 'pivot_rows': rows, 'pivot_columns': cols,
            'minor_determinant_mod_prime': det}

def quartic_certificate() -> dict:
    a, mons, row_labels = build(9,4)
    f = family(9,4,mons)
    assert a.shape == (1008,495) and f.shape == (495,90)
    # Bound products/sums so the following is exact in signed 64-bit arithmetic.
    bound = a.shape[1]*int(np.abs(a).max())*int(np.abs(f).max())
    assert bound < 2**63
    assert np.array_equal(a @ f, np.zeros((1008,90),dtype=np.int64))
    ac = certify_rank(a,405); fc = certify_rank(f,90)
    assert rank_mod(f[:,:81]) == 81
    cert = {'prime': P, 'prime_check': bool(sp.isprime(P)),
            'constraint_shape': list(a.shape), 'basis_shape': list(f.shape),
            'integer_AF_equals_zero': True, 'integer_product_bound': bound,
            'constraint_minor': ac, 'basis_minor': fc,
            'rational_constraint_rank': 405, 'rational_kernel_dimension': 90,
            'restricted_family_dimension': 81, 'additional_directions': 9,
            'monomial_order': 'itertools.combinations_with_replacement(range(9),4)',
            'basis_order': '36 q*x_i*x_j (i<j), 45 z_i*z_j (i<=j), 9 h*x_i; integer-scaled z,h',
            'indexing': 'zero-based'}
    assert cert['prime_check']
    (OUT/'quartic_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    np.savez_compressed(OUT/'quartic_matrices.npz',constraints=a,basis=f,
                        monomials=np.array(mons,dtype=np.int64))
    return {key:cert[key] for key in ['constraint_shape','basis_shape','rational_constraint_rank',
            'rational_kernel_dimension','restricted_family_dimension','additional_directions']}

def square_rank() -> dict:
    n,r=9,4
    subsets=list(combinations(range(n),r))
    e=np.zeros((len(subsets),n),dtype=np.int64)
    for j,I in enumerate(subsets): e[j,list(I)]=1
    pairs=list(combinations(range(n),2))
    w=np.array([[int(set(ij)<=set(I)) for ij in pairs] for I in subsets],dtype=np.int64)
    d=r-e@e.T; d2=d*d
    assert np.array_equal(d2,r*r*np.ones_like(d2)+(1-2*r)*(e@e.T)+2*(w@w.T))
    # Constants and degree-one incidence columns belong to the span of w.
    assert np.array_equal(w.sum(axis=1),np.full(len(w),math.comb(r,2)))
    for i in range(n):
        positions=[j for j,ij in enumerate(pairs) if i in ij]
        assert np.array_equal(w[:,positions].sum(axis=1),(r-1)*e[:,i])
    cert=certify_rank(d2,36)
    result={'n':9,'N':126,'exact_rank_entrywise_square':36,
            'quartic_dimension_in_four_variables':math.comb(7,4),
            'rank_minor':cert,'column_space_contained_in_pair_incidence_space':True}
    (OUT/'square_rank_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    return {k:result[k] for k in ['n','N','exact_rank_entrywise_square','quartic_dimension_in_four_variables']}

def projection_algebra() -> dict:
    r=sp.symbols('r')
    v,w=sp.symbols('v w',commutative=False)
    eq=(r-1)*(v*w+w*v)+v*v+w*w-v-w
    u=v*v*w-w*v*v; z=v*w*w-w*w*v; c=v*w-w*v
    assert sp.expand(v*eq-eq*v-((r-1)*u+z-c))==0
    assert sp.expand(eq*w-w*eq-(u+(r-1)*z-c))==0
    j=sp.Matrix([[0,1],[-1,0]])
    g1=sp.diag(1,1,-1,-1)
    g2=sp.zeros(4);g2[:2,2:]=sp.eye(2);g2[2:,:2]=sp.eye(2)
    g3=sp.zeros(4);g3[:2,2:]=j;g3[2:,:2]=-j
    gs=[g1,g2,g3]
    for a in gs: assert a*a==sp.eye(4)
    for a,b in combinations(gs,2): assert a*b+b*a==sp.zeros(4)
    # Solve the linear equations for a symmetric matrix anticommuting with g1,g2.
    symbasis=[]
    for a in range(4):
        for b in range(a,4):
            m=sp.zeros(4);m[a,b]=1;m[b,a]=1;symbasis.append(m)
    columns=[]
    for m in symbasis:
        columns.append(list(m*g1+g1*m)+list(m*g2+g2*m))
    equations=sp.Matrix.hstack(*[sp.Matrix(c) for c in columns])
    assert len(equations.nullspace())==1
    # Anticommuting also with g3 leaves only zero.
    allcols=[sp.Matrix(list(m*g1+g1*m)+list(m*g2+g2*m)+list(m*g3+g3*m)) for m in symbasis]
    assert sp.Matrix.hstack(*allcols).rank()==10
    return {'free_algebra_commutator_identities':True,
            'symmetric_anticommutant_of_first_two_generators_dimension':1,
            'symmetric_anticommutant_of_all_three_dimension':0,
            'scope':'These identities support, but do not replace, the block-decomposition proof.'}

def jet_and_hessian() -> dict:
    n,r=9,4
    x=sp.symbols('x0:9');sigma=sum(x);s2=sum(t*t for t in x)
    h=sum(t**3 for t in x)-sp.Rational(3,2*r)*sigma*s2+sigma**3/sp.Integer(2*r*r)
    grad=[sp.diff(h,t) for t in x]
    for I in combinations(range(n),r):
        sub={x[i]:int(i in I) for i in range(n)}
        assert h.subs(sub)==0 and all(t.subs(sub)==0 for t in grad)
    # One subset suffices for the symbolic restriction by permutation symmetry.
    I=set(range(r));sub={x[i]:int(i in I) for i in range(n)}
    hh=sp.hessian(h,x).subs(sub)
    cols=[]
    for group in [list(range(r)),list(range(r,n))]:
        for i in group[:-1]:
            v=sp.zeros(n,1);v[i]=1;v[group[-1]]=-1;cols.append(v)
    t=sp.Matrix.hstack(*cols);eps=sp.diag(*[1 if i in I else -1 for i in range(n)])
    assert t.T*hh*t==3*t.T*eps*t
    aa,bb,cc,ll=sp.symbols('aa bb cc ll',positive=True)
    u,v,w=sp.symbols('u v w',real=True)
    block=sp.diag(aa,bb,cc,0)
    variation=sp.zeros(4);variation[0,3]=variation[3,0]=u
    variation[1,3]=variation[3,1]=v;variation[2,3]=variation[3,2]=w
    det=sp.expand((block+ll*variation).det())
    assert sp.expand(det.coeff(ll,2)+bb*cc*u*u+aa*cc*v*v+aa*bb*w*w)==0
    return {'all_126_cubic_values_and_gradients_zero':True,
            'cubic_Hessian_on_tangent_space': '3*diag(epsilon), after restriction',
            'rank_three_determinant_second_coefficient': 'negative sum of three squares',
            'tangent_dimension':7}

def relaxation_witness() -> dict:
    subsets=list(combinations(range(9),4));e=np.zeros((126,9),dtype=np.int64)
    for j,I in enumerate(subsets): e[j,list(I)]=1
    # One-based mathematical notation: f=(1-x_1)(2-x_3-x_4), g=x_1(2*x_3-1).
    f=(1-e[:,0])*(2-e[:,2]-e[:,3]);g=e[:,0]*(2*e[:,2]-1)
    assert (f>=0).all() and (f*g==0).all()
    assert int((f>0).sum())==55 and int((g!=0).sum())==56
    covers=[]
    for a in range(9):
        for b,c in combinations([j for j in range(9) if j!=a],2):
            indices=(e[:,a]==0)&(e[:,b]!=e[:,c])
            assert int(indices.sum())==40
            covers.append(int(f[indices].sum()))
    assert len(covers)==252 and min(covers)==10
    return {'f':'(1-x_1)*(2-x_3-x_4)', 'g':'x_1*(2*x_3-1)',
            'support_f':55,'support_g':56,'fg_zero_at_all_126_points':True,
            'covering_blocks':252,'points_per_block':40,'minimum_cover_sum_f':min(covers),
            'meaning':'A witness that the listed combinatorial necessary conditions alone do not exclude a factorization; not PSD factors.'}

def positive_controls() -> list:
    results=[]
    for n in [5,6,7,8,9,11]:
        factory=FactorFactory(n);subsets,a,b=factory.enumerate();d=distance_matrix(subsets,n)
        prod=a.reshape(len(a),-1)@b.reshape(len(b),-1).T
        error=float(np.abs(prod-d).max());assert error<1.e-10
        results.append({'n':n,'factor_size':factory.size,'number_of_factors_per_side':len(a),'max_abs_trace_error':error})
    return results

def failed_candidate() -> dict:
    path=ROOT/'experiments/best_failed_n7_size4.npz'
    data=np.load(path,allow_pickle=False);u,v=data['uv'];d=data['D']
    a=u@u.transpose(0,2,1);b=v@v.transpose(0,2,1)
    residual=a.reshape(len(a),-1)@b.reshape(len(b),-1).T-d
    return {'status':'NOT A FACTORIZATION',
            'relative_squared_frobenius_residual':float((residual**2).sum()/(d**2).sum()),
            'max_absolute_entry_residual':float(np.abs(residual).max()),
            'min_diagonal_residual':float(np.diag(residual).min()),
            'max_diagonal_residual':float(np.diag(residual).max())}

def main() -> None:
    record={'scope':'Exact finite algebra certificates and numerical checks; no full PF-01 resolution.',
            'python':sys.version.split()[0],'numpy':np.__version__,'sympy':sp.__version__,
            'platform':platform.platform()}
    jobs=[('quartic_kernel',quartic_certificate),('entrywise_square_rank',square_rank),
          ('projection_algebra',projection_algebra),('jets_and_Hessian',jet_and_hessian),
          ('relaxation_witness',relaxation_witness),('positive_controls',positive_controls),
          ('failed_n7_candidate',failed_candidate)]
    for name,job in jobs:
        record[name]=job();print(name+': '+json.dumps(record[name]),flush=True)
    (OUT/'round2_checks.json').write_text(json.dumps(record,indent=2)+'\n')

if __name__=='__main__':main()

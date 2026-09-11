#!/usr/bin/env python3
"""Exact verification of the twelve integral real phase-retrieval measurements.

The all-signals proof is in manuscript/twelve_measurements.tex. This script checks
its algebra and rational inequalities. Optional finite sampling and local searches
are diagnostics only, not substitutes for the proof.

Usage: python verify_r7.py --angles 2001 --restarts 20 --seed 0
Requires Python 3.10+, numpy, sympy, scipy. No network access is used.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from datetime import datetime, timezone
import numpy as np
import sympy as sp
from scipy.optimize import minimize

B = sp.Rational(5, 12)
EPS = sp.Rational(1, 5)
C = 9 + 2 * sp.I


def construction():
    x = sp.symbols('x0:7', real=True)
    a0 = 5 * (x[0] + sp.I*x[1])
    a1 = 12 * (x[2] + sp.I*x[3])
    a3 = 12 * (x[4] + sp.I*x[5])
    a2 = (9-2*sp.I)*x[6] - (x[0]+sp.I*x[1]) - (x[2]+sp.I*x[3])
    assert sp.expand(C*(a2+EPS*B*a1+EPS*a0)) == 85*x[6]
    q = [a0*a0, 2*a0*a1+B*sp.conjugate(a3)**2,
         a1*a1+2*a0*a2-sp.conjugate(a3)**2,
         2*(a0*a3+a1*a2), a2*a2+2*a1*a3, 2*a2*a3+B*a3*a3]
    real_q = [sp.expand(part(z)) for z in q for part in (sp.re, sp.im)]
    matrices = [sp.hessian(z, x)/2 for z in real_q]
    xv = sp.Matrix(x)
    for M, z in zip(matrices, real_q):
        assert M == M.T
        assert all(v.is_Integer for v in M)
        assert sp.expand((xv.T*M*xv)[0]-z) == 0
    rank = sp.Matrix([list(M) for M in matrices]).rank()
    assert rank == 12
    assert max(abs(v) for M in matrices for v in M) == 144
    # Verify the quotient applied to a polynomial square, independently of q.
    zz = sp.symbols('z', real=True)
    p = sp.Poly((a0+a1*zz+a2*zz**2+a3*zz**3)**2, zz)
    quot = [p.nth(0), p.nth(1)+B*sp.conjugate(p.nth(6)),
            p.nth(2)-sp.conjugate(p.nth(6)), p.nth(3), p.nth(4),
            p.nth(5)+B*p.nth(6)]
    assert all(sp.expand(u-v) == 0 for u, v in zip(q, quot))
    return x, real_q, matrices


def exact_proof_checks():
    b, e, gamma, s, p, pp, z = sp.symbols('b e gamma s p pp z')
    def L0(f):
        f = sp.Poly(f, z)
        return f.nth(2)+e*b*f.nth(1)+e*f.nth(0)
    identities = [
        (L0(z*(z-b)*(z-gamma)), -b-(1-e*b*b)*gamma),
        (L0(z**3+gamma*z*z+gamma**2*z+gamma**3), gamma+e*b*gamma**2+e*gamma**3),
        (L0(z*(z*z-s*z+p)), -s+e*b*p),
        (L0((z-b)*(z*z+s*z+pp)), (1-e*b*b)*s-b)]
    assert all(sp.expand(lhs-rhs) == 0 for lhs, rhs in identities)
    assert (sp.Rational(99, 70))**2 > 2
    DA = B+EPS*B**2+EPS*(1+B)+(B+EPS*B**2)*EPS*(1+B)
    r = sp.Rational(99, 70)
    DB = r*(EPS*B+B+r*EPS*B**2)+EPS*B*(B+r*EPS*B**2)
    eta = 77*EPS*B**2
    assert DA == sp.Rational(7453, 8640)
    assert DB == sp.Rational(230141, 282240)
    assert eta == sp.Rational(385, 144)
    assert 77-85*DA == sp.Rational(6355, 1728) > eta
    assert 72-85*DB == sp.Rational(151859, 56448) > eta
    # Every numerical constant in the quantitative proof is checked rationally.
    rmax = sp.Rational(1, 100)
    umax = sp.Rational(1, 10**7)
    assert 2*(1+B*B) < 4
    assert (sp.Rational(1, 20)-umax)/2 > sp.Rational(1, 80)
    assert 8000*umax < rmax
    assert (B-rmax)*(1-B-rmax)**4 > sp.Rational(1, 25)
    assert 6*(1+rmax)**10 < 9
    assert sp.Rational(41,10)+sp.Rational(85,100)*rmax+sp.Rational(1,5)*rmax*rmax < sp.Rational(42,10)
    assert 10*(3+sp.Rational(3,12)+sp.Rational(1,5)) < 35
    assert 2940+1764*rmax < 3000
    assert 3000*8000*umax < eta
    coefficient_factor = sp.Rational(1,25)+(1+sp.Rational(1,144)+sp.Rational(1,25))/81
    assert coefficient_factor == sp.Rational(15433,291600) < sp.Rational(1,16)
    assert 16*umax > sp.Rational(1,10**6)
    return {'case_A_imaginary_lower': str(77-85*DA),
            'case_B_adjacent_imaginary_lower': str(72-85*DB),
            'case_B_opposite_exact': str(eta),
            'coefficient_norm_lower': '1/10000000',
            'integer_coordinate_bilinear_lower': '1/1000000',
            'matrix_count': 12, 'matrix_dimension': 7,
            'matrix_span_rank': 12, 'maximum_absolute_matrix_entry': 144,
            'status': 'Exact algebra/inequality checks passed; analytic proof in manuscript.'}


def factor_grid(n_angles):
    if n_angles == 0:
        return {'status': 'not requested'}
    roots0 = np.exp(1j*(np.pi/4+np.arange(4)*np.pi/2))
    subsets = [(0,)+s for s in itertools.combinations(range(1,6),2)]
    minimum = np.full(10,np.inf)
    for theta in np.linspace(0,2*np.pi,n_angles,endpoint=False):
        t = np.exp(1j*theta)
        roots = np.r_[0, float(B), np.exp(-.5j*theta)*roots0]
        for j, S in enumerate(subsets):
            T = [i for i in range(6) if i not in S]
            f, g = np.poly(roots[list(S)]), np.poly(roots[T])
            lf = complex(C)*(f[1]+float(EPS*B)*f[2]+float(EPS)*f[3])
            lg = complex(C)*(g[1]+float(EPS*B)*g[2]+float(EPS)*g[3])
            minimum[j] = min(minimum[j], abs((t*lf*lg).imag))
    assert min(minimum) >= float(sp.Rational(385,144))-1e-10
    return {'angles': n_angles, 'unordered_partitions': [list(s) for s in subsets],
            'minimum_absolute_imaginary_parts': minimum.tolist(),
            'status': 'Finite diagnostic grid only; no global certification inferred.'}


def local_search(matrices, restarts, seed):
    if restarts == 0:
        return {'status':'not requested'}
    rng = np.random.default_rng(seed)
    a = np.array([np.array(M,dtype=float) for M in matrices])
    def objective(w):
        u, v = w[:7], w[7:]
        nu, nv = np.linalg.norm(u), np.linalg.norm(v)
        if min(nu,nv) < 1e-100:
            return 1e100, np.zeros(14)
        x, y = u/nu, v/nv
        q = np.einsum('i,kij,j->k',x,a,y)
        gx = 2*np.einsum('k,kij,j->i',q,a,y)
        gy = 2*np.einsum('k,kij,i->j',q,a,x)
        return float(q@q), np.r_[(gx-x*(gx@x))/nu,(gy-y*(gy@y))/nv]
    best, values = None, []
    for _ in range(restarts):
        sol = minimize(objective,rng.normal(size=14),jac=True,method='BFGS',
                       options={'gtol':1e-10,'maxiter':1500})
        values.append(float(sol.fun))
        if best is None or sol.fun < best.fun:
            best = sol
    return {'seed':seed,'restarts':restarts,'minimum_found_squared_bilinear_norm':min(values),
            'all_local_objective_values': values,
            'best_x':(best.x[:7]/np.linalg.norm(best.x[:7])).tolist(),
            'best_y':(best.x[7:]/np.linalg.norm(best.x[7:])).tolist(),
            'status':'Local falsification search only; not proof of global optimality.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).parent)
    parser.add_argument('--angles',type=int,default=1001)
    parser.add_argument('--restarts',type=int,default=10)
    parser.add_argument('--seed',type=int,default=0)
    args = parser.parse_args()
    if args.angles < 0 or args.restarts < 0:
        parser.error('angles and restarts must be nonnegative')
    args.out.mkdir(parents=True,exist_ok=True)
    x, quadratics, matrices = construction()
    payload = {'dimension':7,'measurements':12,'entries':'exact integers',
               'coordinate_order':[str(v) for v in x],
               'matrices':[[[int(M[i,j]) for j in range(7)] for i in range(7)] for M in matrices]}
    (args.out/'r7_integer_matrices.json').write_text(json.dumps(payload,indent=2)+'\n')
    (args.out/'r7_integer_quadratics.tex').write_text('\n'.join(sp.latex(q) for q in quadratics)+'\n')
    report = {'utc':datetime.now(timezone.utc).isoformat(),
              'exact_checks':exact_proof_checks(),
              'factor_grid':factor_grid(args.angles),
              'local_search':local_search(matrices,args.restarts,args.seed)}
    path = args.out/f'r7_integer_verification_seed{args.seed}.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['exact_checks'],indent=2))
    print('Report:',path)
    if args.restarts:
        print('Local minimum of squared bilinear norm:',report['local_search']['minimum_found_squared_bilinear_norm'])

if __name__ == '__main__':
    main()

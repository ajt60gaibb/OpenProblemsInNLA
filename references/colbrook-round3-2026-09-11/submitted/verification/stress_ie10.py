#!/usr/bin/env python3
"""High-precision, deterministic IE-10 stress diagnostics.

Uses the exact weighted evaluation model with mpmath arithmetic. These are
numerical tests, not interval certificates or a proof of any probability bound.
They intentionally include highly nonuniform weights, clustered nodes, and
near-uniform cyclic weights close to the defective deterministic example.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp


def inner(x: mp.matrix, y: mp.matrix):
    return (x.H * y)[0]


def norm(x: mp.matrix):
    return mp.sqrt(mp.re(inner(x, x)))


def orthonormal_evaluation(nodes, weights, k):
    """Twice-reorthogonalized modified Gram--Schmidt in high precision."""
    n = len(nodes)
    Q = mp.matrix(n, k)
    columns = []
    for ell in range(k):
        v = mp.matrix([mp.sqrt(weights[j]) * nodes[j]**ell for j in range(n)])
        for _ in range(2):
            for q in columns:
                v -= q * inner(q, v)
        magnitude = norm(v)
        if magnitude <= 0:
            raise ArithmeticError("Evaluation columns lost rank at the selected precision")
        q = v / magnitude
        columns.append(q)
        for j in range(n):
            Q[j, ell] = q[j]
    return Q


def check_case(name, nodes, weights, k):
    n = len(nodes)
    Q = orthonormal_evaluation(nodes, weights, k)
    H = Q.H * mp.diag(nodes) * Q
    eigenvalues, R = mp.eig(H, left=False, right=True)
    d = min(abs(nodes[i]-nodes[j]) for i in range(n) for j in range(i))
    errors = dict(orthonormality=mp.norm(Q.H*Q-mp.eye(k)),
                  right_residual=mp.mpf(0), left_residual=mp.mpf(0),
                  matched_modulus=mp.mpf(0), identity_relative=mp.mpf(0),
                  worst_bound_ratio=mp.mpf(0), max_projector_condition=mp.mpf(0),
                  finite_difference_relative=mp.mpf(0))
    derivative_column = []
    chosen_coordinate = n//2
    for i, lam in enumerate(eigenvalues):
        r = R[:, i]
        r /= norm(r)
        sampled_r = Q*r
        sampled_ell = mp.matrix([nodes[j]**(k-1)*mp.conj(sampled_r[j]) for j in range(n)])
        ell = Q.H*sampled_ell
        alpha = inner(ell, r)
        kap = 1/abs(alpha)
        probabilities = [abs(sampled_r[j])**2 for j in range(n)]
        derivatives = [(nodes[j]-lam)*mp.conj(sampled_ell[j])*sampled_r[j]/(weights[j]*alpha)
                       for j in range(n)]
        derivative_column.append(derivatives[chosen_coordinate])
        lhs = sum(weights[j]*abs(derivatives[j]) for j in range(n))
        rhs = kap*sum(probabilities[j]*abs(nodes[j]-lam) for j in range(n))
        errors['right_residual'] = max(errors['right_residual'], norm(H*r-lam*r))
        errors['left_residual'] = max(errors['left_residual'], norm(H.H*ell-mp.conj(lam)*ell))
        errors['matched_modulus'] = max(errors['matched_modulus'],
                                      max(abs(abs(sampled_r[j])-abs(sampled_ell[j])) for j in range(n)))
        errors['identity_relative'] = max(errors['identity_relative'], abs(lhs-rhs)/(1+rhs))
        errors['worst_bound_ratio'] = max(errors['worst_bound_ratio'], kap/max(2, 8*lhs/d))
        errors['max_projector_condition'] = max(errors['max_projector_condition'], kap)
    h = weights[chosen_coordinate]*mp.mpf('1e-60')
    perturbed = []
    for sign in [-1, 1]:
        new_weights = list(weights)
        new_weights[chosen_coordinate] += sign*h
        new_Q = orthonormal_evaluation(nodes, new_weights, k)
        new_H = new_Q.H*mp.diag(nodes)*new_Q
        new_values = mp.eig(new_H, left=False, right=False)
        indices = [min(range(k), key=lambda j:abs(new_values[j]-lam)) for lam in eigenvalues]
        assert len(set(indices)) == k, 'Perturbed eigenvalue matching is ambiguous'
        perturbed.append([new_values[j] for j in indices])
    for i in range(k):
        fd = (perturbed[1][i]-perturbed[0][i])/(2*h)
        rel = abs(fd-derivative_column[i])/(1+abs(derivative_column[i]))
        errors['finite_difference_relative'] = max(errors['finite_difference_relative'], rel)
    assert errors['finite_difference_relative'] < mp.mpf('1e-30'), (name, errors['finite_difference_relative'])
    for key in ['orthonormality', 'right_residual', 'left_residual', 'matched_modulus', 'identity_relative']:
        assert errors[key] < mp.mpf('1e-70'), (name, key, errors[key])
    assert errors['worst_bound_ratio'] <= 1+mp.mpf('1e-70')
    return {'case': name, 'n': n, 'k': k,
            'minimum_node_separation': mp.nstr(d, 18),
            'weight_ratio': mp.nstr(max(weights)/min(weights), 18),
            'diagnostics': {key: mp.nstr(value, 18) for key, value in errors.items()}}


def run(dps=140):
    if dps < 120:
        raise ValueError('Use at least 120 decimal digits for these stress cases')
    with mp.workdps(dps):
        cases=[]
        for n, k in [(5, 3), (7, 6)]:
            z=[mp.exp(2j*mp.pi*j/n) for j in range(n)]
            w=[mp.power(10, (j-(n//2))*4) for j in range(n)]
            cases.append(check_case(f'cyclic_log_spaced_weights_{n}_{k}', z, w, k))
        for exponent in [8, 20, 35]:
            n,k=7,6
            z=[mp.exp(2j*mp.pi*j/n) for j in range(n)]
            w=[1+mp.power(10,-exponent)*(j+1)**2 for j in range(n)]
            cases.append(check_case(f'near_defective_cyclic_1e-{exponent}', z,w,k))
        for scale in ['0.01', '0.000001']:
            n,k=8,6
            t=[mp.mpf(scale)*(j+1) for j in range(n)]
            z=[(1+1j*s)/(1-1j*s) for s in t]
            w=[mp.mpf(j*j+3*j+1)/(j+2) for j in range(n)]
            cases.append(check_case(f'clustered_rational_circle_{scale}', z,w,k))
        n,k=9,7
        angles=[mp.mpf(j)/7 for j in range(5)]+[mp.pi+mp.mpf(j)/100 for j in range(4)]
        z=[mp.exp(1j*theta) for theta in angles]
        w=[mp.power(10, (j%4)*5-8) for j in range(n)]
        cases.append(check_case('two_clusters_uneven_weights',z,w,k))
    return {'status':'passed', 'mpmath_version':mp.__version__, 'decimal_digits':dps,
            'matrix_cases':len(cases), 'eigenpairs':sum(case['k'] for case in cases),
            'warning':'High-precision floating-point diagnostics, not interval certification or a probability proof',
            'cases':cases}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--digits', type=int, default=140)
    args=parser.parse_args()
    result=run(args.digits)
    text=json.dumps(result, indent=2, allow_nan=False)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__=='__main__':
    main()

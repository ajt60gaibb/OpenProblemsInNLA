#!/usr/bin/env python3
"""Generate rational, independently checkable two-circulant certificates.

This generator uses floating point to find a root and a preconditioner.  Only
verify_conference.py supplies the rigorous existence test.  All JSON integers
are serialized in decimal, with explicitly specified common denominators.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.linalg import qr


def phase_arrays(d, x):
    if d < 3:
        raise ValueError('This certificate family requires d >= 3.')
    h = (d - 1) // 2
    if len(x) != h+d-1:
        raise ValueError('Incorrect number of phases.')
    a = np.zeros(d, dtype=complex)
    a[1:h+1] = np.exp(1j*x[:h])
    a[-h:] = a[1:h+1][::-1].conj()
    if d % 2 == 0:
        a[d//2] = 1
    b = np.exp(1j*np.r_[0.0, x[h:]])
    return a, b


def correlation_model(d, a, b, jac=False, derivative_scale=1.0):
    """Real and imaginary positive-shift correlations and phase Jacobian."""
    h = (d - 1) // 2
    f = np.empty(d-1)
    for s in range(1, h+1):
        z = np.dot(a, np.roll(a, -s).conj()) + np.dot(b, np.roll(b, -s).conj())
        f[2*s-2:2*s] = (z.real, z.imag)
    if d % 2 == 0:
        z = np.dot(a, np.roll(a, -d//2).conj()) + np.dot(b, np.roll(b, -d//2).conj())
        f[-1] = z.real
    if not jac:
        return f
    J = np.empty((d-1, h+d-1))
    shifts = np.arange(1, h+1)
    for v in range(h+d-1):
        if v < h:
            j = v + 1
            entries = [(j, derivative_scale*1j*a[j]),
                       (d-j, -derivative_scale*1j*a[d-j])]
            seq = a
        else:
            j = v-h+1
            entries = [(j, derivative_scale*1j*b[j])]
            seq = b
        z = sum(dz*seq[(l+shifts) % d].conj() + seq[(l-shifts) % d]*dz.conjugate()
                for l, dz in entries)
        J[:2*h:2, v], J[1:2*h:2, v] = z.real, z.imag
        if d % 2 == 0:
            s = d//2
            zz = sum(dz*seq[(l+s) % d].conj() + seq[(l-s) % d]*dz.conjugate()
                     for l, dz in entries)
            J[-1, v] = zz.real
    return f, J


def generate(candidate, out, bits=60, inverse_bits=None, radius_denominator=100000000, product_bits=None):
    raw = json.loads(candidate.read_text())
    d, x = int(raw['d']), np.array(raw['angles'], dtype=float)
    if inverse_bits is None:
        inverse_bits = 32 if d >= 257 else 50
    if product_bits is None and d >= 257:
        product_bits = 20
    a, b = phase_arrays(d, x)
    f, J = correlation_model(d, a, b, True)
    _, _, piv = qr(J, mode='economic', pivoting=True)
    selected = np.sort(piv[:d-1])
    for iteration in range(8):
        a, b = phase_arrays(d, x)
        f, J = correlation_model(d, a, b, True)
        change = np.linalg.solve(J[:, selected], -f)
        x[selected] += change
        if np.max(np.abs(change)) < 2e-15:
            break
    # Rational half-angle anchors; all entries have exact modulus one.
    x = (x+np.pi) % (2*np.pi)-np.pi
    D = 1 << bits
    p = [int(round(float(np.tan(v/2))*D)) for v in x]
    z = np.array([complex((D*D-v*v)/(D*D+v*v), (2*v*D)/(D*D+v*v)) for v in p])
    h = (d-1)//2
    a = np.zeros(d, dtype=complex)
    a[1:h+1] = z[:h]
    a[-h:] = a[1:h+1][::-1].conj()
    if d % 2 == 0:
        a[d//2] = 1
    b = np.r_[1.+0j, z[h:]]
    f, Jall = correlation_model(d, a, b, True, derivative_scale=2.0)
    J = Jall[:, selected]
    Minv = np.linalg.inv(J)
    MD = 1 << inverse_bits
    Mn = [[int(round(float(v)*MD)) for v in row] for row in Minv]
    cert = {
        'format': 'hermitian-conference-cayley-contraction-v1',
        'dimension': d,
        'anchor_half_angle_numerators': p,
        'anchor_half_angle_denominator': D,
        'selected_variables': [int(v) for v in selected],
        'inverse_numerators': Mn,
        'inverse_denominator': MD,
        'radius_numerator': 1,
        'radius_denominator': radius_denominator,
        'verification_bits': 160,
        'generator_diagnostics_not_proof': {
            'source': candidate.name,
            'newton_iterations': iteration+1,
            'max_correlation_residual': float(max(abs(f))),
            'smallest_jacobian_singular_value': float(np.linalg.svd(J, compute_uv=False)[-1]),
            'inverse_infinity_norm': float(np.linalg.norm(Minv, ord=np.inf)),
            'linear_defect_infinity_norm': float(np.linalg.norm(np.eye(d-1)-Minv@J, ord=np.inf)),
        },
    }
    if product_bits is not None:
        cert['jacobian_product_bits'] = int(product_bits)
    out.write_text(json.dumps(cert, indent=2)+'\n')
    print(json.dumps(cert['generator_diagnostics_not_proof'], indent=2))
    return cert


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--inverse-bits', type=int)
    parser.add_argument('--product-bits', type=int)
    args = parser.parse_args()
    generate(args.candidate, args.out, inverse_bits=args.inverse_bits, product_bits=args.product_bits)

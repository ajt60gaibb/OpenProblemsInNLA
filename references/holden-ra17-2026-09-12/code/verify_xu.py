#!/usr/bin/env python3
"""Recompute, without numerical approximations, Xu's rank-one certificates.

The measurement rows, not the saved eliminants, are the input. Both the affine
chart and the projective hyperplane at infinity are checked. GMP accelerates
rational RREF; --backend sympy removes the C++/GMP requirement but can be slower.
Run from any directory: python /path/to/code/verify_xu.py --variant both
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
from typing import Sequence
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

def monomials(n: int, degree: int, exact: bool = False) -> list[tuple[int, ...]]:
    return sorted(
        (e for e in itertools.product(range(degree + 1), repeat=n)
         if sum(e) == degree or (not exact and sum(e) < degree)),
        key=lambda e: (sum(e), e), reverse=True)

def reduced_rows(rows: list[list[int]], backend: str, temp: Path,
                 binary: Path | None, tag: str) -> tuple[sp.Matrix, tuple[int, ...]]:
    if backend == 'sympy':
        rref, pivots = sp.Matrix(rows).rref()
        return rref[:len(pivots), :], tuple(pivots)
    input_path, output_path = temp / (tag + '.in'), temp / (tag + '.out')
    input_path.write_text(f'{len(rows)} {len(rows[0])}\n' + '\n'.join(
        ' '.join(map(str, row)) for row in rows) + '\n', encoding='ascii')
    result = subprocess.run([str(binary), str(input_path), str(output_path)],
                            check=True, text=True, capture_output=True)
    print(result.stdout.strip(), flush=True)
    lines = output_path.read_text(encoding='ascii').splitlines()
    rank, ncols = map(int, lines[0].split())
    pivots = tuple(map(int, lines[1].split()))
    rref = sp.Matrix([[sp.Rational(x) for x in row.split()] for row in lines[2:]])
    require(rref.shape == (rank, ncols) and len(pivots) == rank,
            'malformed rational RREF output')
    require(all(rref[i, j] == (1 if i == k else 0)
                for k, j in enumerate(pivots) for i in range(rank)),
            'pivot columns are not the identity')
    return rref, pivots

def variations(signs: Sequence[int]) -> int:
    nonzero = [x for x in signs if x]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))

def verify_variant(variant: str, backend: str, temp: Path,
                   binary: Path | None, output: Path) -> dict:
    start = time.monotonic()
    data = json.loads((ROOT / 'certificates' / f'measurements_{variant}.json').read_text())
    W = sp.Matrix(data['measurement_rows'])
    require(W.shape == (11, 16) and W.rank() == 11, 'measurement matrix must have rank 11')
    _, pivots = W.rref()
    free_columns = [j for j in range(16) if j not in pivots]
    B = sp.Matrix.hstack(*W.nullspace())
    require(B.shape == (16, 5) and W * B == sp.zeros(11, 5), 'invalid kernel basis')
    require(B == sp.Matrix(data['kernel_basis_rational']), 'stored kernel basis differs')
    a, b, c, z, t = sp.symbols('a b c d t')
    variables = (a, b, c, z)
    X = sp.Matrix(4, 4, B * sp.Matrix((*variables, t)))
    cubics = []
    for I in itertools.combinations(range(4), 3):
        for J in itertools.combinations(range(4), 3):
            poly = sp.Poly(X.extract(I, J).det(), *variables, t, domain=sp.QQ)
            _, poly = poly.clear_denoms()
            _, poly = poly.primitive()
            cubics.append(poly)
    print(f'{variant}: rank(W)=11; 16 cubic minors; free columns={free_columns}', flush=True)
    certificate: dict = {'variant': variant, 'arithmetic': 'exact rational',
                         'measurement_rank': 11, 'free_columns_zero_based': free_columns}
    for kind in ('affine', 'infinity'):
        exact = kind == 'infinity'
        polynomials = [sp.Poly(P.as_expr().subs(t, 0 if exact else 1), *variables)
                       for P in cubics]
        columns = monomials(4, 5, exact)
        column_index = {e: i for i, e in enumerate(columns)}
        multipliers = monomials(4, 2, exact)
        rows: list[list[int]] = []
        for P in polynomials:
            for multiplier in multipliers:
                row = [0] * len(columns)
                for exponent, coefficient in P.as_dict().items():
                    exponent = tuple(x + y for x, y in zip(exponent, multiplier))
                    row[column_index[exponent]] = int(coefficient)
                divisor = math.gcd(*row)
                rows.append([x // divisor for x in row] if divisor else row)
        R, piv = reduced_rows(rows, backend, temp, binary, f'{variant}_{kind}')
        certificate[f'{kind}_macaulay_shape'] = [len(rows), len(columns)]
        certificate[f'{kind}_macaulay_rank'] = len(piv)
        if exact:
            require(len(piv) == len(columns) == 56,
                    'infinity chart did not have full degree-five rank')
            continue
        free = [j for j in range(len(columns)) if j not in piv]
        require(len(piv) == 106 and len(free) == 20, 'unexpected affine rank')
        require((0, 0, 0, 0) in [columns[j] for j in free], 'constant 1 is missing')
        free_index = {col: j for j, col in enumerate(free)}
        pivot_index = {col: i for i, col in enumerate(piv)}
        T = sp.zeros(len(free))
        for j, col in enumerate(free):
            exponent = list(columns[col]); exponent[-1] += 1
            require(tuple(exponent) in column_index, 'multiplication exceeds degree five')
            product = column_index[tuple(exponent)]
            if product in free_index:
                T[free_index[product], j] = 1
            else:
                for i, f in enumerate(free):
                    T[i, j] = -R[pivot_index[product], f]
        polynomial = T.charpoly().as_poly()
        _, polynomial = polynomial.clear_denoms()
        _, polynomial = polynomial.primitive()
        if polynomial.LC() < 0: polynomial = -polynomial
        require(polynomial.degree() == 20, 'unexpected characteristic polynomial degree')
        sequence = sp.sturm(polynomial.as_expr(), polynomial.gen)
        plus, minus = [], []
        for entry in sequence:
            P = sp.Poly(entry, polynomial.gen)
            sign = int(sp.sign(P.LC()))
            plus.append(sign); minus.append(sign * (-1) ** P.degree())
        roots = variations(minus) - variations(plus)
        require(roots == 0, 'eliminant has a real root; verification fails')
        certificate.update({
            'basis_exponents': [columns[col] for col in free],
            'multiplication_variable': 'd',
            'multiplication_matrix': [[str(T[i, j]) for j in range(T.cols)] for i in range(T.rows)],
            'eliminant_coefficients_descending': [str(x) for x in polynomial.all_coeffs()],
            'sturm_signs_plus_infinity': plus,
            'sturm_signs_minus_infinity': minus,
            'sturm_variations_plus_infinity': variations(plus),
            'sturm_variations_minus_infinity': variations(minus),
            'real_root_count': roots,
        })
        print(f'{variant}: degree 20; Sturm variations {variations(minus)} -> '
              f'{variations(plus)}; zero real roots', flush=True)
    saved = json.loads((ROOT / 'certificates' / f'exact_{variant}.json').read_text())
    for key in ('multiplication_matrix', 'eliminant_coefficients_descending',
                'sturm_signs_plus_infinity', 'sturm_signs_minus_infinity', 'real_root_count'):
        require(certificate[key] == saved[key], f'recomputed certificate differs: {key}')
    output.mkdir(parents=True, exist_ok=True)
    (output / f'verified_{variant}.json').write_text(json.dumps(certificate, indent=2) + '\n')
    print(f'{variant}: PASS (including infinity chart), elapsed '
          f'{time.monotonic() - start:.2f} seconds', flush=True)
    return certificate

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant', choices=('paper', 'website', 'both'), default='both')
    parser.add_argument('--backend', choices=('gmp', 'sympy'), default='gmp')
    parser.add_argument('--output', type=Path, default=ROOT / 'results')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='ra17_exact_') as folder:
        temp, binary = Path(folder), None
        if args.backend == 'gmp':
            compiler = shutil.which('g++')
            require(compiler is not None, 'g++ not found; install a compiler or use --backend sympy')
            binary = temp / 'rref'
            command = [compiler, '-std=c++17', '-O2', str(ROOT / 'code' / 'rref.cpp'),
                       '-lgmpxx', '-lgmp', '-o', str(binary)]
            try:
                subprocess.run(command, check=True, text=True, capture_output=True)
            except subprocess.CalledProcessError as error:
                raise RuntimeError('GMP compilation failed. Install GMP development headers '
                                   'or use --backend sympy.\n' + error.stderr) from error
        for variant in ('paper', 'website') if args.variant == 'both' else (args.variant,):
            verify_variant(variant, args.backend, temp, binary, args.output)
    print('All requested exact verifications passed.')

if __name__ == '__main__':
    main()

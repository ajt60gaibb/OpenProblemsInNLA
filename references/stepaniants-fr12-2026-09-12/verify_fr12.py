#!/usr/bin/env python3
"""Exact finite checks supplementary to the matching-indexed FR-12 proof.

Run: python3 verify_fr12.py [--source path/to/original-user-source.tex]
Only Python's standard library is needed. This is not a universal proof
certificate and is not a formal verification of the manuscript.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import permutations, product
from math import factorial, prod
from pathlib import Path
import json


def hadamard(a):
    n = len(a)
    return all(len(row) == n for row in a) and all(
        sum(x*y for x, y in zip(a[i], a[j])) == (n if i == j else 0)
        for i in range(n) for j in range(n)
    )


def all_hadamards(n):
    result = []
    for entries in product((-1, 1), repeat=n*n):
        a = tuple(tuple(entries[i*n:(i+1)*n]) for i in range(n))
        if hadamard(a):
            result.append(a)
    return result


def matchings(positions):
    if not positions:
        yield ()
        return
    u = positions[0]
    for v in positions[1:]:
        remaining = tuple(x for x in positions if x not in (u, v))
        for rest in matchings(remaining):
            yield ((u, v),) + rest


def construct(a, b, matching):
    m = len(a)
    rows = [None]*(2*m)
    for i, (u, v) in enumerate(matching):
        rows[u] = a[i]+b[i]
        rows[v] = a[i]+tuple(-x for x in b[i])
    return tuple(rows)


def recover(c):
    m = len(c)//2
    groups = defaultdict(list)
    for position, row in enumerate(c):
        groups[row[:m]].append(position)
    assert len(groups) == m and all(len(v) == 2 for v in groups.values())
    matching = tuple(sorted(tuple(v) for v in groups.values()))
    a = tuple(c[u][:m] for u, _ in matching)
    b = tuple(c[u][m:] for u, _ in matching)
    return a, b, matching


def finite_enumeration(m):
    matrices = all_hadamards(m)
    matching_list = tuple(matchings(tuple(range(2*m))))
    assert len(matching_list) == factorial(2*m)//(2**m*factorial(m))
    injection_outputs = {}
    for a, b, matching in product(matrices, matrices, matching_list):
        c = construct(a, b, matching)
        assert hadamard(c)
        assert recover(c) == (a, b, matching)
        assert c not in injection_outputs
        injection_outputs[c] = (a, b, matching)

    fibers = Counter()
    for a, b in product(matrices, repeat=2):
        base = tuple(a[i]+b[i] for i in range(m)) + tuple(
            a[i]+tuple(-x for x in b[i]) for i in range(m)
        )
        for perm in permutations(range(2*m)):
            output = tuple(base[i] for i in perm)
            assert hadamard(output)
            fibers[output] += 1
    expected_fiber = 2**m*factorial(m)
    assert set(fibers) == set(injection_outputs)
    assert set(fibers.values()) == {expected_fiber}
    return {
        'm': m,
        'H_m_exhaustive': len(matrices),
        'matching_count': len(matching_list),
        'matching_input_triples': len(matching_list)*len(matrices)**2,
        'row_permutation_input_triples': len(matrices)**2*factorial(2*m),
        'distinct_outputs': len(fibers),
        'row_permutation_fiber_size': expected_fiber,
        'matching_recovery_and_injectivity': True,
        'every_output_hadamard': True,
    }


def recurrence_checks(max_k=10):
    lower = 2  # Exact H(1); only the proved injection is used afterward.
    checks = []
    for k in range(1, max_k+1):
        m = 2**(k-1)
        matching_factor = prod(range(1, 2*m, 2))
        assert matching_factor == factorial(2*m)//(2**m*factorial(m))
        lower = matching_factor*lower**2
        if k >= 2:
            assert matching_factor >= factorial(m) >= (m//2)**(m//2)
            numerator = 2**k*(k-1)*(k-2)
            assert numerator % 8 == 0
            exponent = numerator//8
            assert lower >= 1 << exponent
        else:
            exponent = None
        exact_integer_bytes = lower.to_bytes((lower.bit_length()+7)//8, 'big')
        checks.append({
            'k': k, 'n': 2**k,
            'recurrence_lower_bound_bit_length': lower.bit_length(),
            'recurrence_lower_bound_big_endian_sha256': sha256(exact_integer_bytes).hexdigest(),
            'claimed_power_of_two_exponent': exponent,
            'all_integer_inequalities_pass': True,
        })
    return checks


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        help='Optional original proof source to bind by SHA-256.')
    args = parser.parse_args()
    cases = [finite_enumeration(m) for m in (1, 2)]
    assert [(x['H_m_exhaustive'], x['row_permutation_input_triples'],
             x['distinct_outputs'], x['row_permutation_fiber_size']) for x in cases] == [
        (2, 8, 4, 2), (8, 1536, 192, 8)
    ]
    output = {
        'verdict': 'PASS: supplementary exact finite checks only',
        'arithmetic': 'Exact Python integers; no floating-point decisions',
        'finite_cases': cases,
        'recurrence_checks': recurrence_checks(),
        'scope_limit': 'Finite enumeration and integer checks do not replace the all-order analytic injection and recurrence proof.',
    }
    if args.source is not None:
        source = args.source.read_bytes()
        output['reviewed_source'] = {'bytes': len(source), 'sha256': sha256(source).hexdigest()}
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()

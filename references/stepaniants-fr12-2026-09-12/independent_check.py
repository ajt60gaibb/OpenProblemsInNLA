"""Independent supplementary FR-12 checks; standard-library integer arithmetic.

The all-order proof is audited in REVIEW.md. Finite cases do not prove it.
Run from any directory: python3 independent_check.py
"""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import permutations, product
from math import factorial, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def dot(a, b):
    return sum(x*y for x,y in zip(a,b))


def hadamards(n):
    choices = tuple(product((-1,1), repeat=n))
    result = []
    def extend(rows):
        if len(rows) == n:
            result.append(tuple(rows))
            return
        for row in choices:
            if all(dot(row, previous) == 0 for previous in rows):
                extend(rows+[row])
    extend([])
    return result


def matchings(labels):
    if not labels:
        yield ()
        return
    u = labels[0]
    for j in range(1,len(labels)):
        v = labels[j]
        rest = labels[1:j]+labels[j+1:]
        for tail in matchings(rest):
            yield ((u,v),)+tail


def construct(A, B, matching):
    m = len(A)
    rows = [None]*(2*m)
    for i, (u,v) in enumerate(matching):
        rows[u] = A[i]+B[i]
        rows[v] = A[i]+tuple(-x for x in B[i])
    return tuple(rows)


def decode(C):
    m = len(C)//2
    classes = defaultdict(list)
    for j,row in enumerate(C):
        classes[row[:m]].append(j)
    assert len(classes) == m
    assert all(len(v) == 2 for v in classes.values())
    matching = tuple(sorted(tuple(v) for v in classes.values()))
    A = tuple(C[u][:m] for u,v in matching)
    B = tuple(C[u][m:] for u,v in matching)
    assert construct(A,B,matching) == C
    return A,B,matching


def valid(C):
    n = len(C)
    return all(len(row)==n and all(x in (-1,1) for x in row) for row in C) and all(
        dot(C[i],C[j]) == (n if i==j else 0)
        for i in range(n) for j in range(i+1)
    )


sets = {n: hadamards(n) for n in [1,2,4]}
assert {n:len(v) for n,v in sets.items()} == {1:2,2:8,4:768}
matching_reports = []
for m in [1,2,4]:
    # Full domain for m=1,2; an explicitly limited deterministic domain for m=4.
    chosen = sets[m] if m<=2 else sets[m][::48]
    pairs = tuple(matchings(tuple(range(2*m))))
    assert len(pairs) == factorial(2*m)//(2**m*factorial(m))
    outputs = set()
    for A,B,M in product(chosen, chosen, pairs):
        C = construct(A,B,M)
        assert valid(C)
        assert decode(C) == (A,B,M)
        assert C not in outputs
        outputs.add(C)
    expected = len(chosen)**2*len(pairs)
    assert len(outputs) == expected
    matching_reports.append({'m':m,'domain':'full' if m<=2 else '16 deterministic matrices per input',
                             'input_matrices_per_factor':len(chosen),'matchings':len(pairs),
                             'distinct_valid_outputs':len(outputs),'decoder_exact':True})

fiber_reports = []
for m in [1,2]:
    fibers = Counter()
    for A,B in product(sets[m],repeat=2):
        base = tuple(A[i]+B[i] for i in range(m))+tuple(
            A[i]+tuple(-x for x in B[i]) for i in range(m))
        for permutation in permutations(range(2*m)):
            C = tuple(base[j] for j in permutation)
            fibers[C] += 1
    assert set(fibers.values()) == {2**m*factorial(m)}
    fiber_reports.append({'m':m,'input_triples':sum(fibers.values()),
                          'outputs':len(fibers),'fiber':next(iter(fibers.values()))})

bound_reports = []
# Start from the exact H(2)=8; each later number is only the recursive lower bound.
lower = 8
for k in range(2,13):
    m = 2**(k-1)
    matching_count = prod(2*j-1 for j in range(1,m+1))
    assert matching_count >= factorial(m) >= (m//2)**(m//2)
    lower = matching_count*lower*lower
    # Raising to eight avoids any nonintegral displayed exponent.
    claimed_eighth_power_exponent = 2**k*(k-1)*(k-2)
    assert lower**8 >= 1 << claimed_eighth_power_exponent
    bound_reports.append({'k':k,'recursive_lower_bound_bit_length':lower.bit_length(),
                          'claimed_inequality_checked_exactly':True})

result = {
    'status':'PASS for the specified supplementary exact checks only',
    'scope':'No inference from finite checks to the all-order proof; no external code imported',
    'proof_sha256':sha256((ROOT/'reviewed-proof.tex').read_bytes()).hexdigest(),
    'canonical_target_sha256':sha256((ROOT/'canonical-target.md').read_bytes()).hexdigest(),
    'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    'exact_small_counts':{str(n):len(v) for n,v in sets.items()},
    'matching_construction':matching_reports,
    'row_permutation_fibers':fiber_reports,
    'iterated_integer_bounds':bound_reports,
}
(ROOT/'independent-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

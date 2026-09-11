#!/usr/bin/env python3
"""Exact checks of the rank-two nonnegative approximation hardness reduction.

These tests validate finite instances and identities. The accompanying proof,
not exhaustive tests on bounded instances, establishes NP-hardness.
All arithmetic is rational; no optimizer or floating point is used.
"""
from __future__ import annotations
from itertools import combinations, product
from pathlib import Path
import json
import random
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def encode(n: int, clauses: list[tuple[int, int, int]]) -> s.Matrix:
    if not clauses or set().union(*(set(c) for c in clauses)) != set(range(n)):
        raise ValueError('Use a nonempty formula with no unused variables.')
    C = s.zeros(len(clauses), n + 2)
    for row, clause in enumerate(clauses):
        if len(set(clause)) != 3 or any(i < 0 or i >= n for i in clause):
            raise ValueError('Clauses require three distinct valid variables.')
        for i in clause:
            C[row, i] = 1
        C[row, n] = -1
        C[row, n + 1] = -2
    return C

def reduction(C: s.Matrix) -> tuple[s.Matrix, s.Rational, s.Matrix]:
    N = C.cols
    independent_rows = list(C.T.rref()[1])
    D = C.extract(independent_rows, range(N))
    P = D.T * (D * D.T).inv() * D
    delta, epsilon = s.Rational(1, 12*N), s.Rational(1, 24*N*N)
    X = s.eye(N) + delta / N * s.ones(N) - epsilon * P
    r = len(independent_rows)
    tau = N - r - 2 + r * (1 - epsilon)**2
    return X, tau, P

def sqnorm(M: s.Matrix) -> s.Expr:
    return sum(x*x for x in M)

def check_formula(n: int, clauses: list[tuple[int, int, int]], name: str) -> dict:
    C = encode(n, clauses)
    N = C.cols
    one = s.ones(N, 1)
    X, tau, P = reduction(C)
    r = C.rank()
    delta, epsilon = s.Rational(1, 12*N), s.Rational(1, 24*N*N)
    assert C*one == s.zeros(C.rows, 1)
    assert C*s.Matrix([s.Rational(1,3)]*n + [1,0]) == s.zeros(C.rows,1)
    assert r <= N-2
    assert P == P.T and P*P == P and P*one == s.zeros(N,1)
    assert C*P == C
    assert all(x > 0 for x in X) and tau >= 0
    assert X*one == (1+delta)*one
    assert X*P == (1-epsilon)*P
    PE = s.eye(N) - one*one.T/N - P
    assert X*PE == PE and PE.trace() == N-r-1
    assert tau == sqnorm(X) - (1+delta)**2 - 1
    sat = [bits for bits in product((0,1), repeat=n)
           if all(sum(bits[i] for i in c)==1 for c in clauses)]
    kernel = [bits for bits in product((0,1), repeat=N)
              if 0 < sum(bits) < N and C*s.Matrix(bits) == s.zeros(C.rows,1)]
    expected = {b+(1,0) for b in sat}
    expected |= {tuple(1-x for x in b)+(0,1) for b in sat}
    assert set(kernel) == expected
    witnesses = []
    for bits in kernel:
        chi = s.Matrix(bits)
        k = sum(bits)
        V = (chi-s.Rational(k,N)*one)*(chi-s.Rational(k,N)*one).T / s.Rational(k*(N-k),N)
        Y = (1+delta)/N * one*one.T + V
        W = chi.row_join(one-chi)
        first1, first0 = bits.index(1), bits.index(0)
        H = Y.extract([first1,first0], range(N))
        assert all(x >= 0 for x in W) and all(x > 0 for x in H)
        assert W*H == Y and Y.rank()==2
        assert sqnorm(X-Y) == tau
        assert C*V == s.zeros(C.rows,N)
        assert all(Y[i,j] == (s.Rational(1,k) if bits[i] == bits[j] == 1 else
                               s.Rational(1,N-k) if bits[i] == bits[j] == 0 else 0)+delta/N
                   for i in range(N) for j in range(N))
        witnesses.append(bits)
    result = dict(name=name,n=n,N=N,clauses=clauses,rank_C=r,
                  satisfying_assignments=len(sat),nontrivial_boolean_kernel=len(kernel),
                  threshold=str(tau),minimum_input_entry=str(min(X)),
                  exact_witnesses_checked=len(witnesses))
    if not sat and PE.rank()==1:
        # Only one second eigendirection: every optimal rank-two matrix is this Y.
        Y = (1+delta)/N * one*one.T + PE
        assert Y.rank() == 2 and sqnorm(X-Y) == tau
        assert min(Y) < 0
        result['unique_best_rank_two_min_entry'] = str(min(Y))
        result['input_matrix'] = [[str(X[i,j]) for j in range(N)] for i in range(N)]
    return result

def main() -> None:
    cases = [(3,[(0,1,2)],'one_clause_sat'),
             (4,list(combinations(range(4),3)),'four_triples_unsat'),
             (5,[(0,1,2),(0,3,4)],'two_clause_sat'),
             (5,list(combinations(range(5),3)),'all_five_triples_unsat')]
    rng = random.Random(20260911)
    for n in (5,6,7):
        triples = list(combinations(range(n),3))
        for j in range(4):
            while True:
                clauses = rng.sample(triples,min(len(triples),n+j))
                if set().union(*(set(c) for c in clauses))==set(range(n)):
                    break
            cases.append((n,clauses,f'random_{n}_{j}'))
    results = [check_formula(*case) for case in cases]
    # The scalar identity at the heart of the rounding proof is checked symbolically.
    N = 5
    a,b = s.symbols('a b')
    v = s.symbols('v0:4')
    vv = list(v)+[-sum(v)]
    assert s.expand(sum((b-x)*(x+a) for x in vv)-(N*a*b-sum(x*x for x in vv)))==0
    # Worst-case rounding constant: row l1 norm 6, delta=1/(12N).
    assert 3*N*s.Rational(1,12*N)==s.Rational(1,4)
    output = {'status':'all exact checks passed',
              'scope':'finite examples and symbolic identities, not a substitute for the proof',
              'cases':results,'rounding_identity':'passed'}
    (ROOT/'results').mkdir(exist_ok=True)
    path = ROOT/'results'/'nm03_verification.json'
    path.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':
    main()

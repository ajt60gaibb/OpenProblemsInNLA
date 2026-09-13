#!/usr/bin/env python3
"""Exact rational/symbolic checks for the RA-04 partial-results report.

These finite checks validate identities used in the written proofs.  They do
not certify a universal probability bound or resolve the general conjecture.
Run from the package root: python tests/exact_checks.py --output results/exact_checks.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import random
import sympy as sp


def krylov(nodes: list[sp.Expr], H: sp.Matrix, q: int) -> sp.Matrix:
    if q < 1 or H.rows != len(nodes):
        raise ValueError("Incompatible nodes, starting block, or degree.")
    D = sp.diag(*nodes)
    return sp.Matrix.hstack(*(D**j * H for j in range(q)))


def gap_b(nodes: list[sp.Expr], b: int) -> sp.Expr:
    if len(nodes) == b:
        return sp.Integer(1)
    return min((nodes[i] - nodes[i+b])/nodes[i]
               for i in range(len(nodes)-b))


def near_set(nodes: list[sp.Expr], b: int, i: int) -> list[int]:
    gap = gap_b(nodes, b)
    lower, upper = (1-gap/2)*nodes[i], (1+gap/2)*nodes[i]
    selected = [j for j, x in enumerate(nodes) if lower <= x <= upper]
    if i not in selected or len(selected) > b:
        raise AssertionError("The packing lemma failed.")
    selected += [j for j in range(len(nodes)) if j not in selected][:b-len(selected)]
    return sorted(selected)


def integer_gaussian_surrogate(rows: int, cols: int, seed: int) -> sp.Matrix:
    """A rational test fixture, NOT a sample from a Gaussian law."""
    rng = random.Random(seed)
    return sp.Matrix(rows, cols, [rng.randint(-7, 7) for _ in range(rows*cols)])


def check_generic_rank() -> dict:
    b, t = 3, 3
    nodes = list(map(sp.Rational, [9, 9, 9, 4, 4, 3, 1, 1, 1]))
    H = sp.zeros(b*t, b)
    for i in range(b*t):
        H[i, i % b] = 1
    K = krylov(nodes, H, t)
    determinant = sp.factor(K.det())
    assert determinant != 0
    return {"name": "generic_rank_witness", "passed": True,
            "b": b, "t": t, "gap": str(gap_b(nodes,b)),
            "determinant": str(determinant)}


def check_exact_clusters() -> dict:
    b, t = 2, 3
    centers = list(map(sp.Rational, [9, 4, 1]))
    head = [x for x in centers for _ in range(b)]
    tail = [sp.Rational(1,2), sp.Rational(1,5), sp.Integer(0)]
    nodes = head + tail
    Hblocks = [sp.Matrix([[2, 1], [1, 2]]), sp.Matrix([[1, 2], [3, 1]]),
               sp.Matrix([[3, -1], [1, 1]])]
    T = sp.Matrix([[1, 3], [-2, 1], [4, 2]])
    G = sp.Matrix.vstack(*Hblocks, T)
    x = sp.Symbol('x')
    columns = []
    coefficient_blocks = []
    for r, center in enumerate(centers):
        ell = sp.prod((x-other)/(center-other)
                      for s, other in enumerate(centers) if s != r)
        ell = sp.Poly(sp.expand(ell), x)
        X = sp.diag(*(ell.eval(z) for z in nodes))*G*Hblocks[r].inv()
        columns.append(X)
        coefficient_blocks.append(sp.Matrix.vstack(
            *(ell.nth(j)*Hblocks[r].inv() for j in range(t))))
    Y = sp.Matrix.hstack(*columns)
    C = sp.Matrix.hstack(*coefficient_blocks)
    K = krylov(nodes, G, t)
    assert Y[:b*t, :] == sp.eye(b*t)
    assert K*C == Y
    assert K[b*t:, :]*K[:b*t, :].inv() == Y[b*t:, :]
    return {"name": "exact_cluster_graph", "passed": True,
            "b": b, "t": t, "head_identity": True,
            "krylov_membership": True,
            "tail_frobenius_squared": str(sum(z*z for z in Y[b*t:, :]))}


def check_general_filter() -> dict:
    b, t = 3, 3
    m = b*t
    head = [sp.Rational(z) for z in ['10','10','9.9','8','7.9','7.9','4','3.99','3.98']]
    tail = [sp.Rational(2), sp.Rational(1,3), sp.Integer(0)]
    nodes = head+tail
    x = sp.Symbol('x')
    # Select a nonsingular rational fixture; this is an identity test only.
    for seed in range(10, 100):
        G = integer_gaussian_surrogate(len(nodes), b, seed)
        H = G[:m, :]
        Ccols, Ycols = [], []
        good = True
        for i in range(m):
            J = near_set(head, b, i)
            R = H.extract([j for j in J if j != i], list(range(b)))
            null = R.nullspace()
            if len(null) != 1:
                good = False
                break
            c = null[0]
            alpha = (H[i, :]*c)[0]
            if alpha == 0:
                good = False
                break
            p = sp.Poly(sp.expand(sp.prod(
                (x-head[j])/(head[i]-head[j]) for j in range(m) if j not in J)), x)
            Ccols.append(sp.Matrix.vstack(*(p.nth(j)*c/alpha for j in range(m-b+1))))
            Ycols.append(sp.diag(*(p.eval(z) for z in nodes))*G*c/alpha)
        if good:
            break
    else:
        raise RuntimeError("Unable to construct the rational fixture.")
    C, Y = sp.Matrix.hstack(*Ccols), sp.Matrix.hstack(*Ycols)
    assert Y[:m, :] == sp.eye(m)
    assert krylov(nodes, G, m-b+1)*C == Y
    gap = gap_b(head, b)
    rho = (sp.Rational(3)/gap)**(m-b)
    # Verify the scalar bounds at every tail node of this exact fixture.
    for i in range(m):
        J = near_set(head,b,i)
        for z in tail:
            val = sp.prod((z-head[j])/(head[i]-head[j]) for j in range(m) if j not in J)
            assert abs(val) <= rho
    return {"name": "general_scalar_filter_graph", "passed": True,
            "b": b, "t": t, "degree": m-b, "gap": str(gap),
            "fixture_seed": seed, "head_identity": True,
            "krylov_membership": True, "tail_scalar_bounds": True}


def check_t2_identity() -> dict:
    b, t = 3, 2
    m = b*t
    head = list(map(sp.Rational, [7,7,6,5,4,4]))
    for seed in range(500, 1000):
        H = integer_gaussian_surrogate(m, b, seed)
        K = krylov(head, H, 2)
        if K.det() == 0:
            continue
        choices = [near_set(head, b, i) for i in range(m)]
        if all(H.extract([j for j in range(m) if j not in choices[i]],
                         list(range(b))).det() != 0 for i in range(m)):
            break
    else:
        raise RuntimeError("Unable to construct a t=2 rational fixture.")
    x = sp.Symbol('x')
    for i, J in enumerate(choices):
        S = [j for j in range(m) if j not in J]
        null = K.extract([j for j in range(m) if j != i],list(range(m))).nullspace()
        assert len(null) == 1
        coeff = null[0]
        a, c = coeff[:b, :], coeff[b:, :]
        z = a+head[i]*c
        assert z != sp.zeros(b,1)
        HS = H.extract(S, list(range(b)))
        D = sp.diag(*(1/(head[j]-head[i]) for j in S))
        W = sp.eye(b)-(x-head[i])*HS.inv()*D*HS
        assert sp.simplify((a+x*c)-W*z) == sp.zeros(b,1)
        alpha = (H[i,:]*z)[0]
        assert alpha != 0
        assert K*(coeff/alpha) == sp.eye(m)[:,i]
    return {"name": "t2_leave_one_out_identity", "passed": True,
            "b": b, "t": t, "gap": str(gap_b(head,b)),
            "fixture_seed": seed, "identities_checked": m}


def check_recursive_identity() -> dict:
    """Validate the general recursion in exact arithmetic, not its tail bound."""
    fixtures = [
        (2, 3, ['9', '8', '6', '5', '3', '2']),
        (2, 4, ['10', '10', '8', '7.9', '5', '5', '2', '1.9']),
        (3, 3, ['9', '9', '8.5', '6', '5.9', '5.8', '2', '2', '1.9']),
    ]
    records = []
    x = sp.Symbol('x')
    for b, t, texts in fixtures:
        nodes = [sp.Rational(z) for z in texts]
        m = b*t
        choices = [near_set(nodes,b,i) for i in range(m)]
        for seed in range(800, 900):
            H = integer_gaussian_surrogate(m,b,seed)
            K = krylov(nodes,H,t)
            if K.det() == 0:
                continue
            good = True
            for J in choices:
                S = [j for j in range(m) if j not in J]
                HS = H.extract(S,list(range(b)))
                if krylov([nodes[j] for j in S],HS,t-1).det() == 0:
                    good = False
                    break
            if good:
                break
        else:
            raise RuntimeError('No valid recursive rational fixture found.')
        for i,J in enumerate(choices):
            S = [j for j in range(m) if j not in J]
            HS = H.extract(S,list(range(b)))
            nodesS = [nodes[j] for j in S]
            assert gap_b(nodesS,b) >= gap_b(nodes,b)
            KS = krylov(nodesS,HS,t-1)
            null = K.extract([j for j in range(m) if j != i],list(range(m))).nullspace()
            assert len(null) == 1
            coeff = null[0]
            P = sum((x**r*coeff[r*b:(r+1)*b,:] for r in range(t)),sp.zeros(b,1))
            z = P.subs(x,nodes[i])
            assert z != sp.zeros(b,1)
            ES = sp.Matrix.hstack(*(x**r*sp.eye(b) for r in range(t-1)))*KS.inv()
            D = sp.diag(*(1/(nodes[j]-nodes[i]) for j in S))
            rhs = z-(x-nodes[i])*ES*D*HS*z
            assert sp.simplify(P-rhs) == sp.zeros(b,1)
            alpha = (H[i,:]*z)[0]
            assert alpha != 0
            assert K*(coeff/alpha) == sp.eye(m)[:,i]
        records.append({'b':b,'t':t,'gap':str(gap_b(nodes,b)),
                        'fixture_seed':seed,'identities_checked':m})
    return {'name':'recursive_leave_one_out_identity','passed':True,
            'fixtures':records,'identities_checked':sum(z['identities_checked'] for z in records)}


def check_raw_obstruction() -> dict:
    eta = sp.Symbol('eta', positive=True)
    g1,g2,g3 = sp.symbols('g1 g2 g3', real=True)
    nodes = [sp.Integer(1),eta,eta/2]
    K = krylov(nodes, sp.Matrix([g1,g2,g3]),3)
    c = sp.Matrix([0,-1,1])
    actual = sp.simplify(K*c)
    expected = sp.Matrix([0,g2*(eta**2-eta),g3*(eta**2/4-eta/2)])
    assert sp.simplify(actual-expected) == sp.zeros(3,1)
    assert sp.simplify(c.dot(c)) == 2
    return {"name": "raw_monomial_obstruction", "passed": True,
            "K_times_unnormalized_test_vector": [str(z) for z in actual],
            "squared_norm_expectation_upper_bound": "5*eta**2/8"}


def check_noncommutativity() -> dict:
    B2 = sp.diag(1,2)
    B3 = sp.Matrix([[3,1],[0,4]])
    value_at_B3 = B3**2-B3*(B2+B3)+B2*B3
    assert value_at_B3 == B2*B3-B3*B2
    assert value_at_B3 != sp.zeros(2)
    return {"name": "matrix_lagrange_product_obstruction", "passed": True,
            "value_at_B3": [[str(z) for z in row] for row in value_at_B3.tolist()]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    checks = [check_generic_rank(), check_exact_clusters(), check_general_filter(),
              check_t2_identity(), check_recursive_identity(), check_raw_obstruction(), check_noncommutativity()]
    result = {"arithmetic": "exact rational / symbolic", "sympy_version": sp.__version__,
              "all_passed": all(c['passed'] for c in checks), "checks": checks,
              "limitation": "Finite identity checks are not proofs of the general RA-04 assertion."}
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text+'\n',encoding='utf-8')

if __name__ == '__main__':
    main()

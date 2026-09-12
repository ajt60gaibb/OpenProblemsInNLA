#!/usr/bin/env python3
"""Independent IE-26 exact rational algebra supplement.

All arithmetic is in Q(i). The checker verifies full rational-function and
interpolation identities for an explicit five-node configuration, plus selected
Poisson identities. It does not prove the all-grid analytic bounds: those are
checked in the independent written review. No floating-point arithmetic is used.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json


@dataclass(frozen=True)
class QI:
    real: F = F(0)
    imag: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "real", F(self.real))
        object.__setattr__(self, "imag", F(self.imag))

    @staticmethod
    def cast(z):
        return z if isinstance(z, QI) else QI(z)

    def __add__(self, z):
        z = self.cast(z)
        return QI(self.real + z.real, self.imag + z.imag)

    __radd__ = __add__

    def __neg__(self):
        return QI(-self.real, -self.imag)

    def __sub__(self, z):
        return self + (-self.cast(z))

    def __rsub__(self, z):
        return self.cast(z) - self

    def __mul__(self, z):
        z = self.cast(z)
        return QI(self.real*z.real-self.imag*z.imag,
                  self.real*z.imag+self.imag*z.real)

    __rmul__ = __mul__

    def conjugate(self):
        return QI(self.real, -self.imag)

    def norm2(self):
        return self.real**2 + self.imag**2

    def __truediv__(self, z):
        z = self.cast(z)
        n = z.norm2()
        if n == 0:
            raise ZeroDivisionError
        w = self*z.conjugate()
        return QI(w.real/n, w.imag/n)

    def __rtruediv__(self, z):
        return self.cast(z)/self

    def __pow__(self, exponent):
        if exponent < 0:
            return (QI(1)/self)**(-exponent)
        result = QI(1)
        for _ in range(exponent):
            result = result*self
        return result

    def encoded(self):
        return {"real": str(self.real), "imag": str(self.imag)}


def trim(p):
    p = list(map(QI.cast, p))
    while len(p) > 1 and p[-1] == QI():
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return trim([(p[k] if k < len(p) else QI()) +
                 (q[k] if k < len(q) else QI()) for k in range(n)])


def scale(p, a):
    return trim([c*a for c in p])


def multiply(p, q):
    out = [QI()]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] = out[i+j] + a*b
    return trim(out)


def evaluate(p, z):
    result = QI()
    for c in reversed(p):
        result = result*z+c
    return result


def divide_by_root(p, z):
    n = len(p)-1
    q = [QI()]*n
    q[-1] = p[-1]
    for k in range(n-1, 0, -1):
        q[k-1] = p[k]+z*q[k]
    if p[0]+z*q[0] != QI():
        raise ArithmeticError("Nonzero synthetic-division remainder")
    return trim(q)


def circle_point(t):
    t = F(t)
    return QI((1-t*t)/(1+t*t), 2*t/(1+t*t))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=here/"reviewed-candidate.md")
    parser.add_argument("--canonical", type=Path, default=here/"canonical-target.md")
    parser.add_argument("--output", type=Path, default=here/"exact-algebra-output.json")
    args = parser.parse_args()
    checks = []

    def require(name, condition, scope="exact finite-configuration algebra"):
        if not condition:
            raise ArithmeticError("FAILED: "+name)
        checks.append({"name": name, "scope": scope, "pass": True})

    # Angles are cyclically ordered near the fifth roots of unity. These are
    # concrete rational points, not floating-point approximations to them.
    nodes = [circle_point(t) for t in [0, F(3,4), 3, -3, F(-3,4)]]
    m, N = 5, 2
    require("five distinct unit-circle nodes", len(set(nodes)) == m and all(z.norm2() == 1 for z in nodes))
    P = [QI(1)]
    for z in nodes:
        P = multiply(P, [-z, QI(1)])
    Q = [QI(1)] + [QI()]*(m-1) + [QI(1)]
    require("phase-zero root product and real monic polynomial", P[0] == QI(-1) and P[-1] == QI(1) and all(c.imag == 0 for c in P))
    derivative = [P[k]*k for k in range(1,len(P))]
    quotients = [divide_by_root(P,z) for z in nodes]
    slopes = [evaluate(derivative,z) for z in nodes]
    require("simple roots and derivative normalization", all(v != QI() for v in slopes) and all(evaluate(quotients[j],nodes[j]) == slopes[j] for j in range(m)))
    beta = [evaluate(Q,z)/(2*z*slopes[j]) for j,z in enumerate(nodes)]
    require("strictly positive real residues", all(b.imag == 0 and b.real > 0 for b in beta))
    require("total residue mass is one", sum(beta,QI()) == QI(1))
    require("all squared residue-magnitude identities", all(4*beta[j].norm2()*slopes[j].norm2() == evaluate(Q,z).norm2() for j,z in enumerate(nodes)))
    numerator = [QI()]
    for j,z in enumerate(nodes):
        numerator = add(numerator, scale(multiply([z,QI(1)],quotients[j]), -beta[j]))
    require("full partial-fraction rational-function identity", numerator == scale(Q,-1), "polynomial coefficient identity, hence all nonpole z for this configuration")

    # Columns are Fourier coefficients for the cardinal polynomials. The
    # factor z_j^N places frequencies at -N,...,N, checking their orientation.
    C = [[nodes[j]**N * quotients[j][nu+N]/slopes[j]
          for j in range(m)] for nu in range(-N,N+1)]
    A = [[z**nu for nu in range(-N,N+1)] for z in nodes]
    AC = [[sum((A[i][k]*C[k][j] for k in range(m)),QI()) for j in range(m)] for i in range(m)]
    require("exact Fourier-cardinal inverse with centered frequencies", AC == [[QI(int(i==j)) for j in range(m)] for i in range(m)])
    targets = [circle_point(t) for t in [F(1,2), 1, 2, -2, -1]]
    direct = [[(nodes[j]/z)**N * evaluate(P,z)/((z-nodes[j])*slopes[j]) for j in range(m)] for z in targets]
    via_coefficients = [[sum((z**nu*C[nu+N][j] for nu in range(-N,N+1)),QI()) for j in range(m)] for z in targets]
    require("interpolation-matrix orientation E=B A^{-1}", direct == via_coefficients)

    interior = [QI(), QI(F(1,3),F(1,5)), QI(F(-1,2),F(1,3))]
    for index,z in enumerate(interior):
        inverse_R = -evaluate(Q,z)/evaluate(P,z)
        poisson = sum((beta[j].real*(1-z.norm2())/(z-node).norm2() for j,node in enumerate(nodes)),F())
        require(f"exact Poisson representation at rational interior point {index}", inverse_R.real == poisson and poisson > 0)

    result = {
        "verdict":"PASS",
        "reviewer":"independent Codex agent /root/prepare_manuscripts",
        "arithmetic":"Python standard-library Fraction; exact Q(i) polynomial arithmetic",
        "limitation":"This finite algebra supplement does not prove the all-grid analytic estimates, weak-type theorem, localization, or uniform asymptotic bounds. Those are audited independently in the written review.",
        "source":{"name":args.source.name,"bytes":args.source.stat().st_size,"sha256":digest(args.source)},
        "canonical":{"name":args.canonical.name,"bytes":args.canonical.stat().st_size,"sha256":digest(args.canonical)},
        "checker":{"name":Path(__file__).name,"sha256":digest(Path(__file__))},
        "nodes":[z.encoded() for z in nodes],
        "residues":[str(b.real) for b in beta],
        "check_count":len(checks),"checks":checks,
    }
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"verdict":"PASS","exact_check_count":len(checks),"output":str(args.output)},indent=2))


if __name__ == "__main__":
    main()

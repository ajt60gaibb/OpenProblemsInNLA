"""Portable exact arithmetic checks of selected MF-21 proof identities.

These finite checks supplement the all-m analytic proof in reviewed-proof.md.
They do not prove its uniform estimates, limiting theorem, or full conclusion.
Only the Python standard library is used; no floating-point arithmetic is used.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
from math import comb, factorial
import hashlib
import json

EXPECTED = "98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5"


class G:
    """Gaussian rational."""
    def __init__(self, re=0, im=0):
        if isinstance(re, G):
            self.re, self.im = re.re, re.im
        else:
            self.re, self.im = F(re), F(im)

    def __add__(self, other):
        o = G(other)
        return G(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-G(other))

    def __rsub__(self, other):
        return G(other) - self

    def __mul__(self, other):
        o = G(other)
        return G(self.re*o.re-self.im*o.im, self.re*o.im+self.im*o.re)

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = G(other)
        den = o.re*o.re + o.im*o.im
        assert den
        return G((self.re*o.re+self.im*o.im)/den,
                 (self.im*o.re-self.re*o.im)/den)

    def __rtruediv__(self, other):
        return G(other) / self

    def __pow__(self, power):
        assert isinstance(power, int)
        if power < 0:
            return (1/self)**(-power)
        ans, base = G(1), self
        while power:
            if power % 2:
                ans = ans*base
            base = base*base
            power //= 2
        return ans

    def __eq__(self, other):
        o = G(other)
        return self.re == o.re and self.im == o.im

    def conj(self):
        return G(self.re, -self.im)


def product(xs):
    out = G(1)
    for x in xs:
        out = out*x
    return out


def vandermonde(xs):
    return product(xs[j]-xs[i] for i in range(len(xs)) for j in range(i+1,len(xs)))


def determinant(a):
    a = [[G(v) for v in row] for row in a]
    n = len(a)
    out = G(1)
    for k in range(n):
        pivot = next((j for j in range(k,n) if a[j][k] != 0), None)
        if pivot is None:
            return G(0)
        if pivot != k:
            a[k],a[pivot] = a[pivot],a[k]
            out = -out
        v = a[k][k]
        out = out*v
        for j in range(k+1,n):
            ratio = a[j][k]/v
            for l in range(k+1,n):
                a[j][l] = a[j][l]-ratio*a[k][l]
    return out


def subset_coefficient(roots, indices, m):
    chosen = [roots[j] for j in indices]
    others = [roots[j] for j in range(2*m) if j not in indices]
    exponent = sum(range(m+1,2*m+1)) + sum(j+1 for j in indices)
    sign = -1 if exponent%2 else 1
    return sign*vandermonde(chosen)*vandermonde(others)


def boundary_checks():
    cases = []
    z = G(F(3,5),F(4,5))
    assert z*z.conj() == 1
    for m in range(2,6):
        real_roots = [G(F(1,l+3)) for l in range(m-1)]
        choices = [("real",real_roots)]
        if m >= 3:
            roots = [G(F(1,4),F(1,5)),G(F(1,4),F(-1,5))]
            roots += [G(F(1,l+7)) for l in range(m-3)]
            choices.append(("conjugate",roots))
        for kind, inside in choices:
            outside = [1/r for r in inside]
            roots = inside+[z,z.conj()]+outside
            Q = product(outside)
            f = product(1-r/z for r in inside)
            common = vandermonde(inside)*vandermonde(outside)*Q
            plus = [m-1]+list(range(m+1,2*m))
            minus = [m]+list(range(m+1,2*m))
            cp = subset_coefficient(roots,plus,m)
            cm = subset_coefficient(roots,minus,m)
            # The chosen inherited root ordering makes sigma=-1.
            assert cp == -common*z**(-(m-1))*f.conj()**2
            assert cm == common*z**(m-1)*f**2
            for n in [1,4]:
                powers = list(range(m))+list(range(n+m,n+2*m))
                direct = determinant([[w**k for w in roots] for k in powers])
                expanded = G(0)
                for inds in combinations(range(2*m),m):
                    expanded += subset_coefficient(roots,inds,m)*product(
                        roots[j] for j in inds)**(n+m)
                assert direct == expanded
                leading = cp*(Q*z)**(n+m)+cm*(Q/z)**(n+m)
                expected = -vandermonde(inside)*vandermonde(outside)*Q**(n+m+1)*(
                    z**(n+1)*f.conj()**2-z**(-(n+1))*f**2)
                assert leading == expected
                assert direct.conj() == -direct
                # Endpoint pi: the duplicate columns are present exactly.
                terminal = inside+[G(-1),G(-1)]+outside
                assert determinant([[w**k for w in terminal] for k in powers]) == 0
                assert common != 0
                cases.append({"m":m,"n":n,"stable_list_kind":kind,
                              "full_laplace_identity":"PASS",
                              "two_leading_terms":"PASS","upper_endpoint":"PASS"})
    return cases


def green_checks():
    cases = []
    for m in range(1,21):
        den = (2*m-1)*factorial(m-1)**2
        trace_expanded = sum(
            F((-1)**k*comb(2*m-1,k),2*m+k) for k in range(2*m))/den
        trace_closed = F(factorial(2*m-1)**2,factorial(4*m-1)*den)
        assert trace_expanded == trace_closed
        for x in [F(1,2),F(2,3),F(4,5)]:
            # Exact integration of (t-x)^(2m-2) / t^(2m), from x to 1.
            integ = sum(F(comb(2*m-2,k))*(-x)**(2*m-2-k)*
                        (1-x**(k-2*m+1))/F(k-2*m+1)
                        for k in range(2*m-1))
            from_kernel = x**(2*m)*integ/factorial(m-1)**2
            closed = x**(2*m-1)*(1-x)**(2*m-1)/den
            assert from_kernel == closed
        cases.append({"m":m,"diagonal_and_trace":"PASS","trace":str(trace_closed)})
    return cases


def circulant_checks():
    cases = []
    for m in range(1,9):
        coefs = {k:(-1 if k%2 else 1)*comb(2*m,m+k) for k in range(-m,m+1)}
        for n in [1,2,5,10]:
            N = n+2*m
            for i in range(n):
                for j in range(n):
                    circular = sum(v for k,v in coefs.items() if (k-i+j)%N == 0)
                    assert circular == coefs.get(i-j,0)
            cases.append({"m":m,"n":n,"N":N,"principal_block_identity":"PASS"})
    return cases


def main():
    folder = Path(__file__).resolve().parent
    proof = folder/"reviewed-proof.md"
    assert hashlib.sha256(proof.read_bytes()).hexdigest() == EXPECTED
    result = {
        "verdict":"PASS for the exact identities and finite cases listed",
        "scope":"Supplementary exact algebra and transcription check; not an independent-agent review and not a finite proof of the all-m asymptotic theorem.",
        "arithmetic":"Python standard-library Fraction, Gaussian rationals; no floating point",
        "proof_sha256":EXPECTED,
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "boundary_determinants":boundary_checks(),
        "green_kernel_diagonal_and_trace":green_checks(),
        "circulant_principal_blocks":circulant_checks(),
    }
    output = folder/"exact-check.json"
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(result["verdict"])
    print("Boundary cases:",len(result["boundary_determinants"]))
    print("Green trace orders:",len(result["green_kernel_diagonal_and_trace"]))
    print("Circulant cases:",len(result["circulant_principal_blocks"]))
    print("Output SHA256:",hashlib.sha256(output.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()

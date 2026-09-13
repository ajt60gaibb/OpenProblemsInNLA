"""Independent exact scalar/finite-matrix diagnostics, not Lean proofs.

Uses only Fraction and a small coefficient dictionary. Source identities are
reconstructed independently; no original verifier or project proof is imported.
The universal claims remain obligations. Formalization: George Stepaniants,
Caltech Department of Computing and Mathematical Sciences, with AI assistance.
"""
from pathlib import Path
from fractions import Fraction as F
import datetime, hashlib, json

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
W = P.parents[2]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()


class Poly:
    def __init__(self, terms=0):
        self.t = ({(0, 0): F(terms)} if not isinstance(terms, dict)
                  else {k: F(v) for k, v in terms.items()})
        self.t = {k: v for k, v in self.t.items() if v}
    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = dict(self.t)
        for k, v in other.t.items(): out[k] = out.get(k, F(0)) + v
        return Poly(out)
    __radd__ = __add__
    def __neg__(self): return Poly({k: -v for k, v in self.t.items()})
    def __sub__(self, other): return self + (-other if isinstance(other, Poly) else -F(other))
    def __rsub__(self, other): return Poly(other) - self
    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = {}
        for (a, b), v in self.t.items():
            for (c, d), w in other.t.items():
                k = (a+c, b+d); out[k] = out.get(k, F(0)) + v*w
        return Poly(out)
    __rmul__ = __mul__
    def __pow__(self, n):
        out = Poly(1)
        for _ in range(n): out = out*self
        return out
    def __eq__(self, other): return self.t == (other if isinstance(other, Poly) else Poly(other)).t


d, z = Poly({(1, 0): 1}), Poly({(0, 1): 1})
Q = 2*(d+1)*z**2-(2*d+1)*z+d
SOS = 2*(d-1)*(z-F(1, 2))**2+(d-1)*F(1, 2)+4*(z-F(3, 8))**2+F(7, 16)
assert Q == SOS
for G, fact in [(2*d**2*z, (d-1)*Q),
                (2*d**2, (d-z)*(2*z+d-1)),
                (2*d*z, (d-1)*(z-d)*(2*z-1))]:
    # Clear only the nonzero z denominator from the source's exact expression.
    assert (G-2*z-d**2+1)*z-d*(d-1)*(z-1) == fact

source = W/'references/colbrook-transfer-2026-09-11/manuscripts/02_frobenius_function_transfer.tex'
assert '2(d+1)z^2-(2d+1)z+d' in source.read_text()
definitions = (P/'NLA/RA09/Definitions.lean').read_text()
assert '2*(d+1)*z^2 - (2*d+1)*z + d' in definitions
assert 'open scoped Matrix.Norms.Frobenius' in definitions
assert 'cfc (R := ℝ) f A' in definitions

# Rational diagnostics for actual continuous concave monotone nonnegative maps.
functions = [('identity', lambda x: x), ('positive affine', lambda x: 1+x),
             ('positive constant', lambda x: F(3, 2)),
             ('positive cap', lambda x: 1+min(x, F(1))),
             ('zero', lambda x: F(0))]
grid = list(map(F, ['1/8', '1/2', '1', '2', '5']))
scalar_cases = 0
for label, f in functions:
    for tau in grid:
        if f(tau) == 0:
            assert all(f(x) == 0 for x in [F(0), *grid])
            continue
        c = f(tau)/tau
        for a in grid:
            for b in grid:
                h = max(c*c*a*a-f(a)**2, F(0))
                left = h+2*f(b)*f(a)-2*c*c*b*a-f(b)**2+c*c*b*b
                right = f(b)*max(f(b)-c*b, F(0))*(1-b/a)
                assert right <= left, (label, tau, a, b)
                scalar_cases += 1


def mm(A, B):
    return [[sum((A[i][l]*B[l][j] for l in range(len(B))), F(0))
             for j in range(len(B[0]))] for i in range(len(A))]
def tr(A): return list(map(list, zip(*A)))
def sub(A, B): return [[a-b for a, b in zip(x, y)] for x, y in zip(A, B)]
def diag(a): return [[a[i] if i == j else F(0) for j in range(len(a))] for i in range(len(a))]
def fsq(A): return sum((x*x for r in A for x in r), F(0))
def trace(A): return sum((A[i][i] for i in range(len(A))), F(0))
def comb(U, a): return mm(mm(U, diag(a)), tr(U))
def spectral_trunc(U, a, k): return comb(U, [x if i < k else F(0) for i, x in enumerate(a)])
I = diag([F(1)]*3)
U = [[F(3,5), -F(4,5), F(0)], [F(4,5), F(3,5), F(0)], [F(0),F(0),F(1)]]
assert mm(tr(U), U) == I and mm(U, tr(U)) == I
a = [F(3), F(2), F(1)]
b = [F(3,2), F(1,2), F(1,4)]
A, H = diag(a), comb(U, b)
B = spectral_trunc(U, b, 1)
assert mm(A, H) != mm(H, A)
D = sub(A, H)
assert D[0][0] > 0 and D[0][0]*D[1][1]-D[0][1]*D[1][0] > 0 and D[2][2] > 0
assert all(D[i][2] == D[2][i] == 0 for i in [0,1])
p = [[x*x for x in row] for row in U]
assert all(sum(p[i][j] for i in range(3)) == 1 for j in range(3))
assert all(sum(p[i][:1]) <= 1 for i in range(3))
assert all(b[j]*sum(p[i][j]/a[i] for i in range(3)) <= 1 for j in range(3))
EA = fsq(sub(A,B)); TA = sum(x*x for x in a[1:]); deficit = fsq(A)-fsq(B)
assert EA == sum(x*x for x in a)+b[0]**2-2*b[0]*sum(p[i][0]*a[i] for i in range(3))
cross = trace(mm(B, sub(A,B)))
assert cross >= 0 and EA == deficit-2*cross and EA <= deficit
f = lambda x: 1+x
fA, C = comb(I, list(map(f,a))), spectral_trunc(U,list(map(f,b)),1)
EF = fsq(sub(fA,C)); TF = sum(f(x)**2 for x in a[1:]); c = f(a[1])/a[1]
assert EF == sum(f(x)**2 for x in a)+f(b[0])**2-2*f(b[0])*sum(p[i][0]*f(a[i]) for i in range(3))
assert EF-TF <= c*c*(EA-TA) and c*c*TA <= TF
epsilon = deficit/TA-1
assert epsilon >= 0 and deficit == (1+epsilon)*TA and EF <= (1+epsilon)*TF
positive = {k: str(v) for k,v in {'input_error':EA,'input_tail':TA,'trace_deficit':deficit,
            'cross_trace':cross,'function_error':EF,'function_tail':TF,'epsilon':epsilon}.items()}

# Repeated-zero eigenspaces may have different selected bases: f-truncations
# really differ, while both true errors equal (n-k) f(0)^2.
V = [[F(1),F(0),F(0)], [F(0),F(3,5),-F(4,5)], [F(0),F(4,5),F(3,5)]]
aa = [F(2),F(0),F(0)]; Z = diag(aa)
assert comb(V,aa) == Z and spectral_trunc(V,aa,2) == Z
assert fsq(Z)-fsq(spectral_trunc(V,aa,2)) == fsq(sub(Z,spectral_trunc(I,aa,2))) == 0
Zf = comb(I,list(map(f,aa)))
C1,C2 = spectral_trunc(I,list(map(f,aa)),2), spectral_trunc(V,list(map(f,aa)),2)
assert C1 != C2 and fsq(sub(Zf,C1)) == fsq(sub(Zf,C2)) == (3-2)*f(0)**2 == 1

record = {'verdict':'PASS exact diagnostics only; no universal Lean proof',
          'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'unbounded_coefficient_identities':['SOS polynomial equality',
            'three source normalized branch identities after clearing nonzero z'],
          'coefficient_remainders':[{str(k):str(v) for k,v in (Q-SOS).t.items()}, {}, {}, {}],
          'finite_scalar_cases':scalar_cases,
          'positive_noncommuting_matrix_case':positive,
          'zero_tail_f0_positive_case':{'n':3,'k':2,'f0':'1','both_actual_errors':'1',
             'selected_function_truncations_distinct':True},
          'caveat':'The finite diagnostics test the statement design and exact algebra only. The all-dimension/all-function scalar, CFC, PSD, norm and transfer results remain explicit Lean proof obligations; no bounded interval or numerical certificate is asserted.',
          'input_sha256':{str(x.relative_to(P)):sha(x) for x in
             [P/'NLA/RA09/Definitions.lean',P/'Challenge.lean',P/'NUMERICAL_TARGETS.md',Path(__file__)]},
          'actual_original_source_sha256':sha(source)}
(E/'exact-reconstruction.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))

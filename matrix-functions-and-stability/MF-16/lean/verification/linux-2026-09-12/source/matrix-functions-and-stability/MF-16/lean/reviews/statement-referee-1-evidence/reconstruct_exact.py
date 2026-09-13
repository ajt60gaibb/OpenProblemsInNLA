#!/usr/bin/env python3
"""Independent MF16 diagnostics from the freshly emitted actual AST and rationals.

Standard-library Fraction only. No author checker, numerical library, search or
source mutation. Polynomial identities and interval diagnostics are not Lean proofs.
"""
from collections import defaultdict
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib
import json
import re

E = Path(__file__).resolve().parent
P = E.parent.parent
log = E / 'reviews-statement-referee-1-evidence-Inspect.log'
data = {}
for line in log.read_text().splitlines():
    if re.match(r'^(AST|CENTER|BOX|C|Q|DET|RADIUS|CHECK|BOUND)=', line):
        key, value = line.split('=', 1)
        assert key not in data
        data[key] = value
assert set(data) == {'AST', 'CENTER', 'BOX', 'C', 'Q', 'DET', 'RADIUS', 'CHECK', 'BOUND'}
assert data['CHECK'] == data['BOUND'] == 'true'

def parse(items):
    token = next(items)
    if token[:2] == 'c:':
        return ('c', Q(token[2:]))
    if token[:2] == 'v:':
        i = int(token[2:])
        assert 0 <= i < 3
        return ('v', i)
    if token == 'n':
        return ('n', parse(items))
    assert token in ['a', 'm'], token
    return (token, parse(items), parse(items))

asts = []
for stream in data['AST'].split('|'):
    it = iter(stream.split(','))
    asts.append(parse(it))
    assert next(it, None) is None
assert len(asts) == 3

def evaluate(t, env, const):
    op = t[0]
    if op == 'c': return const(t[1])
    if op == 'v': return env[t[1]]
    if op == 'n': return -evaluate(t[1], env, const)
    a, b = evaluate(t[1], env, const), evaluate(t[2], env, const)
    return a + b if op == 'a' else a * b

class Interval:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        assert self.lo <= self.hi
    @staticmethod
    def of(v): return v if isinstance(v, Interval) else Interval(v)
    def __add__(self, b):
        b = self.of(b); return Interval(self.lo+b.lo, self.hi+b.hi)
    __radd__ = __add__
    def __neg__(self): return Interval(-self.hi, -self.lo)
    def __sub__(self, b): return self + -self.of(b)
    def __rsub__(self, a): return self.of(a) + -self
    def __mul__(self, b):
        b = self.of(b)
        endpoints = [self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi]
        return Interval(min(endpoints), max(endpoints))
    __rmul__ = __mul__
    def abs_bound(self): return max(abs(self.lo), abs(self.hi))
    def serial(self): return [str(self.lo), str(self.hi)]

class Dual:
    def __init__(self, val, derivative):
        self.val = Interval.of(val)
        self.der = tuple(Interval.of(v) for v in derivative)
    @staticmethod
    def const(q): return Dual(q, (0, 0, 0))
    def __add__(self, b): return Dual(self.val+b.val, [a+c for a,c in zip(self.der,b.der)])
    def __neg__(self): return Dual(-self.val, [-a for a in self.der])
    def __mul__(self, b):
        return Dual(self.val*b.val, [a*b.val+self.val*c for a,c in zip(self.der,b.der)])

center = [Q(s) for s in data['CENTER'].split(',')]
bflat = [Q(s) for s in data['BOX'].split(',')]
box = [Interval(*bflat[2*i:2*i+2]) for i in range(3)]
cflat = [Q(s) for s in data['C'].split(',')]
C = [cflat[3*i:3*i+3] for i in range(3)]
assert center == [Q(17471725533,5000000000), -Q(51638297,156250000), Q(2224465749,2500000000)]
radius = Q(1,10000000)
assert all(I.lo == m-radius and I.hi == m+radius for I,m in zip(box,center))
assert box[0].lo > 3 and box[2].lo > 0
assert radius == Q(data['RADIUS'])
assert C == [[Q(17591641083,500000000), Q(20183,10000000000), -Q(17029,10000000000)],
             [-Q(11575092327,500000000), -Q(2477,2000000000), Q(10667,10000000000)],
             [-Q(21469001731,5000000000), -Q(2797,10000000000), Q(2319,10000000000)]]

detC = sum(C[0][j]*(C[1][(j+1)%3]*C[2][(j+2)%3]-C[1][(j+2)%3]*C[2][(j+1)%3]) for j in range(3))
assert detC == Q(data['DET']) == Q(790668616748253,62500000000000000000000000000) != 0
env = [Dual(box[i], [int(i==j) for j in range(3)]) for i in range(3)]
evaluated = [evaluate(ast, env, Dual.const) for ast in asts]
J = [r.der for r in evaluated]
preconditioned = [[int(i==j)-sum(C[i][k]*J[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
q = max(sum(a.abs_bound() for a in row) for row in preconditioned)
assert q == Q(data['Q']) and 0 <= q < Q(27,1000) < 1
fcenter = [evaluate(ast, center, Q) for ast in asts]
displacements = [sum(C[i][j]*fcenter[j] for j in range(3)) for i in range(3)]
images = [Interval(center[i]-displacements[i]-q*radius, center[i]-displacements[i]+q*radius) for i in range(3)]
assert all(box[i].lo < images[i].lo and images[i].hi < box[i].hi for i in range(3))
assert max(abs(v) for v in displacements) < Q(4,10**11)
margins = [min(images[i].lo-box[i].lo, box[i].hi-images[i].hi) for i in range(3)]
assert min(margins) > radius/2

class Poly:
    """Exact sparse Q[x,y,z], independent from the interval evaluator."""
    def __init__(self, value=0):
        if isinstance(value, Poly): self.d = dict(value.d)
        elif isinstance(value, dict): self.d = {m:Q(c) for m,c in value.items() if c}
        else: self.d = {} if not value else {(0,0,0):Q(value)}
    def __add__(self, b):
        b=Poly(b); d=defaultdict(Q,self.d)
        for m,c in b.d.items(): d[m]+=c
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,b): return self+-Poly(b)
    def __rsub__(self,b): return Poly(b)+-self
    def __mul__(self,b):
        b=Poly(b);d=defaultdict(Q)
        for m,c in self.d.items():
            for n,e in b.d.items():d[tuple(a+b for a,b in zip(m,n))]+=c*e
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,b):return self.d==Poly(b).d
    def det_three_remainder(self):
        # The monic rule x*z = y^2 + 3 is exact reduction modulo det(S)-3.
        d=defaultdict(Q)
        for (a,b,c),v in self.d.items():
            k=min(a,c)
            for j in range(k+1):d[(a-k,b+2*j,c-k)]+=v*comb(k,j)*3**(k-j)
        return Poly(d)

def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def mpow(A,n):
    r=[[1,0],[0,1]]
    for _ in range(n):r=mm(r,A)
    return r
def det2(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def word(A,B):return mm(mm(mm(mm(A,B),mpow(A,12)),B),A)

definition=(P/'NLA/MF16/Definitions.lean').read_text()
def matrix_literal(name):
    match=re.search(r'def '+name+r' : RealMatrix := !!\[(.*?)\]',definition,re.S)
    assert match
    return [[Q(s.strip()) for s in row.split(',')] for row in match.group(1).split(';')]
B=matrix_literal('realB');P0=matrix_literal('realP');X0=matrix_literal('realX0')
assert B==[[1,4],[4,17]] and X0==[[3,0],[0,1]]
assert P0==[[4783113,6377496],[6377496,8503345]]
assert word(X0,B)==P0 and det2(B)==1 and det2(X0)==3 and det2(P0)==3**14
assert all(A[0][1]==A[1][0] and A[0][0]>0 and det2(A)>0 for A in [B,P0,X0])
assert '[.X, .B] ++ List.replicate 12 .X ++ [.B, .X]' in definition
letters=['X','B']+['X']*12+['B','X']
assert letters==letters[::-1] and len(letters)==16 and letters.count('X')==14 and letters.count('B')==2

x,y,z=[Poly({tuple(int(i==j) for j in range(3)):1}) for i in range(3)]
S=[[x,y],[y,z]];s=x+z;t=s*s
u=s*(t*(t*(t*(t*(t-30)+324)-1512)+2835)-1458)
v=3*(t*(t*(t*(t*(t-27)+252)-945)+1215)-243)
power=mpow(S,12)
reduced=[[u*S[i][j]-int(i==j)*v for j in range(2)] for i in range(2)]
assert all((power[i][j]-reduced[i][j]).det_three_remainder()==0 for i in range(2) for j in range(2))
W=word(S,B)
Rword=mm(mm(mm(mm(S,B),reduced),B),S)
polys=[evaluate(ast,[x,y,z],Poly) for ast in asts]
assert polys[0]==det2(S)-3
assert polys[1]==Rword[0][0]-P0[0][0] and polys[2]==Rword[0][1]-P0[0][1]
assert all((W[i][j]-Rword[i][j]).det_three_remainder()==0 for i in range(2) for j in range(2))
assert W[0][1]==W[1][0]
assert det2(W)==det2(S)**14
# Exact recovery algebra: if word11=P11 and word12=P12, determinant equality
# forces P11*(word22-P22)=0. P11 is the fixed positive nonzero integer above.
a,b,c=[Poly({tuple(int(i==j) for j in range(3)):1}) for i in range(3)]
assert P0[0][0]*c-P0[0][1]**2-det2(P0)==P0[0][0]*(c-P0[1][1])

result={
 'verdict':'PASS: independent exact interval and generic finite-polynomial diagnostics; no Lean theorem or kernel certificate claimed',
 'Definitions_sha256':hashlib.sha256((P/'NLA/MF16/Definitions.lean').read_bytes()).hexdigest(),
 'actual_inspector_log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
 'actual_AST_constructor_fragment':['const','var 0..2','add','mul','neg'],
 'actual_checker_machine_observation':data['CHECK'],
 'exact_independent_q_matches_actual_Lean_q':str(q),
 'q_decimal_diagnostic':float(q),
 'actual_preconditioner_det':str(detC),'actual_radius':str(radius),
 'centers':[str(a) for a in center],'box':[a.serial() for a in box],
 'interval_jacobian':[[a.serial() for a in row] for row in J],
 'preconditioned_interval_matrix':[[a.serial() for a in row] for row in preconditioned],
 'center_displacements':[str(a) for a in displacements],
 'strict_self_map_image':[a.serial() for a in images],
 'strict_margins':[str(a) for a in margins],
 'all_support_center_det_contraction_selfmap_checks':True,
 'x_lower_endpoint_gt_3':True,'unchanged_source_word_and_matrix_data':True,
 'generic_actual_matrix_twelfth_power_mod_det_three':True,
 'actual_AST_residuals_equal_reduced_word_entries':True,
 'all_four_actual_word_entries_mod_det_three':True,
 'actual_word_symmetry_and_det_power_identity':True,
 'remaining_entry_recovery_polynomial_identity':True,
 'scope_limits':['No Banach/real root established by Python or machine eval.',
                 'No complex PD or real-to-complex bridge proved in Lean at statement stage.',
                 'No final solution export or full universal negation proved yet.']
}
(E/'exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: actual AST/data, all exact checker conditions, q='+str(float(q))+', exact generic matrix/word/determinant bridges diagnostically reproduced.')

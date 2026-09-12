"""Independent statement-referee arithmetic, not a Lean proof certificate.

Uses successive matrix multiplications rather than the author's power table.
Constants were transcribed from the frozen definitions and original source.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
REPO = PROJECT.parents[2]

def mm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(3)), Q(0))
             for j in range(3)] for i in range(3)]

def transpose(a):
    return [list(row) for row in zip(*a)]

def diag(v):
    return [[Q(v[i]) if i == j else Q(0) for j in range(3)] for i in range(3)]

def power(a, n):
    result = diag([1, 1, 1])
    for _ in range(n):
        result = mm(result, a)
    return result

def det(a):
    return (a[0][0] * (a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1] * (a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2] * (a[1][0]*a[2][1]-a[1][1]*a[2][0]))

ints = [[4616, -39, -1250], [-39, 55069, -1519], [-1250, -1519, 6499]]
t = [[Q(v, 8192) for v in row] for row in ints]
d, dinv = diag([16, Q(1,16), 1]), diag([Q(1,16), 16, 1])
a = power(d, 2)
assert a == diag([256, Q(1,256), 1])
assert mm(d, dinv) == mm(dinv, d) == diag([1,1,1])
h = [[Q(1),Q(0),Q(0)], [Q(-39,4616),Q(1),Q(0)],
     [Q(-625,2308),Q(-7060454,254196983),Q(1)]]
pivots = [Q(577,1024), Q(254196983,37814272), Q(1555181999141,2082381684736)]
assert all(x > 0 for x in pivots) and det(h) == 1
assert mm(mm(h,diag(pivots)),transpose(h)) == t == transpose(t)
minors = [Q(ints[0][0]), Q(ints[0][0]*ints[1][1]-ints[0][1]*ints[1][0]), det(ints)]
assert minors == [4616,254196983,1555181999141]
t8 = power(t,8)
b = mm(mm(d,t8),d)
assert mm(mm(dinv,b),dinv) == t8
assert b == transpose(b)
f, e = diag([2,Q(1,2),1]), diag([32,Q(1,32),1])
assert power(f,8) == a and power(e,8) == power(a,5)
assert mm(f,d) == e
n = mm(mm(mm(e,t),d),b)
v = [Q(0),Q(4,5),Q(-3,5)]
assert sum(x*x for x in v) == 1
test = sum(n[0][j]*v[j] for j in range(3))
trace = sum(b[i][i] for i in range(3))
ab = mm(a,b)
frob = sum(x*x for row in ab for x in row)
assert trace < 4**8 and test > 44000 and frob < 10500**2
source_r = [[563431071954661,-4774979464975,-152620714401404],
            [-4774979464975,6722248446399974,-185449303604146],
            [-152620714401404,-185449303604146,793308473748417]]
errors = [[abs(Q(source_r[i][j],10**15)-t[i][j]) for j in range(3)] for i in range(3)]
assert all(x < Q(1,16384) for row in errors for x in row)
assert b != [[17,-4,0],[-4,16385,-8192],[0,-8192,4096]]

def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,list): return [serial(y) for y in x]
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    return x

arithmetic = dict(method='Independent exact Fraction arithmetic; eight successive products; no imported author checker',
    T=t, D=d, A=a, T8=t8, B=b, N=n, AB=ab, unit_vector=v,
    LDL_pivots=pivots, leading_integer_minors=minors, trace_B=trace,
    trace_margin=4**8-trace, test_value=test, test_margin=test-44000,
    frobenius_squared_AB=frob, frobenius_margin=10500**2-frob,
    unique_nearest_dyadic_errors=errors, adapted_B_differs_from_source=True,
    certificate_scope='Finite statement reconstruction only; CFC, norm and singular-value implications still require Lean proof.')
(HERE/'reconstruction.json').write_text(json.dumps(serial(arithmetic),indent=2)+'\n')

sha = lambda b: hashlib.sha256(b).hexdigest()
freeze = json.loads((PROJECT/'reviews/statement-freeze.json').read_text())
for rel, expected in freeze['files'].items():
    assert sha((PROJECT/rel).read_bytes()) == expected, rel
for rel, expected in freeze['source_files'].items():
    assert sha((REPO/rel).read_bytes()) == expected, rel
    original = subprocess.check_output(['git','show',freeze['base_commit']+':'+rel],cwd=REPO)
    assert sha(original) == expected, rel
assert not (PROJECT/'Solution.lean').exists()
assert not (PROJECT/'NLA/MI22/Proof.lean').exists()
cfg=json.loads((PROJECT/'comparator.json').read_text())
assert cfg['definition_names']==[]
assert set(cfg['permitted_axioms']) == {'propext','Classical.choice','Quot.sound'}
challenge=(PROJECT/'Challenge.lean').read_text()
names=re.findall(r'^theorem\s+(\w+)',challenge,re.M)
assert ['NLA.MI22.'+x for x in names] == cfg['theorem_names'] and len(names)==8
inspection=(HERE/'inspection.log').read_text()
audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",inspection)
assert len(audits)==22
for name, raw in audits:
    assert set(x.strip() for x in raw.split(',') if x.strip()) <= set(cfg['permitted_axioms']),name
sections = re.split(r'(?=^def NLA\.MI22\.)',inspection,flags=re.M)
selected = {}
for section in sections:
    if section.startswith('def NLA.MI22.'):
        name=section.split()[1]
        selected[name]={'lines':len(section.splitlines()),'sha256':sha(section.encode())}
for term in ['LinearMap.singularValues','Matrix.toEuclideanLin', 'Matrix.toEuclideanCLM',
             'ContinuousLinearMap.hasOpNorm','EuclideanSpace','CFC.rpow',
             'Complex.normSq','Finset.range','WithLp.toLp']:
    assert term in inspection, term
(HERE/'independent-input-audit.json').write_text(json.dumps(dict(
    statement_files=len(freeze['files']),immutable_source_files=len(freeze['source_files']),
    base=freeze['base_commit'], freeze_sha256=sha((PROJECT/'reviews/statement-freeze.json').read_bytes()),
    all_hashes_match=True,proof_absent=True,comparison_exports=cfg['theorem_names'],
    permitted_axioms=cfg['permitted_axioms'],inspection_axiom_audits=audits,
    actual_definition_sections=selected, inspection_sha256=sha(inspection.encode())),indent=2)+'\n')
print(json.dumps(dict(status='PASS',frozen_files=27,source_files=8,axiom_audits=len(audits),
    trace_B=float(trace),test_value=float(test),frobenius_squared_AB=float(frob),
    reconstruction_sha256=sha((HERE/'reconstruction.json').read_bytes())),indent=2))

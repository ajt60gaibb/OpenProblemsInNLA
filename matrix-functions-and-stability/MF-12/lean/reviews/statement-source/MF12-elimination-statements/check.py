from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import comb
import hashlib
import json
import re
import subprocess

root = Path('/tmp/nla-lean-next-20260915/matrix-functions/MF-12')
out = Path('/tmp/nla-lean-next-20260915/reviews/MF12-elimination-statements')
repo = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
sha = lambda data: hashlib.sha256(data).hexdigest()
source = json.loads((root / 'SOURCE-PROVENANCE.json').read_text())
source_checks = []
for record in source['sources']:
    data = subprocess.check_output(['git', '-C', str(repo), 'show',
        source['upstream_commit'] + ':' + record['canonical_path']])
    retained = (root / record['retained_path']).read_bytes()
    assert data == retained and sha(data) == record['sha256']
    source_checks.append({'path': record['canonical_path'], 'sha256': sha(data),
                          'independently_matches_actual_git_show': True})

def mm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]

def power(a, q):
    b = eye(len(a))
    while q:
        if q % 2:
            b = mm(a, b)
        a = mm(a, a)
        q //= 2
    return b

A = [[F(x) for x in r] for r in [
    [1, 0, 0, 0, 0, 0], [0, F(1,4), F(1,4), 0, 0, 0],
    [0, 0, F(1,4), 0, 0, 0], [0, 0, 0, F(1,2), F(1,2), 0],
    [0, 0, 0, 0, F(1,2), 0], [0, 0, 0, 0, 0, 1]]]
V = [[F(x) for x in r] for r in [[1,0],[0,0],[1,0],[0,0],[0,1],[0,1]]]
U = [[F(x) for x in r] for r in [[1,-1,0,1,0,0],[0,0,0,0,0,1]]]
P = mm(V,U)
assert mm(U,V) == eye(2) and mm(P,P) == P and A != P
ell = lambda q: F(q) * F(1,4) ** q
gain = lambda q: F(q) * F(1,2) ** q
T = lambda q: [[1-ell(q), gain(q)], [F(0),F(1)]]
for q in range(13):
    assert mm(mm(U,power(A,q)),V) == T(q)
    assert gain(q)**2 == q*ell(q)
    assert q == 0 or 0 < ell(q) <= F(1,4)
gap_lists = 0
for length in range(5):
    for qs in product(range(5), repeat=length):
        b = eye(2)
        weights = []
        for i,q in enumerate(qs):
            weight = F(1)
            for qj in qs[i+1:]:
                weight *= 1-ell(qj)
            weights.append(weight)
            b = mm(T(q), b)
        assert all(0 <= w <= 1 for w in weights)
        assert sum((ell(q)*w for q,w in zip(qs,weights)),F(0)) == 1-b[0][0]
        assert sum((gain(q)*w for q,w in zip(qs,weights)),F(0)) == b[0][1]
        assert b[0][1] >= 0 and b[0][1]**2 <= sum(qs)
        gap_lists += 1
for n in range(4,257):
    q=0
    while 4**(q+1) <= n:
        q += 1
    k=n//(q+1)
    r=n-k*(q+1)
    assert q >= 1 and k >= 1 and 4**q <= n < 4**(q+1)
    assert 2*(q+1) <= 4**q and r+k*(q+1)==n and k*ell(q) >= F(1,4)
    assert (1-ell(q))**k <= 1/(1+k*ell(q))
    assert 1-(1-ell(q))**k >= F(1,5)
    if n <= 64:
        W=mm(power(A,r),power(mm(P,power(A,q)),k))
        applied=mm(W,V)
        exact=gain(q)/ell(q)*(1-(1-ell(q))**k)
        assert applied[0][1] == exact
        assert exact**2 >= F(n,200)
for m in range(1,10):
    for n in range(1,33):
        lower_entry=comb(n,m) if n>=m else 1
        assert F(n,m)**m <= lower_entry
        assert all(comb(n,k) <= n**m for k in range(m+1))

names = re.findall(r'^theorem\s+(\w+)', (root/'Challenge.lean').read_text(), re.M)
config=json.loads((root/'comparator.json').read_text())
assert len(names)==28 and config['theorem_names']==['NLA.MF12.'+x for x in names]
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
tracked=['NLA/MF12/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md',
    'SourceCorrespondence.md','comparator.json','formalization.yaml',
    'SOURCE-PROVENANCE.json','lakefile.toml','lake-manifest.json','lean-toolchain']
hashes={p:sha((root/p).read_bytes()) for p in tracked}
for p in tracked:
    dest=out/'reviewed-source'/p
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes((root/p).read_bytes())
checks={
 'scope':'independent mathematical statement review and supplementary exact arithmetic only',
 'reviewer':'/root/next_elimination',
 'reviewer_is_not_MF12_implementer':True,
 'source_hashes':hashes, 'canonical_sources':source_checks,
 'all_28_comparator_targets_match':True, 'replaceable_definition_holes':[],
 'independent_exact_fraction_checks':{
   'alpha_one_half_projection_and_powers_q_zero_through_12':True,
   'gap_lists_with_0_to_4_entries_each_0_to_4':gap_lists,
   'exact_logarithm_division_and_Bernoulli_n_4_through_256':True,
   'six_dimensional_prescribed_lower_word_n_4_through_64':True,
   'Jordan_lower_entry_m_1_through_9_n_1_through_32':True},
 'general_analytic_source_review':True,
 'no_local_Lean_or_Lake_execution':True,
 'remote_statement_elaboration':'pending',
 'proof_implementation_acceptance':'not applicable; proof-free draft',
 'kernel_Comparator_and_controls':'pending',
 'verdict':'APPROVE complete mathematical statement boundary; implementation still gated'}
(out/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'reviewed_hashes':hashes, 'gap_cases':gap_lists,
                 'checks_sha256':sha((out/'CHECKS.json').read_bytes())},indent=2))

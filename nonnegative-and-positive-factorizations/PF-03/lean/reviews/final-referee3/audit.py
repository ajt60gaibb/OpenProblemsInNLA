"""Independent static/evidence/rational-data audit; DOES NOT RUN LEAN or Comparator."""
from pathlib import Path
from fractions import Fraction as F
import ast
import datetime
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
D = ROOT / '.local-recovery-20260918'
P = D / 'development/PF03-agent-packaging-v1/project'
W = D / 'publication/PF03'
U = W / 'nonnegative-and-positive-factorizations/PF-03/lean'
V = U / 'verification/local-2026-09-19'
OUT = Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rawdigest(b): return hashlib.sha256(b).hexdigest()
def readj(p): return json.loads(p.read_text())
def assert_equal(x,y,label):
    if x != y: raise AssertionError(label)
def uncomment(s):
    # All reviewed package comments are nonnested, and this scan does not execute Lean.
    return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
def norm(s): return re.sub(r'\s+','',s)

fpath = D / 'publication/PF03-LOCAL-EVIDENCE-FREEZE.json'
assert_equal(digest(fpath),'dc090fe6ccba8a12f344cb2392267a8f8ffad3be5cf1b552bb821e40fb0099d1','freeze')
freeze = readj(fpath)
for rel,sha in freeze['files'].items(): assert_equal(digest(U/rel),sha,rel)
lean = sorted(P.rglob('*.lean'))
assert_equal(len(lean),61,'Lean file count')
for p in lean: assert_equal(digest(p),digest(U/p.relative_to(P)),str(p))
cfg = readj(P/'comparator.json')
assert_equal(cfg['definition_names'],[],'no replaceable definitions')
assert_equal(set(cfg['permitted_axioms']),{'propext','Classical.choice','Quot.sound'},'allowed axioms')
ct = uncomment((P/'Challenge.lean').read_text())
source_text = {str(p.relative_to(P)):uncomment(p.read_text()) for p in lean}
contract_results = []
for name in cfg['theorem_names']:
    short = name.rsplit('.',1)[-1]
    pattern = rf'\btheorem\s+{short}\b([\s\S]*?)\s*:='
    ref = re.search(pattern,ct)
    impl = [(rel,re.search(pattern,t)) for rel,t in source_text.items() if rel!='Challenge.lean']
    impl = [(rel,m) for rel,m in impl if m]
    assert_equal(len(impl),1,'unique implementation '+name)
    assert_equal(norm(ref.group(1)),norm(impl[0][1].group(1)),'exact source signature '+name)
    contract_results.append({'declaration':name,'source':impl[0][0],'normalized_signature_equal':True})
assert_equal(len(contract_results),25,'contracts')
assert_equal(len(re.findall(r'\bsorry\b',ct)),25,'reference holes')
for rel,t in source_text.items():
    if rel=='Challenge.lean': continue
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',t),rel
    assert not re.search(r'^import\s+Challenge\b',t,re.M),rel

# Validate every original receipt, traverse actual command reuse edges independently,
# and tie the successful source/dependency/log/output hashes to the published files.
audit = readj(V/'LOCAL-REPLAY-AUDIT.json')
receipts,receipt_hashes = {},{}
for run,m in audit['lossless_original_receipts'].items():
    z=(V/m['file']).read_bytes(); raw=gzip.decompress(z)
    assert_equal(rawdigest(z),m['gzip_sha256'],run+' gzip')
    assert_equal(rawdigest(raw),m['original_sha256'],run+' raw')
    receipts[run]=json.loads(raw);receipt_hashes[run]=rawdigest(raw)
records = {m['module']:m for m in audit['module_records']}
assert_equal(len(records),60,'60 implementation plus aggregate modules')
closure = set()
def imports(module):
    rel=module.replace('.','/')+'.lean'
    return re.findall(r'^import\s+(\S+)',source_text[rel],re.M)
def descend(module):
    if module in closure:return
    closure.add(module)
    for dep in imports(module):
        if dep.startswith('NLA.PF03.'):descend(dep)
descend('Solution')
assert_equal(closure,set(records),'complete Solution source closure')
reuse_edges=0
validated=[]
for module,m in records.items():
    rel=m['source'];source_sha=digest(U/rel);out_sha=m['output_sha256']
    assert_equal(source_sha,m['source_sha256'],module+' source')
    run='recovery-047';seen=set();fresh=None
    while True:
        assert run not in seen,module+' reuse cycle';seen.add(run)
        rr=receipts[run]
        assert_equal(rr['source_inputs'][rel],source_sha,module+' receipt source')
        cc=[c for c in rr['commands'] if c['module']==module]
        assert_equal(len(cc),1,module+' unique receipt command')
        c=cc[0]
        assert_equal(c['source_sha256'],source_sha,module+' command source')
        assert_equal(c['output_sha256'],out_sha,module+' command output')
        if c.get('status')=='reused_exact_successful_local_output':
            for dep,sha in c['transitive_source_hashes'].items():
                assert_equal(digest(U/dep),sha,module+' transitive '+dep)
            prior=Path(c['prior_receipt']).parent.name
            assert_equal(c['prior_receipt_sha256'],receipt_hashes[prior],module+' prior receipt')
            run=prior;reuse_edges+=1
        else:
            assert_equal(c['exit_code'],0,module+' successful origin')
            assert '--threads=1' in c['argv'] and '--memory=4096' in c['argv']
            assert_equal(c['argv'][-1],rel,module+' fresh source argv')
            assert_equal(c,m['actual_fresh_command'],module+' archived origin command')
            assert_equal(run,m['fresh_success_run'],module+' fresh run')
            assert_equal(digest(V/m['log']),c['log_sha256'],module+' log')
            assert_equal(digest(Path(c['argv'][c['argv'].index('-o')+1])),out_sha,module+' local olean')
            direct={d for d in imports(module) if d.startswith('NLA.PF03.')}
            assert_equal(set(c['dependency_olean_sha256']),direct,module+' direct dependencies')
            for dep,sha in c['dependency_olean_sha256'].items():
                assert_equal(sha,records[dep]['output_sha256'],module+' imported olean '+dep)
            fresh=c;break
    validated.append({'module':module,'fresh_origin':run,'reuse_edges':len(seen)-1,'source_sha256':source_sha,'output_sha256':out_sha})
assert_equal(digest(Path(audit['aggregate_command']['argv'][0])),audit['compiler_sha256'],'current actual compiler binary')
assert_equal(digest(V/'serial_compile_recovery.py'),audit['runner_sha256'],'runner bytes')
axiomlog=(V/'logs/recovery-047/Solution.log').read_text()
actual=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axiomlog)
assert_equal([x[0] for x in actual],cfg['theorem_names'],'all25 actual axiom reports')
for n,ax in actual: assert_equal(set(ax.split(', ')),set(cfg['permitted_axioms']),n+' axioms')
assert_equal(len(re.findall(r'^#assert_trust kernel ',source_text['Solution.lean'],re.M)),25,'25 trust commands')

# Independent parser: AST whitelist for vectors, integer arithmetic and rational
# division; no import or execution of the author's generator or verifier scripts.
def aval(node):
    if isinstance(node,ast.List):return [aval(x) for x in node.elts]
    if isinstance(node,ast.Constant) and isinstance(node.value,int):return F(node.value)
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -aval(node.operand)
    if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Div):return aval(node.left)/aval(node.right)
    raise ValueError(ast.dump(node)[:100])
def literal_defs(path):
    t=uncomment(path.read_text()); out={}
    starts=list(re.finditer(r'^def (\w+)[^\n]*:=\s*',t,re.M))
    for i,m in enumerate(starts):
        end=starts[i+1].start() if i+1<len(starts) else len(t)
        body=t[m.end():end].strip();body=re.split(r'\nend\b',body)[0].strip()
        out[m.group(1)]=aval(ast.parse(body.replace('![','['),mode='eval').body)
    return out
def fractions(x):return [fractions(y) for y in x] if isinstance(x,list) else F(x)
raw=literal_defs(P/'NLA/PF03/RawData.lean')
cache=literal_defs(P/'NLA/PF03/QuadraticGeneratorCache.lean')['quadraticGeneratorCache']
data=W/'references/holden-pf03-2026-09-13/data'
seed=readj(data/'exact_algebraic_certificate.json');cone=readj(data/'rational_cone_certificate.json')
cf=fractions(seed['coefficient_matrices'])
assert all(x[1:]==[F(0),F(0)] for mat in cf for row in mat for x in row)
expected={'coefficientMatrices':[[[x[0] for x in row] for row in mat] for mat in cf],
 'orthogonalMatrix':fractions(seed['orthogonal_matrix']),'quadraticMatrix':fractions(seed['Q']),
 'restrictedGram':fractions(seed['restricted_gram']),'triangle':fractions(cone['coefficient_triangle']),
 'barycentricCoefficients':fractions(cone['barycentric_coefficients']),
 'generators':fractions(cone['generators']),'positiveSlice':fractions(cone['positive_slice_functional'])}
assert_equal(raw,expected,'all raw literal rational arrays match primary JSON')
z=(F(0),)*3;one=(F(1),F(0),F(0))
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def scale(c,x):return tuple(c*a for a in x)
def mul(x,y):
    a,b,c=x;d,e,f=y
    return (a*d+2*b*f+2*c*e,a*e+b*d+2*c*f,a*f+b*e+c*d)
def total(xs):
    s=z
    for x in xs:s=add(s,x)
    return s
lo,up=fractions(cone['isolation_interval'])
assert 0<lo and lo**3<2<up**3
def lower(x):return x[0]+x[1]*(lo if x[1]>=0 else up)+x[2]*(lo**2 if x[2]>=0 else up**2)
O=raw['orthogonalMatrix'];Q=raw['quadraticMatrix'];G=raw['generators'];H=raw['restrictedGram'];B=raw['coefficientMatrices'];T=raw['triangle']
assert all(O[r][i][k]==B[k][r][i] for r in range(7) for i in range(7) for k in range(3))
for r in range(7):
    for s in range(7):
        assert total(mul(O[r][i],O[s][i]) for i in range(7))==(one if r==s else z)
        assert Q[r][s]==Q[s][r]
assert total(Q[i][i] for i in range(7))==z
local_minors=[]
for i in range(7):
    C=[[B[k][r][i] for k in range(3)] for r in range(7)]
    for a in range(3):
        for b in range(3):
            assert tuple(H[i][a][b])==total(scale(C[r][a]*C[s][b],Q[r][s]) for r in range(7) for s in range(7))
        assert total(mul(H[i][a][b],tuple(F(int(b==k)) for k in range(3))) for b in range(3))==z
    det=add(mul(H[i][0][0],H[i][1][1]),scale(-1,mul(H[i][0][1],H[i][0][1])))
    assert lower(H[i][0][0])>0 and lower(det)>0
    assert C[0][0]*C[1][1]-C[0][1]*C[1][0]!=0
    local_minors.append([str(lower(H[i][0][0])),str(lower(det))])
    for r in range(7):
        for a in range(3):assert G[r][3*i+a]==sum(C[r][k]*T[k][a] for k in range(3))
for r in range(7):
    for j in range(21):assert tuple(cache[r][j])==total(scale(G[s][j],Q[r][s]) for s in range(7))
cross=[lower(total(scale(G[r][3*i+a],cache[r][3*j+b]) for r in range(7)))
 for i in range(7) for j in range(i+1,7) for a in range(3) for b in range(3)]
assert len(cross)==189 and min(cross)>0
assert all(lower(x)>0 for x in raw['barycentricCoefficients'])
assert total(raw['barycentricCoefficients'])==one
for r in range(3):
    assert total(scale(T[r][j],raw['barycentricCoefficients'][j]) for j in range(3))==tuple(F(int(r==k)) for k in range(3))
slicevals=[sum(raw['positiveSlice'][r]*G[r][j] for r in range(7)) for j in range(21)]
assert min(slicevals)>0

formal=readj(U/'formalization.yaml')
schema_path=D/'development/PF03-agent-packaging-v1/consulted/v0.4.schema.json'
try:
    import jsonschema
    jsonschema.Draft202012Validator(readj(schema_path)).validate(formal)
    schema_status='PASS against locally retained pinned v0.4 schema'
except ImportError:
    schema_status='NOT_RUN: jsonschema not installed; no install requested'

result={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/pf03_final_referee3','scope':'Independent static, exact rational-data and existing-evidence audit only',
 'new_Lean_run':False,'Comparator_run':False,'compiled_outputs_rechecked_by_kernel':False,
 'freeze_sha256':digest(fpath),'frozen_files_checked':len(freeze['files']),
 'sealed_Lean_files_checked':len(lean),'source_signature_comparisons':contract_results,
 'trust_scan':'No admitted proofs, custom axioms, unsafe/native verification in implementation; isolated25 Challenge holes only',
 'receipt_files_authenticated':len(receipts),'receipt_reuse_edges_checked':reuse_edges,
 'authenticated_module_records':validated,'axiom_reports_checked':25,
 'finite_data':{'literal_source_arrays':8,'orthogonal_Gram_entries':49,'restricted_entries':63,
 'local_kernel_rows':21,'local_positive_minors':14,'nonzero_rational_minors':7,
 'generator_coordinates':147,'QG_cubic_entries':147,'strict_cross_pairings':189,
 'positive_slice_values':21,'positive_barycentric_values':3,
 'min_cross_lower_approx':float(min(cross)),'min_slice_approx':float(min(slicevals)),
 'note':'Rational checks use exact fractions; displayed approximations are summaries only. These Python checks are not Lean proof evidence.'},
 'schema_validation':schema_status,'completed_target_count_change':0}
(OUT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['source_signature_comparisons','authenticated_module_records']},indent=2))

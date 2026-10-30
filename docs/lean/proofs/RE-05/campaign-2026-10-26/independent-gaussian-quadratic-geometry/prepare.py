#!/usr/bin/env python3
"""Prepare exact independent Gaussian-quadratic source-kind and literal-type audit."""
from pathlib import Path
import hashlib,importlib.util,json,re
B=Path(__file__).resolve().parent;REPO=B.parents[5];C=B.parent;LIVE=REPO/'lean-statements'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('inventory',B/'source_inventory.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
lock=C/'GAUSSIAN_QUADRATIC_FREEZE_2026-10-26.json'
assert sha(lock)=='9fb7b82899007ad24145769be30abc627824d11a79c1c52c204cc7fca786ca24'
f=json.loads(lock.read_text());assert f['new_declarations']==19 and f['definitions']==2 and f['theorems']==17
for x in f['new_sources']+f['prerequisites']:assert sha(REPO/x['path'])==x['sha256']
assert not (B/'source-lock.json').exists()
frozen={};order=[]
def visit(module):
    rel=module.replace('.','/')+'.lean'
    if rel in frozen:return
    p=LIVE/rel;data=p.read_bytes();clean=inv.without_comments(data.decode())
    lexical=re.sub(r'"(?:\\.|[^"\\])*"','""',clean)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b|trustCompiler|debug\.skipKernelTC',lexical),rel
    for deps in re.findall(r'^import\s+(.+)$',clean,re.M):
        for dep in deps.split():
            if (LIVE/(dep.replace('.','/')+'.lean')).is_file():visit(dep)
    frozen[rel]=data;order.append(dict(module=module,path='lean-statements/'+rel,sha256=sha(p)))
roots=['NLA.Proofs.RE05.GaussianQuadraticCovariance','Reviewed.RE05']
for m in roots:visit(m)
assert len(frozen)==11
decls=[d for path,data in frozen.items()for d in inv.declarations_of(path,data)]
for d in decls:
    module=d['source'].removesuffix('.lean').replace('/','.')
    d['audit_id']=('_private.'+module+'.0.'+d['name']) if d['visibility']=='private' else d['name']
assert len(set(d['audit_id']for d in decls))==len(decls)
owned_paths={str(Path(x['path']).relative_to('lean-statements'))for x in f['new_sources']}
owned=[d for d in decls if d['source']in owned_paths]
assert len(owned)==19 and sum(d['kind']=='theorem'for d in owned)==17 and sum(d['kind']=='def'for d in owned)==2
assert all(d['visibility']=='public'for d in owned)
assert sum(d['visibility']=='private'for d in decls)==4
block=dict(key='quadratic',author='/root',author_freeze=dict(path=str(lock.relative_to(REPO)),sha256=sha(lock)),owned=sorted(owned_paths),roots=roots,source_paths=sorted(frozen),declarations=decls,literal_endpoints=[d['name']for d in owned if d['kind']=='theorem'])
cfg=dict(reviewer='/root/recover_geometry',reviewer_authored_owned_sources=[],source_approval_scope='Only all19 declarations/full bodies in the three root-authored GaussianQuadratic modules. All eight prerequisite sources excluded from independent mathematical source approval; their full named/private kinds and trust closures are mechanically checked.',scope='Exact finite Gaussian quadratic integrability/mean, arbitrary nonsymmetric joint moment, centered covariance, and variance at most twice squared Frobenius norm. No actual-offset variance, Markov, tail probability or full Target claim.',blocks=[block],union=order,declarations=decls,owned_declarations=owned,input_lock=dict(path=str((C/'attained-input-lock.json').relative_to(REPO)),sha256=sha(C/'attained-input-lock.json')),borrowed_helpers=[dict(path=str((C/'independent-regression-review'/n).relative_to(REPO)),sha256=sha(B/n))for n in ['source_inventory.py','literal_type.py','audit-preamble.lean.txt','private-access.lean.txt']],independent_edge_consumer_sha256=sha(B/'integration-quadratic.lean.txt'))
assert cfg['input_lock']['sha256']=='05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d'
(B/'source-lock.json').write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps(dict(passed=True,source_lock_sha256=sha(B/'source-lock.json'),source_modules=len(frozen),closure_names=len(decls),owned_names=len(owned),literal_types=17,private_prerequisite_names=4),indent=2))

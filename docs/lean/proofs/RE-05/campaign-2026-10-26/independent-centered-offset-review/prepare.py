#!/usr/bin/env python3
"""Snapshot immutable centered-offset inputs and generate explicit independent raw-type audit inventory."""
from pathlib import Path
import hashlib,importlib.util,json,re,shutil
B=Path(__file__).resolve().parent;REPO=B.parents[5];LIVE=REPO/'lean-statements';C=B.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
BASE=C/'independent-regression-review'
accepted=json.loads((BASE/'ACCEPTANCE.json').read_text());assert sha(BASE/'ACCEPTANCE.json')=='98c3300cfcd7300b6e7c2b084716ac7accce261a6f7e58ceb53469739073edd2'
for n in ['source_inventory.py','literal_type.py','audit-preamble.lean.txt','private-access.lean.txt']:
 assert sha(BASE/n)==accepted['artifact_hashes'][str((BASE/n).relative_to(REPO))];shutil.copyfile(BASE/n,B/n)
spec=importlib.util.spec_from_file_location('inv',B/'source_inventory.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
F=C/'re05-centered-offset-geometry/SOURCE_FREEZE.json';assert sha(F)=='de22f4cd2054265fb2e2a7e1985f11798fc06a6d8b67803e282f8e6313b4aa52'
f=json.loads(F.read_text());assert len(f['new_sources'])==2
for x in f['new_sources']:assert sha(REPO/x['path'])==x['sha256']
frozen={};order=[]
def visit(module):
 rel=module.replace('.','/')+'.lean'
 if rel in frozen:return
 p=LIVE/rel;data=p.read_bytes();clean=inv.without_comments(data.decode());lexical=re.sub(r'"(?:\\.|[^"\\])*"','""',clean)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide)\b|trustCompiler|debug\.skipKernelTC',lexical),rel
 for deps in re.findall(r'^import\s+(.+)$',clean,re.M):
  for dep in deps.split():
   if (LIVE/(dep.replace('.','/')+'.lean')).is_file():visit(dep)
 frozen[rel]=data;order.append({'module':module,'path':'lean-statements/'+rel,'sha256':sha(p)})
roots=['NLA.Proofs.RE05.OffsetContraction','Reviewed.RE05']
for m in roots:visit(m)
assert len(frozen)==32,len(frozen)
assert not any('Gaussian' in p or 'HighDimProb' in p or '/RE06/' in p for p in frozen)
decls=[d for p,v in frozen.items() for d in inv.declarations_of(p,v)]
for d in decls:d['audit_id']=('_private.'+d['source'].removesuffix('.lean').replace('/','.')+'.0.'+d['name']) if d['visibility']=='private' else d['name']
assert len({d['audit_id'] for d in decls})==len(decls)
owned=[str(Path(x['path']).relative_to('lean-statements')) for x in f['new_sources']]
new=[d for d in decls if d['source'] in owned];assert len(new)==17 and sum(d['kind']=='theorem' for d in new)==16
assert all(d['visibility']=='public' for d in new)
consumer=C/'re05-centered-offset-geometry/Consumer.lean';assert sha(consumer)==f['consumer_sha256']
code=consumer.read_text()+'\nexample : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl\n'
extra=['RE05CenteredOffsetGeometryConsumer.'+n for n in ['actual_rhs_centered_quadratics','actual_raw_variance_charge','actual_width_positive','dependent_zero_family_contraction','empty_rhs_zero']]
for n in extra:code+='\n#audit_named '+ ' '.join(json.dumps(s) for s in [n,'Independent_centered_offset_Consumer','public','theorem'])+'\n'
(B/'integration-centered_offset.lean.txt').write_text(code)
prior=json.loads((C/'independent-one-copy-review/source-lock.json').read_text());protected=prior['protected_RE05_proofs'];protected.update({x['path']:x['sha256'] for x in prior['union'] if str(Path(x['path']).relative_to('lean-statements')) in prior['blocks'][0]['owned']});assert len(protected)==31
cfg={'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':'Two frozen deterministic RE05 actual same-plan centered quadratic rhs, draw/copy-invariant actual quadratic matrices, and residual leverage energy/variance-charge contraction. No Gaussian moment, event probability, complete Target, CI or Comparator claim.',
 'blocks':[{'key':'centered_offset','author':'/root/recover_geometry','author_freeze':{'path':str(F.relative_to(REPO)),'sha256':sha(F)},'owned':owned,'roots':roots,'source_paths':sorted(frozen),'declarations':decls,'literal_endpoints':[d['name'] for d in new if d['kind']=='theorem'],'extra_consumer_theorems':extra,'integration_source':{'path':str(consumer.relative_to(REPO)),'sha256':sha(consumer)}}],
 'union':order,'declarations':decls,'owned_declarations':new,'protected_RE05_proofs':protected,
 'input_lock':{'path':str((C/'attained-input-lock.json').relative_to(REPO)),'sha256':sha(C/'attained-input-lock.json')},
 'helper_reuse_source_acceptance':{'path':str((BASE/'ACCEPTANCE.json').relative_to(REPO)),'sha256':sha(BASE/'ACCEPTANCE.json')},'compiler_flags':['-DautoImplicit=false']}
assert cfg['input_lock']['sha256']=='05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d'
assert not (B/'source-lock.json').exists();(B/'source-lock.json').write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps({'sources':len(order),'closure_names':len(decls),'new_names':len(new),'new_raw_types':16,'source_lock_sha256':sha(B/'source-lock.json')},indent=2))

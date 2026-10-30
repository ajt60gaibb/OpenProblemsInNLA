#!/usr/bin/env python3
"""Snapshot immutable one-copy inputs and generate explicit independent raw-type audit inventory."""
from pathlib import Path
import hashlib,importlib.util,json,re,shutil
B=Path(__file__).resolve().parent;REPO=B.parents[5];LIVE=REPO/'lean-statements';C=B.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
BASE=C/'independent-regression-review'
accepted=json.loads((BASE/'ACCEPTANCE.json').read_text());assert sha(BASE/'ACCEPTANCE.json')=='98c3300cfcd7300b6e7c2b084716ac7accce261a6f7e58ceb53469739073edd2'
for n in ['source_inventory.py','literal_type.py','audit-preamble.lean.txt','private-access.lean.txt']:
 assert sha(BASE/n)==accepted['artifact_hashes'][str((BASE/n).relative_to(REPO))];shutil.copyfile(BASE/n,B/n)
spec=importlib.util.spec_from_file_location('inv',B/'source_inventory.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
F=C/'re05-one-copy-geometry/SOURCE_FREEZE.json';assert sha(F)=='8ebaa3281116cf13c0a945f531eaa250cd28b30689e329c123b428ca2929656c'
f=json.loads(F.read_text());assert len(f['new_sources'])==4
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
roots=['NLA.Proofs.RE05.OneCopyError','Reviewed.RE05']
for m in roots:visit(m)
assert len(frozen)==30,len(frozen)
assert not any('Gaussian' in p or 'HighDimProb' in p or '/RE06/' in p or 'CenteredOffset' in p for p in frozen)
decls=[d for p,v in frozen.items() for d in inv.declarations_of(p,v)]
for d in decls:d['audit_id']=('_private.'+d['source'].removesuffix('.lean').replace('/','.')+'.0.'+d['name']) if d['visibility']=='private' else d['name']
assert len({d['audit_id'] for d in decls})==len(decls)
owned=[str(Path(x['path']).relative_to('lean-statements')) for x in f['new_sources']]
new=[d for d in decls if d['source'] in owned];assert len(new)==19 and sum(d['kind']=='theorem' for d in new)==17
assert all(d['visibility']=='public' for d in new)
consumer=C/'re05-one-copy-geometry/Consumer.lean';assert sha(consumer)==f['consumer_sha256']
code=consumer.read_text()+'\nexample : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl\n'
extra=['RE05OneCopyGeometryConsumer.'+n for n in ['same_original_plan_residual_equation','raw_cauchy_error','optimum_before_all_original_plans','actual_zero_optimum','empty_coefficient_bound']]
for n in extra:code+='\n#audit_named '+ ' '.join(json.dumps(s) for s in [n,'Independent_one_copy_Consumer','public','theorem'])+'\n'
(B/'integration-one_copy.lean.txt').write_text(code)
protected=json.loads((C/'independent-golden-thompson-review/source-lock.json').read_text())['protected_RE05_proofs'];assert len(protected)==27
cfg={'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':'Four frozen deterministic RE05 same-plan residual normal equation, Cauchy coefficient error, actual optimum before all plans, and actual original-output relative squared/zero error under explicit lower and offset events. No event probability, complete Target, CI or Comparator claim.',
 'blocks':[{'key':'one_copy','author':'/root/recover_geometry','author_freeze':{'path':str(F.relative_to(REPO)),'sha256':sha(F)},'owned':owned,'roots':roots,'source_paths':sorted(frozen),'declarations':decls,'literal_endpoints':[d['name'] for d in new if d['kind']=='theorem'],'extra_consumer_theorems':extra,'integration_source':{'path':str(consumer.relative_to(REPO)),'sha256':sha(consumer)}}],
 'union':order,'declarations':decls,'owned_declarations':new,'protected_RE05_proofs':protected,
 'input_lock':{'path':str((C/'attained-input-lock.json').relative_to(REPO)),'sha256':sha(C/'attained-input-lock.json')},
 'helper_reuse_source_acceptance':{'path':str((BASE/'ACCEPTANCE.json').relative_to(REPO)),'sha256':sha(BASE/'ACCEPTANCE.json')},'compiler_flags':['-DautoImplicit=false']}
assert cfg['input_lock']['sha256']=='05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d'
assert not (B/'source-lock.json').exists();(B/'source-lock.json').write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps({'sources':len(order),'closure_names':len(decls),'new_names':len(new),'new_raw_types':17,'source_lock_sha256':sha(B/'source-lock.json')},indent=2))

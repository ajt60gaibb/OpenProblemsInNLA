#!/usr/bin/env python3
"""Prepare separately scoped independent RE05 support consumers and snapshot lock."""
from pathlib import Path
import ast,hashlib,importlib.util,json,re,shutil
B=Path(__file__).resolve().parent;REPO=B.parents[5];C=B.parent;LIVE=REPO/'lean-statements'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/independent-full-target-review'
assert sha(old/'replay-corrected.py')=='3726e2202e3c8b73096564b8bfd343fad9e66c84f8c431e91ee8b6cb7aef1b67'
assert not (B/'source-lock.json').exists()
shutil.copyfile(old/'source_inventory.py',B/'source_inventory.py')
spec=importlib.util.spec_from_file_location('inventory',B/'source_inventory.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
text=(old/'replay-corrected.py').read_text();tree=ast.parse(text)
literal=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='literal')
(B/'literal_type.py').write_text('import re\n'+ast.get_source_segment(text,literal)+'\n')
private_literal=(B/'literal_type.py').read_text()
private_literal=private_literal.replace('(?:theorem|lemma)\\s+', '(?:(?:private|local|protected)\\s+)?(?:theorem|lemma)\\s+')
private_literal=private_literal.replace("code=(f'namespace", "application=d['audit_id'] if d['visibility']=='private' else name\n code=(f'namespace")
private_literal=private_literal.replace('exact @{name} ', 'exact @{application} ')
private_literal=private_literal.replace("'application_arguments':args", "'application_arguments':args,'application_name':application,'visibility':d['visibility']")
(B/'literal_type.py').write_text(private_literal)

preamble=ast.literal_eval(next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='preamble' for t in n.targets)).value)
(B/'audit-preamble.lean.txt').write_text(preamble)
table=[('gaussian_moments','/root','GAUSSIAN_MOMENTS_FREEZE_V2_2026-10-26.json',['NLA.Proofs.RE05.GaussianMoments'],'GaussianMomentsConsumerV2.lean.txt')]
expected={'GaussianMoments':'90ccd03775e4d41ce8bd2f923bd9afd09e1fff9374f307d783ce79805ae37fc3'}
freeze_hashes={'gaussian_moments':'d8659205efd0466f9cb2cd7516dd1526d0821a22542d14e09aeba2263bed5912'}
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
    frozen[rel]=data;order.append({'module':module,'path':'lean-statements/'+rel,'sha256':sha(p)})
blocks=[]
for key,author,lock,roots,consumer in table:
    assert sha(C/lock)==freeze_hashes[key]
    d=json.loads((C/lock).read_text())
    for s in d['new_sources']:
        assert sha(REPO/s['path'])==s['sha256']==expected[Path(s['path']).stem]
    roots=roots+['Reviewed.RE05']
    for module in roots:visit(module)
    owned=[str(Path(s['path']).relative_to('lean-statements')) for s in d['new_sources']]
    (B/('integration-'+key+'.lean.txt')).write_bytes((C/consumer).read_bytes())
    assert sha(C/consumer)==d['consumer_sha256']
    blocks.append({'key':key,'author':author,'author_freeze':{'path':str((C/lock).relative_to(REPO)),'sha256':sha(C/lock)},'owned':owned,'roots':roots,'integration_source':{'path':str((C/consumer).relative_to(REPO)),'sha256':sha(C/consumer)}})
assert len(frozen)==7 and all('GaussianWick' not in p for p in frozen)
decls=[d for path,data in frozen.items() for d in inv.declarations_of(path,data)]
for d in decls:
    module=d['source'].removesuffix('.lean').replace('/','.')
    d['audit_id']=('_private.'+module+'.0.'+d['name']) if d['visibility']=='private' else d['name']
assert len(set(d['audit_id'] for d in decls))==len(decls)
owned=[d for d in decls if d['source'] in {p for b in blocks for p in b['owned']}]
assert len(owned)==11 and all(d['kind']=='theorem' for d in owned)
assert sum(d['visibility']=='private' for d in owned)==4
for b in blocks:
    needed=set()
    def closure(m):
        path=m.replace('.','/')+'.lean'
        if path in needed:return
        needed.add(path)
        for dep in re.findall(r'^import\s+(\S+)\s*$',inv.without_comments(frozen[path].decode()),re.M):
            if dep.replace('.','/')+'.lean' in frozen:closure(dep)
    for m in b['roots']:closure(m)
    b['source_paths']=sorted(needed);b['declarations']=[d for d in decls if d['source'] in needed]
    b['literal_endpoints']=[d['name'] for d in owned if d['source'] in b['owned'] and d['kind'] in {'theorem','lemma'}]
config={'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':'One frozen RE05 standard Gaussian scalar moments, all powers integrability and finite-product monomial Fubini module, including all four private calculus helpers; no Wick, concentration, success probability, OriginalClaim, SourceCompanion, full Target, CI or Comparator acceptance.',
 'blocks':blocks,'union':order,'declarations':decls,'owned_declarations':owned,
 'input_lock':{'path':str((C/'attained-input-lock.json').relative_to(REPO)),'sha256':sha(C/'attained-input-lock.json')},
 'borrowed_inventory_helper':{'path':str((old/'source_inventory.py').relative_to(REPO)),'sha256':sha(old/'source_inventory.py')},
 'borrowed_literal_and_macro_driver':{'path':str((old/'replay-corrected.py').relative_to(REPO)),'sha256':sha(old/'replay-corrected.py')}}
assert config['input_lock']['sha256']=='05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d'
(B/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
print(json.dumps({'passed':True,'fresh_union':7,'owned_modules':1,'owned_names':11,'owned_theorems':11,'closure_names':len(decls),'private':sum(x['visibility']=='private' for x in decls),'source_lock_sha256':sha(B/'source-lock.json')},indent=2))

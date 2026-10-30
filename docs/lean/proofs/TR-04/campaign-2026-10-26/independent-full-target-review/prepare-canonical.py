#!/usr/bin/env python3
"""Bind unchanged shared author scopes to the complete frozen canonical package."""
from pathlib import Path
import hashlib,json,subprocess,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(BASE/'prepare.py')],check=True)
c=json.loads((BASE/'source-lock.json').read_text())
assert sha(BASE/'source-lock.json')==sha(BASE/'shared-source-lock-precanonical.json')
freeze=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'
assert sha(freeze)=='8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb'
f=json.loads(freeze.read_text());PROJECT=REPO/f['project']
assert len(f['inputs'])==205 and sum(n.endswith('.lean') for n in f['inputs'])==190
assert all((PROJECT/n).is_file() and not (PROJECT/n).is_symlink() and sha(PROJECT/n)==h for n,h in f['inputs'].items())
shared={r['path'].removeprefix('lean-statements/'):r for r in c['union']}
assert len(shared)==184
for n,r in shared.items():assert sha(PROJECT/n)==r['sha256']==sha(REPO/r['path'])
sys.path.insert(0,str(BASE));from source_inventory import declarations_of
names=[n for n in f['inputs'] if n.endswith('.lean') and n not in {'Challenge.lean','FullChallenge.lean'}]
assert len(names)==188
records=[{'path':'lean-statements/'+n,'sha256':f['inputs'][n],'bytes':(PROJECT/n).stat().st_size} for n in names]
owned=[r for r in records if r['path'].removeprefix('lean-statements/') in {'Solution.lean','FullSolution.lean','Identity.lean','Check.lean'}]
decls=[d for r in records for d in declarations_of(r['path'].removeprefix('lean-statements/'),(PROJECT/r['path'].removeprefix('lean-statements/')).read_bytes())]
for d in decls:
    module=d['source'].removesuffix('.lean').replace('/','.')
    d['audit_id']='_private.'+module+'.0.'+d['name'] if d['visibility']=='private' else d['name']
op={r['path'].removeprefix('lean-statements/') for r in owned};od=[d for d in decls if d['source'] in op]
assert len(od)==4 and all(d['kind'] in {'theorem','lemma'} for d in od)
c['blocks'].append({'key':'canonical_solution','author':'/root (wrapper); legacy source authors retained',
 'author_lock_path':str(freeze.relative_to(REPO)),'author_lock_sha256':sha(freeze),
 'records':records,'owned':owned,'declarations':decls,'owned_declarations':sorted(d['audit_id'] for d in od),
 'owned_source_names':sorted(d['name'] for d in od),
 'author_selected_public_declarations':['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target','NLA.TR04.target_eq_reviewed'],
 'roots':['FullSolution','Identity','Check'],'literal_endpoints':[d['name'] for d in od],
 'author_record_count':0,'reviewer_extra_sources':[]})
c.update(canonical_project=str(PROJECT.relative_to(REPO)),canonical_freeze={'path':str(freeze.relative_to(REPO)),'sha256':sha(freeze)},
 package_inputs=f['inputs'],canonical_Lean_count=190,shared_copy_count=184,proof_module_count=179,
 canonical_comparison_sources=['Challenge.lean','FullChallenge.lean'],shared_sources=list(shared.values()))
c['union']=[{'path':'lean-statements/'+n,'sha256':h,'bytes':(PROJECT/n).stat().st_size} for n,h in f['inputs'].items() if n.endswith('.lean')]
c['scope']='One independent fresh canonical190-source audit for six separately frozen remaining author scopes and canonical proof/identity exports, with188 proof-source declaration inventories and two separate comparison-context modules. Includes all Geo11 and the exact frozen Reviewed mirror. Mathematical complete Target/kernel acceptance and intentional Challenge rejection are separate from authoritative Linux/Comparator/publication acceptance.'
(BASE/'source-lock.json').write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps({'canonical_inputs':205,'Lean_sources':190,'shared_exact_copies':184,'scoped_consumers':7,'source_lock_sha256':sha(BASE/'source-lock.json')}))

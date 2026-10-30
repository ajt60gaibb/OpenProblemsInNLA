#!/usr/bin/env python3
"""Key private audits by exact actual kernel identity, not source-user spelling."""
from pathlib import Path
import hashlib,json
BASE=Path(__file__).resolve().parent
prior=BASE.parent/'independent-initial-family-child-review/replay.py'
s=prior.read_text()
def replace(old,new):
    global s
    assert s.count(old)==1,(old,s.count(old))
    s=s.replace(old,new)
replace('Independent first-family and child initialization fresh kernel replay','Independent actual reverse/final/child-SVD fresh kernel replay')
replace("assert all(d['visibility'] in {'public','private','local'} for d in all_declarations)","""assert all(d['visibility'] in {'public','private','local'} for d in all_declarations)
def audit_identity(d):
 module=d['source'].removesuffix('.lean').replace('/','.')
 return '_private.'+module+'.0.'+d['name'] if d['visibility']=='private' else d['name']
for d in all_declarations:d['audit_id']=audit_identity(d)
for b in config['blocks']:
 sources={r['path'].removeprefix('lean-statements/') for r in b['records']}
 actual=[d for d in all_declarations if d['source'] in sources]
 assert sorted(actual,key=lambda d:d['audit_id'])==sorted(b['declarations'],key=lambda d:d['audit_id']),('Frozen declaration inventory differs',b['key'])""")
replace("p=config['private_name_map'][d['name']];assert p['source']==d['source'] and p['line']==d['line'] and p['kind']==d['kind']","p=config['private_name_map'][d['audit_id']];assert p['source_name']==d['name'] and p['source']==d['source'] and p['line']==d['line'] and p['kind']==d['kind'] and p['actual_kernel_name']==d['audit_id']")
replace("assert len({d['name'] for d in all_declarations})==len(all_declarations)","assert len({d['audit_id'] for d in all_declarations})==len(all_declarations)\nassert len({d['name'] for d in all_declarations if d['visibility']!='private'})==sum(d['visibility']!='private' for d in all_declarations)")
replace("lookup={d['name']:d for d in all_declarations}","lookup={d['name']:d for d in all_declarations if d['visibility']=='public'}")
replace('logInfo m!"AUDITED_KIND {user.getString} {expected.getString}"','logInfo m!"AUDITED_KIND {decl.toString} {expected.getString}"')
replace('logInfo m!"AUDITED_AXIOMS {user.getString} [{body}]"','logInfo m!"AUDITED_AXIOMS {decl.toString} [{body}]"')
replace("expected_names=[d['name'] for d in b['declarations']]","expected_names=[d['audit_id'] for d in b['declarations']]")
replace("config['private_name_map'][d['name']]['actual_kernel_name'] if d['visibility']=='private' else d['name']","d['audit_id']")
replace("sum(d['name'] in b['owned_declarations'] and d['kind'] in {'theorem','lemma'} for d in b['declarations'])","sum(d['audit_id'] in b['owned_declarations'] and d['kind'] in {'theorem','lemma'} for d in b['declarations'])")
(BASE/'replay.py').write_text(s)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(BASE/'driver-provenance.json').write_text(json.dumps({'prior_driver':str(prior),'prior_sha256':sha(prior),'driver_sha256':sha(BASE/'replay.py'),
 'changes':['Use exact module-qualified Lean kernel identities for all private map, counter and axiom-report keys; source-user spelling remains separately recorded.',
 'Replace duplicate-source-user rejection with strict duplicate-actual-identity rejection and retain strict duplicate-public/local-name rejection.',
 'Require each complete block declaration inventory to equal independently re-extracted source declarations, including exact identity, source, line, kind and visibility.',
 'Literal consumers use unique public source names; complete binder/type bytes, proof applications and all pre-existing trust/lexical/runtime/pin/original/fresh-object guards are unchanged.'],
 'trust_guards_removed':False,'proof_source_changes':False},indent=2)+'\n')

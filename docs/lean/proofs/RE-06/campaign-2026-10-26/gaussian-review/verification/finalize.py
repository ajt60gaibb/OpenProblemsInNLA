#!/usr/bin/env python3
"""Combine actual source/audit results after both reproductions finish."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();d=a.output
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((d/'SOURCE_RESULT.json').read_text());t=json.loads((d/'AUDIT_RESULT.json').read_text())
assert s['pass'] and t['pass'] and t['source_result_sha256']==sha((d/'SOURCE_RESULT.json').read_bytes())
checks=s['checks']+t['checks'];commands=s['commands']+t['commands'];assert all(c['pass'] for c in checks) and all(c['exit_code']==c['expected_exit'] for c in commands)
freeze=json.loads((d/'SOURCE_FREEZE.json').read_text());mods={x[len('lean-statements/'):-5].replace('/','.') for x in freeze['files']};new=[e for e in s['declarations'] if e['module'] in mods]
warnings=[]
for c in s['commands']:
 f=d/'logs'/(c['module']+'.log');lines=[x for x in f.read_text().splitlines() if 'warning:' in x]
 if lines:warnings.append({'module':c['module'],'log_sha256':sha(f.read_bytes()),'diagnostic_headers':lines})
r={'pass':True,'reviewer':'/root/verification','non_author':True,'source_commit':s['source_commit'],'binding_metadata_commit':s['binding_metadata_commit'],'scope':'16 frozen Gaussian support modules, conditional actual-law warm tail; no unconditional public success/Target/CI approval','checks':checks,'commands':commands,'fresh_mathematical_closure_sources':23,'additional_fresh_statement_identity_sources':3,'new_frozen_modules':16,'new_support_theorems':sum(e['kind']=='theorem' for e in new),'new_helper_definitions':sum(e['kind']=='definition' for e in new),'all_source_theorems':sum(e['kind']=='theorem' for e in s['declarations']),'all_source_definitions':sum(e['kind']=='definition' for e in s['declarations']),'own_consumers':t['own_consumers'],'warnings':warnings,'source_records':s['source_records'],'private_build':s['private_build'],'compiler_version':s['compiler_version'],'compiler_sha256':s['compiler_sha256'],'public_success_approved':False,'whole_Target_approved':False,'new_Linux_execution':False,'Comparator_execution':False,'bindings':{f:sha((d/f).read_bytes()) for f in ['SOURCE_RESULT.json','AUDIT_RESULT.json','SOURCE_FREEZE.json','CLOSED_SOURCE_BINDING.json','BINDING_PROVENANCE.json','reproduce_sources.py','reproduce_audit.py','consumers.lean.txt','guards.txt','finalize.py']}}
(d/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':True,'checks':len(checks),'actual_commands':len(commands),'new_support_theorems':r['new_support_theorems']}))

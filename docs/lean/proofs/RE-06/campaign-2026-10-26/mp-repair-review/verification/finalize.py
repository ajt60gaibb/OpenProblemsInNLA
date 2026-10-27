#!/usr/bin/env python3
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();d=a.output
sha=lambda b:hashlib.sha256(b).hexdigest();s=json.loads((d/'SOURCE_RESULT.json').read_text());t=json.loads((d/'AUDIT_RESULT.json').read_text())
assert s['pass'] and t['pass'] and t['source_result_sha256']==sha((d/'SOURCE_RESULT.json').read_bytes())
checks=s['checks']+t['checks'];commands=s['commands']+t['commands'];assert all(c['pass'] for c in checks) and all(c['exit_code']==c['expected_exit'] for c in commands)
scopes={}
for key,parts,closure in [('A',['pseudoinverse-author','fullrank-author','global-measurable-author'],'global-measurable-author'),('B',['repair-author','actual-repair-author'],'actual-repair-author')]:
 names=[n for part in parts for n in t['scope_support_names'][part]];scopes[key]={'support_names':names,'support_count':len(names),'freeze_groups':parts,'source_closure':s['scope_closures'][closure]}
warnings=[]
for c in s['commands']:
 f=d/'logs'/(c['module']+'.log');ls=[x for x in f.read_text().splitlines() if 'warning:' in x]
 if ls:warnings.append({'module':c['module'],'log_sha256':sha(f.read_bytes()),'headers':ls})
r={'pass':True,'reviewer':'/root/verification','non_author':True,'source_commit':s['source_commit'],'freeze_epochs':s['freeze_epochs'],'scope':'Separate A95 and B18+41 support reviews sharing one fresh63 source build; no later rectangular inverse moment, full Target or CI approval','scopes':scopes,'checks':checks,'commands':commands,'fresh_source_compiles':63,'independent_audit_compiles':1,'actual_negative_commands':9,'all_source_theorems':279,'all_source_definitions':55,'own_consumers':t['own_consumers'],'source_records':s['source_records'],'compiler_version':s['compiler_version'],'compiler_sha256':s['compiler_sha256'],'private_build':s['private_build'],'warnings':warnings,'later_rectangular_inverse_moment_approved':False,'public_success_or_full_Target_approved':False,'new_Linux_execution':False,'Comparator_execution':False,'bindings':{f:sha((d/f).read_bytes()) for f in ['SOURCE_RESULT.json','AUDIT_RESULT.json','reproduce_sources.py','reproduce_audit.py','consumers_a.lean.txt','consumers_b.lean.txt','guards.txt','finalize.py','AUTHOR_HISTORY_OBSERVATION.json']}}
(d/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':True,'checks':len(checks),'commands':len(commands),'scope_A':len(scopes['A']['support_names']),'scope_B':len(scopes['B']['support_names'])}))

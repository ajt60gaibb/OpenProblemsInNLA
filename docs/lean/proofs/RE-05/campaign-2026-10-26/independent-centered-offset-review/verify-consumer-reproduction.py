#!/usr/bin/env python3
"""Regenerate corrected consumer bytes without executing any Lean command."""
from pathlib import Path
import argparse,ast,hashlib,json,sys
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--lean-bin',required=True);p.add_argument('--package-cache',required=True);p.add_argument('--result-dir',default='run-attempt-1');a=p.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(B/'replay.py')=='c946ea289192c5eae3108eb037df35131d20afd3091215b10c59a86eaee929fc'
tree=ast.parse((B/'replay.py').read_text());prefix=[]
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='OUT' for t in node.targets):break
 prefix.append(node)
else:raise AssertionError('No exact pre-execution boundary')
assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'run','check_output','write_bytes','write_text','mkdir'} for x in prefix for n in ast.walk(x))
original=sys.argv;sys.argv=[str(B/'replay.py'),'--lean-bin',a.lean_bin,'--package-cache',a.package_cache]
namespace={'__file__':str(B/'replay.py'),'__name__':'independent_reproduction'}
try:exec(compile(ast.Module(body=prefix,type_ignores=[]),str(B/'replay.py'),'exec'),namespace)
finally:sys.argv=original
r=json.loads((B/a.result_dir/'result.json').read_text());generated=namespace['consumers'];assert len(generated)==4
for name,data in generated.items():assert hashlib.sha256(data).hexdigest()==r['consumer_sha256'][name]==sha(B/a.result_dir/'sources'/name)
report={'passed':True,'compiler_commands':0,'executed_driver_sha256':sha(B/'replay.py'),'helper_hashes':r['helper_sha256'],'consumer_sha256':r['consumer_sha256'],'all4_consumer_bytes_reproduced_exactly':True,'snapshot_source_count':len(namespace['frozen']),'AST_boundary':'Before OUT assignment, source snapshot/build/pins/subprocess code excluded'}
(B/'CONSUMER_REPRODUCTION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'compiler_commands':0,'consumers':4,'report_sha256':sha(B/'CONSUMER_REPRODUCTION.json')},indent=2))

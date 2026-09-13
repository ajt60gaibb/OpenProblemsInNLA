"""Inspect already completed standalone logs with the final audit's exact assertions.

This does not rerun the Linux tools and does not approve the mathematical project.
"""
from pathlib import Path
import ast, copy, hashlib, json, re

out=Path(__file__).resolve().parent
source=out/'audit_checks.py'
digest=hashlib.sha256(source.read_bytes()).hexdigest()
assert digest==json.loads((out/'audit-script-provenance.json').read_text())['derived_sha256']
tree=ast.parse(source.read_text())
nodes=[node for node in tree.body if isinstance(node,ast.For)
       and isinstance(node.target,ast.Tuple)
       and [x.id for x in node.target.elts]==['label','directory']]
assert len(nodes)==1
node=copy.deepcopy(nodes[0])
node.iter=ast.parse("[('checker-controls', S)]",mode='eval').body
ast.fix_missing_locations(node)
directories=list((out/'artifacts/lean-checker-controls').glob('selftest-*'))
assert len(directories)==1
namespace={'S':directories[0],'re':re,'controls':{}}
exec(compile(ast.Module(body=[node],type_ignores=[]),'same_final_audit_control_assertions','exec'),namespace)
files={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
       for p in directories[0].iterdir() if p.is_file()}
record={'result':'PASS completed standalone control logs only',
        'audit_source_sha256':digest,'exact_final_control_assertions_reused':True,
        'observed':namespace['controls'],'raw_files_sha256':files,
        'project_Comparator_or_full_run_verdict':False,
        'Linux_executions_repeated_by_this_script':False}
(out/'standalone-control-inspection.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))

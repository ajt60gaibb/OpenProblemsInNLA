#!/usr/bin/env python3
"""Explicit runtime launcher for the byte-exact seven-source historical driver.

The historical driver does not acquire new CLI flags. This distinct launcher
validates its hash and copied inputs, then changes only LEAN, CACHE and the
temporary-object parent in an in-memory AST. It retains the original compiler
hash/version and every source/input/consumer/trust check. --check-only verifies
identical generated consumers without building project sources.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,ast,hashlib,json,sys,tempfile
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean-bin',type=Path,required=True)
p.add_argument('--package-cache',type=Path,required=True)
p.add_argument('--object-parent',type=Path,default=Path(tempfile.gettempdir()))
p.add_argument('--run-dir',default='portable-run-1')
p.add_argument('--check-only',action='store_true')
p.add_argument('--report',type=Path)
a=p.parse_args()
assert Path(a.run_dir).name==a.run_dir and a.run_dir not in {'.','..'}
lean=a.lean_bin.resolve();lean=lean/'lean' if lean.is_dir() else lean
cache=a.package_cache.resolve();object_parent=a.object_parent.resolve()
assert lean.is_file() and cache.is_dir() and object_parent.is_dir()
kit=json.loads((HERE/'KIT_INPUTS.json').read_text())
for rec in kit['copied_input_files']:assert sha(HERE/rec['name'])==rec['sha256']
assert sha(lean)==kit['recorded_compiler_binary_sha256']
original=HERE/'historical-driver.py';assert sha(original)==kit['original_driver_sha256']
tree=ast.parse(original.read_text(),filename=str(original));before=ast.parse(original.read_text())
changed={'LEAN':0,'CACHE':0,'temporary_object_parent':0}
def path_expr(s):return ast.Call(func=ast.Name(id='Path',ctx=ast.Load()),args=[ast.Constant(str(s))],keywords=[])
class RuntimePaths(ast.NodeTransformer):
    def visit_Assign(self,node):
        if len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in {'LEAN','CACHE'}:
            key=node.targets[0].id;changed[key]+=1
            node.value=path_expr(lean if key=='LEAN' else cache)
        return self.generic_visit(node)
    def visit_Call(self,node):
        if isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Name) and node.func.value.id=='tempfile' and node.func.attr=='TemporaryDirectory':
            dirs=[kw for kw in node.keywords if kw.arg=='dir'];assert len(dirs)==1
            dirs[0].value=path_expr(object_parent);changed['temporary_object_parent']+=1
        return self.generic_visit(node)
tree=ast.fix_missing_locations(RuntimePaths().visit(tree))
assert changed=={'LEAN':1,'CACHE':1,'temporary_object_parent':1}
functions=lambda t:{n.name:ast.dump(n,include_attributes=False) for n in t.body if isinstance(n,ast.FunctionDef)}
assert functions(before)==functions(tree)
original_result=json.loads((HERE/'accepted-original-result.json').read_text())
assert original_result['passed'] and original_result['driver_sha256']==sha(original)
sys.path.insert(0,str(HERE));sys.argv=[str(original),'--run-dir',a.run_dir]
namespace={'__name__':'__main__','__file__':str(original)}
new_kernel_commands=0;exit_code=0
if a.check_only:
    cut=next(i for i,n in enumerate(tree.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='OUT' for t in n.targets))
    prefix=ast.Module(body=tree.body[:cut],type_ignores=[])
    exec(compile(ast.fix_missing_locations(prefix),str(original),'exec'),namespace)
    generated={n:hashlib.sha256(data).hexdigest() for n,data in namespace['consumers'].items()}
    assert generated==original_result['consumer_sha256']
    assert sha(HERE/'source-lock.json')==original_result['source_lock_sha256']
else:
    assert not (HERE/a.run_dir).exists()
    try:exec(compile(tree,str(original),'exec'),namespace)
    except SystemExit as e:exit_code=int(e.code or 0)
    generated={n:hashlib.sha256(data).hexdigest() for n,data in namespace['consumers'].items()}
    assert generated==original_result['consumer_sha256']
    actual=json.loads((HERE/a.run_dir/'result.json').read_text())
    new_kernel_commands=len(actual['commands'])
report={'passed':exit_code==0,'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'type':'separate_explicit_runtime_launcher','launcher_sha256':sha(Path(__file__)),
 'original_driver_sha256':sha(original),'original_driver_bytes_changed':False,
 'historical_driver_supports_explicit_runtime_flags':False,'AST_runtime_only_substitutions':changed,
 'all_original_function_ASTs_identical':True,'all_generated_consumer_bytes_identical':True,
 'generated_consumer_sha256':generated,'source_lock_sha256':sha(HERE/'source-lock.json'),
 'copied_inputs_sha256':sha(HERE/'KIT_INPUTS.json'),'check_only':a.check_only,
 'new_kernel_commands':new_kernel_commands,'lean':str(lean),'package_cache':str(cache),
 'temporary_object_parent':str(object_parent),'recorded_compiler_hash_guard_preserved':True,
 'runtime_scope':'Explicit filesystem paths for the exact recorded official Darwin compiler SHA and pinned dependency cache; this does not silently accept a different platform binary.',
 'proof_source_or_trust_guard_changes':False,'new_support_acceptance_claimed_by_check_only':False}
output=a.report.resolve() if a.report else HERE/(a.run_dir+'-launcher.json')
assert not output.exists();output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':report['passed'],'check_only':a.check_only,'new_kernel_commands':new_kernel_commands,'report_sha256':sha(output)},indent=2))
raise SystemExit(exit_code)

#!/usr/bin/env python3
"""Validate checker adaptation without fabricating or auditing a CI artifact."""
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[5]
OLD=REPO/'docs/lean/proofs/PF-05/verification/check-linux-artifact.py'
NEW=REPO/'docs/lean/proofs/TR-06/verification/check-linux-artifact.py'
old=ast.parse(OLD.read_text());new=ast.parse(NEW.read_text())
def literal_checks(tree):
 return [n.args[0].value for n in ast.walk(tree)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='check'and isinstance(n.args[0],ast.Constant)]
def assignment(tree,name):
 return next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id==name for t in n.targets))
old_names=literal_checks(old);new_names=literal_checks(new)
rename={'github-PF05-job-success':'github-TR06-job-success','full-target-only-without-holes':'full-target-and-ten-published-exports-without-holes','exact-reviewed-46-Lean-input-set':'exact-reviewed-144-Lean-input-set'}
expected_inherited=[rename.get(n,n)for n in old_names]
assert len(old_names)==28 and len(new_names)==32
assert set(expected_inherited)<=set(new_names)
extra=sorted(set(new_names)-set(expected_inherited));assert len(extra)==4
assert ast.literal_eval(assignment(old,'markers'))==ast.literal_eval(assignment(new,'markers'))
# Two project-set controls plus eleven unchanged actual log-marker controls.
assert len(old_names)+2+len(ast.literal_eval(assignment(old,'markers')))==41
assert len(new_names)+2+len(ast.literal_eval(assignment(new,'markers')))==45
for tree in [old,new]:
 dynamic=[ast.unparse(n.args[0])for n in ast.walk(tree)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='check'and not isinstance(n.args[0],ast.Constant)]
 assert set(dynamic)=={"'exact-project-file-set:' + label","'actual-log-markers:' + name"}
parser=next(n for n in new.body if isinstance(n,ast.FunctionDef)and n.name=='parse_axiom_records')
env={'re':re};exec(compile(ast.Module(body=[parser],type_ignores=[]),'<pure checker parser>','exec'),env)
parse=env['parse_axiom_records']
config=json.loads((REPO/'tensor-computations/TR-06/lean/comparator.json').read_text())
targets=config['theorem_names'];axioms=['propext','Classical.choice','Quot.sound']
check=next(n for n in ast.walk(new)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='check'and isinstance(n.args[0],ast.Constant)and n.args[0].value=='actual-export-standard-axioms')
predicate=compile(ast.Expression(check.args[1]),'<actual checker axiom predicate>','eval')
def accepts(text):return eval(predicate,{'axiom_records':parse(text),'TARGETS':targets,'STANDARD_AXIOMS':axioms})
valid='\n'.join("'"+n+"' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"for n in targets)
tests=[('all11-whitespace-wrapped-allowed',accepts(valid)),
       ('missing-one-export-rejected',not accepts(valid[:valid.rfind("'NLA.TR06.target'")])),
       ('duplicate-export-rejected',not accepts(valid+'\n'+valid.split("\n")[0]+' Classical.choice, Quot.sound]')),
       ('sorryAx-rejected',not accepts(valid.replace('Quot.sound','Quot.sound, sorryAx',1))),
       ('unexpected-export-record-rejected',not accepts(valid+"\n'Other.target' depends on axioms: [propext, Classical.choice, Quot.sound]"))]
local=REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/verification/canonical-144-review-2026-10-23/Solution.lean.log'
tests.append(('actual-local-macOS-eleven-record-format',accepts(local.read_text())))
assert all(value for _,value in tests),tests
# Check all eleven generated actual guards. This is a local generator test only.
harness=ast.parse((REPO/'tools/lean/harness.py').read_text())
generator=next(n for n in harness.body if isinstance(n,ast.FunctionDef)and n.name=='proof_trust_source')
g={'MODULE':re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"),'HarnessError':RuntimeError}
exec(compile(ast.Module(body=[generator],type_ignores=[]),'<local proof trust source generator>','exec'),g)
audit=g['proof_trust_source'](config)
consumer_check=next(n for n in ast.walk(new)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='check'and isinstance(n.args[0],ast.Constant)and n.args[0].value=='consumer-theorem-kind-and-kernel')
consumer_pred=compile(ast.Expression(consumer_check.args[1]),'<actual consumer guard predicate>','eval')
assert eval(consumer_pred,{'audit':audit,'TARGETS':targets})
for name in targets:
 for prefix in ['#assert_proof_constant ','#assert_trust kernel ']:
  assert not eval(consumer_pred,{'audit':audit.replace(prefix+name+'\n',''),'TARGETS':targets}),name
compile(NEW.read_text(),str(NEW),'exec')
help_result=subprocess.run([sys.executable,str(NEW),'--help'],capture_output=True,text=True)
assert help_result.returncode==0
(HERE/'cli-help.txt').write_text(help_result.stdout+help_result.stderr)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'validation_status':'PASS','scope':'Checker syntax, all inherited control names/markers, pure axiom parser and generated-consumer predicate tests only. No actual TR06 CI artifact audit was executed or claimed.','actual_linux_artifact_audit_run':False,'PF05_checker_sha256':sha(OLD),'TR06_checker_sha256':sha(NEW),'inherited_controls':41,'additional_controls':4,'total_controls':45,'inherited_literal_controls':expected_inherited,'additional_literal_controls':extra,'axiom_parser_checks':[{'name':n,'passed':v}for n,v in tests],'all11-generated-proof-kind-and-kernel-guards_checked':True,'missing_guard_mutations_rejected':22,'local_log_format_test_source':str(local.relative_to(REPO)),'local_log_sha256':sha(local),'CLI_help_exit_code':0,'expected_counts':ast.literal_eval(assignment(new,'EXPECTED_COUNTS'))}
(HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k]for k in ['validation_status','actual_linux_artifact_audit_run','inherited_controls','additional_controls','total_controls','TR06_checker_sha256']},indent=2))

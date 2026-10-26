#!/usr/bin/env python3
"""Keep the original execution immutable; correct only future aggregation."""
from pathlib import Path
import ast,hashlib,json
B=Path(__file__).resolve().parent
p=B/'replay-attempt-1.py';s=p.read_text()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(p)=='4b1c9044d7cdd0e75033e58008ff7f6facbfee44cdb5b33d1a54e5b30d287718'
old=""" sorted(n for n,_ in legacy_axioms)==sorted(legacy_expected) and
 sorted(n for n,_ in legacy_kinds)==sorted(legacy_expected+['NLA.TR04.target']) and
 all(set(a.strip() for a in body.split(',') if a.strip())<=ALLOWED for _,body in legacy_axioms) and
 'depends on sorry or unrecognized axioms' in neglog and 'sorryAx' in neglog)"""
new=""" sorted(n for n,_ in legacy_axioms)==sorted(legacy_expected+['NLA.TR04.target']) and
 sorted(n for n,_ in legacy_kinds)==sorted(legacy_expected+['NLA.TR04.target']) and
 all(set(a.strip() for a in body.split(',') if a.strip())==(ALLOWED|{'sorryAx'}) if name=='NLA.TR04.target' else
     set(a.strip() for a in body.split(',') if a.strip())<=ALLOWED for name,body in legacy_axioms) and
 sorted(re.findall(r'AUDITED_ACTUAL (\\S+) (\\S+) (\\S+)',neglog))==sorted((n,n,'public') for n in legacy_expected+['NLA.TR04.target']) and
 neglog.count('error:')==1 and
 "error: #assert_trust: 'NLA.TR04.target' depends on sorry or unrecognized axioms" in neglog and
 'sorryAx: sorryAx' in neglog)"""
assert s.count(old)==1
corrected=s.replace(old,new)
# Every parsed Lean consumer generator, inventory check and kernel-auditor
# preamble remains byte-identical; this is solely Python postprocessing.
def core(text):
    tree=ast.parse(text)
    functions={n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,ast.FunctionDef)}
    preamble=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='preamble' for t in n.targets))
    return functions,preamble
assert core(s)==core(corrected)
raw=json.loads((B/'run-attempt-1/result.json').read_text())
neg=next(v for v in raw['commands'] if v['source']=='Independent_Challenge_Negative.lean')
neglog=(B/'run-attempt-1'/neg['log']).read_text()
import re
env={'neg':neg,'neglog':neglog,'legacy_expected':[d['name'] for d in raw['challenge_negative_control']['original_legacy_declarations']],
 'legacy_axioms':re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',neglog),
 'legacy_kinds':re.findall(r'AUDITED_KIND (\S+) (\S+)',neglog),'ALLOWED':{'propext','Classical.choice','Quot.sound'},'re':re}
tree=ast.parse(corrected)
expression=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='negative_passed' for t in n.targets))
assert eval(compile(ast.Expression(expression),'<corrected-negative-parser>','eval'),env) is True
(B/'replay-corrected.py').write_text(corrected)
out={'passed':True,'original_driver_sha256':sha(p),'corrected_future_driver_sha256':sha(B/'replay-corrected.py'),
 'change':'Only terminal negative-control parsing: count the continued Target axiom record, require exactly standard3+sorryAx there and permitted axioms on every legacy record, exact actual names and one exact expected trust error/exit1.',
 'all_Lean_consumer_generators_kernel_auditor_and_source_guard_functions_identical':True,
 'future_negative_parser_passes_exact_retained_intended_rejection':True,
 'historical_driver_result_logs_or_consumers_rewritten':False,'new_Lean_commands_executed':0,'proof_source_changes':False}
(B/'canonical-replay-aggregation-correction.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

#!/usr/bin/env python3
"""Read-only exact PF05 pre-Solution boundary checks. Run before Solution creation."""
import argparse,hashlib,json,re,subprocess,tomllib
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path.cwd());args=ap.parse_args()
root=args.root.resolve();package=root/'nonnegative-and-positive-factorizations/PF-05/lean'
out=root/'docs/lean/proofs/PF-05/campaign-2026-10-18/canonical-boundary-review-1-evidence';out.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest();checks={};records={}
def check(name,value): checks[name]=bool(value)
lockdata=(package/'pre-solution-boundary-lock.json').read_bytes();lock=json.loads(lockdata)
check('lock_exact_requested_phase',sha(lockdata)=='c0196c6806961a084f6474809e7ac0d60019ae8433455bb2775465329a0a694e')
check('no_Solution_before_review',not (package/'Solution.lean').exists() and not lock['solution_exists'])
for item in lock['copies']:
 s=(root/item['source']).read_bytes();d=(root/item['destination']).read_bytes()
 check('exact_copy:'+item['module'],s==d and sha(s)==item['source_sha256']==item['destination_sha256'])
 records[item['destination']]=sha(d)
for name,h in lock['exports'].items():
 data=(package/name).read_bytes();check('exact_locked_export:'+name,sha(data)==h)
 dest=out/'pre-solution-snapshot'/(name+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);records[str((package/name).relative_to(root))]=sha(data)
live=(package/'NLA/Statements/PF05.lean').read_bytes();frozen=(package/'Reviewed/PF05.lean').read_bytes()
check('live_exact_shared',live==(root/'lean-statements/NLA/Statements/PF05.lean').read_bytes())
check('frozen_exact_shared',frozen==(root/'lean-statements/Reviewed/PF05.lean').read_bytes())
expected=b'/- Frozen statement boundary. Changes reopen independent review. -/\n'+live.replace(b'NLA.Statements.PF05',b'NLA.ReviewedStatements.PF05')
check('frozen_namespace_only_copy',frozen==expected)
challenge=(package/'Challenge.lean').read_text();identity=(package/'Identity.lean').read_text()
check('Challenge_only_deliberate_placeholder',len(re.findall(r'\bsorry\b',challenge))==1 and 'theorem target : NLA.Statements.PF05.Target := by' in challenge and not re.search(r'\baxiom\b',challenge))
check('Challenge_imports_only_live',re.findall(r'^import (.+)$',challenge,re.M)==['NLA.Statements.PF05'])
check('Identity_actual_rfl','NLA.Statements.PF05.Target = NLA.ReviewedStatements.PF05.Target := rfl' in identity and 'sorry' not in identity)
comp=json.loads((package/'comparator.json').read_text());check('Comparator_full_Target_only',comp=={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['NLA.PF05.target'],'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']})
lake=tomllib.loads((package/'lakefile.toml').read_text());check('Lake_pre_solution_default_only',lake['defaultTargets']==['Challenge','Identity'] and not any(x['name']=='Solution' for x in lake['lean_lib']))
check('Lake_immutable_direct_pins',{x['name']:(x['git'],x['rev']) for x in lake['require']}=={'mathlib':('https://github.com/leanprover-community/mathlib4.git','0df444a360eaa60ab8c11dca51a86af692955474'),'leancert':('https://github.com/alerad/leancert','621a43d7cf21f87872392a01e874f2f1dbddc926')})
check('Lean_pin',(package/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
manifest=json.loads((package/'lake-manifest.json').read_text());shared=json.loads((root/'lean-statements/lake-manifest.json').read_text());check('Manifest_same_package_pins',{p['name']:(p.get('url'),p['rev']) for p in manifest['packages']}=={p['name']:(p.get('url'),p['rev']) for p in shared['packages']})
check('closure_exactly_42',len(lock['copies'])==lock['actual_source_copies']==42 and lock['proof_modules']==40)
closure={x['module'] for x in lock['copies']};check('every_local_import_in_exact_copy_closure',all(i in closure for x in lock['copies'] for i in x['imports'] if i.startswith('NLA.')))
check('original_MD_exact_historical',(package/'ORIGINAL.md').read_bytes()==(root/'docs/lean/statements/PF-05/ORIGINAL.md').read_bytes())
check('numerical_spec_exact_historical',(package/'NUMERICAL_TARGETS.md').read_bytes()==(root/'docs/lean/statements/PF-05/NUMERICAL_TARGETS.md').read_bytes())
originals=['nonnegative-and-positive-factorizations/PF-05/README.md','nonnegative-and-positive-factorizations/PF-05/problem.tex','nonnegative-and-positive-factorizations/PF-05/problem.pdf','references/colbrook-factorization-2026-09-11/manuscripts/PF-05_rigidity_with_zeros.tex','references/colbrook-factorization-2026-09-11/manuscripts/PF-05_rigidity_with_zeros.pdf','problem_ids.json']
for name in originals:
 data=(root/name).read_bytes();old=subprocess.run(['git','show','HEAD:'+name],cwd=root,capture_output=True,check=True).stdout
 check('original_unchanged_from_HEAD:'+name,data==old);records[name]=sha(data)
check('canonical_ID_retained',json.loads((root/'problem_ids.json').read_text())['PF-05']=='nonnegative-and-positive-factorizations/PF-05/README.md')
(out/'pre-solution-snapshot/pre-solution-boundary-lock.json.txt').write_bytes(lockdata)
for name in ['ORIGINAL.md','NUMERICAL_TARGETS.md','README.md']:
 (out/'pre-solution-snapshot'/(name+'.txt')).write_bytes((package/name).read_bytes())
result={'phase':'pre-Solution; historical phase must not be reinterpreted as final package config','reviewer':'/root/solved_inventory','checks':checks,'records_sha256':records,'boundary_lock_sha256':sha(lockdata),'passed':all(checks.values()),'authoritative_linux_comparator':False,'scope':'canonical copy/export/config identity and original preservation only; proof authorship excluded; fresh elaboration separate'}
(out/'boundary-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'passed':result['passed'],'checks':len(checks),'failed':[k for k,v in checks.items() if not v]},indent=2));raise SystemExit(0 if result['passed'] else 1)

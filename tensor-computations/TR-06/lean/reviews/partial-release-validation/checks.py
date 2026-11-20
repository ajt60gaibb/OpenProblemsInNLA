from pathlib import Path
import sys,subprocess,json,hashlib,yaml,jsonschema
root=Path('/Users/ajt253/.codex/worktrees/tr06-formal-verification/OpenProblemsInNLA');project=root/'tensor-computations/TR-06/lean';out=Path('/private/tmp/tr06-partial-release-validation');out.mkdir(exist_ok=True)
r={'scope':'Incomplete draft publication checks; not complete problem verification','checks':[]}
cmds=[
[sys.executable,'-m','unittest','discover','-s','tests','-p','test_lean_verification.py','-v'],
[sys.executable,'-m','unittest','discover','-s','tools/lean','-p','test_*.py','-v'],
[sys.executable,'-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'],
[sys.executable,'tools/validate_problem_ids.py','--base-ref','origin/main'],
['git','diff','--check']]
for i,cmd in enumerate(cmds):
 p=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);f=out/f'check-{i}.log';f.write_text(p.stdout);r['checks'].append({'command':cmd,'exit_code':p.returncode,'log':f.name});assert p.returncode==0,p.stdout
print('Infrastructure/ID tests, ID validator, whitespace checks pass.')
m=yaml.safe_load((project/'formalization.yaml').read_text());schema=json.loads((root/'docs/lean/schema/v0.4.schema.json').read_text());jsonschema.validate(m,schema);r['metadata_schema']='pass'
assert m['status']['complete_problem_verified'] is False and m['status']['main_results']==[]
p=subprocess.run([sys.executable,'tools/lean/validate_manifest.py','tensor-computations/TR-06/lean'],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'expected-complete-gate-rejection.log').write_text(p.stdout)
assert p.returncode!=0 and 'Completed project metadata must report zero proof-development sorries' in p.stdout
r['complete_gate']='expected rejection: incomplete metadata';r['comparator_run']=False;r['authoritative_linux_run']=False
frozen=json.loads((project/'reviews/statement-freeze.json').read_text());r['frozen_boundary']={}
for name,h in frozen['source_hashes'].items():
 actual=hashlib.sha256((project/name).read_bytes()).hexdigest();assert h==actual,(name,h,actual);r['frozen_boundary'][name]=actual
protected=['problem_ids.json','tensor-computations/TR-06/README.md','tensor-computations/TR-06/problem.tex','tensor-computations/TR-06/problem.pdf','references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md']
r['protected_files']={}
for name in protected:
 base=subprocess.check_output(['git','show',f'origin/main:{name}'],cwd=root);data=(root/name).read_bytes();assert data==base,name;r['protected_files'][name]=hashlib.sha256(data).hexdigest()
assert not (project/'Solution.lean').exists()
assert sum(line.strip()=='sorry' for line in (project/'Challenge.lean').read_text().splitlines())==10
r['challenge_placeholders']=10;r['completed_problem_targets']=0
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('Schema and frozen/protected sources pass; completed-project gate rejects as expected.')

"""Read-only expected-input inventory; this is not a Linux audit verdict."""
from pathlib import Path
import hashlib,json,subprocess
out=Path(__file__).resolve().parent;repo=Path('/tmp/nla-lean-mi22-worktree');project='matrix-inequalities-and-norms/MI-22/lean';commit='26f526cf8b6232af9528b30616076dc7a2c66ac6'
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
assert git('rev-parse','HEAD').decode().strip()==commit
assert not git('status','--short')
paths=git('ls-tree','-r','--name-only',commit,'--',project).decode().splitlines();assert len(paths)==177
files={}
for name in paths:
 data=git('show',commit+':'+name);assert (repo/name).read_bytes()==data
 files[name[len(project)+1:]]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
freeze=json.loads((repo/project/'verification/proof-freeze.json').read_text())
pack=json.loads((repo/project/'verification/root-linux-packaging.json').read_text())
for name,r in freeze['files'].items():
 target=pack['historical_README_archive'] if name=='README.md' else name
 assert files[target]==r,(name,target)
for name,h in pack['independent_review_hashes'].items():assert files['reviews/'+name]['sha256']==h
conf=json.loads((repo/project/'comparator.json').read_text());assert conf['theorem_names']==pack['exports'];assert len(conf['theorem_names'])==8
assert conf['definition_names']==[] and conf['permitted_axioms']==['propext','Classical.choice','Quot.sound']
record={'status':'Expected input identities PASS; actual Linux result and audit pending','commit':commit,'run':34720684925,'project':project,'tracked_input_count':len(files),'all_worktree_inputs_match_commit':True,'preserved_nonREADME_proof_freeze_files':len(freeze['files'])-1,'unchanged_report_hashes':pack['independent_review_hashes'],'config':conf,'input_files':files}
(out/'preflight.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k] for k in ['status','tracked_input_count','preserved_nonREADME_proof_freeze_files']}))

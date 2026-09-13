"""Bind the now-committed IV-06 candidate before interpreting any Linux result."""
from pathlib import Path
import hashlib, json, subprocess

out=Path(__file__).resolve().parent
config=json.loads((out/'run-config.json').read_text())
repo=Path('/tmp/nla-lean-iv06-worktree')
project=repo/config['project']; commit=config['commit']
git=lambda *args:subprocess.check_output(['git','-C',str(repo),*args])
sha=lambda b:hashlib.sha256(b).hexdigest()
assert git('rev-parse','HEAD').decode().strip()==commit
assert not git('status','--porcelain=v1').strip()
tree=git('ls-tree','-r','--name-only',commit,'--',config['project']).decode().splitlines()
assert len(tree)==config['expected_candidate_inputs']
files={}
for path in tree:
    data=git('show',commit+':'+path)
    assert data==(repo/path).read_bytes(),path
    rel=path[len(config['project'])+1:]
    files[rel]={'bytes':len(data),'sha256':sha(data),
                'git_blob':git('rev-parse',commit+':'+path).decode().strip()}
root_manifest=project/'verification/linux-candidate-2026-09-12/ROOT-EVIDENCE-MANIFEST.json'
assert sha(root_manifest.read_bytes())==config['root_candidate_manifest_sha256']
record=json.loads(root_manifest.read_text())
actual={p.relative_to(root_manifest.parent).as_posix() for p in root_manifest.parent.rglob('*')
        if p.is_file() and p!=root_manifest}
assert actual==set(record['files']) and len(actual)==record['file_count']
for rel,expected in record['files'].items():
    data=(root_manifest.parent/rel).read_bytes()
    assert len(data)==expected['bytes'] and sha(data)==expected['sha256'],rel
for rel,expected in record['metadata_relative_to_project'].items():
    assert files[rel]['sha256']==expected,rel
root_check=(root_manifest.parent/'ROOT-CHECKS.json').read_bytes()
assert sha(root_check)==config['root_candidate_acceptance_sha256']
assert json.loads(root_check)['status']=='APPROVE exact Linux candidate; actual Linux pending'
commit_data=git('cat-file','commit',commit)
for role in ['author','committer']:
    line=next(x for x in commit_data.decode().splitlines() if x.startswith(role+' '))
    assert line.startswith(role+' George Stepaniants <> ')
bound={'status':'Exact committed candidate identity PASS; Linux outcome remains pending',
       'commit':commit,'project':config['project'],'complete_tracked_inputs':len(files),
       'root_candidate_manifest_sha256':sha(root_manifest.read_bytes()),
       'root_candidate_acceptance_sha256':sha(root_check),
       'root_candidate_evidence_count':len(actual),'both_commit_emails_empty':True,
       'files':files}
(out/'committed-candidate.json').write_text(json.dumps(bound,indent=2)+'\n')
print(json.dumps({k:bound[k] for k in ['status','commit','complete_tracked_inputs','root_candidate_evidence_count','both_commit_emails_empty']}))

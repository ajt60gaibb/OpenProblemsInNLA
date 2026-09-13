"""Retain one exact RA09 candidate source snapshot from committed Git blobs.
No dependency object, artifact redownload, or proof rebuild is involved.
"""
from pathlib import Path
import hashlib,json,subprocess
O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
B=json.loads((O/'source-binding.json').read_text())
W=Path(C['worktree']).resolve()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=W).decode().strip()==C['commit']
for n,r in B['candidate_inputs'].items():
    b=subprocess.check_output(['git','cat-file','blob',r['git_blob']],cwd=W)
    assert sha(b)==r['sha256'] and len(b)==r['bytes']
    assert b==(W/C['project']/n).read_bytes()
    p=O/'source'/C['project']/n;p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_bytes()==b,n
    else:p.write_bytes(b)
root=O/'source'/C['project']
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(B['candidate_inputs'])
out={'result':'PASS exact original committed source snapshot',
 'candidate':C['commit'],'path':'source/'+C['project'],'input_count':len(B['candidate_inputs']),
 'bytes':sum(r['bytes'] for r in B['candidate_inputs'].values()),
 'all_Git_blobs_live_candidate_and_retained_bytes_identical':True,
 'nested_manifests_retained':sum(Path(n).name=='EVIDENCE-MANIFEST.json' for n in B['candidate_inputs']),
 'snapshot_purpose':'Retain one immutable full source snapshot so later publication wrapper changes preserve exact evidence.',
 'dependency_objects_copied':False,'artifacts_redownloaded':False}
(O/'candidate-snapshot.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

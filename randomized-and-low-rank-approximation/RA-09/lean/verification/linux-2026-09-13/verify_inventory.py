"""Read-only complete operational seal check against original candidate Git blobs.

Default checks immutable retained input bytes; --live-candidate additionally
requires the current worktree's candidate files to remain identical. This
keeps original evidence checkable after ordinary publication wrapper updates.
No network, Lean, dependency, or Git mutation operation is performed.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
OUTER=O/'EVIDENCE-MANIFEST.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def files():
    out=[]
    for p in O.rglob('*'):
        assert not p.is_symlink(),p
        if p.is_file() and p!=OUTER:out.append(p)
    return sorted(out)
def candidate(live=False):
    b=json.loads((O/'source-binding.json').read_text())
    p=O/'source'/C['project'];w=Path(C['worktree'])
    tree=subprocess.check_output(['git','ls-tree','-r','-z',C['commit'],'--',C['project']],cwd=w)
    actual={}
    for e in tree.split(b'\0'):
        if not e:continue
        header,name=e.split(b'\t',1);mode,kind,blob=header.decode().split()
        assert kind=='blob' and mode in ['100644','100755']
        rel=str(Path(name.decode()).relative_to(C['project']))
        actual[rel]=blob
    assert set(actual)==set(b['candidate_inputs'])
    assert {str(f.relative_to(p)) for f in p.rglob('*') if f.is_file()}==set(actual)
    assert len(actual)==524
    for n,r in b['candidate_inputs'].items():
        assert actual[n]==r['git_blob']
        data=subprocess.check_output(['git','cat-file','blob',r['git_blob']],cwd=w)
        assert hashlib.sha256(data).hexdigest()==r['sha256'] and len(data)==r['bytes']
        assert (p/n).read_bytes()==data,n
        if live:assert (w/C['project']/n).read_bytes()==data,n
    return len(actual)
def verify(live=False):
    r=json.loads(OUTER.read_text())
    assert r['exact_self_exclusion']=='EVIDENCE-MANIFEST.json'
    assert set(r['files'])=={str(f.relative_to(O)) for f in files()}
    assert r['file_count']==len(r['files']) and r['total_including_outer']==len(r['files'])+1
    for n,item in r['files'].items():
        p=O/n;assert p.resolve().is_relative_to(O)
        assert sha(p)==item['sha256'] and p.stat().st_size==item['bytes'],n
    nested=sum(Path(n).name=='EVIDENCE-MANIFEST.json' for n in r['files'])
    assert nested==r['nested_same_basename_manifests_included']==13
    assert sha(O/'OPERATIONAL-REVIEW.md')==r['operational_review_sha256']
    assert candidate(live)==r['original_candidate_inputs_preserved']==524
    return {'verdict':'PASS exact complete operational inventory and all original committed candidate blobs',
      'bound_files':r['file_count'],'including_outer':r['total_including_outer'],'nested_manifests':nested,
      'manifest_sha256':sha(OUTER),'report_sha256':r['operational_review_sha256'],
      'actual_Linux_run':C['run'],'actual_Linux_Comparator':'accepted','coordinator_acceptance_publication':'pending'}
if __name__=='__main__':
    print(json.dumps(verify('--live-candidate' in sys.argv),indent=2))

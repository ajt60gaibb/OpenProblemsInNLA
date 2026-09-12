"""Independent root publication check; no additional mathematical or Linux run."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import yaml

repo = Path(__file__).resolve().parents[5]
pub = Path(__file__).resolve().parent
prefix = 'matrix-inequalities-and-norms/MI-23/lean/'
project = repo/prefix
verified = '17194f9060609acae429e14d3dc3c4562b84f2bd'
upstream = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
integration = 'fa51531e78809904df9a840c7a0bd1fbf9ed7391'
sha = lambda b: hashlib.sha256(b).hexdigest()

def git(*args):
    return subprocess.check_output(['git',*args],cwd=repo)

def blob(rev,path):
    return git('show',rev+':'+path)

assert git('rev-parse','HEAD').decode().strip()==integration
assert git('show','-s','--format=%ae%x00%ce',integration).strip(b'\n')==b'\0'
for ancestor in [verified,upstream]:
    subprocess.run(['git','merge-base','--is-ancestor',ancestor,integration],cwd=repo,check=True)

linux = project/'verification/linux-2026-09-12'
receipt_path = linux/'artifacts/lean-MI-23/verify-20260912T202130Z-4146/result.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['repository_commit']==verified and receipt['project']==prefix.rstrip('/')
assert receipt['config']==json.loads((project/'comparator.json').read_text())
assert len(receipt['input_sha256'])==133
preserved = {}
for rel,expected in receipt['input_sha256'].items():
    assert sha(blob(verified,prefix+rel))==expected,rel
    if rel not in ['README.md','formalization.yaml']:
        assert sha((project/rel).read_bytes())==expected,rel
        preserved[rel]=expected
assert len(preserved)==131

outer=linux/'EVIDENCE-MANIFEST.json'
assert sha(outer.read_bytes())=='9d75182ae4c4afa2e218490ec13406096b0ff3f288d79a98584e7045fc63e37e'
manifest=json.loads(outer.read_text())['files']
assert len(manifest)==248
for rel,item in manifest.items():
    data=(linux/rel).read_bytes()
    assert sha(data)==item['sha256'] and len(data)==item['bytes'],rel
all_evidence={str(f.relative_to(linux)):sha(f.read_bytes()) for f in linux.rglob('*') if f.is_file()}
assert len(all_evidence)==249
assert set(all_evidence)-set(manifest)=={'EVIDENCE-MANIFEST.json'}
assert sha((linux/'OPERATIONAL-REVIEW.md').read_bytes())=='1139c7f2f075021479dbd4501e2530859e9724e87ba52e7551970e38882eaeec'

registry=(repo/'problem_ids.json').read_bytes()
assert registry==blob(upstream,'problem_ids.json')
ids=json.loads(registry);assert len(ids)==217
counts=Counter()
for code,rel in ids.items():
    data=(repo/rel).read_bytes()
    counts[re.search(rb'\*\*Status:\*\* ([^\r\n]+)',data).group(1).decode().strip()]+=1
    if code!='MI-23':
        assert data==blob(upstream,rel),code
    else:
        marker=b'## Problem statement'
        assert data.split(marker,1)[1].strip()==blob(upstream,rel).split(marker,1)[1].strip()
        assert data.split(marker,1)[1].strip()==blob(verified,rel).split(marker,1)[1].strip()
assert counts=={'Lean verified':12,'Solved':78,'Open':55,'Partially resolved':72},counts

pub_names=['CATALOG.md','README.md','RESOLVED.md','matrix-inequalities-and-norms/README.md',
           'matrix-inequalities-and-norms/MI-23/README.md',
           'matrix-inequalities-and-norms/MI-23/problem.tex',
           'matrix-inequalities-and-norms/MI-23/problem.pdf',prefix+'README.md',prefix+'formalization.yaml']
other_files=0
for item in git('ls-tree','-r','-z',upstream).split(b'\0'):
    if not item: continue
    metadata,name=item.split(b'\t',1);rel=name.decode();mode,kind,oid=metadata.split()
    if rel in pub_names or rel.startswith(prefix): continue
    assert kind==b'blob' and mode in [b'100644',b'100755'],rel
    data=(repo/rel).read_bytes()
    local_oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest().encode()
    assert oid==local_oid,rel
    other_files+=1
assert other_files>4500,other_files
for subtree in ['tools','.github','docs/lean']:
    assert git('ls-tree','-r',upstream,'--',subtree)==git('ls-tree','-r',verified,'--',subtree)

old=yaml.safe_load(blob(verified,prefix+'formalization.yaml'))
new=yaml.safe_load((project/'formalization.yaml').read_text())
for key,subkey in [('status','scope'),('review','status'),('review','notes')]:
    old[key].pop(subkey);new[key].pop(subkey)
for key in ['status','note']:
    old['review']['linux_verification'].pop(key);new['review']['linux_verification'].pop(key)
assert old==new,'Unreviewed semantic metadata change'
for rel in [prefix+'README.md',prefix+'formalization.yaml','matrix-inequalities-and-norms/MI-23/README.md']:
    text=(repo/rel).read_text();flat=' '.join(text.split())
    assert 'George Stepaniants' in flat and 'Department of Computing and Mathematical Sciences' in flat
    assert 'California Institute of Technology' in flat and 'Matthew J. Colbrook' in flat
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}',text)
assert 'MI-23' in (repo/'RESOLVED.md').read_text() and 'formalization by George Stepaniants' in (repo/'RESOLVED.md').read_text()
assert 'Ran 17 tests' in (pub/'id-tests.log').read_text()
assert (pub/'id-tests.log').read_text().rstrip().endswith('OK')
for name in ['final-checks.json']:
    checks=json.loads((pub/name).read_text())
    assert all(x['exit_code']==0 for x in checks),name
assert sha((repo/'matrix-inequalities-and-norms/MI-23/problem.pdf').read_bytes())=='a0a82bc6e6ecd6e316b50b1632a45bde5b570838620022ed97a1c4cb7929ace8'
commands=[]
for cmd in [['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],
            ['python3','tools/validate_problem_ids.py','--base-ref',upstream],
            ['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py',prefix.rstrip('/')],
            ['git','diff','--check']]:
    r=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    commands.append(dict(command=cmd,exit_code=r.returncode,output=r.stdout.decode()))
    assert r.returncode==0,r.stdout
report=dict(status='PASS',verified_revision=verified,linux_run=34716784038,integration_commit=integration,
    integrated_upstream=upstream,blank_integration_emails=True,verified_input_count=133,
    unchanged_non_wrapper_inputs=preserved,all_retained_linux_files=all_evidence,
    exact_evidence_count=249,outer_manifest_bound_count=248,outer_manifest_includes_nested=True,
    other_canonical_pages_preserved=216,permanent_IDs=217,all_other_base_files_preserved=other_files,
    branch_counts=dict(counts),commands=commands,
    publication_sha256={r:sha((repo/r).read_bytes()) for r in pub_names},
    pdf_review='Root independently visually inspected all 3 final pages: all text, formulas, code, links and credits readable, with no clipping or missing glyphs.',
    proof_rebuild='Not repeated: actual proof, settings, pins and prior reviews unchanged from the completed Linux run.')
(pub/'ROOT-CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['unchanged_non_wrapper_inputs','all_retained_linux_files','commands','publication_sha256']},indent=2))

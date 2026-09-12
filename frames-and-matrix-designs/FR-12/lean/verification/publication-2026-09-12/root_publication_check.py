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
prefix = 'frames-and-matrix-designs/FR-12/lean/'
project = repo/prefix
verified = '3e20bae9a07b1a33db8fdfb18bdebb9e590071a9'
upstream = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
integration = '0a9f52a2ee8bf4d51e13a14099a566d649d4b453'
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
receipt_path = linux/'artifacts/lean-FR-12/verify-20260912T205219Z-4137/result.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['repository_commit']==verified and receipt['project']==prefix.rstrip('/')
assert receipt['config']==json.loads((project/'comparator.json').read_text())
assert len(receipt['input_sha256'])==137
preserved = {}
for rel,expected in receipt['input_sha256'].items():
    assert sha(blob(verified,prefix+rel))==expected,rel
    if rel not in ['README.md','formalization.yaml']:
        assert sha((project/rel).read_bytes())==expected,rel
        preserved[rel]=expected
assert len(preserved)==135

outer=linux/'EVIDENCE-MANIFEST.json'
assert sha(outer.read_bytes())=='a9dfe074bd299c6826ffe7367f30c5154cf58440a4f88071b8a61ff27eda8aa1'
manifest=json.loads(outer.read_text())['files']
assert len(manifest)==255
for rel,item in manifest.items():
    data=(linux/rel).read_bytes()
    assert sha(data)==item['sha256'] and len(data)==item['bytes'],rel
all_evidence={str(f.relative_to(linux)):sha(f.read_bytes()) for f in linux.rglob('*') if f.is_file()}
assert len(all_evidence)==256
assert set(all_evidence)-set(manifest)=={'EVIDENCE-MANIFEST.json'}
assert sha((linux/'OPERATIONAL-REVIEW.md').read_bytes())=='017e2a22ac88d153a311c7ef344fe0ac0b8d415f926d046da649e210585c53ac'

registry=(repo/'problem_ids.json').read_bytes()
assert registry==blob(upstream,'problem_ids.json')
ids=json.loads(registry);assert len(ids)==217
counts=Counter()
for code,rel in ids.items():
    data=(repo/rel).read_bytes()
    counts[re.search(rb'\*\*Status:\*\* ([^\r\n]+)',data).group(1).decode().strip()]+=1
    if code!='FR-12':
        assert data==blob(upstream,rel),code
    else:
        marker=b'## Statement'
        assert data.split(marker,1)[1].strip()==blob(upstream,rel).split(marker,1)[1].strip()
        assert data.split(marker,1)[1].strip()==blob(verified,rel).split(marker,1)[1].strip()
assert counts=={'Lean verified':12,'Solved':78,'Open':55,'Partially resolved':72},counts

pub_names=['CATALOG.md','README.md','RESOLVED.md','frames-and-matrix-designs/README.md',
           'frames-and-matrix-designs/FR-12/README.md',
           'frames-and-matrix-designs/FR-12/problem.tex',
           'frames-and-matrix-designs/FR-12/problem.pdf',prefix+'README.md',prefix+'formalization.yaml']
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
old['sources'][0].pop('note');new['sources'][0].pop('note')
assert old==new,'Unreviewed semantic metadata change'
for rel in [prefix+'README.md',prefix+'formalization.yaml','frames-and-matrix-designs/FR-12/README.md']:
    text=(repo/rel).read_text();flat=' '.join(text.split())
    assert 'George Stepaniants' in flat and 'Department of Computing and Mathematical Sciences' in flat
    assert 'California Institute of Technology' in flat and 'Ferber' in flat
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}',text)
assert 'FR-12' in (repo/'RESOLVED.md').read_text() and 'Mathematical proof and Lean formalization: George Stepaniants' in (repo/'RESOLVED.md').read_text()
assert 'Ran 17 tests' in (pub/'permanent-id-tests.log').read_text()
assert (pub/'permanent-id-tests.log').read_text().rstrip().endswith('OK')
for name in ['final-checks.json']:
    checks=json.loads((pub/name).read_text())
    assert all(x['exit_code']==0 for x in checks),name
assert sha((repo/'frames-and-matrix-designs/FR-12/problem.pdf').read_bytes())=='a3681bb459fb018f1935980032e0d7b4a522bd515c6e1c945fdec298e07ffe32'
outer_pub=pub/'EVIDENCE-MANIFEST.json'
assert sha(outer_pub.read_bytes())=='787127970e8b1bc7444afeb9066054bb10d1eaba0d391ad063147669a0591930'
pub_files=json.loads(outer_pub.read_text())['files']
assert len(pub_files)==31
for rel,value in pub_files.items():
    expected=value if isinstance(value,str) else value['sha256']
    assert sha((pub/rel).read_bytes())==expected,rel
commands=[]
for cmd in [['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],
            ['python3','tools/validate_problem_ids.py','--base-ref',upstream],
            ['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py',prefix.rstrip('/')],
            ['git','diff','--check']]:
    r=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    commands.append(dict(command=cmd,exit_code=r.returncode,output=r.stdout.decode()))
    assert r.returncode==0,r.stdout
report=dict(status='PASS',verified_revision=verified,linux_run=34718277411,integration_commit=integration,
    integrated_upstream=upstream,blank_integration_emails=True,verified_input_count=137,
    unchanged_non_wrapper_inputs=preserved,all_retained_linux_files=all_evidence,
    exact_evidence_count=256,outer_manifest_bound_count=255,outer_manifest_includes_nested=True,
    other_canonical_pages_preserved=216,permanent_IDs=217,all_other_base_files_preserved=other_files,
    branch_counts=dict(counts),commands=commands,
    publication_sha256={r:sha((repo/r).read_bytes()) for r in pub_names},
    pdf_review='Root independently visually inspected all 3 final pages: all text, formulas, code, links and credits readable, with no clipping or missing glyphs.',
    proof_rebuild='Not repeated: actual proof, settings, pins and prior reviews unchanged from the completed Linux run.')
(pub/'ROOT-CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['unchanged_non_wrapper_inputs','all_retained_linux_files','commands','publication_sha256']},indent=2))

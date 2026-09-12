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
prefix = 'matrix-inequalities-and-norms/MI-22/lean/'
project = repo/prefix
verified = '26f526cf8b6232af9528b30616076dc7a2c66ac6'
upstream = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
integration = '8826d6a27f3d2ede3aabe93cefa3d38e3dfebf2e'
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
receipt_path = linux/'artifacts/lean-MI-22/verify-20260912T214303Z-4163/result.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['repository_commit']==verified and receipt['project']==prefix.rstrip('/')
assert receipt['config']==json.loads((project/'comparator.json').read_text())
assert len(receipt['input_sha256'])==177
preserved = {}
for rel,expected in receipt['input_sha256'].items():
    assert sha(blob(verified,prefix+rel))==expected,rel
    if rel not in ['README.md','formalization.yaml']:
        assert sha((project/rel).read_bytes())==expected,rel
        preserved[rel]=expected
assert len(preserved)==175

outer=linux/'EVIDENCE-MANIFEST.json'
assert sha(outer.read_bytes())=='1247b0cb6deb563d8f32e05f0831432554e68b3536eef5f6b1abae6278a3c18a'
manifest=json.loads(outer.read_text())['files']
assert len(manifest)==303
for rel,item in manifest.items():
    data=(linux/rel).read_bytes()
    assert sha(data)==item['sha256'] and len(data)==item['bytes'],rel
all_evidence={str(f.relative_to(linux)):sha(f.read_bytes()) for f in linux.rglob('*') if f.is_file()}
assert len(all_evidence)==304
assert set(all_evidence)-set(manifest)=={'EVIDENCE-MANIFEST.json'}
assert sha((linux/'OPERATIONAL-REVIEW.md').read_bytes())=='792d6d49b4a4c8fae6fb489c93c55269c18b7b58adfa640ab2568a0b0c8f9e9e'

registry=(repo/'problem_ids.json').read_bytes()
assert registry==blob(upstream,'problem_ids.json')
ids=json.loads(registry);assert len(ids)==217
counts=Counter()
for code,rel in ids.items():
    data=(repo/rel).read_bytes()
    counts[re.search(rb'\*\*Status:\*\* ([^\r\n]+)',data).group(1).decode().strip()]+=1
    if code!='MI-22':
        assert data==blob(upstream,rel),code
    else:
        marker=b'## Problem statement'
        assert data.split(marker,1)[1].strip()==blob(upstream,rel).split(marker,1)[1].strip()
        assert data.split(marker,1)[1].strip()==blob(verified,rel).split(marker,1)[1].strip()
assert counts=={'Lean verified':12,'Solved':78,'Open':55,'Partially resolved':72},counts

pub_names=['CATALOG.md','README.md','RESOLVED.md','matrix-inequalities-and-norms/README.md',
           'matrix-inequalities-and-norms/MI-22/README.md',
           'matrix-inequalities-and-norms/MI-22/problem.tex',
           'matrix-inequalities-and-norms/MI-22/problem.pdf',prefix+'README.md',prefix+'formalization.yaml']
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
old_linux=old['review'].pop('linux_verification')
new_linux=new['review'].pop('linux_verification')
assert old_linux['status']=='pending' and new_linux['status']=='passed'
assert new_linux['commit']==verified and new_linux['run_id']==34720684925
assert new_linux['theorem_count']==8 and new_linux['verified_input_count']==177
assert new_linux['definition_exceptions']==[]
assert set(new_linux['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert new_linux['bound_evidence_files']==303 and new_linux['total_evidence_files']==304
assert new_linux['operational_review_sha256']==sha((linux/'OPERATIONAL-REVIEW.md').read_bytes())
assert new_linux['evidence_manifest_sha256']==sha(outer.read_bytes())
assert (project/new_linux['receipt']).resolve()==receipt_path.resolve()
old_reviewers=old['review'].pop('reviewers');new_reviewers=new['review'].pop('reviewers')
assert new_reviewers[:2]==old_reviewers and len(new_reviewers)==3
assert '/root/formal_review_standards: independent operational referee' in new_reviewers[2]
assert old==new,'Unreviewed semantic metadata change'
assert sha((project/'formalization.yaml').read_bytes())=='fab68766e10e7171ccea7b7cb8d6bf4f1ad510149696bbc23251a4bc6461db42'
assert sha((project/'README.md').read_bytes())=='9ef01cbfcc65eb87aede6ad09b5a8a805eef3642d25e61cc372f6dcb2f2a2a8c'

prepared_path=pub/'EVIDENCE-MANIFEST.json'
assert sha(prepared_path.read_bytes())=='456ae3f3c9a3fa9330ba58912309a263a4395e60a6219d4f13e9c4c163a44211'
prepared=json.loads(prepared_path.read_text());assert len(prepared['files'])==27
for rel,item in prepared['files'].items():
    data=(pub/rel).read_bytes()
    assert sha(data)==item['sha256'] and len(data)==item['bytes'],rel
for rel,item in prepared['current_publication_outputs'].items():
    data=(repo/rel).read_bytes()
    assert sha(data)==item['sha256'] and len(data)==item['bytes'],rel

for rel in [prefix+'README.md',prefix+'formalization.yaml','matrix-inequalities-and-norms/MI-22/README.md']:
    text=(repo/rel).read_text();flat=' '.join(text.split())
    assert 'George Stepaniants' in flat and 'Department of Computing and Mathematical Sciences' in flat
    assert 'California Institute of Technology' in flat and 'Matthew J. Colbrook' in flat
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}',text)
assert 'MI-22' in (repo/'RESOLVED.md').read_text() and '**Lean formalization:** George Stepaniants' in (repo/'RESOLVED.md').read_text()
assert 'Ran 17 tests' in (pub/'id-tests.log').read_text()
assert (pub/'id-tests.log').read_text().rstrip().endswith('OK')
for name in ['final-checks.json']:
    checks=json.loads((pub/name).read_text())
    assert all(x['exit_code']==0 for x in checks),name
assert sha((repo/'matrix-inequalities-and-norms/MI-22/problem.pdf').read_bytes())=='0883c8201253e6e7f6ec3a8c7f65485eb459a3f8119b3d5d18cae9a2bf5356ea'
commands=[]
for cmd in [['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],
            ['python3','tools/validate_problem_ids.py','--base-ref',upstream],
            ['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py',prefix.rstrip('/')],
            ['git','diff','--check']]:
    r=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    commands.append(dict(command=cmd,exit_code=r.returncode,output=r.stdout.decode()))
    assert r.returncode==0,r.stdout
report=dict(status='PASS',verified_revision=verified,linux_run=34720684925,integration_commit=integration,
    integrated_upstream=upstream,blank_integration_emails=True,verified_input_count=177,
    unchanged_non_wrapper_inputs=preserved,all_retained_linux_files=all_evidence,
    exact_evidence_count=304,outer_manifest_bound_count=303,outer_manifest_includes_nested=True,
    other_canonical_pages_preserved=216,permanent_IDs=217,all_other_base_files_preserved=other_files,
    branch_counts=dict(counts),commands=commands,
    publication_sha256={r:sha((repo/r).read_bytes()) for r in pub_names},
    pdf_review='Root independently visually inspected both final pages: all text, formulas, code, links and credits readable, with no clipping or missing glyphs.',
    proof_rebuild='Not repeated: actual proof, settings, pins and prior reviews unchanged from the completed Linux run.')
(pub/'ROOT-CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['unchanged_non_wrapper_inputs','all_retained_linux_files','commands','publication_sha256']},indent=2))
